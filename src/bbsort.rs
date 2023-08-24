
// pub mod vagraph;
use crate::vagraph::vag::*;

// generic functions

use std::fmt::{Debug, Display, LowerHex};
use std::hash::Hash;
use std::default::Default;
use std::collections::HashMap;
use std::cmp::*;

use petgraph::visit::{IntoNodeIdentifiers, IntoNeighbors, NodeIndexable, IntoNeighborsDirected, GraphBase};

use kendalls::tau_b;


// no restrictions on NodeId, EdgeId, etc here -> all goes to VAG

pub fn to_vag<G>(g: G, entry: G::NodeId) -> Result<VirtualAddressGraph<G::NodeId>, SortError> 
    where
        G:  IntoNodeIdentifiers + IntoNeighbors + NodeIndexable + IntoNeighborsDirected +
            NodeWeight<Node = G::NodeId>,
        <G as GraphBase>::NodeId: Copy + Eq + Debug + Display + Hash + Ord + LowerHex,
{
    // if the given graph is empty, then return error
    if g.node_identifiers().count() == 0 { 
        return Err(SortError::EmptyGraph);
    }

    // if the given entry address is not a node of the graph, then return error
    if !g.node_identifiers().any(|x| x == entry) {
        return Err(SortError::InvalidInitialAddress);
    }

    let mut nodes: HashMap<Vertex<G::NodeId>, NoInstrBasicBlock<G::NodeId>> = HashMap::new();

    // going over all the vertices of the given input graph 
    // we collect the relevant data in a hashmap, which will be used later in the VAGraph instance
    for block in g.node_identifiers() {
        nodes.insert( 
            Vertex::Id(block),
            NoInstrBasicBlock::<G::NodeId>::new(
                Vertex::Id(block), 
                g.weight(block), 
                g.neighbors_directed(block, petgraph::Direction::Incoming).map(Vertex::Id).collect(),
                g.neighbors_directed(block, petgraph::Direction::Outgoing).map(Vertex::Id).collect(),
                g.neighbors_directed(block, petgraph::Direction::Incoming).count(),
            )
        );
    }

    let mut vag: VirtualAddressGraph<G::NodeId> = VirtualAddressGraph::new(
        Vertex::Id(entry),
        nodes,
    );

    // deleting the outging edges - whenever we found one: print out !
    let outgoing_edges = vag.erase_outgoing_edges();
    println!("the following edges leave the graph, hence deleted:");
    for (s,t) in outgoing_edges {
        println!("{:x} --> {:x}", s, t);
    }

    Ok(vag)

}


pub fn bbsort<G>(g: G, entry: G::NodeId) -> Result<Vec<G::NodeId>, SortError> 
    where
        G:  IntoNodeIdentifiers + IntoNeighbors + NodeIndexable + IntoNeighborsDirected + 
            NodeWeight<Node = G::NodeId>,
        <G as GraphBase>::NodeId: Copy + Eq + Debug + Display + Hash + Ord + LowerHex, 
{

    // reading and converting the data (with error propagation)
    let vag = to_vag(g, entry)?;

    // if there exists a node which we can not reach from entry -> error
    let unreachable = vag.unreachable_from_start();
    if !unreachable.is_empty() {
        println!("from the start: {:x}, the following nodes are not reachable:", entry);
        for id in unreachable {
            println!("{:x}", id.id().unwrap());
        }
        return Err(SortError::UnreachableNodes);
    }

    let topsort = vag.weighted_order();
    Ok(topsort)

}


// cost of given order 
pub fn cost<G>(g: G, entry: G::NodeId, order: &[G::NodeId]) -> (usize, bool)
    where
        G:  IntoNodeIdentifiers + IntoNeighbors + NodeIndexable + IntoNeighborsDirected +
        NodeWeight<Node = G::NodeId>,
    <G as GraphBase>::NodeId: Copy + Eq + Debug + Display + Hash + Ord + LowerHex + Default,
{
    // TODO: what if the input is bad again ?
    let vag: VirtualAddressGraph<G::NodeId> = to_vag(g, entry).unwrap();

    let mut initial_order: Vec<G::NodeId> = Vec::new();
    for node in vag.nodes().keys() {
        initial_order.push(node.id().unwrap());
    }
    
    // original order = ascending ids
    initial_order.sort();

    println!("starting block's address: {:x}", vag.address().id().unwrap());

    // TODO: legit error handling
    match initial_order.len().cmp(&order.len()) {
        Ordering::Less => { panic!("there were less nodes originally") }
        Ordering::Greater => { panic!("some nodes are missing from the order") }
        Ordering::Equal => (),
    }

    for i in 0..initial_order.len() {
        println!("{:x}, {:x}", initial_order[i], order[i]);
    }

    let kendall_tau = tau_b(&initial_order, order).unwrap().0;
    let original_cost: usize = vag.cost_of_order(initial_order);
    let sorted_cost: usize = vag.cost_of_order(order.to_vec());

    println!("kendall tau: {:#?}", kendall_tau);
    println!("cost of original order: {}", original_cost);
    println!("cost of topological sort: {} \n", sorted_cost);

    (sorted_cost, original_cost >= sorted_cost)
}





#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn empty_graph() {
        let entry: Vertex<u64> = Vertex::Id(0x0);
        let vag: VirtualAddressGraph<u64> = VirtualAddressGraph::new(entry, HashMap::new());
        assert_eq!(to_vag(&vag, entry).is_err_and(|x| x ==  SortError::EmptyGraph), true);       
    }

    #[test]
    fn not_connected() {

        let address: Vertex<u64> = Vertex::Id(0x0);
        let mut nodes: HashMap<Vertex<u64>, NoInstrBasicBlock<u64>> = HashMap::new();

        nodes.insert(
            Vertex::Id(0x0),
            NoInstrBasicBlock::new(
                Vertex::Id(0x0),
                1,
                std::collections::HashSet::<Vertex<u64>>::new(),
                std::collections::HashSet::<Vertex<u64>>::new(),
                0
            )
        );

        nodes.insert(
            Vertex::Id(0x1),
            NoInstrBasicBlock::new(
                Vertex::Id(0x1),
                10,
                std::collections::HashSet::<Vertex<u64>>::new(),
                std::collections::HashSet::<Vertex<u64>>::new(),
                0
            )
        );

        let vag: VirtualAddressGraph<u64> = VirtualAddressGraph::new(
            address,
            nodes
        );

        let vag = to_vag(&vag, address).unwrap();
        let result = bbsort(&vag, Vertex::Id(address));

        assert_eq!(result.is_err_and(|x| x ==  SortError::UnreachableNodes), true);  

    }


    #[test]
    fn invalid_entry_address() {
        let address: Vertex<u64> = Vertex::Id(0x3);
        let mut nodes: HashMap<Vertex<u64>, NoInstrBasicBlock<u64>> = HashMap::new();

        nodes.insert(
            Vertex::Id(0x0),
            NoInstrBasicBlock::new(
                Vertex::Id(0x0),
                1,
                std::collections::HashSet::<Vertex<u64>>::new(),
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x1), Vertex::Id(0x2)]),
                0
            )
        );

        nodes.insert(
            Vertex::Id(0x1),
            NoInstrBasicBlock::new(
                Vertex::Id(0x1),
                10,
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x1)]),
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x2)]),
                1
            )
        );

        nodes.insert(
            Vertex::Id(0x2),
            NoInstrBasicBlock::new(
                Vertex::Id(0x2),
                5,
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x0), Vertex::Id(0x1)]),
                std::collections::HashSet::<Vertex<u64>>::new(),
                2
            )
        );

        let vag: VirtualAddressGraph<u64> = VirtualAddressGraph::new(
            address,
            nodes
        );

        assert_eq!(to_vag(&vag, address).is_err_and(|x| x ==  SortError::InvalidInitialAddress), true);

    }


    #[test]
    fn filtered_targets_two_nodes() {

        let address: Vertex<u64> = Vertex::Id(0x0);
        let mut nodes: HashMap<Vertex<u64>, NoInstrBasicBlock<u64>> = HashMap::new();

        nodes.insert(
            Vertex::Id(0x0),
            NoInstrBasicBlock::new(
                Vertex::Id(0x0),
                1,
                std::collections::HashSet::<Vertex<u64>>::new(),
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x1)]),
                0
            )
        );

        nodes.insert(
            Vertex::Id(0x1),
            NoInstrBasicBlock::new(
                Vertex::Id(0x1),
                10,
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x0)]),
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x2)]),
                0
            )
        );

        let vag: VirtualAddressGraph<u64> = VirtualAddressGraph::new(
            address,
            nodes
        );

        let out_vag = to_vag(&vag, address).unwrap();

        assert_ne!(out_vag.node_at_target(Vertex::Id(Vertex::Id(0x1))).targets().len(), vag.node_at_target(Vertex::Id(0x1)).targets().len());
        assert_eq!(out_vag.node_at_target(Vertex::Id(Vertex::Id(0x1))).targets().len(), 0);

    }


    #[test]
    fn filtered_targets_three_nodes_multiple_phantom_edges() {

        let address: Vertex<u64> = Vertex::Id(0x0);
        let mut nodes: HashMap<Vertex<u64>, NoInstrBasicBlock<u64>> = HashMap::new();

        nodes.insert(
            Vertex::Id(0x0),
            NoInstrBasicBlock::new(
                Vertex::Id(0x0),
                1,
                std::collections::HashSet::<Vertex<u64>>::new(),
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x1), Vertex::Id(0x2), Vertex::Id(0x6)]),
                0
            )
        );

        nodes.insert(
            Vertex::Id(0x1),
            NoInstrBasicBlock::new(
                Vertex::Id(0x1),
                10,
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x1)]),
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x2), Vertex::Id(0x7), Vertex::Id(0x9)]),
                1
            )
        );

        nodes.insert(
            Vertex::Id(0x2),
            NoInstrBasicBlock::new(
                Vertex::Id(0x2),
                5,
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x0), Vertex::Id(0x1)]),
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x6), Vertex::Id(0x7)]),
                2
            )
        );

        let vag: VirtualAddressGraph<u64> = VirtualAddressGraph::new(
            address,
            nodes
        );

        let out_vag = to_vag(&vag, address).unwrap();

        assert_ne!(out_vag.node_at_target(Vertex::Id(Vertex::Id(0x0))).targets().len(), vag.node_at_target(Vertex::Id(0x0)).targets().len());
        assert_ne!(out_vag.node_at_target(Vertex::Id(Vertex::Id(0x1))).targets().len(), vag.node_at_target(Vertex::Id(0x1)).targets().len());
        assert_ne!(out_vag.node_at_target(Vertex::Id(Vertex::Id(0x2))).targets().len(), vag.node_at_target(Vertex::Id(0x2)).targets().len());

        
        assert_eq!(out_vag.node_at_target(Vertex::Id(Vertex::Id(0x0))).targets().len(), 2);
        assert_eq!(out_vag.node_at_target(Vertex::Id(Vertex::Id(0x1))).targets().len(), 1);
        assert_eq!(out_vag.node_at_target(Vertex::Id(Vertex::Id(0x2))).targets().len(), 0);

    }


}

// implement Debug trait by hand later !!
#[derive(Debug, PartialEq, Eq)]
pub enum SortError {
    EmptyGraph,
    UnreachableNodes,
    InvalidInitialAddress,
}



// TODO:
//      * some small graphs where the order can be check by hands -> is the same result, no panic
//      * the target of an edge is not in the graph -> ??


// 