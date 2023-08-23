
// pub mod vagraph;
use crate::vagraph::vag::*;

// generic functions

use std::fmt::{Debug, Display, LowerHex};
use std::hash::Hash;
use std::default::Default;
use std::collections::HashMap;
use std::cmp::*;

use petgraph::visit::{IntoNodeIdentifiers, IntoNeighbors, NodeIndexable, IntoNeighborsDirected, GraphBase, Visitable};

use kendalls::tau_b;


// no restrictions on NodeId, EdgeId, etc here -> all goes to VAG

pub fn to_vag<G>(g: G, entry: G::NodeId) -> Result<VirtualAddressGraph<G::NodeId>, SortError> 
    where
        G:  IntoNodeIdentifiers + IntoNeighbors + NodeIndexable + IntoNeighborsDirected + Visitable +
            NodeWeight<Node = G::NodeId>,
        <G as GraphBase>::NodeId: Copy + Eq + Debug + Display + Hash + Ord + LowerHex,
{
    // if the given graph is empty, then return error
    if g.node_identifiers().count() == 0 { 
        return Err(SortError::EmptyGraph);
    }

    // the initial address of the given graph is the one with the smallest id
    // IS THIS CORRECT AT ALL?
    // let address = g.node_identifiers().min().ok_or(SortError::MissingInitialAddress).unwrap();

    let mut nodes: HashMap<Vertex<G::NodeId>, NoInstrBasicBlock<G::NodeId>> = HashMap::new();

    // instead of goind through all the vertices in the given order
    // we do this using a DFS - which is also used to check if the graph is connected
    petgraph::visit::depth_first_search(&g, Some(entry), |event| {
        if let petgraph::visit::DfsEvent::Finish(block, _) = event {
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
    });

    if nodes.iter().count() != g.node_identifiers().count() {
        println!("address of the graph: {:x}", entry);
        println!("number of find nodes: {}",nodes.iter().count());
        println!("number of nodes: {}", g.node_identifiers().count());
        return Err(SortError::NotStronglyConnectedGraph);
    }

    // DFS for finding not connected components

    /*
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
    */

    let vag: VirtualAddressGraph<G::NodeId> = VirtualAddressGraph::new(
        // *nodes.keys().min().unwrap(),
        Vertex::Id(entry),
        nodes,
    );

    Ok(vag)

}


pub fn bbsort<G>(g: G, entry: G::NodeId) -> Result<Vec<G::NodeId>, SortError> 
    where
        G:  IntoNodeIdentifiers + IntoNeighbors + NodeIndexable + IntoNeighborsDirected + Visitable +
            NodeWeight<Node = G::NodeId>,
        <G as GraphBase>::NodeId: Copy + Eq + Debug + Display + Hash + Ord + LowerHex, 
{

    // propagating the reading errors further
    let topsort = to_vag(g, entry)?.weighted_order();
    Ok(topsort)

    /*
    // NOT GOOD YET!!
    match to_vag(g) {
        Ok(vag) => Ok(vag.weighted_order()),
        Err(err) => Err(err),
    }
    */
    /*
    if let Ok(vag) = to_vag(g) {
        Ok(vag.weighted_order())
    }
    */

}


// cost of given order 
pub fn cost<G>(g: G, entry: G::NodeId, order: &[G::NodeId]) -> (usize, bool)
    where
        G:  IntoNodeIdentifiers + IntoNeighbors + NodeIndexable + IntoNeighborsDirected + Visitable +
        NodeWeight<Node = G::NodeId>,
    <G as GraphBase>::NodeId: Copy + Eq + Debug + Display + Hash + Ord + LowerHex + Default,
{
    // NOT GOOD YET !!
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

        assert_eq!(to_vag(&vag, address).is_err_and(|x| x ==  SortError::NotStronglyConnectedGraph), true);  

    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum SortError {
    EmptyGraph,
    NotStronglyConnectedGraph,
    MissingInitialAddress,
}

// implement Debug trait by hand later !!

// add an initial address input !

// TODO:
//      * empty graph -> Err
//      * not connected graph -> Err
//      * some small graphs where the order can be check by hands -> is the same result, no panic
//      * no initial address -> Err (?)
//      * the target of an edge is not in the graph -> ??


// 