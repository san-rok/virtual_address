
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

pub fn to_vag<G>(g: G) -> VirtualAddressGraph<G::NodeId> 
    where
        G:  IntoNodeIdentifiers + IntoNeighbors + NodeIndexable + IntoNeighborsDirected +
            NodeWeight<Node = G::NodeId>,
        <G as GraphBase>::NodeId: Copy + Eq + Debug + Display + Hash + Ord + LowerHex,
{

    let mut nodes: HashMap<Vertex<G::NodeId>, NoInstrBasicBlock<G::NodeId>> = HashMap::new();

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

    let vag: VirtualAddressGraph<G::NodeId> = VirtualAddressGraph::new(
        *nodes.keys().min().unwrap(),
        nodes,
    );

    vag

}


pub fn bbsort<G>(g: G) -> Vec<G::NodeId> 
    where
        G:  IntoNodeIdentifiers + IntoNeighbors + NodeIndexable + IntoNeighborsDirected + 
            NodeWeight<Node = G::NodeId>,
        <G as GraphBase>::NodeId: Copy + Eq + Debug + Display + Hash + Ord + LowerHex, 
{

    let vag: VirtualAddressGraph<G::NodeId> = to_vag(g);
    vag.weighted_order()

}


// cost of given order 
pub fn cost<G>(g: G, order: &[G::NodeId]) -> (usize, bool)
    where
        G:  IntoNodeIdentifiers + IntoNeighbors + NodeIndexable + IntoNeighborsDirected + 
        NodeWeight<Node = G::NodeId>,
    <G as GraphBase>::NodeId: Copy + Eq + Debug + Display + Hash + Ord + LowerHex + Default,
{
    let vag: VirtualAddressGraph<G::NodeId> = to_vag(g);

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

    }
}



// TODO:
//      * empty graph -> Err
//      * not connected graph -> Err
//      * some small graphs where the order can be check by hands -> is the same result, no panic
//      * no initial address -> Err (?)
//      * the target of an edge is not in the graph -> ??


// 