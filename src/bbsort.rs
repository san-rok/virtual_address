

// pub mod vagraph;
use crate::vagraph::vag::*;

// generic functions

use std::fmt::{Debug, Display, LowerHex};
use std::hash::Hash;

use petgraph::visit::{IntoNodeIdentifiers, IntoNeighbors, NodeIndexable, IntoNeighborsDirected, GraphBase};

// use petgraph::visit::NodeRef;

use std::collections::HashMap;


pub trait NodeWeight {
    type Node; 
    fn weight(&self, node: Self::Node) -> usize;
}

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
                // NOT CORRECT YET! what about the length - this is just a vertex weight
                g.weight(block), 
                // g.neighbors(block).map(|x| Vertex::Id(x)).collect(),
                g.neighbors(block).map(Vertex::Id).collect(),
                g.neighbors_directed(block, petgraph::Direction::Incoming).count(),
            )
        );
    }

    // nodes.sort_by_key(|node| node.address());

    let vag: VirtualAddressGraph<G::NodeId> = VirtualAddressGraph::new(
        // *nodes.iter().map(|(x,_)| x).min().unwrap(),
        *nodes.keys().min().unwrap(),
        nodes,
    );

    vag

}


pub fn sort<G>(g: G) -> Vec<G::NodeId> 
    where
        G:  IntoNodeIdentifiers + IntoNeighbors + NodeIndexable + IntoNeighborsDirected + 
            NodeWeight<Node = G::NodeId>,
        <G as GraphBase>::NodeId: Copy + Eq + Debug + Display + Hash + Ord + LowerHex, 
{

    let vag: VirtualAddressGraph<G::NodeId> = to_vag(g);
    vag.weighted_order()

}

