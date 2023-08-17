
#![feature(impl_trait_in_assoc_type)]

// PART01: Binary struct

pub mod binary;
use crate::binary::*;

// PART02 + PART03.A: Basic Blocks & Control Flow Graph

pub mod cfg;
use crate::cfg::*;

// PART03.B: "Optimal" list of basic blocks

pub mod vagraph;
use crate::vagraph::vag::*;


use kendalls::tau_b;
// use petgraph::visit::IntoNodeIdentifiers;


fn main() {

    let path = String::from("/home/san-rok/projects/testtest/target/debug/testtest");
    let binary = Binary::from_elf(path);

    let virtual_address: u64 =  0x96b4;
    // test: 0x88cb, 0x8870, 0x88b0, 0x8a0d, 0x893e, 0x88f0, 0x8c81, 0x8840, 0x8f41, 0x970b, 0x96b4

    let cfg: ControlFlowGraph = ControlFlowGraph::from_address(&binary, virtual_address);

    let mut f = std::fs::File::create("/home/san-rok/projects/virtual_address/virtual_address.dot").unwrap();
    cfg.render_to(&mut f).unwrap();
    // dot -Tsvg virtual_address.dot > virtual_address.svg

    let vag: VirtualAddressGraph<u64> = VirtualAddressGraph::from_cfg(&cfg);

    let topsort = sort(&vag);

    // let topsort = vag.weighted_order();
    println!("{:x?}", topsort);

    let topsort: Vec<u64> = topsort.iter().map(|&x| x.id().unwrap()).collect();
    println!("cost of order: {}", vag.cost_of_order(topsort));
    


    // test dags 
    let file = std::fs::File::open("cfg.yaml").unwrap();
    let vags: Vec<UnwrappedVAGraph<u64>> = serde_yaml::from_reader(file).unwrap();
    let vags: Vec<VirtualAddressGraph<u64>> = vags.iter().map(|x| x.to_vag()).collect();

    // TBC !!!

    /*
    let mut test_vag = vags.iter_mut().find(|x| x.address() == 0x1845beec0).unwrap();
    // let mut f = std::fs::File::create("/home/san-rok/projects/virtual_address/test_vag.dot").unwrap();
    // test_vag.render_to(&mut f).unwrap();
    // dot -Tsvg test_vag.dot > test_vag.svg

    test_vag.update_in_degrees();

    println!("{:#x?}", test_vag);

    let topsort = test_vag.weighted_order();

    let mut initial_order: Vec<u64> = Vec::new();
        for node in test_vag.nodes() {
            initial_order.push(node.address());
        }
    initial_order.sort();


    println!("nodes originally: {}", initial_order.len());
    println!("nodes after sort: {}", topsort.len());

    for i in 0..initial_order.len() {
        if i < topsort.len() {
            println!("{:x}, {:x}", initial_order[i], topsort[i]);
        } else {
            println!("{:x}, ", initial_order[i]);
        }
    }

    */

    // let original_cost: usize = vag.cost_of_order(initial_order);
    // let sorted_cost: usize = vag.cost_of_order(topsort);

    // println!("cost of original order: {}", original_cost);
    // println!("cost of topological sort: {} \n", sorted_cost);

    let mut better_cost = 0;

    for /* mut */ vag in vags {
        // vag.update_in_degrees();

        // let topsort = vag.weighted_order();
        let topsort = sort(&vag);
        let topsort: Vec<u64> = topsort.iter().map(|&x| x.id().unwrap()).collect();

        // let mut kahngraph: KahnGraph = KahnGraph::from_vag(&dag);
        // let topsort = kahngraph.kahn_algorithm();

        let mut initial_order: Vec<u64> = Vec::new();
        for (node, _) in vag.nodes() {
            initial_order.push(node.id().unwrap());
        }
        initial_order.sort();

        println!("starting block's address: {:x}", vag.address().id().unwrap());

        // println!("initial number of nodes {}", initial_order.len());
        // println!("ordered number of nodes {}", topsort.len());

        for i in 0..initial_order.len() {
            if i < topsort.len() {
                println!("{:x}, {:x}", initial_order[i], topsort[i]);
            } else {
                println!("{:x}, ", initial_order[i]);
            }
        }

        /*
        for i in 0..topsort.len() {
            println!("{:x}, {:x}", initial_order[i], topsort[i]);
        }
        */
    

        let kendall_tau = tau_b(&initial_order, &topsort).unwrap().0;

        // println!("initial order: {:x?}", initial_order);
        // println!("topological sort: {:x?}", topsort);

        let original_cost: usize = vag.cost_of_order(initial_order);
        let sorted_cost: usize = vag.cost_of_order(topsort);

        println!("kendall tau: {:#?}", kendall_tau);
        println!("cost of original order: {}", original_cost);
        println!("cost of topological sort: {} \n", sorted_cost);

        if sorted_cost <= original_cost {
            better_cost += 1;
        }


        // some addresses with big differences: 0x1800c17b0
        /*
        if dag.address() == 0x1800c1530 {
            let mut file = std::fs::File::create("/home/san-rok/projects/virtual_address/test.dot").unwrap();
            dag.render_to(&mut file).unwrap();
        }
        */
    }

    println!("number of times topsort is better: {}", better_cost);

}



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

fn to_vag<G>(g: G) -> VirtualAddressGraph<G::NodeId> 
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
                g.neighbors(block).map(|x| Vertex::Id(x)).collect(),
                g.neighbors_directed(block, petgraph::Direction::Incoming).count(),
            )
        );
    }

    // nodes.sort_by_key(|node| node.address());

    let vag: VirtualAddressGraph<G::NodeId> = VirtualAddressGraph::new(
        *nodes.iter().map(|(x,_)| x).min().unwrap(),
        nodes,
    );

    vag

}


fn sort<G>(g: G) -> Vec<G::NodeId> 
    where
        G:  IntoNodeIdentifiers + IntoNeighbors + NodeIndexable + IntoNeighborsDirected + 
            NodeWeight<Node = G::NodeId>,
        <G as GraphBase>::NodeId: Copy + Eq + Debug + Display + Hash + Ord + LowerHex, 
{

    let vag: VirtualAddressGraph<G::NodeId> = to_vag(g);
    vag.weighted_order()

}





