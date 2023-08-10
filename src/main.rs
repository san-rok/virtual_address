
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
// use crate::vagraph::kahn::*;
// use crate::vagraph::scc::*;


// use petgraph::algo::is_cyclic_directed;
// use petgraph::algo::dominators::*;
// use petgraph::algo::tarjan_scc;
// use petgraph::algo::toposort;
// use petgraph::visit::*;

// use std::collections::BTreeMap;
// use std::collections::HashSet;
// use std::collections::HashMap;
// use std::collections::BinaryHeap;
// use std::collections::VecDeque;

// use std::cmp::*;

// use serde::{Serialize, Deserialize};

use kendalls::tau_b;




/*

#[derive(Debug)]
struct KahnBasicBlock<'a> {
    block: &'a NoInstrBasicBlock,
    // how many of the incoming edges are deleted so far
    // this field will be modified during the weighted Kahn's algorithm
    deleted: usize,
}

impl<'a> KahnBasicBlock<'a> {

    fn address(&self) -> u64 {
        self.block.address()
    }

    fn block(&self) -> &'a NoInstrBasicBlock {
        self.block
    }

    fn len(&self) -> usize {
        self.block.len()
    }

    fn targets(&self) -> &'a [u64] {
        self.block.targets()
    }

    fn indegree(&self) -> usize {
        self.block.indegree()
    }

    fn deleted(&self) -> usize {
        self.deleted
    }

    fn set_deleted(&mut self, deleted: usize) {
        self.deleted = deleted;
    }

    fn recude_by_one(&mut self) {
        self.deleted += 1;
    }
}


#[derive(Debug)]
struct KahnGraph<'a> {
    address: u64,
    nodes: Vec<KahnBasicBlock<'a>>,
}

impl<'a> KahnGraph<'a> {

    // generates a KahnGraph instance from a VAG
    fn from_vag(vag: &'a VirtualAddressGraph) -> Self {

        let mut nodes: Vec<KahnBasicBlock> = Vec::new();

        for node in vag.nodes() {
            nodes.push( KahnBasicBlock{
                    block: node,
                    deleted: 0,
                }
            )
        }

        nodes.sort_by_key(|x| x.address());

        KahnGraph { 
            address: vag.address(), 
            nodes: nodes,
        }

    }

    // returns the address of the KahnGraph (i.e. the starting va)
    fn address(&self) -> u64 {
        self.address
    }

    // returns the slice of KBBs of the KahnGraph
    fn nodes(&self) -> &[KahnBasicBlock<'a>] {
        &self.nodes
    }

    // returns a mutable slice of KBBs of the KahnGraph
    fn nodes_mut(&mut self) -> &mut [KahnBasicBlock<'a>] {
        &mut self.nodes
    }

    fn position(&self, target: u64) -> usize {
        self
            .nodes()
            .binary_search_by(|a| a.address().cmp(&target))
            .unwrap()
    }

    fn node_at_target(&self, target: u64) -> &KahnBasicBlock<'a> {
        let pos = self.position(target);
        &self.nodes()[pos]
    }

    fn node_at_target_mut(&mut self, target: u64) -> &mut KahnBasicBlock<'a> {
        let pos = self.position(target);
        &mut self.nodes_mut()[pos]
    }

    fn reduce_indegree(&mut self, target: u64) -> Option<&'a NoInstrBasicBlock> {
        let kbb = self.node_at_target_mut(target);
        
        kbb.recude_by_one();

        match kbb.indegree() == kbb.deleted() {
            true => Some(kbb.block()),
            false => None,
        }
    }

    fn no_deleted(&mut self) {
        for node in self.nodes_mut() {
            node.set_deleted(0);
        }
    }

    // an implementation of the weighted version of Kahn's topological sorting algorithm 
    // for directed acyclic graphs
    // the weights are used for tie breaking when there are more than one vertex with 
    // zero indegree: sorted by two keys: original in-degree and then lengths of block
    fn kahn_algorithm(&mut self) -> Vec<u64> {

        // topsort: the topological order of the basic blocks - collecting only the addresses
        let mut topsort: Vec<u64> = Vec::new();
        // an auxiliary vector: the zero in-degree vertices of the running algorithm
        let mut visit: BinaryHeap<&NoInstrBasicBlock> = BinaryHeap::new();


        // initialization: collect the initially zero in-degree vertices
        // the binary heap orders them by length
        for node in self.nodes() {
            if node.indegree() == 0 {
                visit.push(node.block());
            }
        }

        while let Some(node) = visit.pop() {
            // reduce the in-degrees of the actual vertex's target(s)
            for target in node.targets() {

                if let Some(block) = self.reduce_indegree(*target) {
                    visit.push(block);
                }
            }

            topsort.push(node.address());
        }

        // for further use we decrease the deleted fields back to zero for all nodes
        self.no_deleted();

        // return topological order
        topsort

    }

}


*/

fn main() {

    let path = String::from("/home/san-rok/projects/testtest/target/debug/testtest");
    let binary = Binary::from_elf(path);

    let virtual_address: u64 =  0x96b4;
    // test: 0x88cb, 0x8870, 0x88b0, 0x8a0d, 0x893e, 0x88f0, 0x8c81, 0x8840, 0x8f41, 0x970b, 0x96b4

    let cfg: ControlFlowGraph = ControlFlowGraph::from_address(&binary, virtual_address);

    // let dominators = simple_fast(&cfg, virtual_address);

    let mut f = std::fs::File::create("/home/san-rok/projects/virtual_address/virtual_address.dot").unwrap();
    cfg.render_to(&mut f).unwrap();
    // dot -Tsvg virtual_address.dot > virtual_address.svg

    let vag: VirtualAddressGraph = VirtualAddressGraph::from_cfg(&cfg);

    let topsort = vag.weighted_order();
    println!("{:x?}", topsort);


    // WHAT DO WE NEED FOR CYCLE BREAKING?
    //      (0) a Components struct: reference for the original VAG, Hash set of subgraph node ids
    //          (0.a) using these field methods can derive the incoming and outgoing edges !!
    //      (1) finds all the bad edges, constituting for cycles
    //      (2) puts back edges - or simply add edges for a VAG instance
    //      (3) adds a starting node to the cycle free VAG: label = 0x0; edges = all the input edges; length = large
    //      (4) adds a terminating node to the cycle free instance: label = 0xfffffffff; edges = all the output edges; length = 0
    //      (5) calculates the order - hopefully use our previous method
    //      (6) inserts back the ordered list to the scc's ordered list in the appropriate place


    // test dags 
    let file = std::fs::File::open("cfg.yaml").unwrap();
    let vags: Vec<VirtualAddressGraph> = serde_yaml::from_reader(file).unwrap();

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

    for vag in vags {
        // vag.update_in_degrees();

        let topsort = vag.weighted_order();

        // let mut kahngraph: KahnGraph = KahnGraph::from_vag(&dag);
        // let topsort = kahngraph.kahn_algorithm();

        let mut initial_order: Vec<u64> = Vec::new();
        for node in vag.nodes() {
            initial_order.push(node.address());
        }
        initial_order.sort();

        println!("starting block's address: {:x}", vag.address());

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

