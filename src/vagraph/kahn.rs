
use std::collections::BinaryHeap;


use crate::vagraph::vag::{VirtualAddressGraph, NoInstrBasicBlock};



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

    /*
    fn len(&self) -> usize {
        self.block.len()
    }
    */

    /*
    fn targets(&self) -> &'a [u64] {
        self.block.targets()
    }
    */

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
pub struct KahnGraph<'a> {
    address: u64,
    nodes: Vec<KahnBasicBlock<'a>>,
}

impl<'a> KahnGraph<'a> {

    // generates a KahnGraph instance from a VAG
    pub fn from_vag(vag: &'a VirtualAddressGraph) -> Self {

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

    /*
    // returns the address of the KahnGraph (i.e. the starting va)
    fn address(&self) -> u64 {
        self.address
    }
    */

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

    /*
    fn node_at_target(&self, target: u64) -> &KahnBasicBlock<'a> {
        let pos = self.position(target);
        &self.nodes()[pos]
    }
    */

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
    pub fn kahn_algorithm(&mut self) -> Vec<u64> {

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