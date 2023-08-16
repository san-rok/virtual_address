
use std::collections::{BinaryHeap, HashMap};


use crate::vagraph::vag::*; //{VirtualAddressGraph, NoInstrBasicBlock};

// use std::fmt::Display;
// use std::hash::Hash;



#[derive(Debug)]
struct KahnBasicBlock<'a, N: VAGNodeId> {
    block: &'a NoInstrBasicBlock<N>,
    // how many of the incoming edges are deleted so far
    // this field will be modified during the weighted Kahn's algorithm
    deleted: usize,
}

impl<'a, N: VAGNodeId> KahnBasicBlock<'a, N> {
    fn address(&self) -> Vertex<N> {
        self.block.address()
    }

    fn block(&self) -> &'a NoInstrBasicBlock<N> {
        self.block
    }

    /*
    fn len(&self) -> usize {
        self.block.len()
    }
    */

    /*
    fn targets(&self) -> &'a [N] {
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
pub struct KahnGraph<'a, N: VAGNodeId> {
    address: Vertex<N>,
    nodes: HashMap<Vertex<N>, KahnBasicBlock<'a, N>>,
}

impl<'a, N: VAGNodeId> KahnGraph<'a, N> {
    // generates a KahnGraph instance from a VAG
    pub fn from_vag(vag: &'a VirtualAddressGraph<N>) -> Self {

        let mut nodes: HashMap<Vertex<N>, KahnBasicBlock<N>> = HashMap::new();

        for (node, block) in vag.nodes() {
            nodes.insert(
                *node,
                KahnBasicBlock::<N>{
                    block: block,
                    deleted: 0,
                }
            );
        }

        // nodes.sort_by_key(|x| x.address());

        KahnGraph { 
            address: vag.address(), 
            nodes,
        }

    }

    /*
    // returns the address of the KahnGraph (i.e. the starting va)
    fn address(&self) -> N {
        self.address
    }
    */

    // returns the slice of KBBs of the KahnGraph
    fn nodes(&self) -> &HashMap<Vertex<N>, KahnBasicBlock<'a, N>> {
        &self.nodes
    }

    // returns a mutable slice of KBBs of the KahnGraph
    fn nodes_mut(&mut self) -> &mut HashMap<Vertex<N>, KahnBasicBlock<'a, N>> {
        &mut self.nodes
    }

    /*
    fn position(&self, target: N) -> usize {
        self
            .nodes()
            .binary_search_by(|a| a.address().cmp(&target))
            .unwrap()
    }
    */

    /*
    fn node_at_target(&self, target: N) -> &KahnBasicBlock<'a> {
        let pos = self.position(target);
        &self.nodes()[pos]
    }
    */

    // a mutable reference for the block at given target
    fn node_at_target_mut(&mut self, target: &Vertex<N>) -> &mut KahnBasicBlock<'a, N> {

        self
            .nodes_mut()
            .get_mut(target)
            .unwrap()

        // let pos = self.position(target);
        // &mut self.nodes_mut()[pos]
    }

    // reduces the indegree of a block during the iterations of Kahn's algorithm
    // this corresponds to the edge deletions 
    // note:    the nummber of deleted edges are counted in the KBB.deleted field
    //          if the deleted == indegree -> the vertex lost all of its incoming edges
    //          hence popped for a possible next vertex for the iteration
    fn reduce_indegree(&mut self, target: &Vertex<N>) -> Option<&'a NoInstrBasicBlock<N>> {
        let kbb = self.node_at_target_mut(target);
        
        kbb.recude_by_one();

        match kbb.indegree() == kbb.deleted() {
            true => Some(kbb.block()),
            false => None,
        }
    }

    // after the Kahn's algorithm is finished it is nice to reset the deleted counters back to 0
    fn no_deleted(&mut self) {
        for (_, block) in self.nodes_mut() {
            block.set_deleted(0);
        }
    }

    // an implementation of the weighted version of Kahn's topological sorting algorithm 
    // for directed acyclic graphs
    // the weights are used for tie breaking when there are more than one vertex with 
    // zero indegree: sorted by two keys: original in-degree and then lengths of block
    // note:    the output vector must contain Vertex<N> elements since we will run it on
    //          the subgraphs obtained from strongly connected components
    pub fn kahn_algorithm(&mut self) -> Vec<Vertex<N>> {

        // topsort: the topological order of the basic blocks - collecting only the addresses
        let mut topsort: Vec<Vertex<N>> = Vec::new();
        // an auxiliary vector: the zero in-degree vertices of the running algorithm
        let mut visit: BinaryHeap<&NoInstrBasicBlock<N>> = BinaryHeap::new();


        // initialization: collect the initially zero in-degree vertices
        // the binary heap orders them by length
        for (_, kahnblock) in self.nodes() {
            if kahnblock.indegree() == 0 {
                visit.push( kahnblock.block());
            }
        }

        while let Some(node) = visit.pop() {
            // reduce the in-degrees of the actual vertex's target(s)
            for target in node.targets() {

                if let Some(block) = self.reduce_indegree(target) {
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