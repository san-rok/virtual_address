
// use std::fmt::Display;
// use std::hash::Hash;

use std::collections::{HashSet, HashMap};
use petgraph::algo::tarjan_scc;

use crate::vagraph::vag::*;


#[derive(Debug)]
pub struct Component<'a, N: VAGNodeId> {
    // the original graph
    graph: &'a VirtualAddressGraph<N>,
    // the strongly connected component
    component: HashSet<Vertex<N>>,
}

impl<'a, N: VAGNodeId> Component<'a, N> {
    // given a VAG instance returns a vector of its components
    pub fn from_vag(vag: &'a VirtualAddressGraph<N>) -> Vec<Self> {

        let mut components: Vec<Self> = Vec::new();

        // tarjan_scc -> vector of strongly connected component's addresses vector
        let scc: Vec<Vec<Vertex<N>>> = tarjan_scc(vag);

        for comp in scc {
            let mut strongly: HashSet<Vertex<N>> = HashSet::new();
            for node in comp {
                // TODO: if let not ??
                match strongly.insert(node) {
                    // when we read a vag into components: no phantom Source and Target vertices
                    false => println!("the node {:x?} is already in", node.id().unwrap()),
                    true => (),
                }
            }

            components.push(
                Self { 
                    graph: vag,
                    component: strongly,
                }
            )
        }

        components

    }

    // returns a reference to the original graph
    fn whole(&self) -> &VirtualAddressGraph<N> {
        self.graph
    }

    // returns the collection of nodes in the strongly connnected component
    pub fn nodes(&self) -> &HashSet<Vertex<N>> {
        &self.component
    }

    // checks if a given node is in the component
    fn contains(&self, node: Vertex<N>) -> bool {
        self
            .nodes()
            .contains(&node)
    }

    // checks if a component is trivial, i.e. it's a single node
    pub fn trivial(&self) -> bool {
        self.nodes().len() == 1
    }

    // returns a reference to the targets of a given vertex in the component
    fn targets(&self, node: Vertex<N>) -> &HashSet<Vertex<N>> {
        self
            .whole()
            .node_at_target(node)
            .targets()
    }

    // TBC!!

    // a collection of incoming edges
    // TODO: HashSet or Vector ??
    fn incoming_edges(&self) -> Vec<(Vertex<N>, Vertex<N>)> {

        let mut incoming: Vec<(Vertex<N>, Vertex<N>)> = Vec::new();

        for (&source, block) in 
                self.whole().nodes().iter().filter(|(&x,_)| !self.contains(x)) {
            for &target in 
                    block.targets().iter().filter(|&x| self.contains(*x)) {        
                incoming.push((source, target));
            }
        }

        /*
        for node in self.nodes() {

            for (source, block) in self.whole().nodes() {
                for target in block.targets() {
                    if target == node && !self.contains(*source) {
                        incoming.push((*source, *node))
                    }
                }
            }
        }
        */

        // sorted by source and then target
        // TODO: is it really needed?
        // incoming.sort_by_key(|item| (item.0, item.0) );
        incoming

    }

    // a collection of outgoing edges
    // TODO: HashSet or Vector ??
    fn outgoing_edges(&self) -> Vec<(Vertex<N>, Vertex<N>)> {

        let mut outgoing: Vec<(Vertex<N>, Vertex<N>)> = Vec::new();

        for &node in self.nodes() {
            for &target in self.targets(node) {
                if !self.contains(target) {
                    outgoing.push((node, target));
                }
            }
        }

        // sorted by source and then target
        // outgoing.sort_by_key(|item| (item.0, item.0) );
        outgoing

    }

    // from a Component it generates a VirtualAddressGraph, where
    // the sources of the incoming edges are merged into one vertex
    // the targets of the outgoing edges are merged into one vertex
    // MAYBE: create an enum that sets if acyclic or not
    pub fn to_acyclic_vag(&self) -> VirtualAddressGraph<N> {

        let address = self.nodes().iter().min().unwrap();

        let mut nodes: HashMap<Vertex<N>, NoInstrBasicBlock<N>> = HashMap::new();
        for node in self.nodes() {
            // TODO: do this without clone()
            // MAYBE: rewrite the whole Kahn's algorithm to accept avoided edges, vertices, etc.
            nodes.insert(
                *node,
                self.whole().node_at_target(*node).clone()
            );
        }

        let mut vag: VirtualAddressGraph<N> = VirtualAddressGraph::new(*address, nodes);
        
        let ins: Vec<(Vertex<N>, Vertex<N>)> = self.incoming_edges();
        let outs: Vec<(Vertex<N>, Vertex<N>)> = self.outgoing_edges();

        vag.add_source_vertex(&ins);
        vag.add_target_vertex(&outs);

        let backs = vag.backedges();

        // this edge erasing won't modify the indegrees -> it is a must to do that in the next line
        vag.erase_edges(&backs);

        // TODO: update the indegrees at the place of modification!!
        vag.update_in_degrees();

        vag

    }


    



}
