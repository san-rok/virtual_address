
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
    // identifier of the component: smallest nodeid
    compid: Vertex<N>,
}

impl<'a, N: VAGNodeId> Component<'a, N> {
    // given a VAG instance returns a vector of its components
    pub fn from_vag(vag: &'a VirtualAddressGraph<N>) -> Vec<Self> {

        let mut components: Vec<Self> = Vec::new();

        // tarjan_scc -> vector of strongly connected component's addresses vector
        let scc: Vec<Vec<Vertex<N>>> = tarjan_scc(vag);

        for comp in scc {
            let mut strongly: HashSet<Vertex<N>> = HashSet::new();
            for node in &comp {
                // TODO: if let not ??
                match strongly.insert(*node) {
                    // when we read a vag into components: no phantom Source and Target vertices
                    false => println!("the node {:x?} is already in", node.id().unwrap()),
                    true => (),
                }
            }

            components.push(
                Self { 
                    graph: vag,
                    component: strongly,
                    // the id of a component is the minimal nodeid inside
                    compid: *comp.iter().min().unwrap(),
                }
            )
        }

        components

    }

    // returns a reference to the original graph
    fn whole(&self) -> &VirtualAddressGraph<N> {
        self.graph
    }

    // the identifier of the component = smallest nodeid inside
    pub fn compid(&self) -> Vertex<N> {
        self.compid
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


    // a collection of incoming edges
    fn incoming_edges(&self) -> Vec<(Vertex<N>, Vertex<N>)> {

        let mut incoming: Vec<(Vertex<N>, Vertex<N>)> = Vec::new();

        for (&source, block) in 
                self.whole().nodes().iter().filter(|(&x,_)| !self.contains(x)) {
            for &target in 
                    block.targets().iter().filter(|&x| self.contains(*x)) {        
                incoming.push((source, target));
            }
        }

        incoming

    }

    // a collection of outgoing edges
    fn outgoing_edges(&self) -> Vec<(Vertex<N>, Vertex<N>)> {

        let mut outgoing: Vec<(Vertex<N>, Vertex<N>)> = Vec::new();

        for &node in self.nodes() {
            for &target in self.targets(node) {
                if !self.contains(target) {
                    outgoing.push((node, target));
                }
            }
        }

        outgoing
    }

    // from a Component it generates a VirtualAddressGraph, where
    // the sources of the incoming edges are merged into one vertex
    // the targets of the outgoing edges are merged into one vertex
    // MAYBE: create an enum that sets if acyclic or not
    pub fn to_acyclic_vag(&self) -> VirtualAddressGraph<N> {

        // let address = self.nodes().iter().min().unwrap();

        let mut nodes: HashMap<Vertex<N>, NoInstrBasicBlock<N>> = HashMap::new();
        for node in self.nodes() {
            // TODO: do this without clone()
            // MAYBE: rewrite the whole Kahn's algorithm to accept avoided edges, vertices, etc.
            nodes.insert(
                *node,
                self.whole().node_at_target(*node).clone()
            );
        }

        let mut vag: VirtualAddressGraph<N> = VirtualAddressGraph::new(self.compid(), nodes);
        
        // all the incoming edges of the component
        let ins: Vec<(Vertex<N>, Vertex<N>)> = self.incoming_edges();
        // all the outgoing edges of the component
        let outs: Vec<(Vertex<N>, Vertex<N>)> = self.outgoing_edges();

        // merge the incoming edges' start nodes into one source node
        // note: no extra update/modification is needed
        vag.add_source_vertex(&ins);
        // merge the outgoing edges' target nodes into one sink node
        // note: no extra update/modification is needed
        vag.add_sink_vertex(&outs);

        // a vector of backtracking edges in the strongly connected component
        let backs = vag.backedges();

        // to break directed cycles we need to throw all of them away
        // note:    the erase_edge() method also modifies the indegree of the target node
        //          hence no extra update/modification is needed
        vag.erase_edges(&backs);

        vag

    }


    



}
