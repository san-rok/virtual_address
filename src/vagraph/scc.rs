
use std::fmt::Display;
use std::hash::Hash;

use std::collections::HashSet;
use petgraph::algo::tarjan_scc;

use crate::vagraph::vag::*;


#[derive(Debug)]
pub struct Component<'a, N> 
where
    N: Copy + Eq + Display + Hash + Ord,
{
    // the original graph
    graph: &'a VirtualAddressGraph<N>,
    // the strongly connected component
    component: HashSet<N>,
}

impl<'a, N> Component<'a, N> 
where
    N: Copy + Eq + Display + Hash + Ord,
{
    // given a VAG instance returns a vector of its components
    pub fn from_vag(vag: &'a VirtualAddressGraph<N>) -> Vec<Self> {

        let mut components: Vec<Self> = Vec::new();

        // tarjan_scc -> vector of strongly connected component's addresses vector
        let scc: Vec<Vec<N>> = tarjan_scc(vag);

        for comp in scc {
            let mut strongly: HashSet<N> = HashSet::new();
            for node in comp {
                // TODO: if let not ??
                match strongly.insert(node) {
                    false => println!("the node {} is already in", node),
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
    fn nodes(&self) -> &HashSet<N> {
        &self.component
    }

    // checks if a given node is in the component
    fn contains(&self, node: N) -> bool {
        self.nodes().contains(&node)
    }

    // checks if a component is trivial, i.e. it's a single node
    pub fn trivial(&self) -> bool {
        self.nodes().len() == 1
    }

    // returns a reference to the targets of a given vertex in the component
    fn targets(&self, node: N) -> &[N] {
        self.whole().node_at_target(node).targets()
    }

    // a collection of incoming edges
    // TODO: HashSet or Vector ??
    fn incoming_edges(&self) -> Vec<(N, N)> {

        let mut incoming: Vec<(N, N)> = Vec::new();

        for node in self.nodes() {

            for block in self.whole().nodes() {
                for target in block.targets() {
                    if target == node && !self.contains(block.address()) {
                        incoming.push((block.address(), *node))
                    }
                }
            }

        }

        // sorted by source and then target
        // TODO: is it really needed?
        incoming.sort_by_key(|item| (item.0, item.0) );
        incoming

    }

    // a collection of outgoing edges
    // TODO: HashSet or Vector ??
    fn outgoing_edges(&self) -> Vec<(N, N)> {

        let mut outgoing: Vec<(N, N)> = Vec::new();

        for &node in self.nodes() {
            for &target in self.targets(node) {
                if !self.contains(target) {
                    outgoing.push((node, target));
                }
            }
        }

        // sorted by source and then target
        outgoing.sort_by_key(|item| (item.0, item.0) );
        outgoing

    }

    // from a Component it generates a VirtualAddressGraph, where
    // the sources of the incoming edges are merged into one vertex
    // the targets of the outgoing edges are merged into one vertex
    // MAYBE: create an enum that sets if acyclic or not
    pub fn to_acyclic_vag(&self) -> VirtualAddressGraph<N> {

        let address = self.nodes().iter().min().unwrap();

        let mut nodes: Vec<NoInstrBasicBlock<N>> = Vec::new();
        for node in self.nodes() {
            // TODO: do this without clone()
            // MAYBE: rewrite the whole Kahn's algorithm to accept avoided edges, vertices, etc.
            nodes.push(self.whole().node_at_target(*node).clone());
        }

        let mut vag: VirtualAddressGraph<N> = VirtualAddressGraph::new(*address, nodes);
        
        // let backs = vag.backedges();
        // for (s, t) in backs {
        //     println!("{} --> {}",s, t);
        // }
        // vag.erase_edges(&backs);


        
        let ins: Vec<(N, N)> = self.incoming_edges();
        let outs: Vec<(N, N)> = self.outgoing_edges();

        vag.add_source_vertex(&ins);
        vag.add_target_vertex(&outs);

        let backs = vag.backedges();

        vag.erase_edges(&backs);

        // TODO: update the indegrees at the place of modification!!
        vag.update_in_degrees();

        vag

    }


    



}
