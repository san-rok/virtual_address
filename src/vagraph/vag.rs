
use std::cmp::*;
use std::collections::{BTreeMap, HashSet};

use crate::cfg::*;
use crate::vagraph::kahn::*;
use crate::vagraph::scc::*;

use serde::{Serialize, Deserialize};

use petgraph::algo::{is_cyclic_directed, tarjan_scc};
use petgraph::visit::*;


// in the ordering of the block only the number of instructions matter
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct NoInstrBasicBlock<N: Eq + Ord> {
    // the virtual address of the block
    address: N,
    // the number of instructions in the block
    len: usize,
    // the addresses of blocks where we will jump next 
    // note: its length is at most two
    targets: Vec<N>,
    // number of blocks from we jump to here
    indegree: usize,
}
// if we consider the block alone, then its indegree is set to be 0

impl<N> NoInstrBasicBlock<N> {

    // sets an instance
    pub fn new(address: N, len: usize, targets: Vec<N>, indegree: usize) -> Self {
        NoInstrBasicBlock::<N> { 
            address, 
            len,
            targets,
            indegree,
        }
    }
    
    // the virtual address of the block
    pub fn address(&self) -> N {
        self.address
    }

    // the number of instructions 
    fn len(&self) -> usize {
        self.len
    }

    // a slice of the target blocks' addresses
    pub fn targets(&self) -> &[N] {
        &self.targets
    }

    // extends the vector of targets by the given address
    // note: we can not modify here the target's indegree !!!
    fn add_target(&mut self, target: N) {
        self.targets.push(target);
    }

    // deletes the given target from the targets vector if it's there (yes it is)
    // note: we can not modify here the target's indegree !!
    fn erase_target(&mut self, target: N) {
        if let Some(pos) = self.targets().iter().position(|x| x == &target) {
            self.targets.remove(pos);
            // as mentioned above: the indegree of the given block does NOT change
            /*
            if self.indegree > 0 {
                self.indegree = self.indegree - 1;
            }
            */
        }
    }

    // the indegree of the block
    pub fn indegree(&self) -> usize {
        self.indegree
    }

    // setter for the indegree
    fn set_indegree(&mut self, indegree: usize) {
        self.indegree = indegree;
    }

    // increase the indegree of the block by 1
    fn increase_indegree(&mut self) {
        self.set_indegree(self.indegree + 1);
    }

    /*
    // decrease the indegree of the block by 1
    // if indegree == 0, then to nothing
    fn decrease_indegree(&mut self) {
        if self.indegree() > 0 {
            self.set_indegree(self.indegree - 1);
        }
    }
    */


    // translates a BasicBlock to NIBB, that is counts the number of instructions
    // TODO: is it any good for that specific choice - BB is my previous "dummy" struct
    fn from_bb(bb: &BasicBlock) -> Self {

        NoInstrBasicBlock { 
            address: bb.address(), 
            len: bb.instructions().len(), 
            targets: bb.targets().to_vec(),
            indegree: 0_usize,
        }

    }

}

///////////////////// TRAITS for NoInstrBasicBlock /////////////////////////

// N: Eq trait bound is declared previously

// equality of NIBB's whenever their addresses are the same
impl<N> PartialEq for NoInstrBasicBlock<N> {
    fn eq(&self, other: &Self) -> bool {
        self.address() == other.address()
    }
}

impl<N> Eq for NoInstrBasicBlock<N> {}

// order of NIBB's: first by the number of incoming edges then by the length of basic block
impl<N> PartialOrd for NoInstrBasicBlock<N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<N> Ord for NoInstrBasicBlock<N> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.indegree().cmp(&other.indegree())
            .then(self.len().cmp(&other.len()))
    }
}

//////////////////////////////////////////////////////////////////////////////////

// almost the same as ControlFlowGraph but with NoInstrBasicBlock structs
#[derive(Serialize, Deserialize, Debug)]
pub struct VirtualAddressGraph<N> {
    // start: N - TODO!
    address: N,
    nodes: Vec<NoInstrBasicBlock<N>>,
}

impl<N> VirtualAddressGraph<N> {

    // creates a new instance given its address and blocks
    // need: keep the fields private from scc
    pub fn new(address: N, nodes: Vec<NoInstrBasicBlock<N>>) -> Self {
        VirtualAddressGraph::<N> { 
            address, 
            nodes,
        }
    }

    // returns the list (BTreeMap - sorted by address) of indegrees of an instance
    fn in_degrees(&self) -> BTreeMap<N, usize> {

        let mut indeg: BTreeMap<N, usize> = BTreeMap::new();
        
        for node in self.nodes() {
            indeg.entry(node.address()).or_insert(0);

            for target in node.targets() {
                indeg.entry(*target).and_modify(|counter| *counter += 1).or_insert(1);
            }
        }
        
        indeg
    }

    // an extra iteration through the nodes of the graph to update the indegrees of the vertices
    // maybe there is a more clever/effective way to do this - where one can use the iteration in
    // from_cfg() method to get the indegrees
    // note: whenever we modify the VAG instance we need to update the indegrees
    // MAYBE: store the nodes in a BTreeMap (ordered by what?);
    pub fn update_in_degrees(&mut self) {
        let indeg = self.in_degrees();

        for node in self.nodes_mut() {
            node.set_indegree( *indeg.get(&node.address()).unwrap() );
        }
    }

    // TODO: is this specific choice for my construction any good ?
    // creates an instance from a ControlFlowGraph
    pub fn from_cfg(cfg: &ControlFlowGraph) -> Self {
        let mut nodes: Vec<NoInstrBasicBlock<u64>> = Vec::new();

        for block in cfg.blocks() {
            let node: NoInstrBasicBlock<u64> = NoInstrBasicBlock::from_bb(block);
            nodes.push(node);
        }

        nodes.sort_by_key(|node| node.address());

        let mut vag: VirtualAddressGraph<u64> = 
        VirtualAddressGraph { 
            address: cfg.address(), 
            nodes,
        };

        // TODO: merge this two iterations - more effective algoithm!!
        vag.update_in_degrees();

        vag

    }

    // the start virtual address
    pub fn address(&self) -> N {
        self.address
    }

    // unmutable slice of nodes
    pub fn nodes(&self) -> &[NoInstrBasicBlock<N>] {
        &self.nodes
    }

    // mutable slice of nodes
    fn nodes_mut(&mut self) -> &mut [NoInstrBasicBlock<N>] {
        &mut self.nodes
    }

    // reference to a node with a given address
    // TODO: error handling
    pub fn node_at_target(&self, target: N) -> &NoInstrBasicBlock<N> {
        // VAG is ordered by addresses
        let pos: usize = self.nodes().binary_search_by(|x| x.address().cmp(&target)).unwrap();
        // let pos = self.nodes().iter().position(|x| x.address() == target).unwrap();
        &self.nodes()[pos]
    }

    // mutable reference to a node with a given address
    fn node_at_target_mut(&mut self, target: N) -> &mut NoInstrBasicBlock<N> {
        let pos: usize = self.nodes().binary_search_by(|x| x.address().cmp(&target)).unwrap();
        // let pos = self.nodes().iter().position(|x| x.address() == target).unwrap();
        &mut self.nodes_mut()[pos]
    }

    // generates the condensed vag - using Tarjan's algorithm
    // TODO: in the scc module there is a method generating components (basicly does
    // the same as the first part of this) -> MERGE THEM!
    fn condense(&self) -> Self {
        
        // tarjan_scc returns reversed topological order
        let scc = tarjan_scc(self);

        // the node label for a sc component = first node's label in tarjan's output
        // TODO: this ad hoc choice seems not that good (considering that later the id will be the smallest address)
        let mut comp_dict: BTreeMap<N, N> = BTreeMap::new();
        for comp in &scc {
            let value = comp[0];
            for node in comp {
                comp_dict.insert(*node, value);
            }
        }

        let mut nodes: Vec<NoInstrBasicBlock<N>> = Vec::new();

        for comp in &scc {
        
            let address: N = comp[0];
            let mut length: usize = 0;
            let mut targets: Vec<N> = Vec::new();

            for node in comp {

                // the block at the given address
                let node = self.node_at_target(*node);
                
                /*
                let pos = self
                    .nodes()
                    .binary_search_by(|block| block.address().cmp(node))
                    .unwrap();
                let node = &self.nodes()[pos];
                */

                length += node.len();

                for target in node.targets() {
                    if !(comp.contains(target) || targets.contains(target)) {
                        // is this .get() fast for BTreeMap ??
                        targets.push( *(comp_dict.get(target).unwrap()) );
                    }
                }   
            }

            nodes.push(
                NoInstrBasicBlock::<N> { 
                    address, 
                    len: length, 
                    targets,
                    indegree: 0_usize,
                }
            );
        }

        // for later use: sort by address
        nodes.sort_by_key(|node| node.address());

        let mut vag: VirtualAddressGraph<N> =
        VirtualAddressGraph { 
            address: self.address(),
            nodes,
        };

        vag.update_in_degrees();

        vag

    }


    pub fn cost_of_order(&self, order: Vec<N>) -> usize {

        // the list of nodes in the given order
        let mut ordered: Vec<&NoInstrBasicBlock<N>> = Vec::new();
        let mut cost: usize = 0;

        for address in &order {

            ordered.push(self.node_at_target(*address));
            /*
            let pos = self
                .nodes()
                .binary_search_by(|x| x.address().cmp(address))
                .unwrap();
            ordered.push(&self.nodes()[pos]);
            */
        }

        for (pos01, block) in ordered.iter().enumerate() {
            for target in block.targets() {
                let mut edge_weight: usize = 0;
                
                // the given order can be any arbitrary
                let pos02: usize = order
                    .iter()
                    .position(|x| x == target)
                    .unwrap();

                // loops would result in invalid range
                if pos01 != pos02 {
                    for node in &ordered[min(pos01, pos02)+1 .. max(pos01, pos02)] {
                        edge_weight += node.len();
                    }
                }

                cost += edge_weight;

            }
        }

        cost
    }


    // collection of such edges that generates cycles in the component
    // TODO: error handling - no backedges when graph is acyclic
    pub fn backedges(&self) -> Vec<(N, N)> {

        let mut backedges: Vec<(N,N)> = Vec::new();

        depth_first_search(self, Some(self.address()), |event| {
            if let DfsEvent::BackEdge(u, v) = event {
                backedges.push((u,v));
            }
        });
    
        backedges
    }


    // add a new node to the existing list of nodes
    // note: the way we use this - no indegree modification is needed for the targets
    fn add_block(&mut self, node: NoInstrBasicBlock<N>) {

        // the new edges modify the indegrees of the targets
        /*
        for target in node.targets() {
            self.node_at_target_mut(*target).increase_indegree();
        }
        */

        // add the new node to the graph
        self.nodes.push(node);

        // the nodes are sorted by address
        self.nodes_mut().sort_by_key(|x| x.address());
    }


    // add the given edge to the VAG: between EXISTING blocks
    fn add_edge(&mut self, edge: (N, N)) {
        self.node_at_target_mut(edge.0).add_target(edge.1);

        // increase the indegree of the target block
        self.node_at_target_mut(edge.1).increase_indegree();
    }

    // add the given edges to the VAG
    // note: the edges vec<(N, N)> needs to be ordered
    fn add_edges(&mut self, edges: &Vec<(N,N)>) {
        // TODO: optimalize !!
        for &edge in edges {
            self.add_edge(edge);
        }
    }

    // erase the given edge from the VAG
    // note: we only erase such edges that points to a non-existing targets (outgoing from a subgraph)
    //       in add_target_vertex() method, hence no indegree modification is necessary
    fn erase_edge(&mut self, edge: (N, N)) {
        self.node_at_target_mut(edge.0).erase_target(edge.1);
    }

    // erase the given edges to the VAG
    // note: we only erase such edges that points to a non-existing targets (outgoing from a subgraph)
    //       in add_target_vertex() method, hence no indegree modification is necessary
    // note: used only when phantom target is added to the graph hence the indegree update is there
    pub fn erase_edges(&mut self, edges: &Vec<(N, N)>)  {
        // TODO: optimalize !!
        for &edge in edges {
            self.erase_edge(edge);
        }
    }

    // given the list of incoming edges: merge their sources into one new vertex
    pub fn add_source_vertex(&mut self, in_edges: &[(N, N)]) {
        // since the source of the incoming edges is not in the VAG - we don't have to delete anything

        // the sources of these edges then are merged into one vertex
        // with 0 indegree and large length
        self.add_block(
            NoInstrBasicBlock {
                address: 0x0,
                len: 9999,
                targets: in_edges.iter().map(|(_s,t)| *t).collect(),
                indegree: 0,
            }
        );

        // the nodes in VAG are sorted by the address
        self.nodes_mut().sort_by_key(|x| x.address());

        // the edges coming from the new vertex increases the indegrees of some of the already existing vertices
        self.update_in_degrees();

    }


    // given the list of outgoing edges: merge their targets into one new vertex
    // note: used only in scc::to_acyclic_vag hence the indegree update is there
    pub fn add_target_vertex(&mut self, out_edges: &Vec<(N, N)>) {

        // delete the original outgoing edges, which points to non-existing vertices
        self.erase_edges(out_edges);

        // the targets of these edges then are merged into one vertex
        // with given indegree and small length
        self.add_block(
            NoInstrBasicBlock {
                address: 0x1,
                len: 0,
                targets: vec![],
                // at the moment no incoming edges declared
                indegree: 0,
                //out_edges.len(),
            }
        );

        // the new outgoing edges will have this new vertex as target
        let mut new_outgoing: Vec<(N,N)> = Vec::new();
        for (source, _target) in out_edges {
            new_outgoing.push( (*source, 0x1) );
        }

        // add these newly generated edges
        // note: add_edges() updates the indegree of this new vertex: 0x1
        self.add_edges(&new_outgoing);

        // the nodes in VAG are sorted by the address
        self.nodes_mut().sort_by_key(|x| x.address());        

    }



    // gets a VAG and returns the "optimal" order of its vertices
    pub fn weighted_order(&self) -> Vec<u64> {
        
        // TODO: is_cyclic_directed is recursive - maybe use topsort, but that seems redundant
        if !(is_cyclic_directed(self)) {
            // Kahn's algorithm
            let mut kahngraph: KahnGraph = KahnGraph::from_vag(self);
            kahngraph.kahn_algorithm()

        } else {
            // collapse the strongly connected components into single vertices
            let condensed = self.condense();

            // Kahn's algorithm for the condensed graph
            let mut kahngraph: KahnGraph = KahnGraph::from_vag(&condensed);
            let mut topsort_condensed = kahngraph.kahn_algorithm();

            // Kahn's algorithm for the strongly connected components
            let components: Vec<Component> = Component::from_vag(self);

            // TODO: use HashMap where key: the id of the component(?) and value is the vector of nodes
            let mut ordered_components: Vec<Vec<u64>> = Vec::new();

            for comp in components {
                // if the component is trivial (i.e. single vertex) -> do nothing
                if !comp.trivial() {
                    // break the cycles and add auxiliary source and target nodes
                    let comp_vag = comp.to_acyclic_vag();

                    // Kahn's algorithm for the given component
                    let mut kahngraph: KahnGraph = KahnGraph::from_vag(&comp_vag);
                    let mut ord_comp: Vec<u64> = kahngraph.kahn_algorithm();

                    // delete the auxiliary nodes from the order
                    // in theory, they must be the first (0x0) and the last (0x1) in the order
                    ord_comp.retain(|&x| x != 0x0 && x != 0x1);

                    ordered_components.push(ord_comp);
                }
            }

            // insert the inside orders of the components in the ordered components list
            let mut topsort: Vec<u64> = Vec::new();

            // TODO: use somehow the component's ids
            while let Some(id) = topsort_condensed.pop() {
                match ordered_components
                        .iter()
                        .position(|x| x.contains(&id)) {
                    Some(pos) => {
                        let mut component = ordered_components.remove(pos);
                        while let Some(node) = component.pop() {
                            topsort.push(node);
                        }
                    }
                    None => {
                        topsort.push(id);
                    }
                }
            }

            // due to the pop()s, the order is reversed
            topsort.reverse();

            topsort
        }
    }

    // from graph to .dot
    /*
    fn render_to<W: std::io::Write>(&self, output: &mut W) -> dot2::Result {
        dot2::render(self, output)
    }
    */



}




    
/////////////////////// TRAITS for VirtualAddressGraph //////////////////////////

// package: petgraph
// for graph algorithms and traversal

// for Tarjan's scc to work we need the following traits to be implemented for VAG
// NOTE: there is a topologiccal sort in petgraph - but it is DFS based

impl<N> petgraph::visit::GraphBase for VirtualAddressGraph<N> {
    type NodeId = N;
    type EdgeId = (N, N);
}


impl<'a, N> petgraph::visit::IntoNodeIdentifiers for &'a VirtualAddressGraph<N> {
    type NodeIdentifiers = impl Iterator<Item = Self::NodeId> + 'a;

    fn node_identifiers(self) -> Self::NodeIdentifiers {
        self.nodes().iter().map(|x| x.address())
    }
}

impl<'a, N> petgraph::visit::IntoNeighbors for &'a VirtualAddressGraph<N> {
    type Neighbors = impl Iterator<Item = Self::NodeId> + 'a;

    fn neighbors(self, a: Self::NodeId) -> Self::Neighbors {

        let pos = 
            self
                .nodes()
                .binary_search_by(|block| block.address().cmp(&a))
                .unwrap();
        self.nodes()[pos].targets().iter().copied()

    }
}

impl<'a, N> petgraph::visit::NodeIndexable for &'a VirtualAddressGraph<N> {

    fn node_bound(&self) -> usize {
        self.nodes().len()
    }

    fn to_index(&self, a: Self::NodeId) -> usize {
        self
            .nodes()
            .binary_search_by(|block| block.address().cmp(&a))
            .unwrap()
    }

    fn from_index(&self, i:usize) -> Self::NodeId {
        assert!(i < self.nodes().len(),"the requested index {} is out-of-bounds", i);
        self.nodes()[i].address()
    }

}

impl<N> petgraph::visit::Visitable for VirtualAddressGraph<N> {
    type Map = HashSet<Self::NodeId>;

    fn visit_map(&self) -> Self::Map {
        HashSet::with_capacity(self.nodes().len())
    }

    fn reset_map(&self, map: &mut Self::Map) {
        map.clear()
    }
}

////////////////////////////////////////////////////////////////////////////////////

// package: dots
// for .dot and hence .svg plot

impl<'a, N> dot2::Labeller<'a> for VirtualAddressGraph<N> {
    type Node = N;
    type Edge = (N, N);
    type Subgraph = ();

    // .dot compatible identifier naming the graph
    fn graph_id(&'a self) -> dot2::Result<dot2::Id<'a>> {
        dot2::Id::new("control_length_flow")
    }

    // maps n to unique (valid .dot) identifier 
    fn node_id(&'a self, n: &Self::Node) -> dot2::Result<dot2::Id<'a>> {
        dot2::Id::new(format!("N0x{:x}", n))
    }

    // labels of nodes
    fn node_label(&'a self, n: &Self::Node) -> dot2::Result<dot2::label::Text<'a>> {
        let label = self
            .nodes()
            .iter()
            .find(|&v| v.address() == *n)
            .map(|v| format!("{:x}: {}", v.address(), v.len()))
            .unwrap();

        Ok(dot2::label::Text::LabelStr(
            label.into()
        ))
    }

}


impl<'a, N> dot2::GraphWalk<'a> for VirtualAddressGraph<N> {
    type Node = N;
    type Edge = (N, N);
    type Subgraph = ();

    // all nodes of the graph
    fn nodes(&self) -> dot2::Nodes<'a, Self::Node> {
        self.nodes().iter().map(|n| n.address()).collect()
    }

    // all edges of the graph
    fn edges(&'a self) -> dot2::Edges<'a, Self::Edge> {

        let mut edges: Vec<(N, N)> = Vec::new();

        for block in self.nodes() {
            let source = block.address();
            for target in block.targets() {
                edges.push( (source, *target) );
            }
        }

        edges.into_iter().collect()
    }

    // source node for the given edge
    fn source(&self, edge: &Self::Edge) -> Self::Node {
        let &(s,_) = edge;
        s
    }

    // target node for the given edge
    fn target(&self, edge: &Self::Edge) -> Self::Node {
        let &(_,t) = edge;
        t
    }

}


////////////////////////////////////////////////////////////////////////////////////