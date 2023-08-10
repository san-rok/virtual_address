
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
pub struct NoInstrBasicBlock {
    // the virtual address of the block
    address: u64,
    // the number of instructions in the block
    len: usize,
    // the addresses of blocks where we will jump next 
    // note: its length is at most two
    targets: Vec<u64>,
    // number of blocks from we jump to here
    indegree: usize,
}
// if we consider the block alone, then its indegree is set to be 0

impl NoInstrBasicBlock {
    
    // returns the virtual address of the block
    pub fn address(&self) -> u64 {
        self.address
    }

    // returns the number of instructions 
    pub fn len(&self) -> usize {
        self.len
    }

    // returns 
    pub fn targets(&self) -> &[u64] {
        &self.targets
    }

    fn add_target(&mut self, target: u64) {
        self.targets.push(target);
    }

    // TODO: error handling
    // TODO: tell rust there won't be an overflow
    fn erase_target(&mut self, target: u64) {
        if let Some(pos) = self.targets().iter().position(|x| x == &target) {
            self.targets.remove(pos);
            if self.indegree > 0 {
                self.indegree = self.indegree - 1;
            }
        }
    }

    pub fn indegree(&self) -> usize {
        self.indegree
    }

    fn set_indegree(&mut self, indegree: usize) {
        self.indegree = indegree;
    }

    fn from_bb(bb: &BasicBlock) -> Self {

        NoInstrBasicBlock { 
            address: bb.address(), 
            len: bb.instructions().len(), 
            targets: bb.targets().to_vec(),
            indegree: 0 as usize,
        }

    }

}

// equality of NIBB's whenever their addresses are the same
impl PartialEq for NoInstrBasicBlock {
    fn eq(&self, other: &Self) -> bool {
        self.address() == other.address()
    }
}

impl Eq for NoInstrBasicBlock {}

// order of NIBB's: first by the number of incoming edges then by the length of basic block
impl PartialOrd for NoInstrBasicBlock {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for NoInstrBasicBlock {
    fn cmp(&self, other: &Self) -> Ordering {
        self.indegree().cmp(&other.indegree())
            .then(self.len().cmp(&other.len()))
    }
}

#[derive(Serialize, Deserialize, Debug)]
pub struct VirtualAddressGraph {
    address: u64,
    nodes: Vec<NoInstrBasicBlock>,
}

impl VirtualAddressGraph {

    // creates a new instance given its address and blocks
    pub fn new(address: u64, nodes: Vec<NoInstrBasicBlock>) -> Self {
        VirtualAddressGraph { 
            address: address, 
            nodes: nodes,
        }
    }


    // returns the list of indegrees of an instance
    // sorted by keys!
    fn in_degrees(&self) -> BTreeMap<u64, usize> {

        // with_capacity(...) ?
        let mut indeg: BTreeMap<u64, usize> = BTreeMap::new();
        
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
    pub fn update_in_degrees(&mut self) {
        let indeg = self.in_degrees();

        for node in self.nodes_mut() {
            node.set_indegree( *indeg.get(&node.address()).unwrap() );
        }
    }

    pub fn from_cfg(cfg: &ControlFlowGraph) -> Self {
        let mut nodes: Vec<NoInstrBasicBlock> = Vec::new();

        for block in cfg.blocks() {
            let node: NoInstrBasicBlock = NoInstrBasicBlock::from_bb(block);
            nodes.push(node);
        }

        nodes.sort_by_key(|node| node.address());

        let mut vag = 
        VirtualAddressGraph { 
            address: cfg.address(), 
            nodes: nodes,
        };

        // TODO: merge this two iterations - more effective algoithm!!
        vag.update_in_degrees();

        vag

    }

    pub fn address(&self) -> u64 {
        self.address
    }

    pub fn nodes(&self) -> &[NoInstrBasicBlock] {
        &self.nodes
    }

    fn nodes_mut(&mut self) -> &mut [NoInstrBasicBlock] {
        &mut self.nodes
    }

    // reference to a node with a given address
    pub fn node_at_target(&self, target: u64) -> &NoInstrBasicBlock {
        // TODO: error handling

        // VAG is ordered by addresses
        // let pos: usize = self.nodes().binary_search_by(|x| x.address().cmp(&target)).unwrap();
        let pos = self.nodes().iter().position(|x| x.address() == target).unwrap();
        &self.nodes()[pos]
    }

    fn node_at_target_mut(&mut self, target: u64) -> &mut NoInstrBasicBlock {
        // let pos: usize = self.nodes().binary_search_by(|x| x.address().cmp(&target)).unwrap();
        let pos = self.nodes().iter().position(|x| x.address() == target).unwrap();
        &mut self.nodes_mut()[pos]
    }

    // generates the condensed vag - using petgraph::algo::tarjan_scc
    fn condense(&self) -> Self {
        
        // tarjan_scc returns reversed topological order
        let scc = tarjan_scc(self);

        // the node label for a sc component = first node's label in tarjan's output
        // the dictionary is stored in a HashMap -> effectiveness ?
        let mut comp_dict: BTreeMap<u64, u64> = BTreeMap::new();
        for comp in &scc {
            let value = comp[0];
            for node in comp {
                comp_dict.insert(*node, value);
            }
        }

        let mut nodes: Vec<NoInstrBasicBlock> = Vec::new();

        for comp in &scc {
        
            let address: u64 = comp[0];
            let mut length: usize = 0;
            let mut targets: Vec<u64> = Vec::new();

            for node in comp {

                let pos = self
                    .nodes()
                    .binary_search_by(|block| block.address().cmp(&node))
                    .unwrap();
                let node = &self.nodes()[pos];

                length = length + node.len();

                for target in node.targets() {
                    if !(comp.contains(target) || targets.contains(target)) {
                        // is this .get() fast for BTreeMap ??
                        targets.push( *(comp_dict.get(target).unwrap()) );
                    }
                }   
            }

            nodes.push(
                NoInstrBasicBlock { 
                    address: address, 
                    len: length, 
                    targets: targets,
                    indegree: 0 as usize,
                }
            );
        }

        // for later use: sort by address
        nodes.sort_by_key(|node| node.address());

        let mut vag =
        VirtualAddressGraph { 
            address: self.address(),
            nodes: nodes,
        };

        vag.update_in_degrees();

        vag

    }


    fn cost_of_order(&self, order: Vec<u64>) -> usize {

        let mut ordered: Vec<&NoInstrBasicBlock> = Vec::new();
        let mut cost: usize = 0;

        for address in &order {
            let pos = self
                .nodes()
                .binary_search_by(|x| x.address().cmp(address))
                .unwrap();
            ordered.push(&self.nodes()[pos]);
        }

        let mut pos01 = 0;
        for block in &ordered {
            /*
            let pos01: usize = order
                .iter()
                .position(|x| x == block.address());
            */
            for target in block.targets() {
                let mut edge_weight: usize = 0;

                let pos02: usize = order
                    .iter()
                    .position(|x| x == target)
                    .unwrap();

                for node in &ordered[min(pos01, pos02)+1 .. max(pos01, pos02)] {
                        edge_weight += node.len();
                }

                cost = cost + edge_weight;

            }


            pos01 += 1;
        }

        cost
    }




    // collection of such edges that generates cycles in the component
    // TODO: error handling - no backedges when graph is acyclic
    pub fn backedges(&self) -> Vec<(u64, u64)> {

        let mut backedges: Vec<(u64,u64)> = Vec::new();

        depth_first_search(self, Some(self.address()), |event| {
            if let DfsEvent::BackEdge(u, v) = event {
                backedges.push((u,v));
            }
        });
    
        backedges
    }


    // add the given edge to the VAG
    fn add_edge(&mut self, edge: (u64, u64)) {

        self.node_at_target_mut(edge.0).add_target(edge.1);

    }

    // add the given edges to the VAG
    // the edges vec<(u64, u64)> needs to be ordered
    fn add_edges(&mut self, edges: &Vec<(u64,u64)>) {

        // TODO: optimalize !!
        for &edge in edges {
            self.add_edge(edge);
        }
        

    }

    // erase the given edge from the VAG
    fn erase_edge(&mut self, edge: (u64, u64)) {
        self.node_at_target_mut(edge.0).erase_target(edge.1);
    }

    // erase the given edges to the VAG
    pub fn erase_edges(&mut self, edges: &Vec<(u64, u64)>)  {

        // TODO: optimalize !!
        for &edge in edges {
            self.erase_edge(edge);
        }

    }

    // given the list of incoming edges: merge their sources into one new vertex
    pub fn add_source_vertex(&mut self, in_edges: &Vec<(u64, u64)>) {
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

    }


    // given the list of outgoing edges: merge their targets into one new vertex
    pub fn add_target_vertex(&mut self, out_edges: &Vec<(u64, u64)>) {

        // delete the original outgoing edges
        self.erase_edges(out_edges);

        // the targets of these edges then are merged into one vertex
        // with given indegree and small length
        self.add_block(
            NoInstrBasicBlock {
                address: 0x1,
                len: 0,
                targets: vec![],
                indegree: out_edges.len(),
            }
        );

        // the new outgoing edges will have this new vertex as target
        let mut new_outgoing: Vec<(u64,u64)> = Vec::new();
        for (source, _target) in out_edges {
            new_outgoing.push( (*source, 0x1) );
        }

        // add these newly generated edges
        self.add_edges(&new_outgoing);

        // the nodes in VAG are sorted by the address
        self.nodes_mut().sort_by_key(|x| x.address());        

    }


    // add a new node to the existing list of nodes
    fn add_block(&mut self, node: NoInstrBasicBlock) {

        self.nodes.push(node);
        self.nodes_mut().sort_by_key(|x| x.address());

    }



    // gets a VAG and returns the "optimal" order of its vertices
    pub fn weighted_order(&self) -> Vec<u64> {
        
        // TODO: is_cyclic_directed is recursive - maybe use topsort, but that seems redundant
        if !(is_cyclic_directed(self)) {
            // Kahn's algorithm
            let mut kahngraph: KahnGraph = KahnGraph::from_vag(self);
            let topsort = kahngraph.kahn_algorithm();   

            topsort

        } else {
            println!("NOT acyclic!");

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
                    // ERROR: println!("{:#x?}", comp_vag);

                    // Kahn's algorithm for the given component
                    let mut kahngraph: KahnGraph = KahnGraph::from_vag(&comp_vag);
                    let mut ord_comp: Vec<u64> = kahngraph.kahn_algorithm();

                    // delete the auxiliary nodes from the order
                    ord_comp.retain(|&x| x != 0x0 && x != 0x1);

                    ordered_components.push(ord_comp);
                }
            }

            // println!("{:#x?}", topsort_condensed);
            // println!("{:#x?}", ordered_components);

            // insert the inside orders of the components in the ordered components list
            let mut topsort: Vec<u64> = Vec::new();

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
    
            // println!("{:#x?}", topsort)

            topsort
        }
    }

    // from graph to .dot
    fn render_to<W: std::io::Write>(&self, output: &mut W) -> dot2::Result {
        dot2::render(self, output)
    }



}




    


// for Tarjan's scc to work we need the following traits to be implemented for VAG
// NOTE: there is a topologiccal sort in petgraph - but it is DFS based

impl petgraph::visit::GraphBase for VirtualAddressGraph {
    type NodeId = u64;
    type EdgeId = (u64, u64);
}


impl<'a> petgraph::visit::IntoNodeIdentifiers for &'a VirtualAddressGraph {
    type NodeIdentifiers = impl Iterator<Item = Self::NodeId> + 'a;

    fn node_identifiers(self) -> Self::NodeIdentifiers {
        self.nodes().iter().map(|x| x.address())
    }
}

impl<'a> petgraph::visit::IntoNeighbors for &'a VirtualAddressGraph {
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


impl<'a> petgraph::visit::NodeIndexable for &'a VirtualAddressGraph {

    fn node_bound(self: &Self) -> usize {
        self.nodes().len()
    }

    fn to_index(self: &Self, a: Self::NodeId) -> usize {
        self
            .nodes()
            .binary_search_by(|block| block.address().cmp(&a))
            .unwrap()
    }

    fn from_index(self: &Self, i:usize) -> Self::NodeId {
        assert!(i < self.nodes().len(),"the requested index {} is out-of-bounds", i);
        self.nodes()[i].address()
    }

}

impl petgraph::visit::Visitable for VirtualAddressGraph {
    type Map = HashSet<Self::NodeId>;

    fn visit_map(&self) -> Self::Map {
        HashSet::with_capacity(self.nodes().len())
    }

    fn reset_map(&self, map: &mut Self::Map) {
        map.clear()
    }
}


impl<'a> dot2::Labeller<'a> for VirtualAddressGraph {
    type Node = u64;
    type Edge = (u64, u64);
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


impl<'a> dot2::GraphWalk<'a> for VirtualAddressGraph {
    type Node = u64;
    type Edge = (u64, u64);
    type Subgraph = ();

    // all nodes of the graph
    fn nodes(&self) -> dot2::Nodes<'a, Self::Node> {
        self.nodes().iter().map(|n| n.address()).collect()
    }

    // all edges of the graph
    fn edges(&'a self) -> dot2::Edges<'a, Self::Edge> {

        let mut edges: Vec<(u64, u64)> = Vec::new();

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
