
use std::cmp::*;
use std::collections::{BTreeMap, HashSet, HashMap};

use crate::{cfg::*, NodeWeight};
use crate::vagraph::kahn::*;
use crate::vagraph::scc::*;

use std::fmt::{Debug, Display, LowerHex};
use std::hash::Hash;
use std::default::Default;

// use either::*;

// use petgraph::Direction::Incoming;
use serde::{Serialize, Deserialize};

use petgraph::algo::{is_cyclic_directed, tarjan_scc};
use petgraph::visit::*;



pub trait VAGNodeId: Copy + Eq + Debug + Display + Hash + Ord + LowerHex {}

impl<T: Copy + Eq + Debug + Display + Hash + Ord + LowerHex> VAGNodeId for T {}

// at some point we would like to use phantom source and target nodes
// to do so - with generic types - we need to introduce an enum with 
// note:    no traits are implemented by hand, hence considering the Ord, PartialOrd traits
//          the order of the variants IS IMPORTANT
#[derive(Serialize, Deserialize, Copy, Clone, Debug, PartialEq, Eq, Hash, Ord, PartialOrd)]
pub enum Vertex<N: VAGNodeId> {
    Source,
    Id(N),
    Sink,
}

impl<N: VAGNodeId> Vertex<N> {

    pub fn id(&self) -> Result<N, &str> {
        match self {
            Self::Source => Err("phantom source node"),
            Self::Sink => Err("phantom sink node"),
            Self::Id(node) => Ok(*node),
        }
    }

} 

///////////////////// TRAITS for Vertex /////////////////////////

// display (it is needed for the test only)

impl<N: VAGNodeId> Display for Vertex<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Source => write!(f, "Source"),
            Self::Sink => write!(f, "Sink"),
            Self::Id(node) => write!(f, "{:x}", node),
        }
    }
}

// lowerhex (it is needed for the test only)

impl<N: VAGNodeId> LowerHex for Vertex<N> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Source => write!(f, "Source"),
            Self::Sink => write!(f, "Sink"),
            Self::Id(node) => LowerHex::fmt(node, f),
        }
    }
}

// default (it is needed for cost only)
// note: the generic type N needs to implement the copy trait
impl<N: VAGNodeId + Default> Default for Vertex<N> {
    fn default() -> Self {
        Vertex::Id( Default::default() )
    }
}

/////////////////////////////////////////////////////////////////////////

// TODO: safe more info about the node - e.g.: incoming neighbors
// in the ordering of the block only the number of instructions matter
#[derive(Serialize, Deserialize, Clone, Debug)]
pub struct NoInstrBasicBlock<N: VAGNodeId>
{
    // the virtual address of the block
    address: Vertex<N>,
    // the number of instructions in the block
    len: usize,
    // the addresses of block from which we can jump to the current block
    // that is: sources = all the direct predecessors of the block
    // note: indegree = #sources !!! (otherwise the block is invalid)
    sources: HashSet<Vertex<N>>,
    // the addresses of blocks where we will jump next 
    // that is: targets = all the direct successors of the block
    // note: its length is at most two
    targets: HashSet<Vertex<N>>,
    // number of blocks from we jump to here
    indegree: usize,
}
// if we consider the block alone, then its indegree is set to be 0

impl<N: VAGNodeId> NoInstrBasicBlock<N> {
    // sets an instance
    pub fn new(address: Vertex<N>, len: usize, sources: HashSet<Vertex<N>> ,targets: HashSet<Vertex<N>>, indegree: usize) -> Self {
        NoInstrBasicBlock::<N> { 
            address, 
            len,
            sources,
            targets,
            indegree,
        }
    }
    
    // the virtual address of the block
    pub fn address(&self) -> Vertex<N> {
        self.address
    }

    // the number of instructions 
    fn len(&self) -> usize {
        self.len
    }

    // a hashset reference of target blocks' addresses
    pub fn targets(&self) -> &HashSet<Vertex<N>> {
        &self.targets
    }

    // a hashset reference of source blocks' addresses
    pub fn sources(&self) -> &HashSet<Vertex<N>> {
        &self.sources
    }

    fn set_sources(&mut self, sources: &HashSet<Vertex<N>>) {
        // takes the union of self.sources and sources
        self.sources.extend(sources);
    }

    // deletes the given source from the sources hashset if it's there (which will hold all the time)
    // note: this also results in an indegree modification
    fn erase_source(&mut self, source: Vertex<N>) {
        if self.sources.remove(&source) {
            // if the given vertex is there -> decrease the indegree too!!
            self.decrease_indegree();
        }

    }

    // extends the vector of targets by the given address
    // note: we can not modify here the target's indegree !!!
    fn add_target(&mut self, target: Vertex<N>) {
        self.targets.insert(target);
        // if it is already in there -> returns false also
    }

    // deletes the given target from the targets vector if it's there (yes it is)
    // note: we can not modify here the target's indegree !!
    fn erase_target(&mut self, target: Vertex<N>) {
        self.targets.remove(&target);
    }

    // the indegree of the block
    pub fn indegree(&self) -> usize {
        self.indegree
    }

    // setter for the indegree
    fn set_indegree(&mut self, indegree: usize) {
        self.indegree = indegree;
    }

    /*
    // increase the indegree of the block by 1
    fn increase_indegree(&mut self) {
        self.set_indegree(self.indegree + 1);
    }
    */

    // decrease the indegree of the block by 1
    // note: extra check wil be needed - this can not go below zero
    fn decrease_indegree(&mut self) {
        self.set_indegree(self.indegree - 1);
    }

}

// translates a BasicBlock to NIBB, that is counts the number of instructions
// TODO: is it any good for that specific choice - BB is my previous "dummy" struct
// BasicBlock struct - not generic type !!
// note: BB contains no information about the sourcing addresses -> sources: empty hashset
impl NoInstrBasicBlock<u64> {
    fn from_bb(bb: &BasicBlock) -> Self{

        let mut targets: HashSet<Vertex<u64>> = HashSet::new();
        for target in bb.targets() {
            targets.insert(Vertex::Id(*target));
        }

        NoInstrBasicBlock::<u64> { 
            address: Vertex::Id(bb.address()),
            len: bb.instructions().len(),
            sources: HashSet::<Vertex<u64>>::new(),
            targets,
            indegree: 0_usize,
        }
    }
}

///////////////////// TRAITS for NoInstrBasicBlock /////////////////////////

// N: Eq trait bound is declared previously

// equality of NIBB's whenever their addresses are the same
impl<N: VAGNodeId> PartialEq for NoInstrBasicBlock<N> {
    fn eq(&self, other: &Self) -> bool {
        self.address() == other.address()
    }
}

impl<N: VAGNodeId> Eq for NoInstrBasicBlock<N> {}

// order of NIBB's: first by the number of incoming edges then by the length of basic block
// WHY: is this bound on N is needed ?
impl<N: VAGNodeId> PartialOrd for NoInstrBasicBlock<N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<N: VAGNodeId> Ord for NoInstrBasicBlock<N> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.indegree().cmp(&other.indegree())
            .then(self.len().cmp(&other.len()))
    }
}

//////////////////////////////////////////////////////////////////////////////////

// almost the same as ControlFlowGraph but with NoInstrBasicBlock structs
#[derive(Serialize, Deserialize, Debug, Clone)]
pub struct VirtualAddressGraph<N: VAGNodeId> {
    // start: N - TODO!
    address: Vertex<N>,
    nodes: HashMap<Vertex<N>, NoInstrBasicBlock<N>>,
}

// ControlFlowGraph struct - not generic type
impl VirtualAddressGraph<u64> {

    // TODO: is this specific choice for my construction any good ?
    // creates an instance from a ControlFlowGraph
    pub fn from_cfg(cfg: &ControlFlowGraph) -> Self {
        // let mut nodes: Vec<NoInstrBasicBlock<u64>> = Vec::new();

        let mut nodes: HashMap<Vertex<u64>, NoInstrBasicBlock<u64>> = HashMap::new();

        for block in cfg.blocks() {
            let node: NoInstrBasicBlock<u64> = NoInstrBasicBlock::from_bb(block);
            let address: Vertex<u64> = Vertex::Id(block.address());
            nodes.insert(address,node);
        }

        // nodes.sort_by_key(|node| node.address());

        let mut vag: VirtualAddressGraph<u64> = 
        VirtualAddressGraph { 
            address: Vertex::Id(cfg.address()), 
            nodes,
        };

        // TODO: merge this two iterations - more effective algoithm!!
        vag.update_sources_and_indegrees();

        vag
    }

}

impl<N: VAGNodeId> VirtualAddressGraph<N> {
    // creates a new instance given its address and blocks
    // need: keep the fields private from scc
    pub fn new(address: Vertex<N>, nodes: HashMap<Vertex<N>, NoInstrBasicBlock<N>>) -> Self {
        VirtualAddressGraph::<N> { 
            address, 
            nodes,
        }
    }

    // returns the list (BTreeMap - sorted by address) of (vertex, sources) pairs of an instance
    fn sources(&self) -> BTreeMap<Vertex<N>, HashSet<Vertex<N>>> {

        let mut sources: BTreeMap<Vertex<N>, HashSet<Vertex<N>>> = BTreeMap::new();

        for (id, node) in self.nodes() {
            sources.entry(*id).or_insert( HashSet::<Vertex<N>>::new() );

            for target in node.targets() {
                sources
                    .entry(*target)
                    .and_modify(|s| { 
                        s.insert(*id); 
                    } )
                    .or_insert_with( || {
                        let mut s: HashSet<Vertex<N>> = HashSet::new();
                        s.insert(*id);
                        s
                    } );
            }
        }

        sources

    }

    // MAYBE: this will be deleted later
    // an extra iteration through the nodes of the graph to update the set of sources of the vertices
    pub fn update_sources(&mut self) {
        let sources: BTreeMap<Vertex<N>, HashSet<Vertex<N>>> = self.sources();

        for (id, node) in self.nodes_mut() {
            node.set_sources( sources.get(id).unwrap() );
        }
    }


    // MAYBE: this will be deleted later 
    // returns the list (BTreeMap - sorted by address) of indegrees of an instance
    // TODO: iterating through the elements of HashMap - is it cheap?
    fn in_degrees(&self) -> BTreeMap<Vertex<N>, usize> {

        let mut indeg: BTreeMap<Vertex<N>, usize> = BTreeMap::new();
        
        for (id, node) in self.nodes() {
            indeg.entry(*id).or_insert(0);

            for target in node.targets() {
                indeg.entry(*target).and_modify(|counter| *counter += 1).or_insert(1);
            }
        }
        
        indeg
    }

    // MAYBE: this will be deleted later
    // an extra iteration through the nodes of the graph to update the indegrees of the vertices
    // maybe there is a more clever/effective way to do this - where one can use the iteration in
    // from_cfg() method to get the indegrees
    // note: whenever we modify the VAG instance we need to update the indegrees
    // MAYBE: store the nodes in a BTreeMap (ordered by what?);
    pub fn update_in_degrees(&mut self) {
        let indeg = self.in_degrees();

        for (id, node) in self.nodes_mut() {
            node.set_indegree( *indeg.get(id).unwrap() );
        }
    }

    // an extra iteration through the nodes of the graph to update the set of sources and
    // the indegrees of the vertices - simultaneously
    // it is really pricey in runtime, hence we would like to use it only once
    // and whenever we modify something locally, then do the update also locally there
    pub fn update_sources_and_indegrees(&mut self) {
        let sources: BTreeMap<Vertex<N>, HashSet<Vertex<N>>> = self.sources();

        for (id, node) in self.nodes_mut() {
            node.set_sources( sources.get(id).unwrap() );
            node.set_indegree( node.sources().len() );
        }

    }



    // the start virtual address
    pub fn address(&self) -> Vertex<N> {
        self.address
    }

    // unmutable slice of nodes
    pub fn nodes(&self) -> &HashMap<Vertex<N>, NoInstrBasicBlock<N>> {
        &self.nodes
    }

    // mutable slice of nodes
    fn nodes_mut(&mut self) -> &mut HashMap<Vertex<N>, NoInstrBasicBlock<N>> {
        &mut self.nodes
    }

    // reference to a node with a given address
    // TODO: error handling
    pub fn node_at_target(&self, target: Vertex<N>) -> &NoInstrBasicBlock<N> {
        self.nodes().get(&target).unwrap()

        /*
        // VAG is ordered by addresses
        let pos: usize = self.nodes().binary_search_by(|x| x.address().cmp(&target)).unwrap();
        // let pos = self.nodes().iter().position(|x| x.address() == target).unwrap();
        &self.nodes()[pos]
        */
    }

    // mutable reference to a node with a given address
    fn node_at_target_mut(&mut self, target: Vertex<N>) -> &mut NoInstrBasicBlock<N> {
        self.nodes_mut().get_mut(&target).unwrap()

        /*
        let pos: usize = self.nodes().binary_search_by(|x| x.address().cmp(&target)).unwrap();
        // let pos = self.nodes().iter().position(|x| x.address() == target).unwrap();
        &mut self.nodes_mut()[pos]
        */
    }

    // generates the condensed vag - using Tarjan's algorithm
    // TODO: in the scc module there is a method generating components (basicly does
    // the same as the first part of this) -> MERGE THEM!
    fn condense(&self) -> Self {
        
        // tarjan_scc returns reversed topological order
        let scc = tarjan_scc(self);

        // the node label for a sc component = first node's label in tarjan's output
        // TODO: this ad hoc choice seems not that good (considering that later the id will be the smallest address)
        // TODO: let the component's ID be the smallest node id in there
        let mut comp_dict: BTreeMap<Vertex<N>, Vertex<N>> = BTreeMap::new();
        for comp in &scc {
            // the component's ID be the smallest node id in there
            let value = comp.iter().min().unwrap();
            for node in comp {
                comp_dict.insert(*node, *value);
            }
        }

        let mut nodes: HashMap<Vertex<N>, NoInstrBasicBlock<N>> = HashMap::new();

        for comp in &scc {
            // the component's ID be the smallest node id in there
            let address: Vertex<N> = *comp.iter().min().unwrap();
            let mut length: usize = 0;
            let mut targets: HashSet<Vertex<N>> = HashSet::new();

            for node in comp {

                // the block at the given address
                let node = self.node_at_target(*node);

                length += node.len();

                for target in node.targets() {
                    if !(comp.contains(target) || targets.contains(target)) {
                        // is this .get() fast for BTreeMap ??
                        targets.insert( *(comp_dict.get(target).unwrap()) );
                    }
                }   
            }

            nodes.insert( 
                address, 
                NoInstrBasicBlock::<N> { 
                    address, 
                    len: length,
                    sources: HashSet::<Vertex<N>>::new(),
                    targets,
                    indegree: 0_usize,
                }
            );
        }

        let mut vag: VirtualAddressGraph<N> =
        VirtualAddressGraph { 
            address: self.address(),
            nodes,
        };

        // the information about the vertices coming in the given vertex can not be
        // derived locally - it seems like a better choice to update this data by an
        // extra iteration on the condensed graph's nodes
        vag.update_sources_and_indegrees();

        vag

    }


    // this method is just an inspector -> no Vertex::{Source, Sink} will be presented
    // no need to wrap the nodes in the argument into Vertex enum
    pub fn cost_of_order(&self, order: Vec<N>) -> usize {

        // the list of nodes in the given order
        let mut ordered: Vec<&NoInstrBasicBlock<N>> = Vec::new();
        let mut cost: usize = 0;

        for address in &order {
            ordered.push(self.node_at_target(Vertex::Id(*address)));
        }

        // starting from the first node of the order we iterate through all the vertices
        // and consider only the outgoing edges (whose are incoming edges for other, no worries)
        // TODO: if there is a back-and-forth edge between nodes: its weight = 0, which is not correct
        for (pos01, block) in ordered.iter().enumerate() {
            for target in block.targets() {
                let mut edge_weight: usize = 0;
                
                // the given order can be any arbitrary, hence there is no binary search
                let pos02: usize = order
                    .iter()
                    .position(|&x| Vertex::Id(x) == *target)
                    .unwrap();

                // note: an edge goes from the last instruction of a block to the first instruction of the other block
                match pos01.cmp(&pos02) {
                    // edge goes forward: pos01 and pos02 are not counted
                    Ordering::Less => {
                        for node in &ordered[pos01+1..pos02] {
                            edge_weight += node.len();
                        }
                    }
                    // edge goes backward: pos01 and pos02 are counted
                    Ordering::Greater => {
                        for node in &ordered[pos02..=pos01] {
                            edge_weight += node.len();
                        }
                    }
                    // loop edge: length of the given node (same as the target)
                    Ordering::Equal => {
                        edge_weight = block.len();
                    }
                }

                cost += edge_weight;

            }
        }

        cost
    }


    // collection of such edges that generates cycles in the component
    // TODO: error handling - no backedges when graph is acyclic
    pub fn backedges(&self) -> Vec<(Vertex<N>, Vertex<N>)> {

        let mut backedges: Vec<(Vertex<N>,Vertex<N>)> = Vec::new();

        depth_first_search(self, Some(self.address()), |event| {
            if let DfsEvent::BackEdge(u, v) = event {
                backedges.push((u,v));
            }
        });
    
        backedges
    }


    // add a new node to the existing list of nodes, without global updates on the graph
    // note: the necessary global updated is needed to be done at the place of modification
    fn add_block_without_update(&mut self, node: NoInstrBasicBlock<N>) {
        // add the new node to the graph
        self.nodes.insert(node.address(), node);
    }

    // given the list of incoming edges: merge their sources into one new vertex
    // TODO: error handling
    // since the source of the incoming edges is not in the VAG - we don't have to delete anything
    pub fn add_source_vertex(&mut self, in_edges: &[(Vertex<N>, Vertex<N>)]) {
        // the sources of these edges then are merged into one vertex
        // with 0 indegree, empty sources hashset and large length
        self.add_block_without_update(
            NoInstrBasicBlock {
                // the reason why we masked N into Vertrex<N> is to have the Vertex::{Source, Sink} fields
                address: Vertex::Source,
                len: 99999,
                sources: HashSet::<Vertex<N>>::new(),
                targets: in_edges.iter().map(|(_,t)| *t).collect(),
                indegree: 0,
            }
        );

        // the edges coming from the new vertex increases the indegrees of some of the already existing vertices
        // MAYBE: this extra update is not needed
        // self.update_in_degrees();

    }


    // given the list of outgoing edges: merge their targets into one new vertex
    // note: used only in scc::to_acyclic_vag hence the indegree update is there
    pub fn add_sink_vertex(&mut self, out_edges: &[(Vertex<N>, Vertex<N>)]) {

        // the targets of these edges then are merged into one vertex
        // with given indegree, hashset of sources and small length
        self.add_block_without_update(
            NoInstrBasicBlock {
                // the reason why we masked N into Vertrex<N> is to have the Vertex::{Source, Sink} fields
                address: Vertex::Sink,
                len: 0,
                sources: out_edges.iter().map(|(s,_)| *s).collect(),
                targets: HashSet::<Vertex<N>>::new(),
                indegree: out_edges.len(),
            }
        );

        // the old targets must be changed to be the new sink vertex
        for (source, target) in out_edges {
            let node = self.node_at_target_mut(*source);
            node.erase_target(*target);
            node.add_target(Vertex::Sink);
        }

        
    }

    // gets a VAG and returns the "optimal" order of its vertices
    // the final order won't contain Vertex::{Source, Sink}, hence we can unwrap the nodeids
    pub fn weighted_order(&self) -> Vec<N> {
        
        // TODO: is_cyclic_directed is recursive - maybe use topsort, but that seems redundant
        if !(is_cyclic_directed(self)) {
            // Kahn's algorithm
            let mut kahngraph: KahnGraph<N> = KahnGraph::from_vag(self);
            // if there is no directed cycle in the graph, then we only have Vertex::Id variants
            kahngraph
                .kahn_algorithm()
                .iter()
                .map(|x| x.id().unwrap())
                .collect()
        } else {
            // collapse the strongly connected components into single vertices
            let condensed = self.condense();

            // Kahn's algorithm for the condensed graph
            let mut kahngraph: KahnGraph<N> = KahnGraph::from_vag(&condensed);
            let mut topsort_condensed = kahngraph.kahn_algorithm();

            // Kahn's algorithm for the strongly connected components
            let components: Vec<Component<N>> = Component::from_vag(self);

            // the order inside the components collected in a HashMap - key: id, value: ordered vector
            let mut ordered_components: HashMap<Vertex<N>, Vec<Vertex<N>>> = HashMap::new();
            // let mut ordered_components: Vec<Vec<Vertex<N>>> = Vec::new();

            for comp in components {
                // if the component is trivial (i.e. single vertex) -> do nothing
                if !comp.trivial() {
                    // MAYBE: this is very expensive in runtime -> modify the component struct ?
                    // let comp_address: Vertex<N> = *comp.nodes().iter().min().unwrap();
                    // break the cycles and add auxiliary source and target nodes
                    let comp_vag = comp.to_acyclic_vag();

                    // Kahn's algorithm for the given component
                    let mut kahngraph: KahnGraph<N> = KahnGraph::from_vag(&comp_vag);
                    let mut ord_comp: Vec<Vertex<N>> = kahngraph.kahn_algorithm();

                    // delete the auxiliary nodes (Vertex::Source and Vertex::Sink) from the order
                    ord_comp.retain(|&x| x != Vertex::Source && x != Vertex::Sink);

                    ordered_components.insert(comp.compid(), ord_comp);
                }
            }

            // insert the inside orders of the components in the ordered components list
            // note: the Vertex enum wrap is not needed anymore 
            let mut topsort: Vec<N> = Vec::new();

            while let Some(id) = topsort_condensed.pop() {
                if let Some(mut component) = ordered_components.remove(&id){
                    while let Some(node) = component.pop(){
                        topsort.push(node.id().unwrap());
                    }
                } else {
                    topsort.push(id.id().unwrap());
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


    // erase the given edge from the VAG, which MUST BE in the edge set of the graph
    // note: this also modifies the .sources and the .indegree fields of the target node
    fn erase_edge(&mut self, edge: (Vertex<N>, Vertex<N>)) {
        self.node_at_target_mut(edge.0).erase_target(edge.1);
        self.node_at_target_mut(edge.1).erase_source(edge.0);    
    }

    // erase the given edges to the VAG
    // note:    we only use this method when we erase the backtracking edges in the Component struct's
    //          to_acyclic_vag() method - since erase_edge() modifies data for both endpoints of the given 
    //          edge, hence no extra modificítion is needed when used
    pub fn erase_edges(&mut self, edges: &[(Vertex<N>, Vertex<N>)])  {
        for &edge in edges {
            self.erase_edge(edge);
        }
    }



}




    
/////////////////////// TRAITS for VirtualAddressGraph //////////////////////////

// package: petgraph
// for graph algorithms and traversal

// for Tarjan's scc to work we need the following traits to be implemented for VAG
// NOTE: there is a topological sort in petgraph - but it is DFS based

impl<N: VAGNodeId> petgraph::visit::GraphBase for VirtualAddressGraph<N> {
    type NodeId = Vertex<N>;
    // type EdgeId = (Vertex<N>, Vertex<N>);
    type EdgeId = (Self::NodeId, Self::NodeId);
}

impl<'a, N: VAGNodeId> petgraph::visit::IntoNodeIdentifiers for &'a VirtualAddressGraph<N> {
    type NodeIdentifiers = impl Iterator<Item = Self::NodeId> + 'a;

    fn node_identifiers(self) -> Self::NodeIdentifiers {
        self.nodes().iter().map(|(x,_)| *x)
    }
}

impl<'a, N: VAGNodeId> petgraph::visit::IntoNeighbors for &'a VirtualAddressGraph<N> {
    type Neighbors = impl Iterator<Item = Self::NodeId> + 'a;

    fn neighbors(self, a: Self::NodeId) -> Self::Neighbors {

        self
            .nodes()
            .get(&a)
            .unwrap()
            .targets()
            .iter()
            .copied()

    }
}

impl<'a, N: VAGNodeId> petgraph::visit::NodeIndexable for &'a VirtualAddressGraph<N> {
    fn node_bound(&self) -> usize {
        self.nodes().len()
    }

    fn to_index(&self, a: Self::NodeId) -> usize {
        // iteration is stable for immutable reference 
        // that is: a simple .iter() will do the job

        self
            .nodes()
            .keys()
            .position(|&x| x == a)
            .unwrap()

        /*
        self
            .nodes()
            .binary_search_by(|block| block.address().cmp(&a))
            .unwrap()
        */
    }

    fn from_index(&self, i:usize) -> Self::NodeId {
        assert!(i < self.nodes().len(),"the requested index {} is out-of-bounds", i);
        *self
            .nodes()
            .keys()
            .nth(i)
            .unwrap()
    }

}

impl<N: VAGNodeId> petgraph::visit::Visitable for VirtualAddressGraph<N> {
    type Map = HashSet<Self::NodeId>;

    fn visit_map(&self) -> Self::Map {
        HashSet::with_capacity(self.nodes().len())
    }

    fn reset_map(&self, map: &mut Self::Map) {
        map.clear()
    }
}



impl<'a, N: VAGNodeId> petgraph::visit::IntoNeighborsDirected for &'a VirtualAddressGraph<N> {
    type NeighborsDirected = impl Iterator<Item = Self::NodeId> + 'a;

    fn neighbors_directed(self, n: Self::NodeId, d: petgraph::Direction) -> Self::NeighborsDirected {
        match d {
            petgraph::Direction::Outgoing => {
                // outgoing nieghbours = targets
                self.node_at_target(n).targets().iter().copied()
            }
            petgraph::Direction::Incoming => {
                // incoming neighbours = sources
                self.node_at_target(n).sources().iter().copied()
            }
        }
    }

} 


////////////////////////////////////////////////////////////////////////////////////

// package: dots
// for .dot and hence .svg plot

impl<'a, N: VAGNodeId> dot2::Labeller<'a> for VirtualAddressGraph<N> {
    type Node = Vertex<N>;
    type Edge = (Vertex<N>, Vertex<N>);
    type Subgraph = ();

    // .dot compatible identifier naming the graph
    fn graph_id(&'a self) -> dot2::Result<dot2::Id<'a>> {
        dot2::Id::new("control_length_flow")
    }

    // maps n to unique (valid .dot) identifier 
    fn node_id(&'a self, n: &Self::Node) -> dot2::Result<dot2::Id<'a>> {
        // TODO: error handling
        dot2::Id::new(format!("N0x{:x}", n.id().unwrap()))
    }

    // label of a node
    fn node_label(&'a self, n: &Self::Node) -> dot2::Result<dot2::label::Text<'a>> {
        let label = self
            .nodes()
            .get_key_value(n)
            .map(|(x,y)| format!("{:x}: {}", x.id().unwrap(), y.len()))
            .unwrap();

        Ok(dot2::label::Text::LabelStr(
            label.into()
        ))
    }

}


impl<'a, N: VAGNodeId> dot2::GraphWalk<'a> for VirtualAddressGraph<N> {
    type Node = Vertex<N>;
    type Edge = (Vertex<N>, Vertex<N>);
    type Subgraph = ();

    // all nodes of the graph
    fn nodes(&self) -> dot2::Nodes<'a, Self::Node>
    // WHY?
    where [N]: ToOwned,
    {
        self
            .nodes()
            .iter()
            .map(|(&x,_)| x)
            .collect()
    }

    // all edges of the graph
    fn edges(&'a self) -> dot2::Edges<'a, Self::Edge> 
    // WHY?
    where [(N,N)]: ToOwned,
    {

        self
            .nodes()
            .iter()
            .flat_map(|(address,block)| 
                block.targets().iter().map(|target| (*address, *target))
            )
            .collect()
    

        /*
        let mut edges: Vec<(Vertex<N>, Vertex<N>)> = Vec::new();

        for (source, node) in self.nodes() {
            // let source = block.address();
            for target in node.targets() {
                edges.push( (*source, *target) );
            }
        }

        edges.into_iter().collect()

        */
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

// trait: NodeWeight  
// for obtaining the node weights

impl<N: VAGNodeId> NodeWeight for &VirtualAddressGraph<N> {
    type Node = Vertex<N>;

    fn weight(&self, node: Self::Node) -> usize {
        self.node_at_target(node).len()
    }

}

////////////////////////////////////////////////////////////////////////////////////


// TBC !! - how to do this ??

#[derive(Serialize, Deserialize)]
pub struct UnwrappedBasicBlock<N: VAGNodeId> {
    address: N,
    len: usize,
    targets: Vec<N>,
    indegree: usize,
}

impl<N: VAGNodeId> UnwrappedBasicBlock<N> {

    fn address(&self) -> N {
        self.address
    }

    pub fn to_nibb(&self) -> NoInstrBasicBlock<N> {

        NoInstrBasicBlock{ 
            address: Vertex::Id(self.address), 
            len: self.len,
            sources: HashSet::<Vertex<N>>::new(), 
            targets: self.targets.iter().map(|&x| Vertex::Id(x)).collect(), 
            indegree: self.indegree, 
        }

    }

}

#[derive(Serialize, Deserialize)]
pub struct UnwrappedVAGraph<N: VAGNodeId> {
    address: N,
    nodes: Vec<UnwrappedBasicBlock<N>>,
}

impl<N: VAGNodeId> UnwrappedVAGraph<N> {

    fn nodes(&self) -> &[UnwrappedBasicBlock<N>] {
        &self.nodes
    }

    pub fn to_vag(&self) -> VirtualAddressGraph<N> {

        let mut wrappednodes: HashMap<Vertex<N>, NoInstrBasicBlock<N>> = HashMap::new();

        for block in self.nodes() {
            wrappednodes.insert(
                Vertex::Id(block.address()),
                block.to_nibb(),
            );
        }


        VirtualAddressGraph { 
            address: Vertex::Id(self.address), 
            nodes: wrappednodes,
        }

    }

}
