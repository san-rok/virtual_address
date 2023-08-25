// pub mod vagraph;
use crate::vagraph::vag::*;

// generic functions

use std::cmp::*;
use std::collections::HashMap;
use std::default::Default;
use std::fmt::{Debug, Display, LowerHex};
use std::hash::Hash;

use petgraph::visit::{
    GraphBase, IntoNeighbors, IntoNeighborsDirected, IntoNodeIdentifiers, NodeIndexable,
};

use kendalls::tau_b;

// no restrictions on NodeId, EdgeId, etc here -> all goes to VAG

fn to_vag<G>(g: G, entry: G::NodeId) -> Result<VirtualAddressGraph<G::NodeId>, SortError>
where
    G: IntoNodeIdentifiers + IntoNeighbors + IntoNeighborsDirected + NodeWeight<Node = G::NodeId>,
    <G as GraphBase>::NodeId: Copy + Eq + Debug + Hash + Ord,
{
    // if the given graph is empty, then return error
    if g.node_identifiers().count() == 0 {
        return Err(SortError::EmptyGraph);
    }

    // if the given entry address is not a node of the graph, then return error
    if !g.node_identifiers().any(|x| x == entry) {
        return Err(SortError::InvalidInitialAddress);
    }

    let mut nodes: HashMap<Vertex<G::NodeId>, NoInstrBasicBlock<G::NodeId>> = HashMap::new();

    // going over all the vertices of the given input graph
    // we collect the relevant data in a hashmap, which will be used later in the VAGraph instance
    for block in g.node_identifiers() {
        nodes.insert(
            Vertex::Id(block),
            NoInstrBasicBlock::<G::NodeId>::new(
                Vertex::Id(block),
                g.weight(block),
                g.neighbors_directed(block, petgraph::Direction::Incoming)
                    .map(Vertex::Id)
                    .collect(),
                g.neighbors_directed(block, petgraph::Direction::Outgoing)
                    .map(Vertex::Id)
                    .collect(),
                g.neighbors_directed(block, petgraph::Direction::Incoming)
                    .count(),
            ),
        );
    }

    let mut vag: VirtualAddressGraph<G::NodeId> =
        VirtualAddressGraph::new(Vertex::Id(entry), nodes);

    let outgoing_edges = vag.erase_outgoing_edges();
    log::debug!("the following edges leave the graph, hence deleted:");
    for (s, t) in outgoing_edges {
        log::debug!("{:x?} --> {:x?}", s, t);
    }

    Ok(vag)
}

/// Returns an order on the blocks of the given control flow graph, such that
/// the overall jumps' weights are locally minimalized.
/// This local minimalization is achieved by Kahn's algorithm spiced up with the
/// following tiebraking heuristic: whenever in a step of the Kahn's algorithm
/// there are multiple nodes to put in the order we choose that which has the most
/// incoming edges (originally) AND the most number of instructions.
///
/// # Arguments
///
/// * `g` - the control flow graph (satisfying several natural traits from petgraph);
/// * `entry` - the starting blocks address (which hence must be a node of g);
///
/// # Errors
///
/// See below!
///
/// etc.
///

pub fn cfg_sort<G>(g: G, entry: G::NodeId) -> Result<Vec<G::NodeId>, SortError>
where
    G: IntoNodeIdentifiers + IntoNeighbors + IntoNeighborsDirected + NodeWeight<Node = G::NodeId>,
    <G as GraphBase>::NodeId: Copy + Eq + Debug + Hash + Ord,
{
    // reading and converting the data (with error propagation)
    let vag = to_vag(g, entry)?;

    // if there exists a node which we can not reach from entry -> error
    let unreachable = vag.unreachable_from_start();
    if !unreachable.is_empty() {
        log::debug!(
            "from the start: {:x?}, the following nodes are not reachable:",
            entry
        );
        for id in unreachable {
            log::debug!("{:x?}", id.id().unwrap());
        }
        return Err(SortError::UnreachableNodes);
    }

    let topsort = vag.weighted_order();
    Ok(topsort)
}

/// Given an order on the block of a control flow graph, it returns an instance of the CfgOrder
/// struct (for definition see below) to gain information about the performance of that order
/// compared to the original order of the blocks (by default: ascending by the addresses)
///
/// # Arguments
///
/// * `g`       - the control flow graph (satisfying several natural traits from petgraph);
/// * `entry`   - the starting blocks address (which hence must be a node of g);
/// * `order`   - the order of the block's addresses we would like to test/compare;
///
/// # Errors
///
/// See below!
///
/// etc.
///

pub fn cfg_cost<G>(
    g: G,
    entry: G::NodeId,
    order: &[G::NodeId],
) -> Result<CfgOrder<G::NodeId>, CostError>
where
    G: IntoNodeIdentifiers + IntoNeighbors + IntoNeighborsDirected + NodeWeight<Node = G::NodeId>,
    <G as GraphBase>::NodeId: Copy + Eq + Debug + Hash + Ord + Default,
{
    // TODO: what if the input is bad again ?
    let vag: VirtualAddressGraph<G::NodeId> = to_vag(g, entry).unwrap();

    // the original order of the nodes is the ascending order of the ids
    let mut original_order: Vec<G::NodeId> = Vec::new();
    for node in vag.nodes().keys() {
        original_order.push(node.id().unwrap());
    }
    original_order.sort();

    // if some nodes missing or there are too much -> return error
    match original_order.len().cmp(&order.len()) {
        Ordering::Less => Err(CostError::MoreNodesthanOriginal),
        Ordering::Greater => Err(CostError::LessNodesThanOriginal),
        Ordering::Equal => {
            let kendall_tau = tau_b(&original_order, order).unwrap().0;
            let original_cost: usize = vag.cost_of_order(&original_order);
            let sorted_cost: usize = vag.cost_of_order(order);

            Ok(CfgOrder {
                entry: entry,
                order: order.to_vec(),
                original_order: original_order,
                cost: sorted_cost,
                original_cost: original_cost,
                kendall_tau: kendall_tau,
            })
        }
    }
}

/// Given an order on the control flow graph's blocks it stores information about
/// its optimality (in the previous sense), compared to the original order of the blocks
///
/// # Fields
///
/// * `entry`           - the starting blocks address (note: it can happen that in the original
///                       order its not the first element);
/// * `order`           - the order we would like to test;
/// * `original_order`  - the original order of the blocks (ascending by addresses);
/// * `cost`            - the cost of the given order;
/// * `original_cost`   - the cost of the original order;
/// * `kendall_tau`     - it measures the difference between two orders (in our case the original
///                       and the given), it's a real number between -1 and +1, where -1 means the
///                       given order is reversing the original, menawhile +1 means that the two orders
///                       are the same;
///
#[derive(Debug, Clone)]
pub struct CfgOrder<N> {
    entry: N,
    order: Vec<N>,
    original_order: Vec<N>,
    cost: usize,
    original_cost: usize,
    kendall_tau: f64,
}

impl<N> CfgOrder<N>
where
    N: Copy + Eq + Debug + Hash + Ord + Default,
{
    pub fn is_better(&self) -> bool {
        self.cost <= self.original_cost
    }
}

impl<N: Display> Display for CfgOrder<N>
where
    N: Copy + Eq + Debug + Display + Hash + Ord + LowerHex + Default,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "starting block's address: {}", self.entry).ok();
        writeln!(f, "original order, sorted order").ok();
        for i in 0..self.original_order.len() {
            writeln!(f, "{:x}, {:x}", self.original_order[i], self.order[i]).ok();
        }
        writeln!(f, "kendall tau: {:#?}", self.kendall_tau).ok();
        writeln!(f, "cost of original order: {}", self.original_cost).ok();
        writeln!(f, "cost of topological sort: {} \n", self.cost)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn empty_graph() {
        let entry: Vertex<u64> = Vertex::Id(0x0);
        let vag: VirtualAddressGraph<u64> = VirtualAddressGraph::new(entry, HashMap::new());
        assert_eq!(
            to_vag(&vag, entry).is_err_and(|x| x == SortError::EmptyGraph),
            true
        );
    }

    #[test]
    fn not_connected() {
        let address: Vertex<u64> = Vertex::Id(0x0);
        let mut nodes: HashMap<Vertex<u64>, NoInstrBasicBlock<u64>> = HashMap::new();

        nodes.insert(
            Vertex::Id(0x0),
            NoInstrBasicBlock::new(
                Vertex::Id(0x0),
                1,
                std::collections::HashSet::<Vertex<u64>>::new(),
                std::collections::HashSet::<Vertex<u64>>::new(),
                0,
            ),
        );

        nodes.insert(
            Vertex::Id(0x1),
            NoInstrBasicBlock::new(
                Vertex::Id(0x1),
                10,
                std::collections::HashSet::<Vertex<u64>>::new(),
                std::collections::HashSet::<Vertex<u64>>::new(),
                0,
            ),
        );

        let vag: VirtualAddressGraph<u64> = VirtualAddressGraph::new(address, nodes);

        let vag = to_vag(&vag, address).unwrap();
        let result = cfg_sort(&vag, Vertex::Id(address));

        assert_eq!(
            result.is_err_and(|x| x == SortError::UnreachableNodes),
            true
        );
    }

    #[test]
    fn invalid_entry_address() {
        let address: Vertex<u64> = Vertex::Id(0x3);
        let mut nodes: HashMap<Vertex<u64>, NoInstrBasicBlock<u64>> = HashMap::new();

        nodes.insert(
            Vertex::Id(0x0),
            NoInstrBasicBlock::new(
                Vertex::Id(0x0),
                1,
                std::collections::HashSet::<Vertex<u64>>::new(),
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x1), Vertex::Id(0x2)]),
                0,
            ),
        );

        nodes.insert(
            Vertex::Id(0x1),
            NoInstrBasicBlock::new(
                Vertex::Id(0x1),
                10,
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x1)]),
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x2)]),
                1,
            ),
        );

        nodes.insert(
            Vertex::Id(0x2),
            NoInstrBasicBlock::new(
                Vertex::Id(0x2),
                5,
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x0), Vertex::Id(0x1)]),
                std::collections::HashSet::<Vertex<u64>>::new(),
                2,
            ),
        );

        let vag: VirtualAddressGraph<u64> = VirtualAddressGraph::new(address, nodes);

        assert_eq!(
            to_vag(&vag, address).is_err_and(|x| x == SortError::InvalidInitialAddress),
            true
        );
    }

    #[test]
    fn filtered_targets_two_nodes() {
        let address: Vertex<u64> = Vertex::Id(0x0);
        let mut nodes: HashMap<Vertex<u64>, NoInstrBasicBlock<u64>> = HashMap::new();

        nodes.insert(
            Vertex::Id(0x0),
            NoInstrBasicBlock::new(
                Vertex::Id(0x0),
                1,
                std::collections::HashSet::<Vertex<u64>>::new(),
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x1)]),
                0,
            ),
        );

        nodes.insert(
            Vertex::Id(0x1),
            NoInstrBasicBlock::new(
                Vertex::Id(0x1),
                10,
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x0)]),
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x2)]),
                0,
            ),
        );

        let vag: VirtualAddressGraph<u64> = VirtualAddressGraph::new(address, nodes);

        let out_vag = to_vag(&vag, address).unwrap();

        assert_ne!(
            out_vag
                .node_at_target(Vertex::Id(Vertex::Id(0x1)))
                .targets()
                .len(),
            vag.node_at_target(Vertex::Id(0x1)).targets().len()
        );
        assert_eq!(
            out_vag
                .node_at_target(Vertex::Id(Vertex::Id(0x1)))
                .targets()
                .len(),
            0
        );
    }

    #[test]
    fn filtered_targets_three_nodes_multiple_phantom_edges() {
        let address: Vertex<u64> = Vertex::Id(0x0);
        let mut nodes: HashMap<Vertex<u64>, NoInstrBasicBlock<u64>> = HashMap::new();

        nodes.insert(
            Vertex::Id(0x0),
            NoInstrBasicBlock::new(
                Vertex::Id(0x0),
                1,
                std::collections::HashSet::<Vertex<u64>>::new(),
                std::collections::HashSet::<Vertex<u64>>::from([
                    Vertex::Id(0x1),
                    Vertex::Id(0x2),
                    Vertex::Id(0x6),
                ]),
                0,
            ),
        );

        nodes.insert(
            Vertex::Id(0x1),
            NoInstrBasicBlock::new(
                Vertex::Id(0x1),
                10,
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x1)]),
                std::collections::HashSet::<Vertex<u64>>::from([
                    Vertex::Id(0x2),
                    Vertex::Id(0x7),
                    Vertex::Id(0x9),
                ]),
                1,
            ),
        );

        nodes.insert(
            Vertex::Id(0x2),
            NoInstrBasicBlock::new(
                Vertex::Id(0x2),
                5,
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x0), Vertex::Id(0x1)]),
                std::collections::HashSet::<Vertex<u64>>::from([Vertex::Id(0x6), Vertex::Id(0x7)]),
                2,
            ),
        );

        let vag: VirtualAddressGraph<u64> = VirtualAddressGraph::new(address, nodes);

        let out_vag = to_vag(&vag, address).unwrap();

        assert_ne!(
            out_vag
                .node_at_target(Vertex::Id(Vertex::Id(0x0)))
                .targets()
                .len(),
            vag.node_at_target(Vertex::Id(0x0)).targets().len()
        );
        assert_ne!(
            out_vag
                .node_at_target(Vertex::Id(Vertex::Id(0x1)))
                .targets()
                .len(),
            vag.node_at_target(Vertex::Id(0x1)).targets().len()
        );
        assert_ne!(
            out_vag
                .node_at_target(Vertex::Id(Vertex::Id(0x2)))
                .targets()
                .len(),
            vag.node_at_target(Vertex::Id(0x2)).targets().len()
        );

        assert_eq!(
            out_vag
                .node_at_target(Vertex::Id(Vertex::Id(0x0)))
                .targets()
                .len(),
            2
        );
        assert_eq!(
            out_vag
                .node_at_target(Vertex::Id(Vertex::Id(0x1)))
                .targets()
                .len(),
            1
        );
        assert_eq!(
            out_vag
                .node_at_target(Vertex::Id(Vertex::Id(0x2)))
                .targets()
                .len(),
            0
        );
    }
}

// implement Debug trait by hand later !!

/// The usual errors that can arose whenever we use the cfg_sort(g, entry) function.
///
/// # Variants
///
/// * `EmptyGraph`              - the input graph: g is empty;
/// * `UnreachableNodes`        - from the given entry address we can not reach all the nodes of
///                               the control flow graph;
/// *`InvalidInitialAddress`    - there is no block in g at the given entry address;
///
/// etc.
///
#[derive(Debug, PartialEq, Eq)]
pub enum SortError {
    EmptyGraph,
    UnreachableNodes,
    InvalidInitialAddress,
}

/// The usual errors that can arose whenever we use the cfg_cost(g, entry, order) function.
///
/// # Variants
///
/// * `LessNodesThanOriginal` - the given order slice contains less nodes than g has;
/// * `MoreNodesThanOriginal` - the given order slice contains more nodes than g has;

#[derive(Debug)]
pub enum CostError {
    LessNodesThanOriginal,
    MoreNodesthanOriginal,
}
