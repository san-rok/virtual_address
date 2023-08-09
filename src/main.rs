
// https://github.com/m4b/goblin/blob/master/examples/lazy_parse.rs
// goblin::ProgramHeader: https://refspecs.linuxfoundation.org/elf/gabi41.pdf (75 oldal)
// https://en.wikipedia.org/wiki/Endianness
// https://docs.rs/goblin/0.7.1/goblin/elf/struct.Elf.html#method.is_object_file

// https://refspecs.linuxfoundation.org/elf/gabi4+/ch5.pheader.html
// http://www.science.unitn.it/~fiorella/guidelinux/tlk/node62.html

// BasibBlock def.: https://en.wikipedia.org/wiki/Basic_block

// git + github:
// https://datacamp.com/tutorial/git-push-pullThe%20function%20end_address%20implemented%20for%20BasicBlock%20struct.
// https://training.github.com/downloads/github-git-cheat-sheet/


// smt solver
// pgo - pref
// break griffin/th

// "rop"-olni

// aida 

// simba vs gamba

// p_offset - a file kezdetétől nézve hol található az adott program
// p_vaddr - az adott program kedzeti virtual address-eSándor Rokob

// r2 -> V (nagy v): itt van az amit vissza akarunk írni;
// note: hexadecimal: 1 byte = 2 karakter

// https://man7.org/linux/man-pages/man5/elf.5.html

// ripr - formatter
// note: indirect branch - long enum; return, interrupt, exception - no address;


// dominator graph - control flow graph

// multi-thread: locks adn dead-locks


// dot -Tsvg virtual_address.dot > virtual_address.svg

// crates

#![feature(impl_trait_in_assoc_type)]

use goblin::elf::*;
// use petgraph::algo::dominators::*;
use petgraph::algo::tarjan_scc;
use petgraph::visit::*;
// use std::collections::HashMap;
use std::fs::File;
use std::io::Read;
// use std::ops::Range;
use std::ops::*;

use std::fmt;

use iced_x86::*;

use std::collections::BTreeMap;
use std::collections::HashSet;
// use std::collections::HashMap;
use std::collections::BinaryHeap;

use std::cmp::*;

use serde::{Serialize, Deserialize};

use kendalls::tau_b;

// PART 01: Binary struct

struct Binary {
    program_header: Vec<ProgramHeader>,
    bytes: Vec<u8>,
}

impl Binary {

    // from path of the exe file to Binary instance
    fn from_elf(path: String) -> Self {
        
        // INITIALIZATION: file read, length
        let mut file = File::open(path).map_err(|_| "open file error").unwrap();
        let file_len = file.metadata().map_err(|_| "get metadata error").unwrap().len();

        // INITIALIZATION: vector of bytes
        let mut contents = vec![0; file_len as usize];
        file.read_exact(&mut contents[..]).map_err(|_| "read header error").unwrap();

        // INITIALIZATION: elf file
        let elf = Elf::parse(&contents[..]).map_err(|_| "cannot parse elf file error").unwrap();

        Binary {
            program_header: elf.program_headers,
            bytes: contents,
        }
    }

    // slice of bytes at a given virtual address range or error:invalid
    fn virtual_address_range<T: RangeBounds<u64>>(&self, range: T) -> Result<&[u8], String> {

        // start bound
        let start: u64 = match range.start_bound() {
            Bound::Unbounded => 0,
            Bound::Excluded(num) => *num + 1,
            Bound::Included(num) => *num
        };

        // index of program containing given virtual address range
        let segment = &self.program_header.iter()
            .position(
                |x|
                    // p_type = "PT_LOAD"
                    x.p_type == 1 && 
                    // given va range is inside the range of program
                    x.p_vaddr <= start && 
                    start <= x.p_vaddr + x.p_filesz
                    // range.end <= x.p_vaddr + x.p_filesz
            )
            .ok_or( String::from("invalid virtual address range error"))?;

        let segment = &self.program_header[*segment];

        // end bound
        let end: u64 = match range.end_bound() {
            Bound::Unbounded => segment.p_vaddr + segment.p_filesz,
            Bound::Excluded(num) => *num - 1,
            Bound::Included(num) => *num,
        };

        if end > segment.p_vaddr + segment.p_filesz {
            Err( String::from("invalid virtual address range error") )
        } else {
            Ok( &self.bytes[ 
                // convert the virtual address to file address
                (start - segment.p_vaddr + segment.p_offset) as usize .. (end - segment.p_vaddr + segment.p_offset) as usize
            ])
        }

    }
    
}


// PART 02: Basic block

#[derive(Clone, Debug)]
struct BasicBlock {
    address: u64,
    instructions: Vec<Instruction>,
    targets: Vec<u64>,
}


// BasicBlocks are ordered acccording to their addresses
impl PartialEq for BasicBlock {

    fn eq(&self, other: &Self) -> bool {
        self.address == other.address
    }
}

impl Eq for BasicBlock {}

impl Ord for BasicBlock {

    fn cmp(&self, other: &Self) -> Ordering {
        self.address.cmp(&other.address)
    }

}

impl PartialOrd for BasicBlock {

    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }

}


impl BasicBlock {

    fn from_address(binary: &Binary, va: u64) -> Self {

        let mut bb: BasicBlock = BasicBlock{
            address: va,
            instructions: Vec::new(),
            targets: Vec::new(),
        };

        let byte_slice = binary.virtual_address_range(va..).unwrap();
        
        // set ip: given virtual address
        let mut decoder = Decoder::with_ip(64, byte_slice, va, 0);
    
        let mut instr = Instruction::default();   

        decoder.decode_out(&mut instr);
        bb.instructions.push(instr);

        // TODO: deal with FlowControl::Call pattern !!

        loop {
            match instr.flow_control() {
                FlowControl::Next |
                FlowControl::Call => {
                    decoder.decode_out(&mut instr);
                    bb.instructions.push(instr);
                }
                FlowControl::ConditionalBranch => {
                    // is_jcc_short_or_near(), is_jcx_short(), is_loop(), is_loopcc()
                    // doesn ot exist: is_jkcc_short_or_near()
                    bb.targets.push(instr.next_ip());
                    bb.targets.push(instr.near_branch_target());
                    break;
                }
                FlowControl::UnconditionalBranch => {
                    if instr.is_jmp_short_or_near() {
                        bb.targets.push(instr.next_ip()); 
                        bb.targets.push(instr.near_branch_target());
                    } else if instr.is_jmp_far() {
                        bb.targets.push(instr.next_ip());
                        bb.targets.push(instr.far_branch_selector() as u64);
                    } else {
                        break;
                    }
                    break;
                }
                /* FlowControl::Call => {
                    if instr.is_call_near() {
                        bb.targets.push(instr.next_ip()); 
                        bb.targets.push(instr.near_branch_target());
                    } else if instr.is_call_far() {
                        bb.targets.push(instr.next_ip());
                        bb.targets.push(instr.far_branch_selector() as u64);
                    } else {
                        break;
                    }
                    break;
                } */
                FlowControl::Return | 
                FlowControl::Interrupt | 
                FlowControl::Exception | 
                FlowControl::XbeginXabortXend |
                FlowControl::IndirectBranch | 
                FlowControl::IndirectCall => {
                    break;
                }
            }
        }

        bb

    }

    // BasicBlock -> address of the last byte
    // maybe: address of the next instruction ??
    fn end_address(&self) -> u64 {
        let instr: Instruction = *(self.instructions).iter().last().unwrap();
        instr.next_ip() - 1
        // instr.ip() + (instr.len() as u64)
    }

    // BasicBlock + va -> address of the next valid instruction (if va = start then itself)
    fn next_valid_instr(&self, va: u64) -> Result<u64, String> {

        // TODO: what if it returns the next basic block's address ??
        let index = self.instructions.iter().position(|x| x.ip() <= va && va < x.next_ip());
        match index {
            Some(i) => {
                if self.instructions[i].ip() == va {
                    Ok(va)
                } else {
                    Ok(self.instructions[i].next_ip())
                }
            }
            None => {
                Err(String::from("address is outside of basic block's range error"))
            }
        }
    }


    // BasicBlock + va -> cut the BB into two BBs at next_valid_instr(va)
    // the second block starts at next_valid_instr(va)
    fn cut_block(self, va: u64) -> Vec<BasicBlock> {

        let valid_va = self.next_valid_instr(va);
        match valid_va {
            Ok(addr) => {
                if self.address < addr && addr <= self.end_address() {
                    let cut_index = self.instructions.iter().position(|&x| x.ip() == addr).unwrap();
                    vec![
                        BasicBlock {
                            address: self.address,
                            instructions: self.instructions[..cut_index].to_vec(),
                            targets: vec![addr],
                        },
                        BasicBlock{
                            address: addr,
                            instructions: self.instructions[cut_index..].to_vec(),
                            targets: self.targets,
                        }
                    ]
                } else {
                    vec![self]
                }
            }
            Err(_) => {
                vec![self]
            }

        }

    }

    
    // BasicBlock -> address (u64)
    fn address(&self) -> u64 {
        self.address
    }

    // BasicBlock -> targets (&[u64])
    fn targets(&self) -> &[u64] {
        &self.targets
    }

    // BasicBlock -> instructions (&[Instruction])
    fn instructions(&self)-> &[Instruction] {
        &self.instructions
    }


}






impl fmt::Display for BasicBlock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        
        write!(f, "address:\n       {:016x}\n", &self.address)?;
        writeln!(f, "basic block:")?;

        // options format:
        // https://docs.rs/iced-x86/latest/src/iced_x86/instruction.rs.html#3767-3797
        let mut formatter = MasmFormatter::new();
        formatter.options_mut().set_branch_leading_zeros(false);
        formatter.options_mut().set_uppercase_hex(false);
        
        for instruction in &self.instructions {

            write!(f,"      {:016x}: ", instruction.ip())?;

            let mut output = String::new();
            formatter.format(instruction, &mut output);
            f.write_str(&output)?;

            writeln!(f)?;
        }
        
        writeln!(f, "target(s):")?;

        for element in &self.targets {
            writeln!(f,"      {:016x}", element)?;
        }

        Ok(())
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    // TEST: next_valid_instr() method
    #[test]
    fn next_valid_va() {

        let path = String::from("/home/san-rok/projects/testtest/target/debug/testtest");
        let binary = Binary::from_elf(path);

        let virtual_address: u64 = 0x8840;

        let bb = BasicBlock::from_address(&binary, virtual_address);


        assert_eq!(Err(String::from("address is outside of basic block's range error")), bb.next_valid_instr(0x8838));
        assert_eq!(Err(String::from("address is outside of basic block's range error")), bb.next_valid_instr(0x8853));


        assert_eq!(Ok(0x8847), bb.next_valid_instr(0x8842));
        assert_eq!(Ok(0x8847), bb.next_valid_instr(0x8846));
        assert_eq!(Ok(0x884e), bb.next_valid_instr(0x8849));
        assert_eq!(Ok(0x884e), bb.next_valid_instr(0x884e));
        assert_eq!(Ok(0x8853), bb.next_valid_instr(0x8852));
    }



}

// PART 03A: Control flow graph
struct ControlFlowGraph {
    address: u64,
    blocks: Vec<BasicBlock>,
}


impl ControlFlowGraph {

    // explore control flow graph from a given virtual address (using DFS)
    fn from_address(binary: &Binary, va: u64) -> Self {

        let mut blocks: BTreeMap<u64, BasicBlock> = BTreeMap::new();
        let mut addresses: Vec<u64> = Vec::new();
    
        addresses.push(va);
    
        while let Some(address) = addresses.pop() {
    
            let bb = BasicBlock::from_address(binary, address);
    
            // is this clone too much?
            let mut targets  = bb.targets().to_vec();
    
            blocks.insert(bb.address(), bb);
    
            while let Some(target) = targets.pop() {
    
                let cut = blocks
                    .range(..target)
                    .next_back()
                    .map(|(&x, _)| x);
                
                match cut {
                    Some(addr) if target <= blocks.get(&addr).unwrap().end_address() => {
                        let tmp_block = blocks.remove(&addr).unwrap();
                        let cut_blocks = tmp_block.cut_block(target);
                        for i in cut_blocks {
                            blocks.insert(i.address(), i);
                        }
                    } 
                    _ => {
                        if !addresses.contains(&target) {
                            addresses.push(target);
                        }
                    }
                }
            }
        }

        let mut blocks: Vec<BasicBlock> = blocks.into_values().collect::<Vec<BasicBlock>>();
        blocks.sort();

        ControlFlowGraph{
            address: va,
            blocks: blocks,
        }
    }

    // Graph -> address (u64)
    fn address(&self) -> u64 {
        self.address
    }

    // Graph -> blocks (&[BasicBlock])
    fn blocks(&self) -> &[BasicBlock] {
        &self.blocks
    }
    
    // from graph to .dot
    fn render_to<W: std::io::Write>(&self, output: &mut W) -> dot2::Result {
        dot2::render(self, output)
    }

}


impl<'a> dot2::Labeller<'a> for ControlFlowGraph {
    type Node = u64;
    type Edge = (u64, u64);
    type Subgraph = ();

    // .dot compatible identifier naming the graph
    fn graph_id(&'a self) -> dot2::Result<dot2::Id<'a>> {
        dot2::Id::new("control_flow")
    }

    // maps n to unique (valid .dot) identifier 
    fn node_id(&'a self, n: &Self::Node) -> dot2::Result<dot2::Id<'a>> {
        dot2::Id::new(format!("N0x{:x}", n))
    }

    // labels of nodes
    fn node_label(&'a self, n: &Self::Node) -> dot2::Result<dot2::label::Text<'a>> {
        let label = self.blocks.iter().find(|&v| v.address() == *n).map(|v| format!("{}", v)).unwrap();

        Ok(dot2::label::Text::LabelStr(
            label.into()
        ))
    }

}


impl<'a> dot2::GraphWalk<'a> for ControlFlowGraph {
    type Node = u64;
    type Edge = (u64, u64);
    type Subgraph = ();

    // all nodes of the graph
    fn nodes(&self) -> dot2::Nodes<'a, Self::Node> {
        self.blocks().iter().map(|n| n.address()).collect()
    }

    // all edges of the graph
    fn edges(&'a self) -> dot2::Edges<'a, Self::Edge> {

        let mut edges: Vec<(u64, u64)> = Vec::new();

        for block in self.blocks() {
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



// in the ordering of the block only the number of instructions matter
#[derive(Serialize, Deserialize, Clone, Debug)]
struct NoInstrBasicBlock {
    address: u64,
    len: usize,
    targets: Vec<u64>,
    indegree: usize,
}
// if we consider the block alone, then its indegree is set to be 0

impl NoInstrBasicBlock {
    
    fn address(&self) -> u64 {
        self.address
    }

    fn len(&self) -> usize {
        self.len
    }

    fn targets(&self) -> &[u64] {
        &self.targets
    }

    fn add_target(&mut self, target: u64) {
        self.targets.push(target);
    }

    // TODO: error handling
    fn erease_target(&mut self, target: u64) {
        self.targets.retain(|&x| x != target);
    }

    fn indegree(&self) -> usize {
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
struct VirtualAddressGraph {
    address: u64,
    nodes: Vec<NoInstrBasicBlock>,
}

impl VirtualAddressGraph {

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
    fn update_in_degrees(&mut self) {
        let indeg = self.in_degrees();

        for node in self.nodes_mut() {
            node.set_indegree( *indeg.get(&node.address()).unwrap() );
        }
    }

    fn from_cfg(cfg: &ControlFlowGraph) -> Self {
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

    fn address(&self) -> u64 {
        self.address
    }

    fn nodes(&self) -> &[NoInstrBasicBlock] {
        &self.nodes
    }

    fn nodes_mut(&mut self) -> &mut [NoInstrBasicBlock] {
        &mut self.nodes
    }

    // reference to a node with a given address
    fn node_at_target(&self, target: u64) -> &NoInstrBasicBlock {
        // TODO: error handling

        // VAG is ordered by addresses
        let pos: usize = self.nodes().binary_search_by(|x| x.address().cmp(&target)).unwrap();
        // let pos = self.nodes().iter().position(|x| x.address() == target).unwrap();
        &self.nodes()[pos]
    }

    fn node_at_target_mut(&mut self, target: u64) -> &mut NoInstrBasicBlock {
        let pos: usize = self.nodes().binary_search_by(|x| x.address().cmp(&target)).unwrap();
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
    fn backedges(&self) -> Vec<(u64, u64)> {

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

    // erease the given edge from the VAG
    fn erease_edge(&mut self, edge: (u64, u64)) {
        self.node_at_target_mut(edge.0).erease_target(edge.1);
    }

    // erease the given edges to the VAG
    fn erease_edges(&mut self, edges: &Vec<(u64, u64)>)  {

        // TODO: optimalize !!
        for &edge in edges {
            self.erease_edge(edge);
        }

    }





    }



    // add phantom start
    // add phantom end

    // TBC ...


    // from graph to .dot
    /*
    fn render_to<W: std::io::Write>(&self, output: &mut W) -> dot2::Result {
        dot2::render(self, output)
    }
    */


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




/*
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
*/


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
    // println!("{:#x?}", vag);
    
    
    let components: Vec<Component> = Component::from_vag(&vag);

    /*
    for comp in components {
        let incoming = comp.incoming_edges();
        let outgoing = comp.outgoing_edges();
        println!("incoming edges:");
        for (source, target) in incoming {
            println!("{:x} --> {:x}", source, target);
        }
        println!("nodes:");
        for node in comp.nodes() {
            println!("{:x}", node);
        }
        println!("outgoing edges:");
        for (source, target)in outgoing {
            println!("{:x} --> {:x}", source, target);
        }
    }
    */
    

    // let scc = tarjan_scc(&vag);
    // println!("{:#x?}", scc);


    let condensed = vag.condense();
    // println!("{:#x?}", condensed);

    // Kahn's algorithm
    let mut kahngraph: KahnGraph = KahnGraph::from_vag(&condensed);

    // println!("{:#x?}", kahngraph);

    let mut initial_order: Vec<u64> = Vec::new();
        for node in kahngraph.nodes() {
            initial_order.push(node.address());
        }
    initial_order.sort();

    let topsort = kahngraph.kahn_algorithm();
    println!("starting block's address: {:x}", kahngraph.address());

    for i in 0..topsort.len() {
        println!("{:x}, {:x}", initial_order[i], topsort[i]);
    }

    let kendall_tau = tau_b(&initial_order, &topsort).unwrap().0;
    println!("kendall tau: {:#?} \n", kendall_tau);

    println!("cost of original order: {}", condensed.cost_of_order(initial_order));
    println!("cost of topological sort: {}", condensed.cost_of_order(topsort));



    // WHAT DO WE NEED FOR CYCLE BREAKING?
    //      (0) a Components struct: reference for the original VAG, Hash set of subgraph node ids
    //          (0.a) using these field methods can derive the incoming and outgoing edges !!
    //      (1) finds all the bad edges, constituting for cycles
    //      (2) puts back edges - or simply add edges for a VAG instance
    //      (3) adds a starting node to the cycle free VAG: label = 0x0; edges = all the input edges; length = large
    //      (4) adds a terminating node to the cycle free instance: label = 0xfffffffff; edges = all the output edges; length = 0
    //      (5) calculates the order - hopefully use our previous method
    //      (6) inserts back the ordered list to the scc's ordered list in the appropriate place

    /*
    // test dags 
    let file = std::fs::File::open("dag.yaml").unwrap();
    let dags: Vec<VirtualAddressGraph> = serde_yaml::from_reader(file).unwrap();

    

    let mut better_cost: usize = 0;

    for mut dag in dags {
        dag.update_in_degrees();

        let mut kahngraph: KahnGraph = KahnGraph::from_vag(&dag);
        let topsort = kahngraph.kahn_algorithm();

        let mut initial_order: Vec<u64> = Vec::new();
        for node in kahngraph.nodes() {
            initial_order.push(node.address());
        }
        initial_order.sort();

        println!("starting block's address: {:x}", kahngraph.address());

        for i in 0..topsort.len() {
            println!("{:x}, {:x}", initial_order[i], topsort[i]);
        }
    

        let kendall_tau = tau_b(&initial_order, &topsort).unwrap().0;

        // println!("initial order: {:x?}", initial_order);
        // println!("topological sort: {:x?}", topsort);

        let original_cost: usize = dag.cost_of_order(initial_order);
        let sorted_cost: usize = dag.cost_of_order(topsort);

        println!("kendall tau: {:#?}", kendall_tau);
        println!("cost of original order: {}", original_cost);
        println!("cost of topological sort: {} \n", sorted_cost);

        if sorted_cost <= original_cost {
            better_cost += 1;
        }


        // some addresses with big differences: 0x1800c17b0
        if dag.address() == 0x1800c1530 {
            let mut file = std::fs::File::create("/home/san-rok/projects/virtual_address/test.dot").unwrap();
            dag.render_to(&mut file).unwrap();
        }
    }


    println!("number of better cost cases: {}", better_cost);    

    */


    // let mut ordered: Vec<TestGraph> = Vec::new();

}


#[derive(Debug)]
struct Component<'a> {
    // the original graph
    graph: &'a VirtualAddressGraph,
    // the strongly connected component
    component: HashSet<u64>,
}

impl<'a> Component<'a> {

    // given a VAG instance returns a vector of its components
    fn from_vag(vag: &'a VirtualAddressGraph) -> Vec<Self> {

        let mut components: Vec<Self> = Vec::new();

        // tarjan_scc -> vector of strongly connected component's addresses vector
        let scc: Vec<Vec<u64>> = tarjan_scc(vag);

        for comp in scc {
            let mut strongly: HashSet<u64> = HashSet::new();
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
    fn whole(&self) -> &VirtualAddressGraph {
        self.graph
    }

    // returns the collection of nodes in the strongly connnected component
    fn nodes(&self) -> &HashSet<u64> {
        &self.component
    }

    // checks if a given node is in the component
    fn contains(&self, node: u64) -> bool {
        self.nodes().contains(&node)
    }

    // checks if a component is trivial, i.e. it's a single node
    fn trivial(&self) -> bool {
        if self.nodes().len() == 1 {
            true
        } else {
            false
        }
    }

    // returns a reference to the targets of a given vertex in the component
    fn targets(&self, node: u64) -> &[u64] {
        self.whole().node_at_target(node).targets()
    }

    // a collection of incoming edges
    // TODO: HashSet or Vector ??
    fn incoming_edges(&self) -> Vec<(u64, u64)> {

        let mut incoming: Vec<(u64, u64)> = Vec::new();

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
        incoming.sort_by_key(|item| (item.0, item.0) );
        incoming

    }

    // a collection of outgoing edges
    // TODO: HashSet or Vector ??
    fn outgoing_edges(&self) -> Vec<(u64, u64)> {

        let mut outgoing: Vec<(u64, u64)> = Vec::new();

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

    // TODO: make this better, that is no copying blocks !!!
    // maybe we should have not a VirtualAddressGraph, just a vector of &NoInstrBasicBlock references
    fn to_vag(&self) -> VirtualAddressGraph {

        let address = self.nodes().iter().min().unwrap();

        let mut nodes: Vec<NoInstrBasicBlock> = Vec::new();
        for node in self.nodes() {
            nodes.push(self.whole().node_at_target(*node).clone());
        }

        VirtualAddressGraph { 
            address: *address, 
            nodes: nodes,
        }

    }

    



}






/*
#[derive(Serialize, Deserialize, Debug)]
struct TestGraph {
    graph: VirtualAddressGraph,
    kendall_tau: f64,
    original_order: Vec<u64>,
    topsort_order: Vec<u64>,
}
*/

// PART 03B: list of instructions
// hint: use petgraph crate: https://docs.rs/petgraph/latest/petgraph/algo/dominators/index.html





// why dominator tree:  Prosser, Reese T. (1959). "Applications of Boolean matrices to the analysis of flow diagrams"
// basic block scheduling; dominator tree
// https://stackoverflow.com/questions/39613095/minimize-amount-of-jumps-when-compiling-to-assembly
// https://www.cs.cornell.edu/courses/cs6120/2019fa/blog/codestitcher/




// petgraph traits implemented for ControlFlowGraph

/*
impl petgraph::visit::GraphBase for ControlFlowGraph {
    type NodeId = u64;
    type EdgeId = (u64, u64);
}


impl<'a> petgraph::visit::IntoNeighbors for &'a ControlFlowGraph {
    // type Neighbors = core::slice::Iter<'a, Self::NodeId>
    // here Iterator<Item = Self::NodeId> expects: u64, but obtains: &u64
    // how to solve?
    // type Neighbors = std::vec::IntoIter<Self::NodeId>;
    // type Neighbors = std::iter::Copied<std::slice::Iter<'a, u64>>;

    type Neighbors = impl Iterator<Item = Self::NodeId> + 'a;

    
    // TODO: binary search !!
    // e.g.: order the blocks when CFG is generated!
    // or use BTM or HashMap
    fn neighbors(self, a: Self::NodeId) -> Self::Neighbors {
        // let targets = 
        // (*self)
        //    .blocks().iter()
        //    .find(|x| x.address() == a)
        //    .map(|x| x.targets()).unwrap().iter().copied()
        // targets

        let pos = 
            self
                .blocks()
                .binary_search_by(|block| block.address().cmp(&a))
                .unwrap();
        self.blocks()[pos].targets().iter().copied()

        // let pos = (*self).blocks().binary_search(a)
    }
}


impl petgraph::visit::Visitable for ControlFlowGraph {
    type Map = HashSet<Self::NodeId>;

    fn visit_map(&self) -> Self::Map {
        HashSet::with_capacity(self.blocks().len())
    }

    fn reset_map(&self, map: &mut Self::Map) {
        map.clear()
    }
}


impl<'a> petgraph::visit::IntoNodeIdentifiers for &'a ControlFlowGraph {
    // without impl trait associated type ?
    // std::iter::Map<,...> - what is the second argument here?    
    type NodeIdentifiers = impl Iterator<Item = Self::NodeId> + 'a;

    fn node_identifiers(self) -> Self::NodeIdentifiers {
        self.blocks().iter().map(|x| x.address())
    }
}


impl<'a> petgraph::visit::NodeIndexable for &'a ControlFlowGraph {

    fn node_bound(self: &Self) -> usize {
        self.blocks().len()
    }

    fn to_index(self: &Self, a: Self::NodeId) -> usize {
        self
            .blocks()
            .binary_search_by(|block| block.address().cmp(&a))
            .unwrap()
    }

    fn from_index(self: &Self, i:usize) -> Self::NodeId {
        assert!(i < self.blocks().len(),"the requested index {} is out-of-bounds", i);
        self.blocks()[i].address()
    }

}

*/

// DOMINATORS

/*

println!("{:#x?}", dominators);

    for node in cfg.blocks() {
        let nodelabel = node.address();
        if nodelabel != cfg.address() {
            println!("the immediate dominator of {:x} is: {:x}", nodelabel, dominators.immediate_dominator(nodelabel).unwrap())
        }
        
    }


    // ControlFlowGraph as DominatorTree - not correct yet
    let mut dom_tree: ControlFlowGraph = ControlFlowGraph::new(virtual_address);
    for block in cfg.blocks(){
        let node = block.address();
        // let instr: Vec<Instruction> = block.instructions().to_vec();
        let targets: Vec<u64> = dominators.immediately_dominated_by(node).collect();
        let bb = BasicBlock{
            address: node,
            instructions: block.instructions().to_vec(),
            targets: targets,
        };
        dom_tree.push(bb);
    }

    let mut f2 = std::fs::File::create("/home/san-rok/projects/virtual_address/dominator.dot").unwrap();
    dom_tree.render_to(&mut f2).unwrap();
    // dot -Tsvg virtual_address.dot > virtual_address.svg






*/



/*
fn h<V: Eq>(v: V) -> impl Eq{
    v == v
}

fn h2(v: impl Eq) -> bool {
    v == v
}
*/
















//////// JUNK ////////

/*
let mut dictionary: Vec<NodeIndex> = Vec::new();
let mut graph = Graph::<&BasicBlock, ()>::new();
for block in cfg.blocks() {
    let node = graph.add_node(block);
    dictionary.push(node);
}

for node in dictionary {
    for target in graph.node_weight(node).unwrap().targets() {
        let n = graph.node_indices().find(|i| graph.node_weight(*i).unwrap().address() == *target).unwrap();
        graph.add_edge(node, n, ());
    }
}
let dominators = simple_fast(&graph, 0.into());
println!("{:#x?}", dominators);
*/

/*
match cut {
    Some(addr) => {
        if target <= blocks.get(&addr).unwrap().end_address() {
            let tmp_block = blocks.remove(&addr).unwrap();
            let cut_blocks = tmp_block.cut_block(target);
            for i in cut_blocks {
                blocks.insert(i.address(), i);
            }
        } else {
            if !addresses.contains(&target) {
                addresses.push(target);
            }
        }                        
    }
    // this None is possible
    None => {
        if !addresses.contains(&target) {
            addresses.push(target);
        }
    }
}
*/

/*

let mut component_dictionary: HashMap<u64, u64> = HashMap::new();
    for comp in &scc {
        let value = comp[0];
        for node in comp {
            component_dictionary.insert(*node, value);
        }
    }

    let mut nodes: Vec<NoInstrBasicBlock> = Vec::new();

    for component in &scc {
        let address: u64 = component[0];

        let mut length: usize = 0;
        let mut targets: Vec<u64> = Vec::new();

        for node in component {

            let pos = vag
                .nodes()
                .binary_search_by(|block| block.address().cmp(&node))
                .unwrap();
            let node = &vag.nodes()[pos];

            length = length + node.len();

            for target in node.targets() {
                if !(component.contains(target) || targets.contains(target)) {
                    targets.push( *(component_dictionary.get(target).unwrap()) );
                }
            }
        }



        nodes.push(
            NoInstrBasicBlock { 
                address: address, 
                len: length, 
                targets: targets,
            }
        );
    }

    nodes.reverse();

    let condensed: VirtualAddressGraph = VirtualAddressGraph { 
        address: virtual_address,
        nodes: nodes,
    };


*/

/*

// from a node of length n -> a (directed) path of length n
    // the inside addresses are dummy (i.e. not valid instruction addresses)
    /*
    fn to_path(&self) -> Vec<NoInstrBasicBlock> {

        let mut path: Vec<NoInstrBasicBlock> = Vec::new();

        if self.len() > 1 {
            for i in 0..self.len()-1 {
                path.push(
                    NoInstrBasicBlock { 
                        address: self.address() + (i as u64), 
                        len: 1, 
                        targets: vec![self.address + (i+1) as u64],
                    }
                )
            }

            path.push(
                NoInstrBasicBlock { 
                    address: self.address() + ((self.len()-1) as u64), 
                    len: 1, 
                    targets: self.targets().to_vec(),
                }
            )

        } else {
            path.push(self.clone());
        }

        path
    }
    */

    // TODO: make it more sophisticated!
    /*
    fn from_path(path: Vec<NoInstrBasicBlock>) -> Self {

        NoInstrBasicBlock { 
            address: path[0].address(), 
            len: path.len(), 
            targets: path[path.len()].targets().to_vec()
        }

    }
    */


*/

/*
    fn reduce_indegree(&'a mut self, target: u64) -> Option<KahnBasicBlock> {
        let pos = self
            .nodes()
            .binary_search_by(|a| a.address().cmp(&target))
            .unwrap();

        self.nodes_mut()[pos].recude_by_one();

        
        let kbb: KahnBasicBlock = self.nodes()[pos];

        match kbb.indegree() == kbb.deleted() {
            true => Some(kbb),
            false => None,
        }
        
    }

    let mut topsort: Vec<u64> = Vec::new();
    let mut visit: BinaryHeap<&NoInstrBasicBlock> = BinaryHeap::new();


    for node in kahngraph.nodes() {
        if node.indegree() == 0 {
            visit.push(node.block());
        }
    }

    while let Some(node) = visit.pop() {
        for target in node.targets() {

            if let Some(kahnblock) = kahngraph.reduce_indegree(*target) {
                visit.push(kahnblock);
            }


             // let mut kbb = kahngraph.mut_node_at_target(*target);
            /*
            let pos = kahngraph
                .nodes()
                .binary_search_by(|a| a.address().cmp(&target))
                .unwrap();

            let mut block = &mut kahngraph.nodes_mut()[pos];
            block.recude_by_one();

            //let pos = kahngraph.position(*target);
            // kahngraph.nodes_mut()[pos].recude_by_one();
            // kahngraph.nodes_mut()[pos].deleted += 1;

        
            // kahngraph.reduce_indegree(*target);
            
            */


        }

        topsort.push(node.address());
    }

    println!("{:#x?}", topsort);
*/

/*
        
    let mut topsort: Vec<u64> = Vec::new();
    let mut visit: Vec<u64> = Vec::new();

    for (node, indeg) in &id {
        if *indeg == 0 {
            visit.push(*node);
            // id.remove(&node);
        }
    }

    // visit.sort_by(|a,b| dict.get(a).unwrap().cmp( dict.get(b).unwrap() ));

    // visit.sort_by(|a,b| (id_dict.get(a).unwrap() + lengths.get(a).unwrap())
    //    .cmp(id_dict.get(b).unwrap() + lengths.get(b).unwrap()));

    visit.sort_by_key(|a| (dict.get(a).unwrap(), lengths.get(a).unwrap()));
    
    /*
    visit.sort_by(|a, b|         
        if dict.get(a).unwrap() == dict.get(b).unwrap() {
            lengths.get(a).unwrap().cmp(lengths.get(b).unwrap())
        } else {
            dict.get(a).unwrap().cmp(dict.get(b).unwrap())
        }
    );
    */
    // visit.sort_by(|a,b| fix_id_dict.get(a).unwrap().cmp(fix_id_dict.get(b).unwrap()));


    // println!("{:#x?}", visit);

    while let Some(node) = visit.pop() {
        let pos = condensed
            .nodes()
            .binary_search_by(|a| a.address().cmp(&node))
            .unwrap();

        for target in condensed.nodes()[pos].targets() {
            id.entry(*target).and_modify(|x| *x -= 1);
            if id.get(target).unwrap() == &0 {
                visit.push(*target);
            }
        }
        // println!("id_dict: {:#x?}", id_dict);

        topsort.push(node);
        // println!("topological sort: {:#x?}", topsort);

        println!("pre sort visit: {:x?}", visit);

        visit.sort_by_key(|a| (dict.get(a).unwrap(), lengths.get(a).unwrap()));


        // visit.sort_by(|a,b| dict.get(a).unwrap().cmp(dict.get(b).unwrap()));
        
        /*
        visit.sort_by(|a, b|         
            if dict.get(a).unwrap() == dict.get(b).unwrap() {
                lengths.get(a).unwrap().cmp(lengths.get(b).unwrap())
            } else {
                dict.get(a).unwrap().cmp(dict.get(b).unwrap())
            }
        );
        */
        
        println!("post sort visit: {:x?}", visit);
        // TBC !!


        // dummy path -> node

    }


    println!("topological sort: {:#x?}", topsort);

    // println!("{:x}", 36785);
    // println!("{:x}", 36841);

    /*
    for node in condensed.nodes() {
        let pos = topsort.iter().position(|n| *n==node.address()).unwrap();
        let mut i = 0;
        for address in &topsort[pos..pos + node.len()] {
            if i == 0 {
                println!{"start: {:x} with length {}", node.address(), node.len()};
            }
            assert_eq!(*address, node.address()+i);
            println!("topsort: {:x}, condensed: {:x}", address, node.address()+i);
            i += 1;
        }
    }
    */
    

*/

/*
#[derive(Debug)]
struct Component {
    in_edges: Vec<(u64, u64)>,
    component: VirtualAddressGraph,
    out_edges: Vec<(u64, u64)>,
}


impl Component {

    fn from_vag(vag: &VirtualAddressGraph) -> Vec<Self> {

        let mut components: Vec<Self> = Vec::new();

        // tarjan_scc -> vector of strongly connected component's addresses vector
        let scc: Vec<Vec<u64>> = tarjan_scc(vag);

        // ad hoc choice:
        // the node label for a sc component = first node's label in tarjan's output
        let mut comp_dict: BTreeMap<u64, u64> = BTreeMap::new();
        for comp in &scc {
            let value = comp[0];
            for node in comp {
                comp_dict.insert(*node, value);
            }
        }



        for component in &scc {
            let address: u64 = component[0];
            let mut nodes: Vec<NoInstrBasicBlock> = Vec::new();

            let mut targets: Vec<(u64, u64)> = Vec::new();
            let mut sources: Vec<(u64, u64)> = Vec::new();



            for addr in component {

                let pos = vag
                    .nodes()
                    .binary_search_by(|block| block.address().cmp(&addr))
                    .unwrap();
                let node = &vag.nodes()[pos];

                // edges leave component
                for target in node.targets() {
                    if !component.contains(target) {
                        targets.push((*addr,*target));
                    }
                }

                // edges enter component
                for block in vag.nodes() {
                    for target in block.targets() {
                        if target == addr && !component.contains(&block.address()) {
                            sources.push((block.address(), *addr));
                        }
                    }
                }

                // isn't this clone() too much?
                // maybe we only need reference the original
                nodes.push(node.clone());

            }

            

           
            components.push(
                Component { 
                    in_edges: sources, 
                    component: VirtualAddressGraph { 
                        address: address, 
                        nodes: nodes,
                    },
                    out_edges: targets,
                }
            );
        }
        
        components

    }

    fn in_edges(&self) -> &[(u64, u64)] {
        &self.in_edges
    }

    fn address(&self) -> u64 {
        self.component.address()
    }

    // it must create a new VAG - since the end vertex can be a new target for many nodes
    // MAYBE: I'm in a wrong mindset ...
    fn to_phantom_vag(&self) -> () {

        // let mut blocks: Vec<NoInstrBasicBlock> = Vec::new();

        /*
        
        NoInstrBasicBlock { 
                address: 0, 
                len: 1, 
                targets: self.in_edges().iter().map(|(x,y)| *y).collect(),
                indegree: 0,
            }
        
        */

        

        

    }

    // generates the condensed vag - using petgraph::algo::tarjan_scc
    /*
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
     */




}


 */






