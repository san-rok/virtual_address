
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
use std::fs::File;
use std::io::Read;
// use std::ops::Range;
use std::ops::*;

use std::fmt;

use iced_x86::*;

use std::collections::BTreeMap;
// use std::collections::HashSet;
use std::collections::HashMap;

use std::cmp::*;

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

    // new
    fn new(va: u64) -> Self {
        Self {
            address: va,
            blocks: Vec::new(),
        }
    }

    // push in a new block - for a control flow graph it is not necessary
    fn push(&mut self, block: BasicBlock) -> () {

        match self.blocks().binary_search(&block) {
            Ok(_) => {}
            Err(pos) => self.blocks.insert(pos, block),
        }

        // self.blocks.push(block);
        // self.blocks.sort();
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

// in the ordering of the block only the number of instructions matter
#[derive(Debug, Eq, PartialEq, Ord, PartialOrd)]
struct NoInstrBasicBlock {
    address: u64,
    len: usize,
    targets: Vec<u64>,
}

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

    fn from_bb(bb: &BasicBlock) -> Self {

        NoInstrBasicBlock { 
            address: bb.address(), 
            len: bb.instructions().len(), 
            targets: bb.targets().to_vec(),
        }

    }

}

#[derive(Debug)]
struct VirtualAddressGraph {
    address: u64,
    nodes: Vec<NoInstrBasicBlock>,
}

impl VirtualAddressGraph {

    fn from_cfg(cfg: &ControlFlowGraph) -> Self {
        let mut nodes: Vec<NoInstrBasicBlock> = Vec::new();

        for block in cfg.blocks() {
            let node: NoInstrBasicBlock = NoInstrBasicBlock::from_bb(block);
            nodes.push(node);
        }

        VirtualAddressGraph { 
            address: cfg.address(), 
            nodes: nodes,
        }
    }

    fn address(&self) -> u64 {
        self.address
    }

    fn nodes(&self) -> &[NoInstrBasicBlock] {
        &self.nodes
    }

    // generates the condensed vag - using petgraph::algo::tarjan_scc
    fn condense(&self) -> Self {
        
        // tarjan_scc returns reversed topological order
        let scc = tarjan_scc(self);

        // the node label for a sc component = first node's label in tarjan's output
        // the dictionary is stored in a HashMap -> effectiveness ?
        let mut comp_dict: HashMap<u64, u64> = HashMap::new();
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
                        targets.push( *(comp_dict.get(target).unwrap()) );
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

        // for later use: sort by address
        nodes.sort();

        VirtualAddressGraph { 
            address: self.address(),
            nodes: nodes,
        }
    }

}


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



fn main() {

    let path = String::from("/home/san-rok/projects/testtest/target/debug/testtest");
    let binary = Binary::from_elf(path);

    let virtual_address: u64 =  0x970b;
    // test: 0x88cb, 0x8870, 0x88b0, 0x8a0d, 0x893e, 0x88f0, 0x8c81, 0x8840

    let cfg: ControlFlowGraph = ControlFlowGraph::from_address(&binary, virtual_address);

    // let dominators = simple_fast(&cfg, virtual_address);

    let mut f = std::fs::File::create("/home/san-rok/projects/virtual_address/virtual_address.dot").unwrap();
    cfg.render_to(&mut f).unwrap();
    // dot -Tsvg virtual_address.dot > virtual_address.svg

    let vag: VirtualAddressGraph = VirtualAddressGraph::from_cfg(&cfg);
    println!("{:#x?}", vag);
    
    let scc = tarjan_scc(&vag);
    println!("{:#x?}", scc);


    let condensed = vag.condense();
    println!("{:#x?}", condensed);

}


// PART 03B: list of instructions
// hint: use petgraph crate: https://docs.rs/petgraph/latest/petgraph/algo/dominators/index.html





// why dominator tree:  Prosser, Reese T. (1959). "Applications of Boolean matrices to the analysis of flow diagrams"
// basic block scheduling; dominator tree
// https://stackoverflow.com/questions/39613095/minimize-amount-of-jumps-when-compiling-to-assembly
// https://www.cs.cornell.edu/courses/cs6120/2019fa/blog/codestitcher/




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



