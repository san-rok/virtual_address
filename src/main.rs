
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

// p_offset - a file kezdetétől nézve hol található az adott program
// p_vaddr - az adott program kedzeti virtual address-eSándor Rokob

// r2 -> V (nagy v): itt van az amit vissza akarunk írni;
// note: hexadecimal: 1 byte = 2 karakter

// https://man7.org/linux/man-pages/man5/elf.5.html

// ripr - formatter
// note: indirect branch - long enum; return, interrupt, exception - no address;


// dominator graph - control flow graph


// dot -Tsvg virtual_address.dot > virtual_address.svg

// crates

use goblin::elf::*;
use std::fs::File;
use std::io::Read;
// use std::ops::Range;
use std::ops::*;

use std::fmt;

use iced_x86::*;

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

#[derive(Debug)]
struct BasicBlock {
    address: u64,
    instructions: Vec<Instruction>,
    targets: Vec<u64>,
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

fn from_address_to_bbvec(binary: &Binary, va: u64) -> Vec<BasicBlock> {

    let mut blocks: Vec<BasicBlock> = Vec::new();

    let mut addresses: Vec<u64> = Vec::new();

    addresses.push(va);

    while let Some(address) = addresses.pop() {

        let bb = BasicBlock::from_address(binary, address);

        // how to use bb.targets directly ?
        let mut targets: Vec<u64>  = bb.targets.iter().copied().collect();

        blocks.push(bb);

        while let Some(target) = targets.pop() {

            let cut_block = 
                    blocks.iter()
                            .position(|x| x.address < target && target <= x.address + (x.instructions.len() as u64));
                            // TODO: x.instruction.len() - not correct!

            match cut_block {
                Some(i) => {
                    let tmp_block = blocks.remove(i);
                        
                    let cut_instr = tmp_block.instructions.iter().position(|&x| x.ip() == target);

                    match cut_instr {
                        Some(j) => {

                            blocks.push(
                                BasicBlock {
                                    address: address,
                                    instructions: tmp_block.instructions[..j].to_vec(),
                                    targets: vec![target],
                                }
                            );

                            blocks.push(
                                BasicBlock{
                                    address: target,
                                    instructions: tmp_block.instructions[j..].to_vec(),
                                    targets: tmp_block.targets,
                                }
                            );
                        }
                        None => {
                            // TODO: ??
                            // 
                        }
                    }
                }
                None => {
                    if !addresses.contains(&target) {
                        addresses.push(target);
                    }
                }
            }             
        }
    }

    blocks

}

struct Graph {
    nodes: Vec<u64>,
    edges: Vec<(u64, u64)>,
    blocks: Vec<BasicBlock>,
}

impl Graph {

    fn from_address(binary: &Binary, va: u64) -> Self {

        let blocks: Vec<BasicBlock> = from_address_to_bbvec(binary, va);
        let mut nodes: Vec<u64> = Vec::new();
        let mut edges: Vec<(u64, u64)> = Vec::new();

        for block in &blocks {
            nodes.push( block.address );
            
            for target in &block.targets {
                edges.push( (block.address, *target ));
            }
        }

        Graph {
            nodes,
            edges,
            blocks,
        }
    }

    // from graph to .dot
    fn render_to<W: std::io::Write>(&self, output: &mut W) -> dot2::Result {
        dot2::render(self, output)
    }

}


impl<'a> dot2::Labeller<'a> for Graph {
    type Node = u64;
    type Edge = &'a (u64, u64);
    type Subgraph = ();

    fn graph_id(&'a self) -> dot2::Result<dot2::Id<'a>> {
        dot2::Id::new("control_flow")
    }

    fn node_id(&'a self, n: &Self::Node) -> dot2::Result<dot2::Id<'a>> {
        dot2::Id::new(format!("N0x{:x}", n))
    }

    fn node_label(&'a self, n: &Self::Node) -> dot2::Result<dot2::label::Text<'a>> {
        let index = self.nodes.iter().position(|v| v == n).unwrap();
        let label = format!("{}", self.blocks[index]);
        Ok(dot2::label::Text::LabelStr(
            label.into()
            // format!("{}", self.blocks[index]).as_str().into()
            // self.labels[index].as_str().into()
        ))
    }

    // edge labels?
}


impl<'a> dot2::GraphWalk<'a> for Graph {
    type Node = u64;
    type Edge = &'a (u64, u64);
    type Subgraph = ();


    fn nodes(&'a self) -> dot2::Nodes<'a, Self::Node> {
        self.nodes.iter().map(|n| *n).collect()
    }


    fn edges(&'a self) -> dot2::Edges<'a, Self::Edge> {
        self.edges.iter().collect()
    }


    fn source(&'a self, edge: &Self::Edge) -> Self::Node {
        let & &(s,_) = edge;
        s
    }

    fn target(&'a self, edge: &Self::Edge) -> Self::Node {
        let & &(_,t) = edge;
        t
    }

}



fn main() {

    let path = String::from("/home/san-rok/projects/testtest/target/debug/testtest");
    let binary = Binary::from_elf(path);

    let virtual_address: u64 = 0x8840;
    // test: 0x88cb, 0x8870, 0x88b0, 0x8a0d, 0x893e

    let graph: Graph = Graph::from_address(&binary, virtual_address);

    let mut f = std::fs::File::create("/home/san-rok/projects/virtual_address/virtual_address.dot").unwrap();
    graph.render_to(&mut f).unwrap();

}


// PART 03B: list of instructions
// hint: use petgraph crate: https://docs.rs/petgraph/latest/petgraph/algo/dominators/index.html
// why dominator tree:  Prosser, Reese T. (1959). "Applications of Boolean matrices to the analysis of flow diagrams"
// basic block scheduling; dominator tree























//////// JUNK ////////

/*
let mut file = File::open("/home/san-rok/projects/testtest/target/debug/testtest")
.map_err(|_| "open file error").unwrap();

let file_len = file.metadata().map_err(|_| "get metadata error").unwrap().len();

println!("{}", file_len);

let mut contents = vec![0; file_len as usize];


file.read_exact(&mut contents[..])
.map_err(|_| "read header error").unwrap();
*/

/*
let header = Elf::parse_header(&contents[..ELF64_HDR_SIZE]).map_err(|_| "parse elf header error").unwrap();

// if there are no program segments then error
 if header.e_phnum == 0 { panic!("ELF doesn't have any program segments"); }
 let mut elf = Elf::lazy_parse(header).map_err(|_| "cannot parse ELF file").unwrap();
 // read in program header table
 // size of program header in bytes
 let program_hdr_table_size = header.e_phnum * header.e_phentsize;
 file.seek(SeekFrom::Start(header.e_phoff))
     .map_err(|_| "seek error").unwrap();
 file.read_exact(
 &mut contents[ELF64_HDR_SIZE..ELF64_HDR_SIZE + (program_hdr_table_size as usize)],
 )
     .map_err(|_| "read program header table error").unwrap();
 let ctx = Ctx {
     le: Endian::Little,
     container: Container::Big,
 };
 elf.program_headers = ProgramHeader::parse(
 &contents,
 header.e_phoff as usize,
 header.e_phnum as usize,
     ctx,
 )
     .map_err(|_| "parse program headers error").unwrap();
 // println!("{:#?}", elf);
 */

/*

let header = Elf::parse_header(&contents).map_err(|_| "parse elf header error").unwrap();

    // println!("{:#?}", header);

    // if there are no program segments then error
    // if header.e_phnum == 0 { return Err("ELF doesn't have any program segments"); }

    // read in program header table
    // size of program header in bytes
    let program_hdr_table_size = header.e_phnum * header.e_phentsize;
    file.seek(SeekFrom::Start(header.e_phoff))
        .map_err(|_| "seek error").unwrap();
    file.read_exact(
        &mut contents[ELF64_HDR_SIZE..ELF64_HDR_SIZE + (program_hdr_table_size as usize)],
    )
    .map_err(|_| "read program header table error").unwrap();


    let mut elf = Elf::lazy_parse(header).map_err(|_| "cannot parse ELF file").unwrap();

    let ctx = Ctx {
        le: Endian::Little,
        container: Container::Big,
    };

    elf.program_headers = ProgramHeader::parse(
        &contents,
        header.e_phoff as usize,
        header.e_phnum as usize,
        ctx,
    )
    .map_err(|_| "parse program headers error").unwrap();

*/

/*

// no virtual addresses here !!
// mapped: from program headers - maybe: virtual_address_to_byte_index function
// let start: usize = range.start as usize;
// let end: usize = range.end as usize;

*/

/*

    /*
    for _i in 0..31 {
        decoder.decode_out(&mut instr);

        println!("{:016x} {}, type {:?}", instr.ip() /*+ 0x8853*/, instr, instr.flow_control());
        // dummy !!
        // if instr.op0_kind() == OpKind::NearBranch64 {
        //    println!("{:016x}", instr.near_branch_target());
        // }
        // println!("{:#x?}", instr);
        // println!("{:#x?}", instr.flow_control());

        // println!("{:?}", instr.next_ip());
    }
    

     */

    // mnemonic() -> instruction name
    // 


    /*
    let bytes = b"\x31\xed";
    let mut decoder = Decoder::new(64, bytes, 0);
    
    let instr = decoder.decode();

    println!("{:?}", instr);

    */

    /*
    let path = String::from("/home/san-rok/projects/testtest/target/debug/testtest");
    let binary = Binary::from_elf(path);

    // println!("ELF header: {:#?}", binary.elf_header);
    println!("Program headers table: {:#?}", binary.program_header);

    let byte_slice = binary.virtual_address_range(0x89e0..0x89f0).unwrap();

    for i in byte_slice {
        println!("{:x}", i);
    }
    */





*/

/*

    /*
    match instr.flow_control() {
        FlowControl::Exception => bb.targets.push(instr.ip() + bb.address),
        FlowControl::Return => bb.targets.push(instr.ip() + bb.address),
        FlowControl::UnconditionalBranch => {
            if instr.is_jmp_short_or_near() { 
                bb.targets.push(instr.near_branch_target());
            } else if instr.is_jmp_far() {
                bb.targets.push(instr.far_branch_selector() as u64);
            }
        }
        FlowControl::ConditionalBranch => {
            bb.targets.push(instr.ip() + bb.address + 0x1);
            if instr.is_jcc_short_or_near() {
                bb.targets.push(instr.near_branch_target());
            } 
            else if instr.is_jcx_short() {
                bb.targets.push(instr.near_branch_target()); // not checked yet
            } else if instr.is_loop() || instr.is_loopcc() {
                bb.targets.push(instr.near_branch_target()); // not checked yet
            }
            // else if instr.is_jkcc_short_or_near() { bb.targets.push(instr.near_branch_target());}
        }
        FlowControl::IndirectBranch => {
            if instr.is_jmp_near_indirect() {
                bb.targets.push(instr.near_branch_target());
            }
            // TODO !!
        }
        _ => {
            bb.targets.push(instr.ip() + bb.address + 0x1);
        }
    }
    */

*/

/*

    let byte_slice = binary.virtual_address_range(virtual_address..(virtual_address + 0x1000)).unwrap();
    let mut decoder = Decoder::new(64, byte_slice, 0);
    // let instr1 = decoder.decode();
    
    let mut bb: BasicBlock = BasicBlock{
        address: virtual_address,
        instructions: Vec::new(),
        targets: Vec::new(),
    };

    let mut instr = Instruction::default();   


    decoder.decode_out(&mut instr);
    bb.instructions.push(instr);

    
    for _i in 0..60 {
        decoder.decode_out(&mut instr);
        bb.instructions.push(instr);
    }
*/

/*

    let mut nodes: Vec<(u64, String)> = Vec::new();
    let mut edges: Vec<(u64, u64)> = Vec::new();

    let mut count: Vec<u64> = Vec::new();

    count.push(virtual_address);

    while !count.is_empty() {
        let current_source = count.pop().unwrap();

        let bb = BasicBlock::from_address(&binary, current_source);

        nodes.push((bb.address, format!("{}", bb)));

        let mut current_targets = bb.targets;

        while !current_targets.is_empty() {
            let current_target = current_targets.pop().unwrap();

            edges.push((current_source, current_target));

            if !count.contains(&current_target) {
                count.push(current_target);
            }

            
        }
    }


*/

/*


struct Graph {
    nodes: Vec<(u64, String)>,
    edges: Vec<(u64, u64)>, //(source, target)
}

impl Graph {

    // bfs for control flow graph
    fn from_address(binary: &Binary, va: u64) -> Self {

        let mut nodes: Vec<(u64, String)> = Vec::new();
        let mut edges: Vec<(u64, u64)> = Vec::new();

        let mut ud_nodes: Vec<u64> = Vec::new();

        ud_nodes.push(va);

        while !ud_nodes.is_empty() {
            let source = ud_nodes.pop().unwrap();
    
            let bb = BasicBlock::from_address(&binary, source);
    
            nodes.push((bb.address, format!("{}", bb)));
    
            let mut targets_all = bb.targets;
    
            while !targets_all.is_empty() {
                let target = targets_all.pop().unwrap();
    
                edges.push((source, target));
    
                if !ud_nodes.contains(&target) {
                    ud_nodes.push(target);
                }                
            }
        }

        Graph {
            nodes: nodes,
            edges: edges,
        }
    

    }

}



*/

/*
   println!("nodes:");
   for i in 0..graph.nodes.len() {
       println!("{:016x}", graph.nodes[i]);
       println!("{}", graph.labels[i]);
   }
   println!("edges:");
   for i in graph.edges {
       println!("{:x?}", i);
   }
*/

/*
fn render_to<W: std::io::Write>(graph: &Graph, output: &mut W) -> dot2::Result {
    dot2::render(graph, output)
}
*/

/*



struct Graph {
    nodes: Vec<u64>,
    labels: Vec<String>,
    edges: Vec<(u64, u64)>, //(source, target)
}

impl Graph {

    // bfs for control flow graph
    fn from_address(binary: &Binary, va: u64) -> Self {

        let mut nodes: Vec<u64> = Vec::new();
        let mut labels: Vec<String> = Vec::new();
        let mut edges: Vec<(u64, u64)> = Vec::new();

        let mut ud_nodes: Vec<u64> = Vec::new();

        ud_nodes.push(va);

        while !ud_nodes.is_empty() {
            let source = ud_nodes.pop().unwrap();
    
            let bb = BasicBlock::from_address(&binary, source);
    
            nodes.push(bb.address);
            labels.push(format!("{}", bb));
    
            let mut targets_all = bb.targets;
    
            while !targets_all.is_empty() {
                let target = targets_all.pop().unwrap();
    
                edges.push((source, target));
    
                if !ud_nodes.contains(&target) {
                    ud_nodes.push(target);
                }                
            }
        }

        Graph {
            nodes: nodes,
            labels: labels,
            edges: edges,
        }
    }

    // from graph to .dot
    fn render_to<W: std::io::Write>(&self, output: &mut W) -> dot2::Result {
        dot2::render(self, output)
    }

}

impl<'a> dot2::Labeller<'a> for Graph {
    type Node = u64;
    type Edge = &'a (u64, u64);
    type Subgraph = ();

    fn graph_id(&'a self) -> dot2::Result<dot2::Id<'a>> {
        dot2::Id::new("control_flow")
    }

    fn node_id(&'a self, n: &Self::Node) -> dot2::Result<dot2::Id<'a>> {
        dot2::Id::new(format!("N0x{:x}", n))
    }

    fn node_label(&'a self, n: &Self::Node) -> dot2::Result<dot2::label::Text<'a>> {
        let index = self.nodes.iter().position(|v| v == n).unwrap();
        Ok(dot2::label::Text::LabelStr(
            self.labels[index].as_str().into()
        ))
    }

    // edge labels?
}


impl<'a> dot2::GraphWalk<'a> for Graph {
    type Node = u64;
    type Edge = &'a (u64, u64);
    type Subgraph = ();


    fn nodes(&'a self) -> dot2::Nodes<'a, Self::Node> {
        self.nodes.iter().map(|n| *n).collect()
    }


    fn edges(&'a self) -> dot2::Edges<'a, Self::Edge> {
        self.edges.iter().collect()
    }


    fn source(&'a self, edge: &Self::Edge) -> Self::Node {
        let & &(s,_) = edge;
        s
    }

    fn target(&'a self, edge: &Self::Edge) -> Self::Node {
        let & &(_,t) = edge;
        t
    }

}




*/

/*
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn valid_virtual_address() {

        let path = String::from("/home/san-rok/projects/testtest/target/debug/testtest");
        let binary = Binary::from_elf(path);

        let byte_slice = binary.virtual_address_range(0x89e0..0x89e4).unwrap();

        assert_eq!(&[ 0x48, 0x83, 0xec, 0x38 ], byte_slice);

    }
}
*/

/*

// slice of bytes at a given virtual address range or error:invalid
    fn virtual_address_range(&self, range: Range<u64>) -> Result<&[u8], String> {

        // index of program containing given virtual address range
        let segment = &self.program_header.iter()
            .position(
                |x|
                    // p_type = "PT_LOAD"
                    x.p_type == 1 && 
                    // given va range is inside the range of program
                    x.p_vaddr <= range.start && 
                    range.end <= x.p_vaddr + x.p_filesz
            )
            .ok_or( String::from("invalid virtual address range error"))?;

        let segment = &self.program_header[*segment];

        Ok( &self.bytes[ 
            // convert the virtual address to file address
            (range.start - segment.p_vaddr + segment.p_offset) as usize .. (range.end - segment.p_vaddr + segment.p_offset) as usize
        ])
    }

*/

/*


struct Graph {
    nodes: Vec<u64>,
    // basicblocks: Vec<BasicBlock>,
    labels: Vec<String>,
    edges: Vec<(u64, u64)>, //(source, target)
}

impl Graph {

    // dfs for control flow graph
    fn from_address(binary: &Binary, va: u64) -> Self {

        let mut nodes: Vec<u64> = Vec::new();
        // let mut basicblocks: Vec<BasicBlock> = Vec::new();
        let mut labels: Vec<String> = Vec::new();
        let mut edges: Vec<(u64, u64)> = Vec::new();

        let mut ud_nodes: Vec<u64> = Vec::new();

        ud_nodes.push(va);

        while !ud_nodes.is_empty() {
            let source = ud_nodes.pop().unwrap();
    
            let bb = BasicBlock::from_address(binary, source);
    
            nodes.push(bb.address);
            // basicblocks.push(bb);
            labels.push(format!("{}", bb));
    
            let mut targets_all = bb.targets;
    
            while !targets_all.is_empty() {
                let target = targets_all.pop().unwrap();
    
                edges.push((source, target));
    
                if !ud_nodes.contains(&target) {
                    ud_nodes.push(target);
                }                
            }
        }

        Graph {
            nodes,
            // basicblocks: basicblocks,
            labels,
            edges,
        }
    }

    // from graph to .dot
    fn render_to<W: std::io::Write>(&self, output: &mut W) -> dot2::Result {
        dot2::render(self, output)
    }

}

impl<'a> dot2::Labeller<'a> for Graph {
    type Node = u64;
    type Edge = &'a (u64, u64);
    type Subgraph = ();

    fn graph_id(&'a self) -> dot2::Result<dot2::Id<'a>> {
        dot2::Id::new("control_flow")
    }

    fn node_id(&'a self, n: &Self::Node) -> dot2::Result<dot2::Id<'a>> {
        dot2::Id::new(format!("N0x{:x}", n))
    }

    fn node_label(&'a self, n: &Self::Node) -> dot2::Result<dot2::label::Text<'a>> {
        let index = self.nodes.iter().position(|v| v == n).unwrap();
        Ok(dot2::label::Text::LabelStr(
            // format!("{}", self.basicblocks[index]).as_str().into()
            self.labels[index].as_str().into()
        ))
    }

    // edge labels?
}


impl<'a> dot2::GraphWalk<'a> for Graph {
    type Node = u64;
    type Edge = &'a (u64, u64);
    type Subgraph = ();


    fn nodes(&'a self) -> dot2::Nodes<'a, Self::Node> {
        self.nodes.iter().map(|n| *n).collect()
    }


    fn edges(&'a self) -> dot2::Edges<'a, Self::Edge> {
        self.edges.iter().collect()
    }


    fn source(&'a self, edge: &Self::Edge) -> Self::Node {
        let & &(s,_) = edge;
        s
    }

    fn target(&'a self, edge: &Self::Edge) -> Self::Node {
        let & &(_,t) = edge;
        t
    }

}




*/

/*
struct Graph {
    nodes: Vec<u64>,
    edges: Vec<(u64, u64)>, //(source, target)
    blocks: Vec<BasicBlock>,
}

impl Graph {

    // dfs for control flow graph
    fn from_address(binary: &Binary, va: u64) -> Self {

        let mut nodes: Vec<u64> = Vec::new();
        let mut edges: Vec<(u64, u64)> = Vec::new();
        let mut blocks: Vec<BasicBlock> = Vec::new();

        let mut start_end_address: Vec<(u64, u64)> = Vec::new();

        let mut ud_nodes: Vec<u64> = Vec::new();

        ud_nodes.push(va);

        while let Some(source) = ud_nodes.pop(){
    
            let bb = BasicBlock::from_address(binary, source);
    
            nodes.push(bb.address);

            // how to use bb.targets directly ?
            let mut targets: Vec<u64>  = bb.targets.iter().copied().collect();

            start_end_address.push((
                bb.instructions[0].ip(),
                bb.instructions.iter().last().unwrap().ip()
            ));

            blocks.push(bb);

            while let Some(target) = targets.pop() {
                edges.push((source, target));
    
                if !ud_nodes.contains(&target) {
                    ud_nodes.push(target);
                }                
            }

            


            let cut_block = blocks.iter().position(|&x| x.address < target && target <= x.address + (x.instructions.len() as u64));

                match cut_block {
                    Some(index) => {
                        let tmp01_block = blocks.remove(index);
                        
                        let cut_instr = tmp01_block.instructions.iter().position(|&x| x.ip() == target);

                        


                        tmp01_block
                    }
                }


            // TBC !!

            
        }

        Graph {
            nodes,
            edges,
            blocks,
        }
    }



    /*
    // from graph to .dot
    fn render_to<W: std::io::Write>(&self, output: &mut W) -> dot2::Result {
        dot2::render(self, output)
    }
     */

}

*/

/*
impl<'a> dot2::Labeller<'a> for Graph {
    type Node = u64;
    type Edge = &'a (u64, u64);
    type Subgraph = ();

    fn graph_id(&'a self) -> dot2::Result<dot2::Id<'a>> {
        dot2::Id::new("control_flow")
    }

    fn node_id(&'a self, n: &Self::Node) -> dot2::Result<dot2::Id<'a>> {
        dot2::Id::new(format!("N0x{:x}", n))
    }

    fn node_label(&'a self, n: &Self::Node) -> dot2::Result<dot2::label::Text<'a>> {
        let index = self.nodes.iter().position(|v| v == n).unwrap();
        Ok(dot2::label::Text::LabelStr(
            // format!("{}", self.basicblocks[index]).as_str().into()
            self.labels[index].as_str().into()
        ))
    }

    // edge labels?
}


impl<'a> dot2::GraphWalk<'a> for Graph {
    type Node = u64;
    type Edge = &'a (u64, u64);
    type Subgraph = ();


    fn nodes(&'a self) -> dot2::Nodes<'a, Self::Node> {
        self.nodes.iter().map(|n| *n).collect()
    }


    fn edges(&'a self) -> dot2::Edges<'a, Self::Edge> {
        self.edges.iter().collect()
    }


    fn source(&'a self, edge: &Self::Edge) -> Self::Node {
        let & &(s,_) = edge;
        s
    }

    fn target(&'a self, edge: &Self::Edge) -> Self::Node {
        let & &(_,t) = edge;
        t
    }

}

 */














