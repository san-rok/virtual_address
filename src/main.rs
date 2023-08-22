
#![feature(impl_trait_in_assoc_type)]

// PART01: Binary struct

pub mod binary;
use crate::binary::*;

// PART02 + PART03.A: Basic Blocks & Control Flow Graph

pub mod cfg;
use crate::cfg::*;

// PART03.B: "Optimal" list of basic blocks

pub mod vagraph;
use crate::vagraph::vag::*;

pub mod bbsort;
use crate::bbsort::*;


fn main() {

    let path = String::from("/home/san-rok/projects/testtest/target/debug/testtest");
    let binary = Binary::from_elf(path);

    let virtual_address: u64 =  0x96b4;
    // test: 0x88cb, 0x8870, 0x88b0, 0x8a0d, 0x893e, 0x88f0, 0x8c81, 0x8840, 0x8f41, 0x970b, 0x96b4

    let cfg: ControlFlowGraph = ControlFlowGraph::from_address(&binary, virtual_address);

    let mut f = std::fs::File::create("/home/san-rok/projects/virtual_address/virtual_address.dot").unwrap();
    cfg.render_to(&mut f).unwrap();
    // dot -Tsvg virtual_address.dot > virtual_address.svg

    let vag: VirtualAddressGraph<u64> = VirtualAddressGraph::from_cfg(&cfg);

    let topsort = bbsort(&vag);

    // let topsort = vag.weighted_order();
    println!("{:x?}", topsort);

    let topsort: Vec<u64> = topsort.iter().map(|&x| x.id().unwrap()).collect();
    println!("cost of order: {}", vag.cost_of_order(topsort));
    
    // test dags 
    let file = std::fs::File::open("cfg.yaml").unwrap();
    let vags: Vec<UnwrappedVAGraph<u64>> = serde_yaml::from_reader(file).unwrap();
    let vags: Vec<VirtualAddressGraph<u64>> = vags.iter().map(|x| x.to_vag()).collect();

    /*
    for (index, vag) in vags.iter().enumerate() {
        if vag.address().id().unwrap() == 0x180531370 {
            println!("position: {}", index);
        }
    }
    */

    /*
    let vag = vags.iter().find(|x| x.address().id().unwrap() == 0x180531370).unwrap();
    let mut file = std::fs::File::create("/home/san-rok/projects/virtual_address/test.dot").unwrap();
    vag.render_to(&mut file).unwrap();
    */

    let mut counter: usize = 0;

    for vag in vags {
        let topsort = bbsort(&vag);
        // let topsort: Vec<u64> = topsort.iter().map(|&x| x.id().unwrap()).collect();
        if cost(&vag, &topsort).1 { counter += 1; }
    }

    println!("better results: {}", counter);


}








