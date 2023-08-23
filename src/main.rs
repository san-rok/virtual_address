
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

    let topsort = bbsort(&vag, vag.address()).unwrap();

    // let topsort = vag.weighted_order();
    println!("{:x?}", topsort);

    let topsort: Vec<u64> = topsort.iter().map(|&x| x.id().unwrap()).collect();
    println!("cost of order: {}", vag.cost_of_order(topsort));
    
    // test dags 
    let file = std::fs::File::open("cfg.yaml").unwrap();
    let vags: Vec<UnwrappedVAGraph<u64>> = serde_yaml::from_reader(file).unwrap();
    let vags: Vec<VirtualAddressGraph<u64>> = vags.iter().map(|x| x.to_vag()).collect();

    
    let vag = vags.iter().find(|x| x.address().id().unwrap() == 0x184502670).unwrap();
    // let topsort = bbsort(vag);
    // cost(vag, &topsort);

    let mut file = std::fs::File::create("/home/san-rok/projects/virtual_address/test.dot").unwrap();
    vag.render_to(&mut file).unwrap();
    // dot -Tsvg test.dot > test.svg

    let mut count_better: usize = 0;
    let mut count_connected: usize = 0;

    for vag in vags {
        println!("start address of the graph: {:x}", vag.address().id().unwrap());

        /*
        match bbsort(&vag) {
            Ok(topsort) => {
                if cost(&vag, &topsort).1 { counter += 1; }    
            }
            Err(err) => Err(err),
        }
        */


        
        if let Ok(topsort) = bbsort(&vag, vag.address()) {
            count_connected += 1;
            if cost(&vag, vag.address(), &topsort).1 { count_better += 1; } 
        }
        

        // let topsort = bbsort(&vag);
        // if cost(&vag, &topsort).1 { counter += 1; }
    }

    println!("connected cfgs: {}", count_connected);
    println!("better results: {}", count_better);



}








