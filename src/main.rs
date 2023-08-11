
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


use kendalls::tau_b;


fn main() {

    let path = String::from("/home/san-rok/projects/testtest/target/debug/testtest");
    let binary = Binary::from_elf(path);

    let virtual_address: u64 =  0x96b4;
    // test: 0x88cb, 0x8870, 0x88b0, 0x8a0d, 0x893e, 0x88f0, 0x8c81, 0x8840, 0x8f41, 0x970b, 0x96b4

    let cfg: ControlFlowGraph = ControlFlowGraph::from_address(&binary, virtual_address);

    let mut f = std::fs::File::create("/home/san-rok/projects/virtual_address/virtual_address.dot").unwrap();
    cfg.render_to(&mut f).unwrap();
    // dot -Tsvg virtual_address.dot > virtual_address.svg

    let vag: VirtualAddressGraph = VirtualAddressGraph::from_cfg(&cfg);

    let _topsort = vag.weighted_order();
    // println!("{:x?}", topsort);


    


    // test dags 
    let file = std::fs::File::open("cfg.yaml").unwrap();
    let vags: Vec<VirtualAddressGraph> = serde_yaml::from_reader(file).unwrap();

    /*
    let mut test_vag = vags.iter_mut().find(|x| x.address() == 0x1845beec0).unwrap();
    // let mut f = std::fs::File::create("/home/san-rok/projects/virtual_address/test_vag.dot").unwrap();
    // test_vag.render_to(&mut f).unwrap();
    // dot -Tsvg test_vag.dot > test_vag.svg

    test_vag.update_in_degrees();

    println!("{:#x?}", test_vag);

    let topsort = test_vag.weighted_order();

    let mut initial_order: Vec<u64> = Vec::new();
        for node in test_vag.nodes() {
            initial_order.push(node.address());
        }
    initial_order.sort();


    println!("nodes originally: {}", initial_order.len());
    println!("nodes after sort: {}", topsort.len());

    for i in 0..initial_order.len() {
        if i < topsort.len() {
            println!("{:x}, {:x}", initial_order[i], topsort[i]);
        } else {
            println!("{:x}, ", initial_order[i]);
        }
    }

    */

    // let original_cost: usize = vag.cost_of_order(initial_order);
    // let sorted_cost: usize = vag.cost_of_order(topsort);

    // println!("cost of original order: {}", original_cost);
    // println!("cost of topological sort: {} \n", sorted_cost);

    let mut better_cost = 0;

    for mut vag in vags {
        vag.update_in_degrees();

        let topsort = vag.weighted_order();

        // let mut kahngraph: KahnGraph = KahnGraph::from_vag(&dag);
        // let topsort = kahngraph.kahn_algorithm();

        let mut initial_order: Vec<u64> = Vec::new();
        for node in vag.nodes() {
            initial_order.push(node.address());
        }
        initial_order.sort();

        println!("starting block's address: {:x}", vag.address());

        // println!("initial number of nodes {}", initial_order.len());
        // println!("ordered number of nodes {}", topsort.len());

        for i in 0..initial_order.len() {
            if i < topsort.len() {
                println!("{:x}, {:x}", initial_order[i], topsort[i]);
            } else {
                println!("{:x}, ", initial_order[i]);
            }
        }

        /*
        for i in 0..topsort.len() {
            println!("{:x}, {:x}", initial_order[i], topsort[i]);
        }
        */
    

        let kendall_tau = tau_b(&initial_order, &topsort).unwrap().0;

        // println!("initial order: {:x?}", initial_order);
        // println!("topological sort: {:x?}", topsort);

        let original_cost: usize = vag.cost_of_order(initial_order);
        let sorted_cost: usize = vag.cost_of_order(topsort);

        println!("kendall tau: {:#?}", kendall_tau);
        println!("cost of original order: {}", original_cost);
        println!("cost of topological sort: {} \n", sorted_cost);

        if sorted_cost <= original_cost {
            better_cost += 1;
        }


        // some addresses with big differences: 0x1800c17b0
        /*
        if dag.address() == 0x1800c1530 {
            let mut file = std::fs::File::create("/home/san-rok/projects/virtual_address/test.dot").unwrap();
            dag.render_to(&mut file).unwrap();
        }
        */
    }

    println!("number of times topsort is better: {}", better_cost);


}

