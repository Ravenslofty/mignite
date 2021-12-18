#![allow(warnings)]

use mignite::mig4::Mig;

use mignite::mig4_map::Mapper;

fn compute_cuts(max_cuts: usize, max_inputs: usize, lut_area: &[u32], lut_delay: &[&[i32]], wire_delay: i32, mig: &Mig) {
    let mut depth1_mapper = Mapper::new(max_cuts, max_inputs, lut_area, lut_delay, wire_delay, mig);
    depth1_mapper.compute_cuts(Mapper::cut_rank_depth, Mapper::cut_rank_size, Mapper::cut_rank_area_flow);
    let luts = depth1_mapper.map_luts(true);
    let area = luts.iter().map(|cut| lut_area[cut.input_count()]).sum::<u32>();
    let mut best = area;

    for _ in 1..=2 {
        depth1_mapper.compute_cuts(Mapper::cut_rank_area_flow, Mapper::cut_rank_edge_flow, Mapper::cut_rank_fanin_refs);
        let luts = depth1_mapper.map_luts(false);
    }

    for _ in 1..=2 {
        depth1_mapper.compute_cuts(Mapper::cut_rank_exact_area, Mapper::cut_rank_exact_edge, Mapper::cut_rank_fanin_refs);
        let luts = depth1_mapper.map_luts(false);
    }

    /*for _ in 0..10 {
        //println!("=== AREA/EDGE FLOW ===");
        depth1_mapper.compute_cuts(Mapper::cut_rank_area_flow, Mapper::cut_rank_edge_flow, Mapper::cut_rank_fanin_refs);
        let luts = depth1_mapper.map_luts(false);
        //println!("=== EXACT AREA/EDGE ===");
        depth1_mapper.compute_cuts(Mapper::cut_rank_exact_area, Mapper::cut_rank_exact_edge, Mapper::cut_rank_fanin_refs);
        let luts = depth1_mapper.map_luts(false);
        let area = luts.iter().map(|cut| lut_area[cut.input_count()]).sum::<u32>();
        if area < best {
            best = area
        } else {
            break;
        }
    }*/
    depth1_mapper.map_luts(true);
}

fn main() {
    const UNIT_K: usize = 4;
    const UNIT_C: usize = 8;
    const UNIT_W: i32 = 1;
    const UNIT_LUT_AREA: [u32; 7] = [0, 1, 1, 1, 1, 1, 1];
    const UNIT_LUT_DELAY: [&[i32]; 7] = [&[], &[0], &[0, 0], &[0, 0, 0], &[0, 0, 0, 0], &[0, 0, 0, 0, 0], &[0, 0, 0, 0, 0, 0]];

    const ICE40HX_K: usize = 4;
    const ICE40HX_C: usize = 8;
    const ICE40HX_W: i32 = 350;
    const ICE40HX_LUT_AREA: [u32; 5] = [0, 1, 1, 1, 1];
    const ICE40HX_LUT_DELAY: [&[i32]; 5] = [&[], &[316], &[316, 379], &[316, 379, 400], &[316, 379, 400, 449]];

    const ECP5_K: usize = 7;
    const ECP5_C: usize = 8;
    const ECP5_W: i32 = 300;
    const ECP5_LUT_AREA: [u32; 8] = [0, 1, 1, 1, 1, 2, 4, 8];
    const ECP5_LUT_DELAY: [&[i32]; 8] = [&[], &[141], &[141, 275], &[141, 275, 379], &[141, 275, 379, 379], &[151, 239, 373, 477, 477], &[148, 292, 380, 514, 618, 618], &[148, 289, 433, 521, 655, 759, 759]];

    const NEXUS_K: usize = 5;
    const NEXUS_C: usize = 8;
    const NEXUS_W: i32 = 300;
    const NEXUS_LUT_AREA: [u32; 6] = [0, 1, 1, 1, 1, 2];
    const NEXUS_LUT_DELAY: [&[i32]; 6] = [&[], &[233], &[233, 233], &[233, 233, 233], &[233, 233, 233, 233], &[171, 303, 306, 309, 311]];

    const CV_K: usize = 6;
    const CV_C: usize = 8;
    const CV_W: i32 = 600;
    const CV_LUT_AREA: [u32; 7] = [0, 1, 1, 1, 1, 1, 2];
    const CV_LUT_DELAY: [&[i32]; 7] = [&[], &[97], &[97, 400], &[97, 400, 510], &[97, 400, 510, 512], &[97, 400, 510, 512, 583], &[97, 400, 510, 512, 583, 605]];

    let mut mig = Mig::from_aiger("adder.aag");

    mig.cleanup_graph();

    //mig.to_graphviz("after.dot").unwrap();
    println!();
    println!("Unit delay:");
    println!();
    compute_cuts(UNIT_C, UNIT_K, &UNIT_LUT_AREA, &UNIT_LUT_DELAY, UNIT_W, &mig);

    println!();
    println!("iCE40HX:");
    println!();
    compute_cuts(ICE40HX_C, ICE40HX_K, &ICE40HX_LUT_AREA, &ICE40HX_LUT_DELAY, ICE40HX_W, &mig);

    println!();
    println!("ECP5:");
    println!();
    compute_cuts(ECP5_C, ECP5_K, &ECP5_LUT_AREA, &ECP5_LUT_DELAY, ECP5_W, &mig);

    println!();
    println!("Nexus:");
    println!();
    compute_cuts(NEXUS_C, NEXUS_K, &NEXUS_LUT_AREA, &NEXUS_LUT_DELAY, NEXUS_W, &mig);

    println!();
    println!("Cyclone V:");
    println!();
    compute_cuts(CV_C, CV_K, &CV_LUT_AREA, &CV_LUT_DELAY, CV_W, &mig);

    //mig.to_graphviz("before.dot").unwrap();

    //mig.optimise_global();
    //mig.optimise_area(&mig.input_nodes());

    //let f = std::fs::File::create("test.il").unwrap();
    //mig.to_rtlil(f).unwrap();
}
