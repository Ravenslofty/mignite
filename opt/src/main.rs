#![allow(warnings)]

use mignite::mig4::Mig;

use mignite::mig4_map::Mapper;

fn main() {
    const UNIT_K: usize = 4;
    const UNIT_C: usize = 8;
    const UNIT_W: i32 = 1;
    const UNIT_LUT_AREA: [u32; 5] = [0, 1, 1, 1, 1];
    const UNIT_LUT_DELAY: [&[i32]; 5] = [&[], &[0], &[0, 0], &[0, 0, 0], &[0, 0, 0, 0]];

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

    const CV_K: usize = 6;
    const CV_C: usize = 8;
    const CV_W: i32 = 600;
    const CV_LUT_AREA: [u32; 7] = [0, 1, 1, 1, 1, 1, 2];
    const CV_LUT_DELAY: [&[i32]; 7] = [&[], &[97], &[97, 400], &[97, 400, 510], &[97, 400, 510, 512], &[97, 400, 510, 512, 583], &[97, 400, 510, 512, 583, 605]];

    let mut mig = Mig::from_aiger("chess-noresyn.aag");

    mig.cleanup_graph();

    //mig.to_graphviz("after.dot").unwrap();
    println!();
    println!("Unit delay:");
    println!();
    let mut depth1_mapper = Mapper::new(UNIT_C, UNIT_K, &UNIT_LUT_AREA, &UNIT_LUT_DELAY, UNIT_W, &mig);
    depth1_mapper.compute_cuts(Mapper::cut_rank_depth, Mapper::cut_rank_size, Mapper::cut_rank_area_flow);
    let luts = depth1_mapper.map_luts(true);
    let area = luts.iter().map(|cut| UNIT_LUT_AREA[cut.input_count()]).sum::<u32>();
    //depth1_mapper.compute_cuts(Mapper::cut_rank_depth, Mapper::cut_rank_size, Mapper::cut_rank_area_flow);
    //depth1_mapper.map_luts(true);
    let mut best = area;
    for _ in 0..10 {
        depth1_mapper.compute_cuts(Mapper::cut_rank_area_flow, Mapper::cut_rank_fanin_refs, Mapper::cut_rank_depth);
        let luts = depth1_mapper.map_luts(true);
        let area = luts.iter().map(|cut| UNIT_LUT_AREA[cut.input_count()]).sum::<u32>();
        if area < best {
            best = area
        } else {
            break;
        }
    }

    println!();
    println!("iCE40HX:");
    println!();
    let mut depth1_mapper = Mapper::new(ICE40HX_C, ICE40HX_K, &ICE40HX_LUT_AREA, &ICE40HX_LUT_DELAY, ICE40HX_W, &mig);
    depth1_mapper.compute_cuts(Mapper::cut_rank_depth, Mapper::cut_rank_size, Mapper::cut_rank_area_flow);
    let luts = depth1_mapper.map_luts(true);
    let area = luts.iter().map(|cut| ICE40HX_LUT_AREA[cut.input_count()]).sum::<u32>();
    //depth1_mapper.compute_cuts(Mapper::cut_rank_depth, Mapper::cut_rank_size, Mapper::cut_rank_area_flow);
    //depth1_mapper.map_luts(true);
    let mut best = area;
    for _ in 0..10 {
        depth1_mapper.compute_cuts(Mapper::cut_rank_area_flow, Mapper::cut_rank_fanin_refs, Mapper::cut_rank_depth);
        let luts = depth1_mapper.map_luts(true);
        let area = luts.iter().map(|cut| ICE40HX_LUT_AREA[cut.input_count()]).sum::<u32>();
        if area < best {
            best = area
        } else {
            break;
        }
    }

    /*let mut depth2_mapper = Mapper::new(ICE40HX_C, ICE40HX_K, &ICE40HX_LUT_AREA, &ICE40HX_LUT_DELAY, ICE40HX_W, &mig);
    depth2_mapper.compute_cuts(Mapper::cut_rank_depth, Mapper::cut_rank_area_flow, Mapper::cut_rank_size);
    depth2_mapper.map_luts();

    let mut area_flow_mapper = Mapper::new(ICE40HX_C, ICE40HX_K, &ICE40HX_LUT_AREA, &ICE40HX_LUT_DELAY, ICE40HX_W, &mig);
    area_flow_mapper.compute_cuts(Mapper::cut_rank_area_flow, Mapper::cut_rank_fanin_refs, Mapper::cut_rank_depth);
    area_flow_mapper.map_luts();*/

    println!();
    println!("ECP5:");
    println!();
    let mut depth1_mapper = Mapper::new(ECP5_C, ECP5_K, &ECP5_LUT_AREA, &ECP5_LUT_DELAY, ECP5_W, &mig);
    depth1_mapper.compute_cuts(Mapper::cut_rank_depth, Mapper::cut_rank_size, Mapper::cut_rank_area_flow);
    let luts = depth1_mapper.map_luts(true);
    let area = luts.iter().map(|cut| ECP5_LUT_AREA[cut.input_count()]).sum::<u32>();
    //depth1_mapper.compute_cuts(Mapper::cut_rank_depth, Mapper::cut_rank_size, Mapper::cut_rank_area_flow);
    //depth1_mapper.map_luts(true);
    let mut best = area;
    for _ in 0..10 {
        depth1_mapper.compute_cuts(Mapper::cut_rank_area_flow, Mapper::cut_rank_fanin_refs, Mapper::cut_rank_depth);
        let luts = depth1_mapper.map_luts(true);
        let area = luts.iter().map(|cut| ECP5_LUT_AREA[cut.input_count()]).sum::<u32>();
        if area < best {
            best = area
        } else {
            break;
        }
    }

    println!();
    println!("Cyclone V:");
    println!();
    let mut depth1_mapper = Mapper::new(CV_C, CV_K, &CV_LUT_AREA, &CV_LUT_DELAY, CV_W, &mig);
    depth1_mapper.compute_cuts(Mapper::cut_rank_depth, Mapper::cut_rank_size, Mapper::cut_rank_area_flow);
    let luts = depth1_mapper.map_luts(true);
    let area = luts.iter().map(|cut| CV_LUT_AREA[cut.input_count()]).sum::<u32>();
    //depth1_mapper.compute_cuts(Mapper::cut_rank_depth, Mapper::cut_rank_size, Mapper::cut_rank_area_flow);
    //depth1_mapper.map_luts(true);
    let mut best = area;
    for _ in 0..10 {
        depth1_mapper.compute_cuts(Mapper::cut_rank_area_flow, Mapper::cut_rank_fanin_refs, Mapper::cut_rank_depth);
        let luts = depth1_mapper.map_luts(true);
        let area = luts.iter().map(|cut| CV_LUT_AREA[cut.input_count()]).sum::<u32>();
        if area < best {
            best = area
        } else {
            break;
        }
    }

    //mig.to_graphviz("before.dot").unwrap();

    //mig.optimise_global();
    //mig.optimise_area(&mig.input_nodes());


    //let f = std::fs::File::create("test.il").unwrap();
    //mig.to_rtlil(f).unwrap();
}
