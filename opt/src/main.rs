use mignite::mig4::Mig;

use mignite::mig4_map::Mapper;

fn main() {
    let mig = Mig::from_aiger("chess-resyn.aag");

    //mig.optimise_area(&mig.input_nodes());

    let mut depth1_mapper = Mapper::new(8, 4, &mig);
    depth1_mapper.compute_cuts(Mapper::cut_rank_depth, Mapper::cut_rank_size, Mapper::cut_rank_area_flow);
    let luts = depth1_mapper.map_luts();

    for lut in luts {
        
    }

    /* let mut depth2_mapper = Mapper::new(8, 4, &mig);
    depth2_mapper.compute_cuts(Mapper::cut_rank_depth, Mapper::cut_rank_area_flow, Mapper::cut_rank_size);
    depth2_mapper.map_luts();

    let mut area_flow_mapper = Mapper::new(8, 4, &mig);
    area_flow_mapper.compute_cuts(Mapper::cut_rank_area_flow, Mapper::cut_rank_fanin_refs, Mapper::cut_rank_depth);
    area_flow_mapper.map_luts();*/

    //mig.to_graphviz("before.dot").unwrap();

    //mig.optimise_global();
    //mig.optimise_area(&mig.input_nodes());

    //mig.to_graphviz("after.dot").unwrap();
    //let f = std::fs::File::create("test.il").unwrap();
    //mig.to_rtlil(f).unwrap();
}
