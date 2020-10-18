use mignite::mig4::Mig;

use mignite::mig4_map::Mapper;

fn main() {
    let mut mig = Mig::from_aiger("netlist.aag");

    let mut mapper = Mapper::new(999, 4, mig);

    mapper.compute_cuts();

    //mig.to_graphviz("before.dot").unwrap();

    //mig.optimise_global();
    //mig.optimise_area(&mig.input_nodes());

    //mig.to_graphviz("after.dot").unwrap();
    //let f = std::fs::File::create("test.il").unwrap();
    //mig.to_rtlil(f).unwrap();
}
