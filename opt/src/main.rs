use mignite::mig4::Mig;

fn main() {
    let mut mig = Mig::from_aiger("mem_ctrl.aag");

    //mig.to_graphviz("before.dot").unwrap();

    mig.optimise_area();

    //mig.to_graphviz("after.dot").unwrap();
    let f = std::fs::File::create("test.il").unwrap();
    mig.to_rtlil(f).unwrap();
}
