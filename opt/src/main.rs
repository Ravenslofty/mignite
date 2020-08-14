use mignite::mig4::Mig;

fn main() {
    let mut mig = Mig::from_aiger("add_15_15.aag");

    //mig.to_graphviz("before.dot").unwrap();

    mig.optimise_area();

    mig.to_graphviz("after.dot").unwrap();
}
