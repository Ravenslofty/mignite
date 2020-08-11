use mignite::mig4::Mig;

fn main() {
    let mut mig = Mig::from_aiger("add_15_15.aag");

    //mig.optimise_size(1);
    //let count = mig.count_nodes();
    //eprintln!("MIG has {} reachable majority gates.", count);

    mig.optimise_area();

    mig.to_graphviz("graph.dot").unwrap();
    //mig.optimise_size(100);

    //let count = mig.count_nodes();
    //eprintln!("MIG has {} reachable majority gates.", count);
}
