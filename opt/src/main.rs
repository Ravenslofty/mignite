use mignite::mig4::Mig;

fn main() {
    let mut mig = Mig::from_aiger("mem_ctrl.aag");

    //mig.optimise_size(1);
    //let count = mig.count_nodes();
    //eprintln!("MIG has {} reachable majority gates.", count);

    //mig.to_graphviz("before.dot").unwrap();

    mig.optimise_area();

    mig.to_graphviz("after.dot").unwrap();
    //mig.optimise_size(100);

    //let count = mig.count_nodes();
    //eprintln!("MIG has {} reachable majority gates.", count);
}
