use mignite::mig4::Mig;

fn main() {
    let mut mig = Mig::from_aiger("add_15_15.aig");

    //mig.optimise_size(1);
    //let count = mig.count_nodes();
    //eprintln!("MIG has {} reachable majority gates.", count);

    mig.print_graph();
    //mig.optimise_size(100);

    //let count = mig.count_nodes();
    //eprintln!("MIG has {} reachable majority gates.", count);
}
