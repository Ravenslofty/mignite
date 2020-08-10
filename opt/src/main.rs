use mignite::mig4::Mig;

fn main() {
    let mut mig = Mig::from_aiger("adder.aag");

    //mig.optimise_size(1);
    //let count = mig.count_nodes();
    //eprintln!("MIG has {} reachable majority gates.", count);

    mig.optimise_area();

    //mig.print_graph();
    //mig.optimise_size(100);

    //let count = mig.count_nodes();
    //eprintln!("MIG has {} reachable majority gates.", count);
}
