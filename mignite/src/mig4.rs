use petgraph::prelude::*;
use aiger::Literal;

#[derive(Hash)]
pub enum MigNode {
    Input(u32),
    Output(u32),
    Zero,
    Majority,
}

#[derive(Default)]
pub struct Mig {
    graph: StableGraph<MigNode, bool, Directed>,
    zero: NodeIndex,
}

impl Mig {
    pub fn from_aiger(path: &str) -> Self {
        let file = std::fs::File::open(path).unwrap();
        let reader = aiger::Reader::from_reader(file).unwrap();
        let mut mig = Self::default();

        mig.zero = mig.graph.add_node(MigNode::Zero);

        for record in reader.records() {
            match record.unwrap() {
                aiger::Aiger::Input(Literal(index)) => {
                    mig.graph.add_node(MigNode::Input(index as u32));
                },
                aiger::Aiger::Latch { output, input } => {
                    todo!("latches")
                },
                aiger::Aiger::Output(Literal(index)) => {
                    mig.graph.add_node(MigNode::Output(index as u32));
                },
                aiger::Aiger::AndGate { output, inputs } => {
                    //let Literal(output) = output;
                    let Literal(input0) = inputs[0];
                    let Literal(input1) = inputs[1];

                    let gate = mig.graph.add_node(MigNode::Majority);
                    mig.graph.update_edge(NodeIndex::new(input0 >> 1), gate, input0 & 1 == 1);
                    mig.graph.update_edge(NodeIndex::new(input1 >> 1), gate, input1 & 1 == 1);
                    mig.graph.update_edge(mig.zero, gate, false);
                },
            }
        }

        mig
    }

    pub fn print_graph(&self) {
        println!("strict digraph {{");

        for node in self.graph.node_indices() {
            match self.graph[node] {
                MigNode::Input(index) => {
                    println!("{} [shape=box,color=blue,label=\"Input {}\"];", node.index(), index);
                },
                MigNode::Output(index) => {
                    println!("{} [shape=box,color=green,label=\"Output {}\"];", node.index(), index);
                },
                MigNode::Zero => {},
                MigNode::Majority => {
                    println!("{} [label=\"Majority {0}\"];", node.index());
                },
            }
        }

        for edge in self.graph.edge_indices() {
            let (to, from) = self.graph.edge_endpoints(edge).unwrap();

            match self.graph[from] {
                MigNode::Input(index) => {
                    print!("{} -> {}", from.index(), to.index());
                },
                MigNode::Output(index) => {
                    print!("{} -> {}", from.index(), to.index());
                },
                MigNode::Zero => {
                    println!("z{} [label=\"Zero\"];", from.index());
                    print!("z{} -> {0}", from.index());
                },
                MigNode::Majority => {
                    print!("{} -> {}", from.index(), to.index());
                },
            }

            println!(" {};", if self.graph[edge] { "[dir=both,arrowtail=odot]" } else { "" });
        }

        println!("}}");
    }
}