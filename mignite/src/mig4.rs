use petgraph::prelude::*;

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
        assert_eq!(mig.zero.index(), 0);

        // Pre-emptively mark every variable as a majority gate - most will be
        // but we'll replace those that aren't while we parse.
        for variable in 1..=reader.header().m {
            let node_index = mig.graph.add_node(MigNode::Majority);
            assert_eq!(node_index.index(), variable);
        }

        for record in reader.records() {
            match record.unwrap() {
                aiger::Aiger::Input(l) => {
                    mig.graph[NodeIndex::new(l.variable())] = MigNode::Input(l.variable() as u32);
                },
                aiger::Aiger::Latch { output: _, input: _ } => {
                    todo!("latches")
                },
                aiger::Aiger::Output(l) => {
                    let output_node = mig.graph.add_node(MigNode::Output(l.variable() as u32));
                    mig.graph.add_edge(NodeIndex::new(l.variable()), output_node, l.is_inverted());
                },
                aiger::Aiger::AndGate { output, inputs } => {
                    let input0 = inputs[0];
                    let input1 = inputs[1];

                    let gate = NodeIndex::new(output.variable());

                    let i0 = mig.graph.add_edge(NodeIndex::new(input0.variable()), gate, input0.is_inverted());
                    let i1 = mig.graph.add_edge(NodeIndex::new(input1.variable()), gate, input1.is_inverted());
                    let i2 = mig.graph.add_edge(mig.zero, gate, false);

                    eprintln!("{} = {}{} AND {}{}", output.variable(), input0.variable(), if input0.is_inverted() { "'" } else { "" }, input1.variable(), if input1.is_inverted() { "'" } else { "" });
                    eprintln!("{} {} {}", i0.index(), i1.index(), i2.index());
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
                    let (x, y, z) = self.try_unwrap_majority(node).expect("majority node with less than three inputs");
                    let x_edge = self.graph().find_edge(x, node).expect("no edge from x to node, but x is an input of node");
                    let y_edge = self.graph().find_edge(y, node).expect("no edge from y to node, but y is an input of node");
                    let z_edge = self.graph().find_edge(z, node).expect("no edge from z to node, but z is an input of node");
                    let x_is_inverted = *self.graph().edge_weight(x_edge).expect("edge from x to node has no weight");
                    let y_is_inverted = *self.graph().edge_weight(y_edge).expect("edge from y to node has no weight");
                    let z_is_inverted = *self.graph().edge_weight(z_edge).expect("edge from z to node has no weight");
                    if x == self.zero {
                        if x_is_inverted {
                            println!("{} [label=\"OR {0}\"];", node.index());
                        } else {
                            println!("{} [label=\"AND {0}\"];", node.index());
                        }
                    } else if y == self.zero {
                        if y_is_inverted {
                            println!("{} [label=\"OR {0}\"];", node.index());
                        } else {
                            println!("{} [label=\"AND {0}\"];", node.index());
                        }
                    } else if z == self.zero {
                        if z_is_inverted {
                            println!("{} [label=\"OR {0}\"];", node.index());
                        } else {
                            println!("{} [label=\"AND {0}\"];", node.index());
                        }
                    } else {
                        println!("{} [label=\"Majority {0}\"];", node.index());
                    }
                },
            }
        }

        for edge in self.graph.edge_indices() {
            let (to, from) = self.graph.edge_endpoints(edge).unwrap();

            match self.graph[to] {
                MigNode::Input(index) => {
                    print!("{} -> {}", to.index(), from.index());
                },
                MigNode::Output(index) => {
                    print!("{} -> {}", to.index(), from.index());
                },
                MigNode::Zero => {
                    println!("z{} [label=\"\", shape=point];", from.index());
                    print!("z{} -> {0}", from.index());
                },
                MigNode::Majority => {
                    print!("{} -> {}", to.index(), from.index());
                },
            }

            println!(" {};", if self.graph[edge] { "[dir=both,arrowtail=odot]" } else { "" });
        }

        println!("}}");
    }

    pub fn graph(&self) -> &StableGraph<MigNode, bool> {
        &self.graph
    }

    pub fn graph_mut(&mut self) -> &mut StableGraph<MigNode, bool> {
        &mut self.graph
    }

    pub fn try_unwrap_majority(&self, node: NodeIndex) -> Option<(NodeIndex, NodeIndex, NodeIndex)> {
        let mut iter = self.graph.neighbors_directed(node, Incoming);
        if let (Some(x), Some(y), Some(z)) = (iter.next(), iter.next(), iter.next()) {
            assert_eq!(iter.next(), None);
            return Some((x, y, z))
        }
        None
    }
}
