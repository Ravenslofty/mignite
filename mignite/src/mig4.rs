use std::collections::HashMap;
use std::convert::TryFrom;
use std::io::Write;

use petgraph::{prelude::*, visit::EdgeRef};

#[derive(Debug, PartialEq)]
pub enum MigNode {
    Input(u32),
    Output(u32),
    Zero,
    Majority,
}

#[derive(Default)]
pub struct Mig {
    graph: StableGraph<MigNode, bool, Directed>,
    symbol_table: HashMap<u32, String>,
    zero: NodeIndex,
}

impl Mig {
    #[allow(clippy::similar_names)]
    #[must_use]
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

        let mut inputs = vec![];
        let mut outputs = vec![];

        for record in reader.records() {
            match record.unwrap() {
                aiger::Aiger::Input(l) => {
                    let index = u32::try_from(l.variable()).unwrap();
                    mig.graph[NodeIndex::new(l.variable())] = MigNode::Input(index);
                    inputs.push(index);
                },
                aiger::Aiger::Latch { output: _, input: _ } => {
                    todo!("latches")
                },
                aiger::Aiger::Output(l) => {
                    let index = u32::try_from(l.variable()).unwrap();
                    let output_node = mig.graph.add_node(MigNode::Output(index));
                    mig.graph.add_edge(NodeIndex::new(l.variable()), output_node, l.is_inverted());
                    outputs.push(index);
                },
                aiger::Aiger::AndGate { output, inputs } => {
                    let input0 = inputs[0];
                    let input1 = inputs[1];

                    let gate = NodeIndex::new(output.variable());

                    mig.graph.add_edge(NodeIndex::new(input0.variable()), gate, input0.is_inverted());
                    mig.graph.add_edge(NodeIndex::new(input1.variable()), gate, input1.is_inverted());
                    mig.graph.add_edge(mig.zero, gate, false);
                },
                aiger::Aiger::Symbol { type_spec, position, symbol } => {
                    let index = match type_spec {
                        aiger::Symbol::Input => inputs[position],
                        aiger::Symbol::Output => outputs[position],
                        aiger::Symbol::Latch => continue,
                    };

                    mig.symbol_table.insert(index, symbol);
                }
            }
        }

        mig
    }

    #[allow(clippy::missing_errors_doc)]
    pub fn to_graphviz(&self, path: &str) -> std::io::Result<()> {
        let mut f = std::fs::File::create(path)?;

        writeln!(f, "strict digraph {{")?;

        for node in self.graph.node_indices() {
            match self.graph[node] {
                MigNode::Input(index) => {
                    writeln!(f, "{} [shape=box,color=blue,label=\"Input {}\"];", node.index(), index)?;
                },
                MigNode::Output(index) => {
                    writeln!(f, "{} [shape=box,color=green,label=\"Output {}\"];", node.index(), index)?;
                },
                MigNode::Zero => {},
                MigNode::Majority => {
                    let (x_edge, y_edge, z_edge) = self.try_unwrap_majority(node).expect("majority node with less than three inputs");
                    let (x, _) = self.graph().edge_endpoints(x_edge).unwrap();
                    let (y, _) = self.graph().edge_endpoints(y_edge).unwrap();
                    let (z, _) = self.graph().edge_endpoints(z_edge).unwrap();
                    let x_is_inverted = *self.graph().edge_weight(x_edge).expect("edge from x to node has no weight");
                    let y_is_inverted = *self.graph().edge_weight(y_edge).expect("edge from y to node has no weight");
                    let z_is_inverted = *self.graph().edge_weight(z_edge).expect("edge from z to node has no weight");
                    if (x == self.zero && x_is_inverted) || (y == self.zero && y_is_inverted) || (z == self.zero && z_is_inverted) {
                        writeln!(f, "{} [label=\"OR {0}\"];", node.index())?;
                    } else if (x == self.zero && !x_is_inverted) || (y == self.zero && !y_is_inverted) || (z == self.zero && !z_is_inverted) {
                        writeln!(f, "{} [label=\"AND {0}\"];", node.index())?;
                    } else {
                        writeln!(f, "{} [label=\"Majority {0}\"];", node.index())?;
                    }
                },
            }
        }

        for edge in self.graph.edge_indices() {
            let (to, from) = self.graph.edge_endpoints(edge).unwrap();

            match self.graph[to] {
                MigNode::Input(_) | MigNode::Output(_) | MigNode::Majority => {
                    write!(f, "{} -> {}", to.index(), from.index())?;
                },
                MigNode::Zero => {
                    writeln!(f, "z{} [label=\"\", shape=point];", from.index())?;
                    write!(f, "z{} -> {0}", from.index())?;
                },
            }

            writeln!(f, " {};", if self.graph[edge] { "[dir=both,arrowtail=odot]" } else { "" })?;
        }

        writeln!(f, "}}")
    }

    #[must_use]
    pub fn graph(&self) -> &StableGraph<MigNode, bool> {
        &self.graph
    }

    pub fn graph_mut(&mut self) -> &mut StableGraph<MigNode, bool> {
        &mut self.graph
    }

    #[must_use]
    pub fn symbol(&self, index: u32) -> Option<&String> {
        self.symbol_table.get(&index)
    }

    #[must_use]
    pub fn try_unwrap_majority(&self, node: NodeIndex) -> Option<(EdgeIndex, EdgeIndex, EdgeIndex)> {
        match self.graph[node] {
            MigNode::Input(_) | MigNode::Output(_) | MigNode::Zero => None,
            MigNode::Majority => {
                let mut iter = self.graph.edges_directed(node, Incoming);
                match (iter.next(), iter.next(), iter.next()) {
                    (Some(x), Some(y), Some(z)) => {
                        assert_eq!(iter.next(), None, "majority gate with more than three inputs");
                        Some((x.id(), y.id(), z.id()))
                    },
                    (Some(x), Some(y), None) => panic!("majority gate {} has two inputs: {} and {}", node.index(), x.id().index(), y.id().index()),
                    (Some(x), None, None) => panic!("majority gate {} has one input: {}", node.index(), x.id().index()),
                    (None, None, None) => panic!("majority gate {} has zero inputs", node.index()),
                    (_, _, _) => unreachable!()
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Mig, MigNode};

    #[test]
    fn try_unwrap_majority() {
        let mut mig = Mig::default();

        let node_input0 = mig.graph.add_node(MigNode::Input(0));
        let node_input1 = mig.graph.add_node(MigNode::Input(1));
        let node_input2 = mig.graph.add_node(MigNode::Input(2));
        let node_majority = mig.graph.add_node(MigNode::Majority);

        let edge_input0 = mig.graph.add_edge(node_input0, node_majority, false);
        let edge_input1 = mig.graph.add_edge(node_input1, node_majority, false);
        let edge_input2 = mig.graph.add_edge(node_input2, node_majority, false);

        // This is the best way I've got for order-independent comparison of
        // tuples
        let edges = mig
            .try_unwrap_majority(node_majority)
            .expect("try_unwrap_majority should return Some(_) for a majority gate");
        let edges = [edges.0, edges.1, edges.2];

        assert!(edges.contains(&edge_input0));
        assert!(edges.contains(&edge_input1));
        assert!(edges.contains(&edge_input2));
    }

    #[test]
    fn try_unwrap_majority_not_a_majority() {
        let mut mig = Mig::default();

        let node_input = mig.graph.add_node(MigNode::Input(0));
        let node_output = mig.graph.add_node(MigNode::Output(1));
        let node_zero = mig.graph.add_node(MigNode::Zero);

        assert_eq!(mig.try_unwrap_majority(node_input), None);
        assert_eq!(mig.try_unwrap_majority(node_output), None);
        assert_eq!(mig.try_unwrap_majority(node_zero), None);
    }

}
