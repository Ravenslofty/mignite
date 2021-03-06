use std::collections::HashMap;
use std::convert::TryFrom;
use std::io::Write;

use petgraph::{prelude::*, visit::EdgeRef};

#[derive(Clone, Copy, Debug, PartialEq)]
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
                }
                aiger::Aiger::Latch {
                    output: _,
                    input: _,
                } => todo!("latches"),
                aiger::Aiger::Output(l) => {
                    let index = u32::try_from(l.variable()).unwrap();
                    let output_node = mig.graph.add_node(MigNode::Output(index));
                    mig.graph
                        .add_edge(NodeIndex::new(l.variable()), output_node, l.is_inverted());
                    outputs.push(index);
                }
                aiger::Aiger::AndGate { output, inputs } => {
                    let input0 = inputs[0];
                    let input1 = inputs[1];

                    let gate = NodeIndex::new(output.variable());

                    mig.graph.add_edge(
                        NodeIndex::new(input0.variable()),
                        gate,
                        input0.is_inverted(),
                    );
                    mig.graph.add_edge(
                        NodeIndex::new(input1.variable()),
                        gate,
                        input1.is_inverted(),
                    );
                    mig.graph.add_edge(mig.zero, gate, false);
                }
                aiger::Aiger::Symbol {
                    type_spec,
                    position,
                    symbol,
                } => {
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
                    writeln!(
                        f,
                        "{} [shape=box,color=blue,label=\"Input {}\"];",
                        node.index(),
                        index
                    )?;
                }
                MigNode::Output(index) => {
                    writeln!(
                        f,
                        "{} [shape=box,color=green,label=\"Output {}\"];",
                        node.index(),
                        index
                    )?;
                }
                MigNode::Zero => {}
                MigNode::Majority => {
                    let (x_edge, y_edge, z_edge) = self
                        .try_unwrap_majority(node)
                        .expect("majority node with less than three inputs");
                    let (x, _) = self.graph().edge_endpoints(x_edge).unwrap();
                    let (y, _) = self.graph().edge_endpoints(y_edge).unwrap();
                    let (z, _) = self.graph().edge_endpoints(z_edge).unwrap();
                    let x_is_inverted = *self
                        .graph()
                        .edge_weight(x_edge)
                        .expect("edge from x to node has no weight");
                    let y_is_inverted = *self
                        .graph()
                        .edge_weight(y_edge)
                        .expect("edge from y to node has no weight");
                    let z_is_inverted = *self
                        .graph()
                        .edge_weight(z_edge)
                        .expect("edge from z to node has no weight");
                    if (x == self.zero && x_is_inverted)
                        || (y == self.zero && y_is_inverted)
                        || (z == self.zero && z_is_inverted)
                    {
                        writeln!(f, "{} [label=\"OR {0}\"];", node.index())?;
                    } else if (x == self.zero && !x_is_inverted)
                        || (y == self.zero && !y_is_inverted)
                        || (z == self.zero && !z_is_inverted)
                    {
                        writeln!(f, "{} [label=\"AND {0}\"];", node.index())?;
                    } else {
                        writeln!(f, "{} [label=\"Majority {0}\"];", node.index())?;
                    }
                }
            }
        }

        for edge in self.graph.edge_indices() {
            let (to, from) = self.graph.edge_endpoints(edge).unwrap();

            match self.graph[to] {
                MigNode::Input(_) | MigNode::Output(_) | MigNode::Majority => {
                    write!(f, "{} -> {}", to.index(), from.index())?;
                }
                MigNode::Zero => {
                    writeln!(f, "z{} [label=\"\", shape=point];", from.index())?;
                    write!(f, "z{} -> {0}", from.index())?;
                }
            }

            writeln!(
                f,
                " {};",
                if self.graph[edge] {
                    "[dir=both,arrowtail=odot]"
                } else {
                    ""
                }
            )?;
        }

        writeln!(f, "}}")
    }

    pub(crate) const fn graph(&self) -> &StableGraph<MigNode, bool> {
        &self.graph
    }

    pub(crate) fn graph_mut(&mut self) -> &mut StableGraph<MigNode, bool> {
        &mut self.graph
    }

    #[must_use]
    pub fn is_edge_inverted(&self, edge: EdgeIndex) -> bool {
        self.graph[edge]
    }

    #[must_use]
    pub fn edge_source(&self, edge: EdgeIndex) -> NodeIndex {
        self.graph.edge_endpoints(edge).unwrap().0
    }

    pub fn add_edge(&mut self, source: NodeIndex, target: NodeIndex, inverted: bool) -> EdgeIndex {
        self.graph.add_edge(source, target, inverted)
    }

    pub fn remove_edge(&mut self, edge: EdgeIndex) -> bool {
        self.graph.remove_edge(edge).unwrap_or_else(|| panic!("tried to remove edge {} twice", edge.index()))
    }

    #[must_use]
    pub fn node_type(&self, node: NodeIndex) -> MigNode {
        self.graph[node]
    }

    pub fn add_node(&mut self, kind: MigNode) -> NodeIndex {
        self.graph.add_node(kind)
    }

    pub fn remove_node(&mut self, node: NodeIndex) -> MigNode {
        self.graph.remove_node(node).unwrap()
    }

    #[must_use]
    pub fn input_nodes(&self) -> Vec<NodeIndex> {
        self.graph().externals(Incoming).collect::<Vec<_>>()
    }

    #[must_use]
    pub fn output_edges(&self, node: NodeIndex) -> petgraph::stable_graph::Neighbors<bool, u32> {
        self.graph.neighbors_directed(node, Outgoing)
    }

    #[must_use]
    pub fn node_count(&self) -> usize {
        self.graph.node_count()
    }

    #[must_use]
    pub fn edge_count(&self) -> usize {
        self.graph.edge_count()
    }

    #[must_use]
    pub fn symbol(&self, index: u32) -> Option<&String> {
        self.symbol_table.get(&index)
    }

    #[must_use]
    pub fn try_unwrap_majority(
        &self,
        node: NodeIndex,
    ) -> Option<(EdgeIndex, EdgeIndex, EdgeIndex)> {
        match self.graph[node] {
            MigNode::Input(_) | MigNode::Output(_) | MigNode::Zero => None,
            MigNode::Majority => {
                let mut iter = self.graph.edges_directed(node, Incoming);
                match (iter.next(), iter.next(), iter.next()) {
                    (Some(x), Some(y), Some(z)) => {
                        if let Some(w) = iter.next() {
                            dbg!(w);
                            panic!("majority gate {} has {} inputs", node.index(), iter.count()+4);
                        }
                        Some((x.id(), y.id(), z.id()))
                    }
                    (Some(x), Some(y), None) => panic!(
                        "majority gate {} has two inputs: {} and {}",
                        node.index(),
                        x.id().index(),
                        y.id().index()
                    ),
                    (Some(x), None, None) => panic!(
                        "majority gate {} has one input: {}",
                        node.index(),
                        x.id().index()
                    ),
                    (None, None, None) => panic!("majority gate {} has zero inputs", node.index()),
                    (_, _, _) => unreachable!(),
                }
            }
        }
    }

    #[must_use]
    pub fn try_unwrap_and(&self, node: NodeIndex) -> Option<(EdgeIndex, EdgeIndex)> {
        let (x_edge, y_edge, z_edge) = self.try_unwrap_majority(node)?;
        let x = self.edge_source(x_edge);
        let y = self.edge_source(y_edge);
        let z = self.edge_source(z_edge);
        let x_is_inverted = self.is_edge_inverted(x_edge);
        let y_is_inverted = self.is_edge_inverted(y_edge);
        let z_is_inverted = self.is_edge_inverted(z_edge);

        if x == self.zero && !x_is_inverted {
            Some((y_edge, z_edge))
        } else if y == self.zero && !y_is_inverted {
            Some((x_edge, z_edge))
        } else if z == self.zero && !z_is_inverted {
            Some((x_edge, y_edge))
        } else {
            None
        }
    }

    #[must_use]
    pub fn try_unwrap_or(&self, node: NodeIndex) -> Option<(EdgeIndex, EdgeIndex)> {
        let (x_edge, y_edge, z_edge) = self.try_unwrap_majority(node)?;
        let x = self.edge_source(x_edge);
        let y = self.edge_source(y_edge);
        let z = self.edge_source(z_edge);
        let x_is_inverted = self.is_edge_inverted(x_edge);
        let y_is_inverted = self.is_edge_inverted(y_edge);
        let z_is_inverted = self.is_edge_inverted(z_edge);

        if x == self.zero && x_is_inverted {
            Some((y_edge, z_edge))
        } else if y == self.zero && y_is_inverted {
            Some((x_edge, z_edge))
        } else if z == self.zero && z_is_inverted {
            Some((x_edge, y_edge))
        } else {
            None
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
