use crate::mig4;

use petgraph::prelude::*;

impl mig4::Mig {
    pub fn transform_majority(&mut self, node: NodeIndex) -> Option<()> {
        let (x, y, z) = self.try_unwrap_majority(node)?;
        let x_edge = self.graph().find_edge(x, node).expect("no edge from x to node, but x is an input of node");
        let y_edge = self.graph().find_edge(y, node).expect("no edge from y to node, but y is an input of node");
        let x_is_inverted = self.graph().edge_weight(x_edge).expect("edge from x to node has no weight");
        let y_is_inverted = self.graph().edge_weight(y_edge).expect("edge from y to node has no weight");

        if x == y {
            if x_is_inverted == y_is_inverted {
                // M(x, x, y) => x
                let mut outputs = self.graph().neighbors_directed(node, Outgoing).detach();
                while let Some((edge, output)) = outputs.next(self.graph()) {
                    let inverted = self.graph_mut().remove_edge(edge).unwrap();
                    self.graph_mut().add_edge(x, output, inverted);
                }
                self.graph_mut().remove_node(node);
                return Some(());
            } else {
                // M(x, x', y) => y
            }
        }

        None
    }

    pub fn optimise_area(&mut self) {
        // Find graph inputs.
        let inputs = self.graph().externals(Incoming).collect::<Vec<_>>();

        // Explore tree.
        let mut dfs = DfsPostOrder::empty(self.graph());
        for input in inputs {
            dfs.move_to(input);
            while let Some(node) = dfs.next(self.graph()) {
                self.transform_majority(node);
            }
        }
    }
}