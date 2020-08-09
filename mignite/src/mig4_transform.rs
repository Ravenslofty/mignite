use crate::mig4;

use petgraph::prelude::*;
use mig4::MigNode;

impl mig4::Mig {
    fn substitute(&mut self, node: NodeIndex, from: NodeIndex, to: NodeIndex, invert: bool) -> Option<()> {
        let mut dfs = DfsPostOrder::new(self.graph(), node);
        let mut did_something = false;
        while let Some(node) = dfs.next(self.graph()) {
            if let Some((x, y, z)) = self.try_unwrap_majority(node) {
                if x == from {
                    let edge = self.graph().find_edge(x, node).unwrap();
                    let inverted = self.graph_mut().remove_edge(edge).unwrap();
                    self.graph_mut().add_edge(to, node, if invert { !inverted } else { inverted });
                    did_something = true;
                }

                if y == from {
                    let edge = self.graph().find_edge(y, node).unwrap();
                    let inverted = self.graph_mut().remove_edge(edge).unwrap();
                    self.graph_mut().add_edge(to, node, if invert { !inverted } else { inverted });
                    did_something = true;
                }

                if z == from {
                    let edge = self.graph().find_edge(z, node).unwrap();
                    let inverted = self.graph_mut().remove_edge(edge).unwrap();
                    self.graph_mut().add_edge(to, node, if invert { !inverted } else { inverted });
                    did_something = true;
                }
            }
        }

        if did_something { Some(()) } else { None }
    }

    fn transform_inverters(&mut self, node: NodeIndex) -> Option<()> {
        let (x, y, z) = self.try_unwrap_majority(node)?;
        let x_edge = self.graph().find_edge(x, node).expect("no edge from x to node, but x is an input of node");
        let y_edge = self.graph().find_edge(y, node).expect("no edge from y to node, but y is an input of node");
        let z_edge = self.graph().find_edge(z, node).expect("no edge from z to node, but z is an input of node");
        let x_is_inverted = *self.graph().edge_weight(x_edge).expect("edge from x to node has no weight");
        let y_is_inverted = *self.graph().edge_weight(y_edge).expect("edge from y to node has no weight");
        let z_is_inverted = *self.graph().edge_weight(z_edge).expect("edge from z to node has no weight");

        let mut inverter_propagation = |x: NodeIndex, y: NodeIndex, z: NodeIndex, x_is_inverted: bool, y_is_inverted: bool| {
            if x_is_inverted && y_is_inverted {
                let mut inputs = self.graph().neighbors_directed(node, Incoming).detach();
                while let Some(edge) = inputs.next_edge(self.graph()) {
                    let inverted = self.graph_mut().edge_weight_mut(edge).unwrap();
                    *inverted = !*inverted;
                }

                let mut outputs = self.graph().neighbors_directed(node, Outgoing).detach();
                while let Some(edge) = outputs.next_edge(self.graph()) {
                    let inverted = self.graph_mut().edge_weight_mut(edge).unwrap();
                    *inverted = !*inverted;
                }

                eprintln!("{}: M({}', {}', {}') => M({1}, {2}, {3})' (Ω.I)", node.index(), x.index(), y.index(), z.index());

                return Some(())
            }
            None
        };

        inverter_propagation(x, y, z, x_is_inverted, y_is_inverted)
        .or_else(|| inverter_propagation(y, z, x, y_is_inverted, z_is_inverted))
        .or_else(|| inverter_propagation(z, x, y, z_is_inverted, x_is_inverted))
    }

    fn transform_majority(&mut self, node: NodeIndex) -> Option<()> {
        let mut majority = |mig: &mut Self, x: NodeIndex, y: NodeIndex, z: NodeIndex, x_is_inverted: bool, y_is_inverted: bool| {
            if x == y {
                if !x_is_inverted && !y_is_inverted {
                    // M(x, x, y) => x
                    let mut outputs = mig.graph().neighbors_directed(node, Outgoing).detach();
                    while let Some((edge, output)) = outputs.next(mig.graph()) {
                        let inverted = mig.graph_mut().remove_edge(edge).unwrap();
                        mig.graph_mut().add_edge(x, output, inverted);
                    }
                    mig.graph_mut().remove_node(node);
                    eprintln!("{}: M({}, {}, {}) => {1} (Ω.M)", node.index(), x.index(), y.index(), z.index());
                    return Some(());
                } else { /*
                    // M(x, x', y) => y
                    let mut outputs = self.graph().neighbors_directed(node, Outgoing).detach();
                    while let Some((edge, output)) = outputs.next(self.graph()) {
                        let inverted = self.graph_mut().remove_edge(edge).unwrap();
                        self.graph_mut().add_edge(z, output, inverted);
                    }
                    self.graph_mut().remove_node(node);
                    eprintln!("{}: M({}, {}, {}) => {1} (Ω.M)", node.index(), x.index(), y.index(), z.index());
                    return Some(());*/
                }
            }
            None
        };

        let (x, y, z) = self.try_unwrap_majority(node)?;
        let x_edge = self.graph().find_edge(x, node).expect("no edge from x to node, but x is an input of node");
        let y_edge = self.graph().find_edge(y, node).expect("no edge from y to node, but y is an input of node");
        let z_edge = self.graph().find_edge(z, node).expect("no edge from z to node, but z is an input of node");
        let x_is_inverted = *self.graph().edge_weight(x_edge).expect("edge from x to node has no weight");
        let y_is_inverted = *self.graph().edge_weight(y_edge).expect("edge from y to node has no weight");
        let z_is_inverted = *self.graph().edge_weight(z_edge).expect("edge from z to node has no weight");

        if node == NodeIndex::new(31) {
            dbg!(x_edge);
            dbg!(y_edge);
            dbg!(z_edge);
            dbg!(x_is_inverted);
            dbg!(y_is_inverted);
            dbg!(z_is_inverted);
        }

        majority(self, x, y, z, x_is_inverted, y_is_inverted)
        //.or_else(|| majority(y, z, x, y_is_inverted, z_is_inverted))
        //.or_else(|| majority(z, x, y, z_is_inverted, x_is_inverted))
    }

    /// Transform `M(x, y, M(u, v, z))` into `M(M(x, y, u), M(x, y, v), z)`.
    /*#[allow(clippy::many_single_char_names)]
    pub fn transform_distributivity(&mut self, node: NodeIndex) -> Option<()> {
        let (x, y, z) = self.try_unwrap_majority(node)?;
        let mut distributivity = |x: NodeIndex, y: NodeIndex, b: NodeIndex| {
            //    a
            //  / | \
            // x  y  b
            //     / | \
            //    u  v  z
            let (u, v, z) = self.try_unwrap_majority(b)?;

            let x_to_node = self.graph().find_edge(x, node).unwrap();
            let y_to_node = self.graph().find_edge(y, node).unwrap();
            let b_to_node = self.graph().find_edge(b, node).unwrap();

            let x_to_node_inverted = *self.graph().edge_weight(x_to_node).unwrap();
            let y_to_node_inverted = *self.graph().edge_weight(y_to_node).unwrap();
            let b_to_node_inverted = *self.graph().edge_weight(b_to_node).unwrap();

            if y_to_node_inverted || b_to_node_inverted {
                return None;
            }

            let c = self.graph_mut().add_node(MigNode::Majority);
            self.graph_mut().add_edge(x, c, false);
            self.graph_mut().update_edge(y, c, false);
            self.graph_mut().update_edge(u, c, false);

            let d = self.graph_mut().add_node(MigNode::Majority);
            self.graph_mut().update_edge(x, d, false);
            self.graph_mut().update_edge(y, d, false);
            self.graph_mut().update_edge(v, d, false);

            self.graph_mut().remove_edge(x_to_node).unwrap();
            self.graph_mut().remove_edge(y_to_node).unwrap();
            self.graph_mut().remove_edge(b_to_node).unwrap();

            self.graph_mut().update_edge(node, c, x_to_node_inverted);
            self.graph_mut().update_edge(node, d, y_to_node_inverted);
            self.graph_mut().update_edge(node, z, b_to_node_inverted);

            eprintln!("{}: M({}, {}, M({}, {}, {})) => (distributivity)", node.index(), x.index(), y.index(), u.index(), v.index(), z.index());

            Some(())
        };

        distributivity(x, y, z)
        .or_else(|| distributivity(y, z, x))
        .or_else(|| distributivity(z, x, y))
    }*/

    fn transform_relevance(&mut self, node: NodeIndex) -> Option<()> {
        let (x, y, z) = self.try_unwrap_majority(node)?;
        let mut relevance = |x, y, z| {

            let node_to_y = self.graph().find_edge(node, y).unwrap();
            let y_is_inverted = *self.graph().edge_weight(node_to_y).unwrap();

            let mut dfs = DfsPostOrder::new(self.graph(), z);
            let mut did_something = false;

            while let Some(node) = dfs.next(self.graph()) {
                if let Some((x2, y2, z2)) = self.try_unwrap_majority(node) { 
                    if x2 == x {
                        let edge = self.graph().find_edge(x2, node).unwrap();
                        self.graph_mut().remove_edge(edge).unwrap();
                        self.graph_mut().add_edge(y, node, !y_is_inverted);
                        eprintln!("{}: replacing {} with {} (relevance)", node.index(), x2.index(), y.index());
                        did_something = true;
                    }
                    
                    if y2 == x {
                        let edge = self.graph().find_edge(y2, node).unwrap();
                        self.graph_mut().remove_edge(edge).unwrap();
                        self.graph_mut().add_edge(y, node, !y_is_inverted);
                        eprintln!("{}: replacing {} with {} (relevance)", node.index(), y2.index(), y.index());
                        did_something = true;
                    }

                    if z2 == x {
                        let edge = self.graph().find_edge(z2, node).unwrap();
                        self.graph_mut().remove_edge(edge).unwrap();
                        self.graph_mut().add_edge(y, node, !y_is_inverted);
                        eprintln!("{}: replacing {} with {} (relevance)", node.index(), z2.index(), y.index());
                        did_something = true;
                    }
                }
            }

            if did_something { Some(()) } else { None }
        };

        relevance(x, y, z);
        relevance(y, z, x);
        relevance(z, x, y)
    }

    pub fn cleanup_graph(&mut self) {
        let mut did_something = true;
        while did_something {
            did_something = false;

            let indices = self.graph().node_indices().collect::<Vec<_>>();
            let inputs = self.graph().externals(Incoming).collect::<Vec<_>>();

            for node in indices.into_iter().filter(|node| !inputs.contains(node)) {
                if self.graph().neighbors_directed(node, Incoming).count() == 0 {
                    self.graph_mut().remove_node(node);
                    did_something = true;
                }
            }
        }
    }

    pub fn optimise_area(&mut self) {
        // Clean up graph orphans.
        //self.cleanup_graph();

        // Find graph inputs.
        let inputs = self.graph().externals(Incoming).collect::<Vec<_>>();

        // Explore tree.

        //self.transform_relevance(input);
    
        for n in 0..1 {
            eprintln!("{}:", n);
            let mut dfs = DfsPostOrder::empty(self.graph());
            for input in inputs.clone() {
                dfs.move_to(input);
                while let Some(node) = dfs.next(self.graph()) {
                    //self.transform_inverters(node);
                }
            }

            let mut dfs = DfsPostOrder::empty(self.graph());
            for input in inputs.clone() {
                dfs.move_to(input);
                while let Some(node) = dfs.next(self.graph()) {
                    self.transform_majority(node);
                }
            }

            self.cleanup_graph();
        }

    }
}