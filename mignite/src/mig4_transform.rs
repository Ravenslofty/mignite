use crate::mig4;

use petgraph::prelude::*;
use mig4::MigNode;

impl mig4::Mig {
    fn transform_inverters(&mut self, node: NodeIndex) -> Option<()> {
        let (x_edge, y_edge, z_edge) = self.try_unwrap_majority(node)?;
        let (x, _) = self.graph().edge_endpoints(x_edge).unwrap();
        let (y, _) = self.graph().edge_endpoints(y_edge).unwrap();
        let (z, _) = self.graph().edge_endpoints(z_edge).unwrap();
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
        let mut majority = |mig: &mut Self, x_edge: EdgeIndex, y_edge: EdgeIndex, z_edge: EdgeIndex, x: NodeIndex, y: NodeIndex, z: NodeIndex, x_is_inverted: bool, y_is_inverted: bool, z_is_inverted: bool| {
            if x == y {
                if x_is_inverted == y_is_inverted {
                    // M(x, x, y) => x
                    let mut outputs = mig.graph().neighbors_directed(node, Outgoing).detach();
                    while let Some((edge, output)) = outputs.next(mig.graph()) {
                        let inverted = mig.graph_mut().remove_edge(edge).unwrap();
                        mig.graph_mut().add_edge(x, output, x_is_inverted ^ inverted);
                    }
                    mig.graph_mut().remove_node(node);
                    eprintln!("{}: M({}, {}, {}) => {1} (Ω.M)", node.index(), x.index(), y.index(), z.index());
                    return Some(());
                } else {
                    // M(x, x', y) => y
                    let mut outputs = mig.graph().neighbors_directed(node, Outgoing).detach();
                    while let Some((edge, output)) = outputs.next(mig.graph()) {
                        let inverted = mig.graph_mut().remove_edge(edge).unwrap();
                        mig.graph_mut().add_edge(z, output,  z_is_inverted ^ inverted);
                    }
                    mig.graph_mut().remove_node(node);
                    eprintln!("{}: M({}, {}', {}) => {3} (Ω.M')", node.index(), x.index(), y.index(), z.index());
                    return Some(());
                }
            }
            None
        };

        let (x_edge, y_edge, z_edge) = self.try_unwrap_majority(node)?;
        let (x, _) = self.graph().edge_endpoints(x_edge).unwrap();
        let (y, _) = self.graph().edge_endpoints(y_edge).unwrap();
        let (z, _) = self.graph().edge_endpoints(z_edge).unwrap();
        let x_is_inverted = *self.graph().edge_weight(x_edge).expect("edge from x to node has no weight");
        let y_is_inverted = *self.graph().edge_weight(y_edge).expect("edge from y to node has no weight");
        let z_is_inverted = *self.graph().edge_weight(z_edge).expect("edge from z to node has no weight");

        majority(self, x_edge, y_edge, z_edge, x, y, z, x_is_inverted, y_is_inverted, z_is_inverted)
        .or_else(|| majority(self, y_edge, z_edge, x_edge, y, z, x, y_is_inverted, z_is_inverted, x_is_inverted))
        .or_else(|| majority(self, z_edge, x_edge, y_edge, z, x, y, z_is_inverted, x_is_inverted, y_is_inverted))
    }

    /// Transform `M(M(x, y, u), M(x, y, v), z)` into `M(x, y, M(u, v, z))`.
    #[allow(clippy::many_single_char_names)]
    pub fn transform_distributivity(&mut self, node: NodeIndex) -> Option<()> {
        let (x_edge, y_edge, z_edge) = self.try_unwrap_majority(node)?;
        let (x, _) = self.graph().edge_endpoints(x_edge).unwrap();
        let (y, _) = self.graph().edge_endpoints(y_edge).unwrap();
        let (z, _) = self.graph().edge_endpoints(z_edge).unwrap();

        let mut distributivity = |b_edge: EdgeIndex, c_edge: EdgeIndex, z_edge: EdgeIndex, b: NodeIndex, c: NodeIndex, z: NodeIndex| {
            //        node
            //    /    |    \
            //   b     c     z
            // / | \ / | \
            // x y u x y v

            let b_is_inverted = self.graph()[b_edge];
            let c_is_inverted = self.graph()[c_edge];
            let z_is_inverted = self.graph()[z_edge];

            let (x1_edge, y1_edge, u_edge) = self.try_unwrap_majority(b)?;
            let (x2_edge, y2_edge, v_edge) = self.try_unwrap_majority(c)?;

            let (x1, _) = self.graph().edge_endpoints(x1_edge).unwrap();
            let (y1, _) = self.graph().edge_endpoints(y1_edge).unwrap();
            let (u, _) = self.graph().edge_endpoints(u_edge).unwrap();

            let x1_is_inverted = self.graph()[x1_edge];
            let y1_is_inverted = self.graph()[y1_edge];
            let u_is_inverted = self.graph()[u_edge];

            let (x2, _) = self.graph().edge_endpoints(x2_edge).unwrap();
            let (y2, _) = self.graph().edge_endpoints(y2_edge).unwrap();
            let (v, _) = self.graph().edge_endpoints(v_edge).unwrap();

            let x2_is_inverted = self.graph()[x2_edge];
            let y2_is_inverted = self.graph()[y2_edge];
            let v_is_inverted = self.graph()[v_edge];

            if x1 != x2 || y1 != y2 || (x1_is_inverted ^ b_is_inverted) != (x2_is_inverted ^ c_is_inverted) || (y1_is_inverted ^ b_is_inverted) != (y2_is_inverted ^ c_is_inverted) {
                return None;
            }

            let d = self.graph_mut().add_node(MigNode::Majority);

            self.graph_mut().add_edge(u, d, u_is_inverted ^ b_is_inverted);
            self.graph_mut().add_edge(v, d, v_is_inverted ^ c_is_inverted);
            self.graph_mut().add_edge(z, d, z_is_inverted);

            self.graph_mut().remove_edge(b_edge);
            self.graph_mut().remove_edge(c_edge);
            self.graph_mut().remove_edge(z_edge);

            self.graph_mut().add_edge(x1, node, x1_is_inverted ^ b_is_inverted);
            self.graph_mut().add_edge(y1, node, y1_is_inverted ^ b_is_inverted);
            self.graph_mut().add_edge(d, node, false);

            eprintln!("{}: M(M({}, {}, {}), M({}, {}, {}), {}) => M({1}, {2}, M({3}, {6}, {7})) (Ω.D)", node.index(), x1.index(), y1.index(), u.index(), x2.index(), y2.index(), v.index(), z.index());

            Some(())
        };

        distributivity(x_edge, y_edge, z_edge, x, y, z)
        .or_else(|| distributivity(y_edge, z_edge, x_edge, y, z, x))
        .or_else(|| distributivity(z_edge, x_edge, y_edge, z, x, y))
    }

    fn transform_relevance(&mut self, node: NodeIndex) -> Option<()> {
        let (x_edge, y_edge, z_edge) = self.try_unwrap_majority(node)?;
        let (x, _) = self.graph().edge_endpoints(x_edge).unwrap();
        let (y, _) = self.graph().edge_endpoints(y_edge).unwrap();
        let (z, _) = self.graph().edge_endpoints(z_edge).unwrap();

        let mut relevance = |x_edge: EdgeIndex, y_edge: EdgeIndex, z_edge: EdgeIndex, x: NodeIndex, y: NodeIndex, z: NodeIndex| {

            let y_is_inverted = *self.graph().edge_weight(y_edge).unwrap();

            let mut dfs = DfsPostOrder::new(self.graph(), z);
            let mut did_something = false;

            while let Some(node) = dfs.next(self.graph()) {
                if let Some((x2_edge, y2_edge, z2_edge)) = self.try_unwrap_majority(node) {

                    let (x2, _) = self.graph().edge_endpoints(x2_edge).unwrap();
                    let (y2, _) = self.graph().edge_endpoints(y2_edge).unwrap();
                    let (z2, _) = self.graph().edge_endpoints(z2_edge).unwrap();

                    if x2 == x {
                        self.graph_mut().remove_edge(x2_edge).unwrap();
                        self.graph_mut().add_edge(y, node, !y_is_inverted);
                        eprintln!("{}: replacing {} with {} (Ω.R)", node.index(), x2.index(), y.index());
                        did_something = true;
                    }
                    
                    if y2 == x {
                        self.graph_mut().remove_edge(y2_edge).unwrap();
                        self.graph_mut().add_edge(y, node, !y_is_inverted);
                        eprintln!("{}: replacing {} with {} (Ω.R)", node.index(), y2.index(), y.index());
                        did_something = true;
                    }

                    if z2 == x {
                        self.graph_mut().remove_edge(z2_edge).unwrap();
                        self.graph_mut().add_edge(y, node, !y_is_inverted);
                        eprintln!("{}: replacing {} with {} (Ω.R)", node.index(), z2.index(), y.index());
                        did_something = true;
                    }
                }
            }

            if did_something { Some(()) } else { None }
        };

        relevance(x_edge, y_edge, z_edge, x, y, z);
        relevance(y_edge, z_edge, x_edge, y, z, x);
        relevance(z_edge, x_edge, y_edge, z, x, y)
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
            eprintln!("GC: there are {} nodes and {} edges in the graph", self.graph().node_count(), self.graph().edge_count());
        }
    }

    pub fn optimise_area(&mut self) {
        // Clean up graph orphans.
        self.cleanup_graph();

        // Find graph inputs.
        let inputs = self.graph().externals(Incoming).collect::<Vec<_>>();

        // Explore tree.   
        for n in 0..10 {
            eprintln!("{}:", n);
            let mut dfs = DfsPostOrder::empty(self.graph());
            for input in inputs.clone() {
                dfs.move_to(input);
                while let Some(node) = dfs.next(self.graph()) {
                    self.transform_inverters(node);
                }
            }

            let mut dfs = Dfs::empty(self.graph());
            for input in inputs.clone() {
                dfs.move_to(input);
                while let Some(node) = dfs.next(self.graph()) {
                    self.transform_majority(node);
                }
            }

            let mut dfs = Dfs::empty(self.graph());
            for input in inputs.clone() {
                dfs.move_to(input);
                while let Some(node) = dfs.next(self.graph()) {
                    self.transform_distributivity(node);
                }
            }

            for input in inputs.clone() {
                self.transform_relevance(input);
            }

            let mut dfs = Dfs::empty(self.graph());
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

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! assert_edge {
        ($graph:expr, $a:expr, $b:expr, $weight:expr) => {
            let edge = $graph
                .find_edge($a, $b)
                .expect(&format!("edge between {:?} and {:?} to exist", $a, $b));
            assert_eq!(
                $graph[edge], $weight,
                "edge between {:?} and {:?} has weight {:?}, expected {:?}",
                $a, $b, $graph[edge], $weight,
            );
        };
    }

    #[test]
    fn transform_majority_same() {
        let mut mig = mig4::Mig::default();

        let node_input0 = mig.graph_mut().add_node(MigNode::Input(0));
        let node_input1 = mig.graph_mut().add_node(MigNode::Input(1));
        let node_output = mig.graph_mut().add_node(MigNode::Output(2));
        let node_majority = mig.graph_mut().add_node(MigNode::Majority);

        mig.graph_mut().add_edge(node_input0, node_majority, false);
        mig.graph_mut().add_edge(node_input0, node_majority, false);
        mig.graph_mut().add_edge(node_input1, node_majority, false);
        mig.graph_mut().add_edge(node_majority, node_output, false);

        mig.transform_majority(node_majority)
            .expect("transformation to succeed");

        assert_edge!(mig.graph(), node_input0, node_output, false);
    }

    #[test]
    fn transform_majority_same_input_inverter() {
        let mut mig = mig4::Mig::default();

        let node_input0 = mig.graph_mut().add_node(MigNode::Input(0));
        let node_input1 = mig.graph_mut().add_node(MigNode::Input(1));
        let node_output = mig.graph_mut().add_node(MigNode::Output(2));
        let node_majority = mig.graph_mut().add_node(MigNode::Majority);

        mig.graph_mut().add_edge(node_input0, node_majority, true);
        mig.graph_mut().add_edge(node_input0, node_majority, true);
        mig.graph_mut().add_edge(node_input1, node_majority, false);
        mig.graph_mut().add_edge(node_majority, node_output, false);

        mig.transform_majority(node_majority)
            .expect("transformation to succeed");

        assert_edge!(mig.graph(), node_input0, node_output, true);
    }

    #[test]
    fn transform_majority_same_output_inverter() {
        let mut mig = mig4::Mig::default();

        let node_input0 = mig.graph_mut().add_node(MigNode::Input(0));
        let node_input1 = mig.graph_mut().add_node(MigNode::Input(1));
        let node_output = mig.graph_mut().add_node(MigNode::Output(2));
        let node_majority = mig.graph_mut().add_node(MigNode::Majority);

        mig.graph_mut().add_edge(node_input0, node_majority, false);
        mig.graph_mut().add_edge(node_input0, node_majority, false);
        mig.graph_mut().add_edge(node_input1, node_majority, false);
        mig.graph_mut().add_edge(node_majority, node_output, true);

        mig.transform_majority(node_majority)
            .expect("transformation to succeed");

        assert_edge!(mig.graph(), node_input0, node_output, true);
    }

    #[test]
    fn transform_majority_same_input_and_output_inverter() {
        let mut mig = mig4::Mig::default();

        let node_input0 = mig.graph_mut().add_node(MigNode::Input(0));
        let node_input1 = mig.graph_mut().add_node(MigNode::Input(1));
        let node_output = mig.graph_mut().add_node(MigNode::Output(2));
        let node_majority = mig.graph_mut().add_node(MigNode::Majority);

        mig.graph_mut().add_edge(node_input0, node_majority, true);
        mig.graph_mut().add_edge(node_input0, node_majority, true);
        mig.graph_mut().add_edge(node_input1, node_majority, false);
        mig.graph_mut().add_edge(node_majority, node_output, true);

        mig.transform_majority(node_majority)
            .expect("transformation to succeed");

        assert_edge!(mig.graph(), node_input0, node_output, false);
    }

    #[test]
    fn transform_majority_different() {
        let mut mig = mig4::Mig::default();

        let node_input0 = mig.graph_mut().add_node(MigNode::Input(0));
        let node_input1 = mig.graph_mut().add_node(MigNode::Input(1));
        let node_output = mig.graph_mut().add_node(MigNode::Output(2));
        let node_majority = mig.graph_mut().add_node(MigNode::Majority);

        mig.graph_mut().add_edge(node_input0, node_majority, false);
        mig.graph_mut().add_edge(node_input0, node_majority, true);
        mig.graph_mut().add_edge(node_input1, node_majority, false);
        mig.graph_mut().add_edge(node_majority, node_output, false);

        mig.transform_majority(node_majority)
            .expect("transformation to succeed");

        assert_edge!(mig.graph(), node_input1, node_output, false);
    }

    #[test]
    fn transform_majority_different_input_inverter() {
        let mut mig = mig4::Mig::default();

        let node_input0 = mig.graph_mut().add_node(MigNode::Input(0));
        let node_input1 = mig.graph_mut().add_node(MigNode::Input(1));
        let node_output = mig.graph_mut().add_node(MigNode::Output(2));
        let node_majority = mig.graph_mut().add_node(MigNode::Majority);

        mig.graph_mut().add_edge(node_input0, node_majority, false);
        mig.graph_mut().add_edge(node_input0, node_majority, true);
        mig.graph_mut().add_edge(node_input1, node_majority, true);
        mig.graph_mut().add_edge(node_majority, node_output, false);

        mig.transform_majority(node_majority)
            .expect("transformation to succeed");

        assert_edge!(mig.graph(), node_input1, node_output, true);
    }

    #[test]
    fn transform_majority_different_output_inverter() {
        let mut mig = mig4::Mig::default();

        let node_input0 = mig.graph_mut().add_node(MigNode::Input(0));
        let node_input1 = mig.graph_mut().add_node(MigNode::Input(1));
        let node_output = mig.graph_mut().add_node(MigNode::Output(2));
        let node_majority = mig.graph_mut().add_node(MigNode::Majority);

        mig.graph_mut().add_edge(node_input0, node_majority, false);
        mig.graph_mut().add_edge(node_input0, node_majority, true);
        mig.graph_mut().add_edge(node_input1, node_majority, false);
        mig.graph_mut().add_edge(node_majority, node_output, true);

        mig.transform_majority(node_majority)
            .expect("transformation to succeed");

        assert_edge!(mig.graph(), node_input1, node_output, true);
    }

    #[test]
    fn transform_majority_different_input_and_output_inverter() {
        let mut mig = mig4::Mig::default();

        let node_input0 = mig.graph_mut().add_node(MigNode::Input(0));
        let node_input1 = mig.graph_mut().add_node(MigNode::Input(1));
        let node_output = mig.graph_mut().add_node(MigNode::Output(2));
        let node_majority = mig.graph_mut().add_node(MigNode::Majority);

        mig.graph_mut().add_edge(node_input0, node_majority, false);
        mig.graph_mut().add_edge(node_input0, node_majority, true);
        mig.graph_mut().add_edge(node_input1, node_majority, true);
        mig.graph_mut().add_edge(node_majority, node_output, true);

        mig.transform_majority(node_majority)
            .expect("transformation to succeed");

        assert_edge!(mig.graph(), node_input1, node_output, false);
    }

    #[test]
    fn transform_distributivity() {
        let mut mig = mig4::Mig::default();

        // Set up M(M(x, y, u), M(x, y, v), z)
        let node_input_x = mig.graph_mut().add_node(MigNode::Input(0));
        let node_input_y = mig.graph_mut().add_node(MigNode::Input(1));
        let node_input_z = mig.graph_mut().add_node(MigNode::Input(2));
        let node_input_u = mig.graph_mut().add_node(MigNode::Input(3));
        let node_input_v = mig.graph_mut().add_node(MigNode::Input(4));

        let node_majority_inner0 = mig.graph_mut().add_node(MigNode::Majority);
        let node_majority_inner1 = mig.graph_mut().add_node(MigNode::Majority);
        let node_majority_outer = mig.graph_mut().add_node(MigNode::Majority);

        mig.graph_mut()
            .add_edge(node_input_x, node_majority_inner0, false);
        mig.graph_mut()
            .add_edge(node_input_y, node_majority_inner0, false);
        mig.graph_mut()
            .add_edge(node_input_u, node_majority_inner0, false);

        mig.graph_mut()
            .add_edge(node_input_x, node_majority_inner1, false);
        mig.graph_mut()
            .add_edge(node_input_y, node_majority_inner1, false);
        mig.graph_mut()
            .add_edge(node_input_v, node_majority_inner1, false);

        mig.graph_mut()
            .add_edge(node_majority_inner0, node_majority_outer, false);
        mig.graph_mut()
            .add_edge(node_majority_inner1, node_majority_outer, false);
        mig.graph_mut()
            .add_edge(node_input_z, node_majority_outer, false);

        mig.transform_distributivity(node_majority_outer)
            .expect("transformation to succeed");

        // Check for expected transformation: M(x, y, M(u, v, z))
        // Find the node that should represent the inner majority gate `M(u, v, z)`
        let new_node_majority_inner = {
            let mut i = mig.graph().neighbors_directed(node_input_u, Outgoing);
            let n = i
                .next()
                .expect("input u should be an input to the inner majority gate");
            assert_eq!(
                i.next(),
                None,
                "input u should only be an input to one node"
            );

            n
        };
        assert_edge!(mig.graph(), node_input_u, new_node_majority_inner, false);
        assert_edge!(mig.graph(), node_input_v, new_node_majority_inner, false);
        assert_edge!(mig.graph(), node_input_z, new_node_majority_inner, false);

        // Find the node that should represent the outer majority gate `M(x, y, ...)`
        let new_node_majority_outer = {
            let mut i = mig
                .graph()
                .neighbors_directed(new_node_majority_inner, Outgoing);
            let n = i
                .next()
                .expect("inner majority gate should be an input to the outer majority gate");
            assert_eq!(
                i.next(),
                None,
                "inner majority gate should only be an input to one node"
            );

            n
        };
        assert_edge!(mig.graph(), node_input_x, new_node_majority_outer, false);
        assert_edge!(mig.graph(), node_input_y, new_node_majority_outer, false);
        assert_edge!(
            mig.graph(),
            new_node_majority_inner,
            new_node_majority_outer,
            false
        );
    }

    #[test]
    fn transform_distributivity_inner_common_inverted() {
        let mut mig = mig4::Mig::default();

        // Set up M(M(x', y, u), M(x', y, v), z)
        let node_input_x = mig.graph_mut().add_node(MigNode::Input(0));
        let node_input_y = mig.graph_mut().add_node(MigNode::Input(1));
        let node_input_z = mig.graph_mut().add_node(MigNode::Input(2));
        let node_input_u = mig.graph_mut().add_node(MigNode::Input(3));
        let node_input_v = mig.graph_mut().add_node(MigNode::Input(4));

        let node_majority_inner0 = mig.graph_mut().add_node(MigNode::Majority);
        let node_majority_inner1 = mig.graph_mut().add_node(MigNode::Majority);
        let node_majority_outer = mig.graph_mut().add_node(MigNode::Majority);

        mig.graph_mut()
            .add_edge(node_input_x, node_majority_inner0, true);
        mig.graph_mut()
            .add_edge(node_input_y, node_majority_inner0, false);
        mig.graph_mut()
            .add_edge(node_input_u, node_majority_inner0, false);

        mig.graph_mut()
            .add_edge(node_input_x, node_majority_inner1, true);
        mig.graph_mut()
            .add_edge(node_input_y, node_majority_inner1, false);
        mig.graph_mut()
            .add_edge(node_input_v, node_majority_inner1, false);

        mig.graph_mut()
            .add_edge(node_majority_inner0, node_majority_outer, false);
        mig.graph_mut()
            .add_edge(node_majority_inner1, node_majority_outer, false);
        mig.graph_mut()
            .add_edge(node_input_z, node_majority_outer, false);

        mig.transform_distributivity(node_majority_outer)
            .expect("transformation to succeed");

        // Check for expected transformation: M(x', y, M(u, v, z))
        // Find the node that should represent the inner majority gate `M(u, v, z)`
        let new_node_majority_inner = {
            let mut i = mig.graph().neighbors_directed(node_input_u, Outgoing);
            let n = i
                .next()
                .expect("input u should be an input to the inner majority gate");
            assert_eq!(
                i.next(),
                None,
                "input u should only be an input to one node"
            );

            n
        };
        assert_edge!(mig.graph(), node_input_u, new_node_majority_inner, false);
        assert_edge!(mig.graph(), node_input_v, new_node_majority_inner, false);
        assert_edge!(mig.graph(), node_input_z, new_node_majority_inner, false);

        // Find the node that should represent the outer majority gate `M(x', y, ...)`
        let new_node_majority_outer = {
            let mut i = mig
                .graph()
                .neighbors_directed(new_node_majority_inner, Outgoing);
            let n = i
                .next()
                .expect("inner majority gate should be an input to the outer majority gate");
            assert_eq!(
                i.next(),
                None,
                "inner majority gate should only be an input to one node"
            );

            n
        };
        assert_edge!(mig.graph(), node_input_x, new_node_majority_outer, true);
        assert_edge!(mig.graph(), node_input_y, new_node_majority_outer, false);
        assert_edge!(
            mig.graph(),
            new_node_majority_inner,
            new_node_majority_outer,
            false
        );
    }

    #[test]
    fn transform_distributivity_inner_different_first_inverted() {
        let mut mig = mig4::Mig::default();

        // Set up M(M(x, y, u'), M(x, y, v), z)
        let node_input_x = mig.graph_mut().add_node(MigNode::Input(0));
        let node_input_y = mig.graph_mut().add_node(MigNode::Input(1));
        let node_input_z = mig.graph_mut().add_node(MigNode::Input(2));
        let node_input_u = mig.graph_mut().add_node(MigNode::Input(3));
        let node_input_v = mig.graph_mut().add_node(MigNode::Input(4));

        let node_majority_inner0 = mig.graph_mut().add_node(MigNode::Majority);
        let node_majority_inner1 = mig.graph_mut().add_node(MigNode::Majority);
        let node_majority_outer = mig.graph_mut().add_node(MigNode::Majority);

        mig.graph_mut()
            .add_edge(node_input_x, node_majority_inner0, false);
        mig.graph_mut()
            .add_edge(node_input_y, node_majority_inner0, false);
        mig.graph_mut()
            .add_edge(node_input_u, node_majority_inner0, true);

        mig.graph_mut()
            .add_edge(node_input_x, node_majority_inner1, false);
        mig.graph_mut()
            .add_edge(node_input_y, node_majority_inner1, false);
        mig.graph_mut()
            .add_edge(node_input_v, node_majority_inner1, false);

        mig.graph_mut()
            .add_edge(node_majority_inner0, node_majority_outer, false);
        mig.graph_mut()
            .add_edge(node_majority_inner1, node_majority_outer, false);
        mig.graph_mut()
            .add_edge(node_input_z, node_majority_outer, false);

        mig.transform_distributivity(node_majority_outer)
            .expect("transformation to succeed");

        // Check for expected transformation: M(x, y, M(u', v, z))
        // Find the node that should represent the inner majority gate `M(u', v, z)`
        let new_node_majority_inner = {
            let mut i = mig.graph().neighbors_directed(node_input_u, Outgoing);
            let n = i
                .next()
                .expect("input u should be an input to the inner majority gate");
            assert_eq!(
                i.next(),
                None,
                "input u should only be an input to one node"
            );

            n
        };
        assert_edge!(mig.graph(), node_input_u, new_node_majority_inner, true);
        assert_edge!(mig.graph(), node_input_v, new_node_majority_inner, false);
        assert_edge!(mig.graph(), node_input_z, new_node_majority_inner, false);

        // Find the node that should represent the outer majority gate `M(x, y, ...)`
        let new_node_majority_outer = {
            let mut i = mig
                .graph()
                .neighbors_directed(new_node_majority_inner, Outgoing);
            let n = i
                .next()
                .expect("inner majority gate should be an input to the outer majority gate");
            assert_eq!(
                i.next(),
                None,
                "inner majority gate should only be an input to one node"
            );

            n
        };
        assert_edge!(mig.graph(), node_input_x, new_node_majority_outer, false);
        assert_edge!(mig.graph(), node_input_y, new_node_majority_outer, false);
        assert_edge!(
            mig.graph(),
            new_node_majority_inner,
            new_node_majority_outer,
            false
        );
    }

    #[test]
    fn transform_distributivity_inner_different_second_inverted() {
        let mut mig = mig4::Mig::default();

        // Set up M(M(x, y, u), M(x, y, v'), z)
        let node_input_x = mig.graph_mut().add_node(MigNode::Input(0));
        let node_input_y = mig.graph_mut().add_node(MigNode::Input(1));
        let node_input_z = mig.graph_mut().add_node(MigNode::Input(2));
        let node_input_u = mig.graph_mut().add_node(MigNode::Input(3));
        let node_input_v = mig.graph_mut().add_node(MigNode::Input(4));

        let node_majority_inner0 = mig.graph_mut().add_node(MigNode::Majority);
        let node_majority_inner1 = mig.graph_mut().add_node(MigNode::Majority);
        let node_majority_outer = mig.graph_mut().add_node(MigNode::Majority);

        mig.graph_mut()
            .add_edge(node_input_x, node_majority_inner0, false);
        mig.graph_mut()
            .add_edge(node_input_y, node_majority_inner0, false);
        mig.graph_mut()
            .add_edge(node_input_u, node_majority_inner0, false);

        mig.graph_mut()
            .add_edge(node_input_x, node_majority_inner1, false);
        mig.graph_mut()
            .add_edge(node_input_y, node_majority_inner1, false);
        mig.graph_mut()
            .add_edge(node_input_v, node_majority_inner1, true);

        mig.graph_mut()
            .add_edge(node_majority_inner0, node_majority_outer, false);
        mig.graph_mut()
            .add_edge(node_majority_inner1, node_majority_outer, false);
        mig.graph_mut()
            .add_edge(node_input_z, node_majority_outer, false);

        mig.transform_distributivity(node_majority_outer)
            .expect("transformation to succeed");

        // Check for expected transformation: M(x, y, M(u, v', z))
        // Find the node that should represent the inner majority gate `M(u, v', z)`
        let new_node_majority_inner = {
            let mut i = mig.graph().neighbors_directed(node_input_u, Outgoing);
            let n = i
                .next()
                .expect("input u should be an input to the inner majority gate");
            assert_eq!(
                i.next(),
                None,
                "input u should only be an input to one node"
            );

            n
        };
        assert_edge!(mig.graph(), node_input_u, new_node_majority_inner, false);
        assert_edge!(mig.graph(), node_input_v, new_node_majority_inner, true);
        assert_edge!(mig.graph(), node_input_z, new_node_majority_inner, false);

        // Find the node that should represent the outer majority gate `M(x, y, ...)`
        let new_node_majority_outer = {
            let mut i = mig
                .graph()
                .neighbors_directed(new_node_majority_inner, Outgoing);
            let n = i
                .next()
                .expect("inner majority gate should be an input to the outer majority gate");
            assert_eq!(
                i.next(),
                None,
                "inner majority gate should only be an input to one node"
            );

            n
        };
        assert_edge!(mig.graph(), node_input_x, new_node_majority_outer, false);
        assert_edge!(mig.graph(), node_input_y, new_node_majority_outer, false);
        assert_edge!(
            mig.graph(),
            new_node_majority_inner,
            new_node_majority_outer,
            false
        );
    }

    #[test]
    fn transform_distributivity_inner_inverted() {
        let mut mig = mig4::Mig::default();

        // Set up M(M(x', y, u), M'(x, y', v), z)
        let node_input_x = mig.graph_mut().add_node(MigNode::Input(0));
        let node_input_y = mig.graph_mut().add_node(MigNode::Input(1));
        let node_input_z = mig.graph_mut().add_node(MigNode::Input(2));
        let node_input_u = mig.graph_mut().add_node(MigNode::Input(3));
        let node_input_v = mig.graph_mut().add_node(MigNode::Input(4));

        let node_majority_inner0 = mig.graph_mut().add_node(MigNode::Majority);
        let node_majority_inner1 = mig.graph_mut().add_node(MigNode::Majority);
        let node_majority_outer = mig.graph_mut().add_node(MigNode::Majority);

        mig.graph_mut()
            .add_edge(node_input_x, node_majority_inner0, true);
        mig.graph_mut()
            .add_edge(node_input_y, node_majority_inner0, false);
        mig.graph_mut()
            .add_edge(node_input_u, node_majority_inner0, false);

        mig.graph_mut()
            .add_edge(node_input_x, node_majority_inner1, false);
        mig.graph_mut()
            .add_edge(node_input_y, node_majority_inner1, true);
        mig.graph_mut()
            .add_edge(node_input_v, node_majority_inner1, false);

        mig.graph_mut()
            .add_edge(node_majority_inner0, node_majority_outer, false);
        mig.graph_mut()
            .add_edge(node_majority_inner1, node_majority_outer, true);
        mig.graph_mut()
            .add_edge(node_input_z, node_majority_outer, false);

        mig.transform_distributivity(node_majority_outer)
            .expect("transformation to succeed");

        // Check for expected transformation: M(x', y, M(u, v', z))
        // Find the node that should represent the inner majority gate `M(u, v', z)`
        let new_node_majority_inner = {
            let mut i = mig.graph().neighbors_directed(node_input_u, Outgoing);
            let n = i
                .next()
                .expect("input u should be an input to the inner majority gate");
            assert_eq!(
                i.next(),
                None,
                "input u should only be an input to one node"
            );

            n
        };
        assert_edge!(mig.graph(), node_input_u, new_node_majority_inner, false);
        assert_edge!(mig.graph(), node_input_v, new_node_majority_inner, true);
        assert_edge!(mig.graph(), node_input_z, new_node_majority_inner, false);

        // Find the node that should represent the outer majority gate `M(x', y, ...)`
        let new_node_majority_outer = {
            let mut i = mig
                .graph()
                .neighbors_directed(new_node_majority_inner, Outgoing);
            let n = i
                .next()
                .expect("inner majority gate should be an input to the outer majority gate");
            assert_eq!(
                i.next(),
                None,
                "inner majority gate should only be an input to one node"
            );

            n
        };
        assert_edge!(mig.graph(), node_input_x, new_node_majority_outer, true);
        assert_edge!(mig.graph(), node_input_y, new_node_majority_outer, false);
        assert_edge!(
            mig.graph(),
            new_node_majority_inner,
            new_node_majority_outer,
            false
        );
    }

    #[test]
    fn transform_distributivity_inner_common_different_signs() {
        let mut mig = mig4::Mig::default();

        // Set up M(M(x', y, u), M(x, y, v), z)
        let node_input_x = mig.graph_mut().add_node(MigNode::Input(0));
        let node_input_y = mig.graph_mut().add_node(MigNode::Input(1));
        let node_input_z = mig.graph_mut().add_node(MigNode::Input(2));
        let node_input_u = mig.graph_mut().add_node(MigNode::Input(3));
        let node_input_v = mig.graph_mut().add_node(MigNode::Input(4));

        let node_majority_inner0 = mig.graph_mut().add_node(MigNode::Majority);
        let node_majority_inner1 = mig.graph_mut().add_node(MigNode::Majority);
        let node_majority_outer = mig.graph_mut().add_node(MigNode::Majority);

        mig.graph_mut()
            .add_edge(node_input_x, node_majority_inner0, true);
        mig.graph_mut()
            .add_edge(node_input_y, node_majority_inner0, false);
        mig.graph_mut()
            .add_edge(node_input_u, node_majority_inner0, false);

        mig.graph_mut()
            .add_edge(node_input_x, node_majority_inner1, false);
        mig.graph_mut()
            .add_edge(node_input_y, node_majority_inner1, false);
        mig.graph_mut()
            .add_edge(node_input_v, node_majority_inner1, true);

        mig.graph_mut()
            .add_edge(node_majority_inner0, node_majority_outer, false);
        mig.graph_mut()
            .add_edge(node_majority_inner1, node_majority_outer, false);
        mig.graph_mut()
            .add_edge(node_input_z, node_majority_outer, false);

        mig.transform_distributivity(node_majority_outer)
            .ok_or(())
            .expect_err("transformation to fail");
    }
}
