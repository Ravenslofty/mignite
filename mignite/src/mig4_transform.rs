use crate::mig4;

use mig4::MigNode;
use petgraph::prelude::*;

impl mig4::Mig {
    fn transform_majority(&mut self, node: NodeIndex) -> Option<()> {
        let (x, y, z) = self.try_unwrap_majority(node)?;

        let mut majority = |x_edge: EdgeIndex, y_edge: EdgeIndex, z_edge: EdgeIndex| {
            let x = self.edge_source(x_edge);
            let y = self.edge_source(y_edge);
            let z = self.edge_source(z_edge);
            let x_is_inverted = self.is_edge_inverted(x_edge);
            let y_is_inverted = self.is_edge_inverted(y_edge);
            let z_is_inverted = self.is_edge_inverted(z_edge);

            if x == y {
                let mut outputs = self.output_edges(node).detach();
                while let Some((edge, output)) = outputs.next(self.graph()) {
                    let inverted = self.remove_edge(edge);
                    if x_is_inverted == y_is_inverted {
                        // M(x, x, y) => x
                        self.add_edge(x, output, x_is_inverted ^ inverted);
                    } else {
                        // M(x, x', y) => y
                        self.add_edge(z, output, z_is_inverted ^ inverted);
                    }   
                }
                self.remove_node(node);
                return Some(());
            }
            None
        };

        majority(x, y, z)
            .or_else(|| majority(y, z, x))
            .or_else(|| majority(z, x, y))
    }

    /// Transform `M(x, u, M(y, u, z))` to `M(z, u, M(y, u, x))`
    #[allow(clippy::many_single_char_names, clippy::shadow_unrelated)]
    pub fn transform_associativity(&mut self, node: NodeIndex) -> Option<()> {
        type Input = (NodeIndex, bool);

        let classify_inputs = |i1: Input, i2: Input, i3: Input, i4: Input, i5: Input| {
            let all = [i1, i2, i3, i4, i5];
            let mut shared = std::collections::HashSet::new();
            let mut unique = std::collections::HashSet::new();

            for input in &all {
                let count = all.iter().filter(|input2| *input2 == input).count();

                if count == 1 {
                    unique.insert(*input);
                } else {
                    shared.insert(*input);
                }
            }

            (shared, unique)
        };

        let (x_edge, y_edge, z_edge) = self.try_unwrap_majority(node)?;

        let mut associativity = |outer1_edge: EdgeIndex, outer2_edge: EdgeIndex, outer3_edge: EdgeIndex| {
            let outer1 = self.edge_source(outer1_edge);
            let outer2 = self.edge_source(outer2_edge);
            let outer3 = self.edge_source(outer3_edge);
            let outer1_is_inverted = self.is_edge_inverted(outer1_edge);
            let outer2_is_inverted = self.is_edge_inverted(outer2_edge);
            let outer3_is_inverted = self.is_edge_inverted(outer3_edge);

            let (inner1_edge, inner2_edge, inner3_edge) = self.try_unwrap_majority(outer3)?;
            let inner1 = self.edge_source(inner1_edge);
            let inner2 = self.edge_source(inner2_edge);
            let inner3 = self.edge_source(inner3_edge);
            let inner1_is_inverted = self.is_edge_inverted(inner1_edge);
            let inner2_is_inverted = self.is_edge_inverted(inner2_edge);
            let inner3_is_inverted = self.is_edge_inverted(inner3_edge);

            if outer1_is_inverted
                || outer2_is_inverted
                || outer3_is_inverted
                || inner1_is_inverted
                || inner2_is_inverted
                || inner3_is_inverted
            {
                return None;
            }

            let (shared, unique) = classify_inputs(
                (outer1, outer1_is_inverted),
                (outer2, outer2_is_inverted),
                (inner1, inner1_is_inverted ^ outer3_is_inverted),
                (inner2, inner2_is_inverted ^ outer3_is_inverted),
                (inner3, inner3_is_inverted ^ outer3_is_inverted),
            );

            if shared.len() != 1 || unique.len() != 3 {
                return None;
            }

            let mut shared_iter = shared.iter();
            let mut unique_iter = unique.iter();

            // u is the shared input.
            let (u, u_is_inverted) = shared_iter.next().unwrap();

            let u_is_inner = *u == inner1 || *u == inner2 || *u == inner3;
            let u_is_outer = *u == outer1 || *u == outer2;

            assert!(u_is_inner && u_is_outer);

            // TODO: this needs to figure out which input is in the outer gate.
            let (x, x_is_inverted) = unique_iter.next().unwrap();
            let (y, y_is_inverted) = unique_iter.next().unwrap();
            let (z, z_is_inverted) = unique_iter.next().unwrap();

            let mut rewrite = |x: &NodeIndex, x_is_inverted: &bool, x_edge: EdgeIndex, y: &NodeIndex, y_is_inverted: &bool, _y_edge: EdgeIndex, z: &NodeIndex, z_is_inverted: &bool, _z_edge: EdgeIndex| {
                let x_is_inner = *x == inner1 || *x == inner2 || *x == inner3;
                let y_is_inner = *y == inner1 || *y == inner2 || *y == inner3;
                let z_is_inner = *z == inner1 || *z == inner2 || *z == inner3;

                if x_is_inner || !y_is_inner || !z_is_inner || x_edge == outer3_edge {
                    return None;
                }

                //  node
                // / | \
                // x u outer3
                //     / | \
                //     y u z

                let e = self.add_node(MigNode::Majority);
                self.add_edge(*u, e, *u_is_inverted);
                self.add_edge(*x, e, *x_is_inverted);
                self.add_edge(*y, e, *y_is_inverted);

                self.remove_edge(outer3_edge);
                self.remove_edge(x_edge);
                self.add_edge(e, node, false);
                self.add_edge(*z, node, *z_is_inverted);

                //eprintln!("swapped {} with {}", x.index(), z.index());

                Some(())
            };

            // When all you have is a hammer to deal with commutativity...
            rewrite(x, x_is_inverted, x_edge, y, y_is_inverted, y_edge, z, z_is_inverted, z_edge)
            .or_else(|| rewrite(y, y_is_inverted, y_edge, z, z_is_inverted, z_edge, x, x_is_inverted, x_edge))
            .or_else(|| rewrite(z, z_is_inverted, z_edge, x, x_is_inverted, x_edge, y, y_is_inverted, y_edge))
        };

        associativity(x_edge, y_edge, z_edge)
            .or_else(|| associativity(y_edge, z_edge, x_edge))
            .or_else(|| associativity(z_edge, x_edge, y_edge))
    }

    /// Transform `M(M(x, y, u), M(x, y, v), z)` into `M(x, y, M(u, v, z))`.
    #[allow(clippy::many_single_char_names, clippy::similar_names)]
    pub fn transform_distributivity(&mut self, node: NodeIndex) -> Option<()> {
        type Input = (NodeIndex, bool);
        let classify_inputs = |i1: Input, i2: Input, i3: Input, i4: Input, i5: Input, i6: Input| {
            let all = [i1, i2, i3, i4, i5, i6];
            let mut shared = std::collections::HashSet::new();
            let mut unique = std::collections::HashSet::new();

            for input in &all {
                let count = all.iter().filter(|input2| *input2 == input).count();

                if count == 1 {
                    unique.insert(*input);
                } else {
                    shared.insert(*input);
                }
            }

            (shared, unique)
        };

        let (x_edge, y_edge, z_edge) = self.try_unwrap_majority(node)?;
        let x = self.edge_source(x_edge);
        let y = self.edge_source(y_edge);
        let z = self.edge_source(z_edge);

        let mut distributivity = |b_edge: EdgeIndex,
                                  c_edge: EdgeIndex,
                                  z_edge: EdgeIndex,
                                  b: NodeIndex,
                                  c: NodeIndex,
                                  z: NodeIndex| {
            //         j
            //    /    |    \
            //   b     c     z
            // / | \ / | \
            // x y u x y v

            let b_is_inverted = self.is_edge_inverted(b_edge);
            let c_is_inverted = self.is_edge_inverted(c_edge);
            let z_is_inverted = self.is_edge_inverted(z_edge);

            let (x1_edge, y1_edge, u_edge) = self.try_unwrap_majority(b)?;
            let (x2_edge, y2_edge, v_edge) = self.try_unwrap_majority(c)?;

            let x1 = self.edge_source(x1_edge);
            let y1 = self.edge_source(y1_edge);
            let u = self.edge_source(u_edge);

            let x1_is_inverted = self.is_edge_inverted(x1_edge);
            let y1_is_inverted = self.is_edge_inverted(y1_edge);
            let u_is_inverted = self.is_edge_inverted(u_edge);

            let x2 = self.edge_source(x2_edge);
            let y2 = self.edge_source(y2_edge);
            let v = self.edge_source(v_edge);

            let x2_is_inverted = self.is_edge_inverted(x2_edge);
            let y2_is_inverted = self.is_edge_inverted(y2_edge);
            let v_is_inverted = self.is_edge_inverted(v_edge);

            let (shared, unique) = classify_inputs(
                (x1, x1_is_inverted ^ b_is_inverted),
                (y1, y1_is_inverted ^ b_is_inverted),
                (u, u_is_inverted ^ b_is_inverted),
                (x2, x2_is_inverted ^ c_is_inverted),
                (y2, y2_is_inverted ^ c_is_inverted),
                (v, v_is_inverted ^ c_is_inverted),
            );

            if shared.len() != 2 || unique.len() != 2 {
                return None;
            }

            // Distributivity improves area if j is the sole user of both b and c, and is area-neutral if j is the sole user of one of b or c.
            let b_parents = self.output_edges(b).count();
            let c_parents = self.output_edges(c).count();

            if b_parents > 1 && c_parents > 1 {
                return None;
            }

            let mut shared_iter = shared.iter();
            let mut unique_iter = unique.iter();

            let d = self.add_node(MigNode::Majority);

            let nx1 = shared_iter.next().unwrap();
            let ny1 = shared_iter.next().unwrap();
            let nu = unique_iter.next().unwrap();
            let nv = unique_iter.next().unwrap();

            self.add_edge(nu.0, d, nu.1);
            self.add_edge(nv.0, d, nv.1);
            self.add_edge(z, d, z_is_inverted);

            self.remove_edge(b_edge);
            self.remove_edge(c_edge);
            self.remove_edge(z_edge);

            self.add_edge(nx1.0, node, nx1.1);
            self.add_edge(ny1.0, node, ny1.1);
            self.add_edge(d, node, false);

            Some(())
        };

        distributivity(x_edge, y_edge, z_edge, x, y, z)
            .or_else(|| distributivity(y_edge, z_edge, x_edge, y, z, x))
            .or_else(|| distributivity(z_edge, x_edge, y_edge, z, x, y))
    }

    fn transform_inverters(&mut self, node: NodeIndex) -> Option<()> {
        let (x_edge, y_edge, z_edge) = self.try_unwrap_majority(node)?;
        let x_is_inverted = self.is_edge_inverted(x_edge);
        let y_is_inverted = self.is_edge_inverted(y_edge);
        let z_is_inverted = self.is_edge_inverted(z_edge);

        let mut inverter_propagation = |x_is_inverted: bool, y_is_inverted: bool| {
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

                return Some(());
            }
            None
        };

        inverter_propagation(x_is_inverted, y_is_inverted)
            .or_else(|| inverter_propagation(y_is_inverted, z_is_inverted))
            .or_else(|| inverter_propagation(z_is_inverted, x_is_inverted))
    }

    pub fn transform_relevance(&mut self, node: NodeIndex) -> Option<()> {
        let (x_edge, y_edge, z_edge) = self.try_unwrap_majority(node)?;

        let mut relevance = |x_edge: EdgeIndex, y_edge: EdgeIndex, z_edge: EdgeIndex| {
            let mut x_is_inverted = self.is_edge_inverted(x_edge);
            let mut y_is_inverted = self.is_edge_inverted(y_edge);
            let z_is_inverted = self.is_edge_inverted(z_edge);
            let mut x = self.edge_source(x_edge);
            let mut y = self.edge_source(y_edge);
            let z = self.edge_source(z_edge);

            if self.node_type(x) == MigNode::Zero {
                if self.node_type(y) == MigNode::Zero {
                    return None;
                }
                std::mem::swap(&mut x, &mut y);
                std::mem::swap(&mut x_is_inverted, &mut y_is_inverted);
            }

            let (a_edge, b_edge, c_edge) = self.try_unwrap_majority(z)?;
            let a = self.edge_source(a_edge);
            let b = self.edge_source(b_edge);
            let c = self.edge_source(c_edge);
            let a_is_inverted = self.is_edge_inverted(a_edge);
            let b_is_inverted = self.is_edge_inverted(b_edge);
            let c_is_inverted = self.is_edge_inverted(c_edge);

            if a == x || b == x || c == x {
                let d = self.add_node(MigNode::Majority);
                if a == x {
                    self.add_edge(y, d, a_is_inverted ^ x_is_inverted ^ !y_is_inverted);
                } else {
                    self.add_edge(a, d, a_is_inverted);
                }

                if b == x {
                    self.add_edge(y, d, b_is_inverted ^ x_is_inverted ^ !y_is_inverted);
                } else {
                    self.add_edge(b, d, b_is_inverted);
                }

                if c == x {
                    self.add_edge(y, d, c_is_inverted ^ x_is_inverted ^ !y_is_inverted);
                } else {
                    self.add_edge(c, d, c_is_inverted);
                }

                self.remove_edge(z_edge);
                self.add_edge(d, node, z_is_inverted);

                return Some(());
            }

            None
        };

        let mut did_something = relevance(x_edge, y_edge, z_edge).is_some();
        did_something |= relevance(y_edge, z_edge, x_edge).is_some();
        did_something |= relevance(z_edge, x_edge, y_edge).is_some();
        if did_something {
            Some(())
        } else {
            None
        }
    }

    pub fn cleanup_graph(&mut self) {
        // Attempt to deduplicate the graph.
        let mut hash: std::collections::HashMap<[(NodeIndex<u32>, bool); 3], NodeIndex> =
            std::collections::HashMap::new();

        let node_indices = self.graph().node_indices().collect::<Vec<_>>();
        for node in node_indices {
            if let Some((x_edge, y_edge, z_edge)) = self.try_unwrap_majority(node) {
                let x = self.edge_source(x_edge);
                let y = self.edge_source(y_edge);
                let z = self.edge_source(z_edge);
                let x_is_inverted = self.is_edge_inverted(x_edge);
                let y_is_inverted = self.is_edge_inverted(y_edge);
                let z_is_inverted = self.is_edge_inverted(z_edge);

                let children = [(x, x_is_inverted), (y, y_is_inverted), (z, z_is_inverted)];

                if let Some(dest) = hash.get(&children) {
                    let mut outputs = self.output_edges(node).detach();
                    while let Some((edge, output)) = outputs.next(self.graph()) {
                        let inverted = self.remove_edge(edge);
                        self.add_edge(*dest, output, inverted);
                    }
                    continue;
                }

                let children_inverted = [
                    (x, !x_is_inverted),
                    (y, !y_is_inverted),
                    (z, !z_is_inverted),
                ];

                if let Some(dest) = hash.get(&children_inverted) {
                    let mut outputs = self.output_edges(node).detach();
                    while let Some((edge, output)) = outputs.next(self.graph()) {
                        let inverted = self.remove_edge(edge);
                        self.add_edge(*dest, output, !inverted);
                    }
                    continue;
                }

                hash.insert(children, node);
            }
        }

        // Look for orphan nodes (nodes not connected to an output).
        let mut did_something = true;
        while did_something {
            #[allow(clippy::shadow_unrelated)]
            let nodes = self.node_count();

            *self.graph_mut() = self.graph().filter_map(|node, kind| {
                if *kind == MigNode::Majority && self.graph().neighbors_directed(node, Outgoing).count() == 0 {
                    None
                } else {
                    Some(*kind)
                }
            }, |_edge, kind| Some(*kind));

            did_something = self.node_count() < nodes;
        }
    }

    pub fn print_stats(&self) {
        // Calculate graph depth (for fun).
        let mut max_depth = 0;
        let mut max_depth_input = 0_usize;
        let mut max_depth_output = 0_usize;
        let mut sum_depth = 0;
        let mut sum_outputs = 0;

        let inputs = self.graph().externals(Outgoing).collect::<Vec<_>>();
        let outputs = self.graph().externals(Incoming);

        for output in outputs {
            let counts = petgraph::algo::dijkstra(self.graph(), output, None, |_| 1);

            for input in &inputs {
                if let Some(depth) = counts.get(input) {
                    if *depth > max_depth {
                        max_depth = *depth;
                        max_depth_input = input.index();
                        max_depth_output = output.index();
                    }
                    sum_depth += depth;
                    sum_outputs += 1;
                }
            }
        }

        eprintln!("MIG: maximum gate depth is {} between input {} and output {}, average gate depth is {:.1}", max_depth, max_depth_input, max_depth_output, f64::from(sum_depth) / f64::from(sum_outputs));
        eprintln!(
            "MIG: there are {} nodes and {} edges in the graph",
            self.node_count(),
            self.edge_count()
        );
    }

    pub fn optimise_area(&mut self) {
        // Clean up graph orphans.
        self.print_stats();
        self.cleanup_graph();
        self.print_stats();

        // Find graph inputs.
        let inputs = self.graph().externals(Incoming).collect::<Vec<_>>();

        // Helper functions.
        let majority = |graph: &mut Self| {
            let mut did_something = true;
            eprintln!("   Majority:\t\trewriting gates dominated by a node");
            while did_something {
                did_something = false;
                let mut dfs = DfsPostOrder::empty(graph.graph());
                let mut nodes = Vec::new();
                for input in inputs.clone() {
                    dfs.move_to(input);
                    while let Some(node) = dfs.next(graph.graph()) {
                        did_something |= graph.transform_inverters(node).is_some();
                        nodes.push(node);
                    }
                }

                for node in nodes {
                    did_something |= graph.transform_majority(node).is_some();
                }
            }
        };

        let distributivity = |graph: &mut Self| {
            let mut did_something = true;
            eprintln!("   Distributivity:\trewriting gates with common children");
            while did_something {
                did_something = false;
                let mut dfs = DfsPostOrder::empty(graph.graph());
                let mut nodes = Vec::new();
                for input in inputs.clone() {
                    dfs.move_to(input);
                    while let Some(node) = dfs.next(graph.graph()) {
                        did_something |= graph.transform_inverters(node).is_some();
                        nodes.push(node);
                    }
                }

                for node in nodes {
                    did_something |= graph.transform_distributivity(node).is_some();
                }
            }
        };

        let associativity = |graph: &mut Self| {
            eprintln!("   Associativity:\tswapping terms across gates");
            // Because associativity is a reversible transformation, running it multiple times infinite-loops.
            let mut dfs = DfsPostOrder::empty(graph.graph());
            let mut nodes = Vec::new();
            for input in inputs.clone() {
                dfs.move_to(input);
                while let Some(node) = dfs.next(graph.graph()) {
                    graph.transform_inverters(node);
                    nodes.push(node);
                }
            }

            for node in nodes {
                graph.transform_associativity(node);
            }
        };

        let relevance = |graph: &mut Self| {
            let mut did_something = true;
            eprintln!("   Relevance:\t\trewriting don't-care terms to increase common terms");
            while did_something {
                did_something = false;
                let mut dfs = DfsPostOrder::empty(graph.graph());
                let mut nodes = Vec::new();
                for input in inputs.clone() {
                    dfs.move_to(input);
                    while let Some(node) = dfs.next(graph.graph()) {
                        did_something |= graph.transform_inverters(node).is_some();
                        nodes.push(node);
                    }
                }

                for node in nodes {
                    did_something |= graph.transform_relevance(node).is_some();
                }
            }
        };

        // Explore tree.
        for n in 0..100 {
            let node_count = self.node_count();
            let edge_count = self.edge_count();

            eprintln!("{}:", n);

            majority(self);
            distributivity(self);
            relevance(self);
            //associativity(self);
            //majority(self);
            //distributivity(self);

            self.cleanup_graph();
            self.print_stats();

            if node_count == self.node_count() && edge_count == self.edge_count() {
                break;
            }
        }
        self.print_stats();
    }
}

#[cfg(test)]
mod tests {
    use super::{mig4, MigNode, Outgoing};

    macro_rules! assert_edge {
        ($graph:expr, $a:expr, $b:expr, $weight:expr) => {
            let edge = $graph
                .find_edge($a, $b)
                .unwrap_or_else(|| panic!("edge between {:?} and {:?} to exist", $a, $b));
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

        let node_output = mig.graph_mut().add_node(MigNode::Output(0));

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

        mig.graph_mut()
            .add_edge(node_majority_outer, node_output, false);

        mig.transform_distributivity(node_majority_outer)
            .expect("transformation to succeed");

        mig.cleanup_graph();

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

        let node_output = mig.graph_mut().add_node(MigNode::Output(0));

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

        mig.graph_mut()
            .add_edge(node_majority_outer, node_output, false);

        mig.transform_distributivity(node_majority_outer)
            .expect("transformation to succeed");

        mig.cleanup_graph();

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

        let node_output = mig.graph_mut().add_node(MigNode::Output(0));

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

        mig.graph_mut()
            .add_edge(node_majority_outer, node_output, false);

        mig.transform_distributivity(node_majority_outer)
            .expect("transformation to succeed");

        mig.cleanup_graph();

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

        let node_output = mig.graph_mut().add_node(MigNode::Output(0));

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

        mig.graph_mut()
            .add_edge(node_majority_outer, node_output, false);

        mig.transform_distributivity(node_majority_outer)
            .expect("transformation to succeed");

        mig.cleanup_graph();

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

        let node_output = mig.graph_mut().add_node(MigNode::Output(0));

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

        mig.graph_mut()
            .add_edge(node_majority_outer, node_output, false);

        mig.transform_distributivity(node_majority_outer)
            .expect("transformation to succeed");

        mig.cleanup_graph();

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

    /*#[test]
    fn transform_relevance() {
        let mut mig = mig4::Mig::default();

        // Set up M(x, y, M(x, u, v))
        let node_input_x = mig.graph_mut().add_node(MigNode::Input(0));
        let node_input_y = mig.graph_mut().add_node(MigNode::Input(1));
        let node_input_u = mig.graph_mut().add_node(MigNode::Input(2));
        let node_input_v = mig.graph_mut().add_node(MigNode::Input(3));

        let node_majority_inner = mig.graph_mut().add_node(MigNode::Majority);
        let node_majority_outer = mig.graph_mut().add_node(MigNode::Majority);

        mig.graph_mut()
            .add_edge(node_input_x, node_majority_inner, false);
        mig.graph_mut()
            .add_edge(node_input_u, node_majority_inner, false);
        mig.graph_mut()
            .add_edge(node_input_v, node_majority_inner, false);

        mig.graph_mut()
            .add_edge(node_input_x, node_majority_outer, false);
        mig.graph_mut()
            .add_edge(node_input_y, node_majority_outer, false);
        mig.graph_mut()
            .add_edge(node_majority_inner, node_majority_outer, false);

        mig.to_graphviz("graph.dot");

        mig.transform_relevance(node_majority_outer)
            .expect("transformation to succeed");

        assert_edge!(mig.graph(), node_input_y, node_majority_inner, true);
    }*/
}
