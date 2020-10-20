use std::cmp::Ordering;

use crate::mig4;

use itertools::Itertools;
use petgraph::prelude::*;

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
pub struct Cut {
    inputs: Vec<usize>,
    output: usize,
    nodes: Vec<usize>,
}

impl Cut {
    #[must_use] 
    pub fn new(inputs: Vec<usize>, output: usize, nodes: Vec<usize>) -> Self {
        assert!((0..inputs.len() - 1).all(|i| inputs[i] <= inputs[i + 1]));
        assert!((0..nodes.len() - 1).all(|i| nodes[i] <= nodes[i + 1]));
        assert!(nodes.contains(&output));
        Self { inputs, output, nodes }
    }

    #[must_use]
    pub fn single_node(node: usize) -> Self {
        Self::new(vec![node], node, vec![node])
    }

    #[must_use]
    pub fn input_count(&self) -> usize {
        if self.inputs.contains(&0) {
            self.inputs.len() - 1
        } else {
            self.inputs.len()
        }
    }

    #[must_use]
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Merge three cuts into a new cut, rooted at `output`.
    ///
    /// This method is linear in the number of nodes in `x`, `y` and `z`.
    #[must_use]
    pub fn union(x: &Self, y: &Self, z: &Self, output: usize) -> Self {
        let nodes = [x.output, y.output, z.output];
        let inputs = x.inputs.iter().merge(&y.inputs).merge(&z.inputs).dedup().copied().collect::<Vec<_>>();
        let nodes = x.nodes.iter().merge(&y.nodes).merge(&z.nodes).merge(&nodes).dedup().copied().collect::<Vec<_>>();
        Self {
            inputs,
            output,
            nodes,
        }
    }

    /// `self` dominates `rhs` if all the nodes in `rhs` are contained in `self`.
    /// A cut does not dominate itself.
    #[must_use]
    pub fn dominates(&self, rhs: &Self) -> bool {
        self != rhs && rhs.nodes.iter().all(|node| self.nodes.binary_search(node).is_ok())
    }

    pub fn inputs(&self) -> impl Iterator<Item=NodeIndex> + '_ {
        self.inputs.iter().map(|node| NodeIndex::new(*node))
    }

    pub fn nodes(&self) -> impl Iterator<Item=NodeIndex> + '_ {
        self.nodes.iter().map(|node| NodeIndex::new(*node))
    }
}

pub struct Mapper<'a> {
    max_cuts: usize,
    max_inputs: usize,
    lut_area: &'a [u32],
    lut_delay: &'a [&'a [i32]],
    wire_delay: i32,
    mig: &'a mig4::Mig,
    cuts: Vec<Vec<Cut>>,
    depth: Vec<i32>,
    max_depth: i32,
    height: Vec<i32>,
    area_flow: Vec<f32>,
    references: Vec<u32>,
}

impl<'a> Mapper<'a> {
    #[must_use]
    pub fn new(max_cuts: usize, max_inputs: usize, lut_area: &'a [u32], lut_delay: &'a [&'a [i32]], wire_delay: i32, mig: &'a mig4::Mig) -> Self {
        let len = mig.node_count();
        Self {
            max_cuts,
            max_inputs,
            lut_area,
            lut_delay,
            wire_delay,
            mig,
            cuts: vec![Vec::new(); len],
            depth: vec![-1000; len],
            max_depth: -1000,
            height: vec![-1000; len],
            area_flow: vec![1.0; len],
            references: vec![0; len],
        }
    }

    #[must_use]
    #[inline]
    pub fn cut_depth(&self, cut: &Cut) -> i32 {
        /*cut.inputs.iter().filter(|node| **node != 0).sorted_by_key(|node| self.depth[**node]).rev().enumerate().map(|(index, node)| {
            self.depth[*node] + self.lut_delay[cut.input_count()][index]
        }).max().unwrap() + self.wire_delay*/
        cut.inputs.iter().filter(|node| **node != 0).enumerate().map(|(index, node)| {
            self.depth[*node] + self.lut_delay[cut.input_count()][index]
        }).max().unwrap() + self.wire_delay
    }

    #[must_use]
    #[inline]
    pub fn area_flow(&self, cut: &Cut) -> f32 {
        (cut.inputs.iter().map(|node| self.area_flow[*node]).sum::<f32>() + self.lut_area[cut.input_count()] as f32) / (self.mig.output_edges(NodeIndex::new(cut.output)).count() as f32)
    }

    #[must_use]
    #[inline]
    pub fn cut_rank_depth(&self, lhs: &Cut, rhs: &Cut) -> Ordering {
        let lhs = self.cut_depth(lhs);
        let rhs = self.cut_depth(rhs);
        lhs.cmp(&rhs)
    }

    #[must_use]
    #[inline]
    pub fn cut_rank_size(&self, lhs: &Cut, rhs: &Cut) -> Ordering {
        let lhs = lhs.input_count();
        let rhs = rhs.input_count();
        lhs.cmp(&rhs)
    }

    #[must_use]
    #[inline]
    pub fn cut_rank_area_flow(&self, lhs: &Cut, rhs: &Cut) -> Ordering {
        let lhs = self.area_flow(lhs);
        let rhs = self.area_flow(rhs);
        lhs.partial_cmp(&rhs).unwrap()
    }

    #[must_use]
    #[inline]
    pub fn cut_rank_fanin_refs(&self, lhs: &Cut, rhs: &Cut) -> Ordering {
        let lhs = lhs.inputs.iter().map(|node| self.references[*node]).sum::<u32>() / (lhs.inputs.len() as u32);
        let rhs = rhs.inputs.iter().map(|node| self.references[*node]).sum::<u32>() / (rhs.inputs.len() as u32);
        lhs.cmp(&rhs)
    }

    pub fn compute_cuts<F1, F2, F3>(&mut self, sort_first: F1, sort_second: F2, sort_third: F3) 
    where F1: Fn(&Self, &Cut, &Cut) -> Ordering, F2: Fn(&Self, &Cut, &Cut) -> Ordering, F3: Fn(&Self, &Cut, &Cut) -> Ordering
    {
        let mut iter = petgraph::visit::Topo::new(self.mig.graph());

        let mut cut_count = 0;

        while let Some(node) = iter.next(&self.mig.graph()) {
            if let Some((x_edge, y_edge, z_edge)) = self.mig.try_unwrap_majority(node) {
                let x = self.mig.edge_source(x_edge);
                let y = self.mig.edge_source(y_edge);
                let z = self.mig.edge_source(z_edge);

                if self.cuts[x.index()].is_empty() {
                    self.cuts[x.index()] = vec![Cut::single_node(x.index())];
                    self.depth[x.index()] = 0;
                    self.area_flow[x.index()] = 0.0;
                }

                if self.cuts[y.index()].is_empty() {
                    self.cuts[y.index()] = vec![Cut::single_node(y.index())];
                    self.depth[y.index()] = 0;
                    self.area_flow[y.index()] = 0.0;
                }

                if self.cuts[z.index()].is_empty() {
                    self.cuts[z.index()] = vec![Cut::single_node(z.index())];
                    self.depth[z.index()] = 0;
                    self.area_flow[z.index()] = 0.0;
                }

                // Compute the trivial cut of this node.
                let mut inputs = vec![x.index(), y.index(), z.index()];
                let mut nodes = vec![x.index(), y.index(), z.index(), node.index()];
                inputs.sort_unstable();
                nodes.sort_unstable();
                let cut = Cut::new(inputs, node.index(), nodes);

                let cuts = self.cuts[x.index()].iter()
                .cartesian_product(&self.cuts[y.index()])
                .cartesian_product(&self.cuts[z.index()])
                .map(|((x_cut, y_cut), z_cut)| Cut::union(x_cut, y_cut, z_cut, node.index()))
                .chain(std::iter::once(cut))
                .chain(self.cuts[node.index()].first().cloned())
                .filter(|candidate| candidate.input_count() <= self.max_inputs)
                .filter(|candidate| {
                    if self.height[node.index()] < 0 {
                        return true;
                    }
                    assert!(self.max_depth - self.height[node.index()] >= 0);
                    if self.cut_depth(candidate) > self.max_depth - self.height[node.index()] {
                        dbg!(node.index(), self.cut_depth(candidate), self.max_depth, self.height[node.index()]);
                        return false;
                    }
                    true
                })
                .collect::<Vec<Cut>>();

                assert!(!cuts.is_empty());

                // Check for dominated cuts.
                let cuts = cuts.iter()
                .filter(|candidate| !cuts.iter().any(|cut| cut.dominates(candidate)))
                .sorted_by(|lhs, rhs| sort_first(self, lhs, rhs).then_with(|| sort_second(self, lhs, rhs)).then_with(|| sort_third(self, lhs, rhs)))
                .take(self.max_cuts)
                .cloned()
                .collect::<Vec<Cut>>();

                cut_count += cuts.len();

                self.cuts[node.index()] = cuts;

                let best_cut = &self.cuts[node.index()][0];

                self.depth[node.index()] = self.cut_depth(best_cut);
                self.area_flow[node.index()] = self.area_flow(best_cut);

                for input in &best_cut.inputs {
                    self.references[*input] += 1;
                }
            }
        }

        self.max_depth = *self.depth.iter().max().unwrap();

        println!("Found {} cuts", cut_count);
    }

    pub fn map_luts(&mut self, build_heights: bool) -> Vec<Cut> {
        let mut frontier = self.mig.graph().externals(Outgoing).flat_map(|output| self.mig.graph().neighbors_directed(output, Incoming)).collect::<Vec<_>>();
        let mut mapping = Vec::new();
        let mut mapped_nodes = Vec::new();
        let input_nodes = self.mig.input_nodes();
        let mut max_label = 0;
        let mut max_height = 0;

        if build_heights {
            for node in &frontier {
                self.height[node.index()] = 0;
            }
        }

        while let Some(node) = frontier.pop() {
            let cut = self.cuts[node.index()][0].clone();
            max_label = max_label.max(self.depth[node.index()]);
            max_height = max_height.max(self.height[node.index()]);

            for (index, input) in cut.inputs().filter(|node| node.index() != 0).enumerate() {
                if build_heights {
                    assert!(self.height[node.index()] >= 0);
                    self.height[input.index()] = self.height[input.index()].max(self.height[node.index()] + self.lut_delay[cut.input_count()][index] + self.wire_delay);
                    assert!(self.height[input.index()] > self.height[node.index()]);
                    assert!(self.height[input.index()] + self.depth[input.index()] <= self.max_depth);
                }
                if !mapped_nodes.contains(&input) && !input_nodes.contains(&input) {
                    frontier.push(input)
                }
            }

            mapped_nodes.push(NodeIndex::new(cut.output));
            mapping.push(cut);
        }

        println!("Mapped to {} LUTs", mapping.len());
        println!("Estimated area: {} units", mapping.iter().map(|cut| self.lut_area[cut.input_count()]).sum::<u32>());

        for i in 0..=self.max_inputs {
            println!("LUT{}: {}", i, mapping.iter().filter(|cut| cut.input_count() == i).count());
        }

        println!("Maximum delay: {}", max_label);
        println!("Maximum height: {}", max_height);

        assert_eq!(max_label - 1, max_height);

        mapping
    }
}