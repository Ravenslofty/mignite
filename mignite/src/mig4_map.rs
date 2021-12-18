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
        assert!(nodes.len() == 1 || !inputs.contains(&output));
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
    required: Vec<i32>,
    area_flow: Vec<f32>,
    edge_flow: Vec<f32>,
    references: Vec<u32>,
}

impl<'a> Mapper<'a> {
    #[must_use]
    pub fn new(max_cuts: usize, max_inputs: usize, lut_area: &'a [u32], lut_delay: &'a [&'a [i32]], wire_delay: i32, mig: &'a mig4::Mig) -> Self {
        assert!(!petgraph::algo::is_cyclic_directed(mig.graph()));

        let len = mig.graph().node_indices().map(|node| node.index()).max().unwrap() + 1;
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
            required: vec![-1; len],
            area_flow: vec![0.0; len],
            edge_flow: vec![0.0; len],
            references: vec![0; len],
        }
    }

    #[must_use]
    #[inline]
    pub fn cut_depth(&self, cut: &Cut) -> i32 {
        cut.inputs.iter().filter(|node| **node != 0).sorted_by_key(|node| self.depth[**node]).rev().enumerate().map(|(index, node)| {
            self.depth[*node] + self.lut_delay[cut.input_count()][index]
        }).max().unwrap_or(0) + self.wire_delay
    }

    #[must_use]
    #[inline]
    pub fn area_flow(&self, cut: &Cut) -> f32 {
        (cut.inputs.iter().map(|node| self.area_flow[*node]).sum::<f32>() + self.lut_area[cut.input_count()] as f32) / (self.references[cut.output].min(1) as f32)
    }

    #[must_use]
    #[inline]
    pub fn edge_flow(&self, cut: &Cut) -> f32 {
        (cut.inputs.iter().map(|node| self.edge_flow[*node]).sum::<f32>() + cut.input_count() as f32) / (self.references[cut.output].min(1) as f32)
    }

    #[must_use]
    #[inline]
    pub fn exact_area(&mut self, cut: &Cut) -> u32 {
        let references = self.references.clone();
        if let Some(repr_cut) = self.cuts[cut.output].first() {
            if cut == repr_cut {
                let area2 = self.exact_area_ref(cut);
                let area1 = self.exact_area_deref(cut);
                //assert_eq!(area1, area2);
                self.references = references;
                return area1;
            }
        }

        let area1 = self.exact_area_deref(cut);
        let area2 = self.exact_area_ref(cut);
        //assert_eq!(area1, area2);
        self.references = references;
        area1
    }

    fn exact_area_deref(&mut self, cut: &Cut) -> u32 {
        let mut area = self.lut_area[cut.input_count()];
        for input in &cut.inputs {
            if !self.mig.input_nodes().contains(&NodeIndex::new(*input)) && self.references[*input] >= 1 {
                assert!(self.references[*input] >= 1, "reference count of {} is zero before decrementing", *input);
                self.references[*input] -= 1;
                if self.references[*input] == 0 {
                    area += self.exact_area_deref(&self.cuts[*input][0].clone());
                }
            }
        }
        area
    }

    fn exact_area_ref(&mut self, cut: &Cut) -> u32 {
        let mut area = self.lut_area[cut.input_count()];
        for input in &cut.inputs {
            if !self.mig.input_nodes().contains(&NodeIndex::new(*input)) {
                if self.references[*input] == 0 {
                    area += self.exact_area_ref(&self.cuts[*input][0].clone());
                }
                self.references[*input] += 1;
            }
        }
        area
    }

    #[must_use]
    #[inline]
    pub fn exact_edge(&mut self, cut: &Cut) -> usize {
        let references = self.references.clone();
        if let Some(repr_cut) = self.cuts[cut.output].first() {
            if cut == repr_cut {
                let area2 = self.exact_edge_deref(cut);
                let area1 = self.exact_edge_ref(cut);
                self.references = references;
                //assert_eq!(area1, area2);
                return area1;
            }
        }

        let area1 = self.exact_edge_ref(cut);
        //let area2 = self.exact_edge_deref(cut);
        self.references = references;
        //assert_eq!(area1, area2);
        area1
    }

    fn exact_edge_deref(&mut self, cut: &Cut) -> usize {
        let mut area = cut.input_count();
        for input in &cut.inputs {
            if !self.mig.input_nodes().contains(&NodeIndex::new(*input)) && self.references[*input] >= 1 {
                assert!(self.references[*input] >= 1, "reference count of {} is zero before decrementing", *input);
                self.references[*input] -= 1;
                if self.references[*input] == 0 {
                    area += self.exact_edge_deref(&self.cuts[*input][0].clone());
                }
            }
        }
        area
    }

    fn exact_edge_ref(&mut self, cut: &Cut) -> usize {
        let mut area = cut.input_count();
        for input in &cut.inputs {
            if !self.mig.input_nodes().contains(&NodeIndex::new(*input)) {
                if self.references[*input] == 0 {
                    area += self.exact_edge_ref(&self.cuts[*input][0].clone());
                }
                self.references[*input] += 1;
            }
        }
        area
    }

    #[must_use]
    #[inline]
    pub fn cut_rank_depth(&mut self, lhs: &Cut, rhs: &Cut) -> Ordering {
        let lhs = self.cut_depth(lhs);
        let rhs = self.cut_depth(rhs);
        lhs.cmp(&rhs)
    }

    #[must_use]
    #[inline]
    pub fn cut_rank_size(&mut self, lhs: &Cut, rhs: &Cut) -> Ordering {
        let lhs = lhs.input_count();
        let rhs = rhs.input_count();
        lhs.cmp(&rhs)
    }

    #[must_use]
    #[inline]
    pub fn cut_rank_area_flow(&mut self, lhs: &Cut, rhs: &Cut) -> Ordering {
        let lhs = self.area_flow(lhs);
        let rhs = self.area_flow(rhs);
        lhs.partial_cmp(&rhs).unwrap()
    }

    #[must_use]
    #[inline]
    pub fn cut_rank_edge_flow(&mut self, lhs: &Cut, rhs: &Cut) -> Ordering {
        let lhs = self.edge_flow(lhs);
        let rhs = self.edge_flow(rhs);
        lhs.partial_cmp(&rhs).unwrap()
    }

    #[must_use]
    #[inline]
    pub fn cut_rank_fanin_refs(&mut self, lhs: &Cut, rhs: &Cut) -> Ordering {
        let lhs = lhs.inputs.iter().map(|node| self.references[*node]).sum::<u32>() / (lhs.inputs.len() as u32);
        let rhs = rhs.inputs.iter().map(|node| self.references[*node]).sum::<u32>() / (rhs.inputs.len() as u32);
        lhs.cmp(&rhs)
    }

    #[must_use]
    #[inline]
    pub fn cut_rank_exact_area(&mut self, lhs: &Cut, rhs: &Cut) -> Ordering {
        let lhs = self.exact_area(lhs);
        let rhs = self.exact_area(rhs);
        lhs.cmp(&rhs)
    }

    #[must_use]
    #[inline]
    pub fn cut_rank_exact_edge(&mut self, lhs: &Cut, rhs: &Cut) -> Ordering {
        let lhs = self.exact_edge(lhs);
        let rhs = self.exact_edge(rhs);
        lhs.cmp(&rhs)
    }

    #[allow(clippy::missing_panics_doc)]
    pub fn compute_cuts<F1, F2, F3>(&mut self, sort_first: F1, sort_second: F2, sort_third: F3)
    where F1: Fn(&mut Self, &Cut, &Cut) -> Ordering, F2: Fn(&mut Self, &Cut, &Cut) -> Ordering, F3: Fn(&mut Self, &Cut, &Cut) -> Ordering
    {
        for node in self.mig.graph().node_indices() {
            self.depth[node.index()] = -1000;
            self.area_flow[node.index()] = 0.0;
            self.edge_flow[node.index()] = 0.0;
            self.references[node.index()] = 0;
        }

        for node in self.mig.input_nodes() {
            self.cuts[node.index()] = vec![Cut::single_node(node.index())];
            self.depth[node.index()] = 0;
            self.area_flow[node.index()] = 0.0;
            self.edge_flow[node.index()] = 0.0;
        }

        for node in self.mig.graph().externals(Outgoing) {
            if let mig4::MigNode::Output(node) = self.mig.graph()[node] {
                self.references[node as usize] = 1;
            }
        }

        let mut iter = petgraph::visit::Topo::new(self.mig.graph());

        let mut cut_count = 0;

        while let Some(node) = iter.next(&self.mig.graph()) {
            if let Some((x_edge, y_edge, z_edge)) = self.mig.try_unwrap_majority(node) {
                let x = self.mig.edge_source(x_edge);
                let y = self.mig.edge_source(y_edge);
                let z = self.mig.edge_source(z_edge);

                // Compute the trivial cut of this node.
                //let mut inputs = vec![x.index(), y.index(), z.index()];
                //let mut nodes = vec![x.index(), y.index(), z.index(), node.index()];
                let mut inputs = vec![node.index()];
                let mut nodes = vec![node.index()];
                //inputs.sort_unstable();
                //nodes.sort_unstable();
                let cut = Cut::new(inputs, node.index(), nodes);

                let max_inputs = self.max_inputs;
                let required = self.required[node.index()];

                let cuts = self.cuts[x.index()].iter()
                .cartesian_product(&self.cuts[y.index()])
                .cartesian_product(&self.cuts[z.index()])
                .map(|((x_cut, y_cut), z_cut)| Cut::union(x_cut, y_cut, z_cut, node.index()))
                .chain(self.cuts[node.index()].first().cloned())
                .filter(|candidate| candidate.input_count() <= max_inputs)
                .filter(|candidate| required < 0 || self.cut_depth(candidate) <= required)
                .collect_vec();

                let mut cuts = cuts.into_iter()
                .sorted_by(|lhs, rhs| sort_first(self, lhs, rhs).then_with(|| sort_second(self, lhs, rhs)).then_with(|| sort_third(self, lhs, rhs)))
                .dedup()
                .take(self.max_cuts)
                .collect_vec();

                cuts.push(cut);

                assert!(!cuts.is_empty());

                cut_count += cuts.len();

                self.cuts[node.index()] = cuts;
                let best_cut = &self.cuts[node.index()][0];

                for input in &best_cut.inputs {
                    self.references[*input] += 1;
                    self.area_flow[*input] = self.area_flow(&self.cuts[*input][0]);
                    self.edge_flow[*input] = self.edge_flow(&self.cuts[*input][0]);
                }

                self.depth[node.index()] = self.cut_depth(best_cut);
                self.area_flow[node.index()] = self.area_flow(best_cut);
                self.edge_flow[node.index()] = self.edge_flow(best_cut);

                self.max_depth = self.max_depth.max(self.depth[node.index()]);
            }
        }

        println!("Found {} cuts", cut_count);
    }

    #[allow(clippy::missing_panics_doc)]
    pub fn map_luts(&mut self, print_stats: bool) -> Vec<Cut> {
        let mut frontier = self.mig.graph()
            .externals(Outgoing)
            .flat_map(|output| self.mig.graph().neighbors_directed(output, Incoming))
            .filter(|node| self.mig.node_type(*node) == mig4::MigNode::Majority)
            .collect::<Vec<_>>();
        let mut mapping = Vec::new();
        let mut mapped_nodes = Vec::new();
        let input_nodes = self.mig.input_nodes();

        while let Some(node) = frontier.pop() {
            let cut = &self.cuts[node.index()][0];
            for input in cut.inputs().filter(|node| node.index() != 0) {
                if !mapped_nodes.contains(&input) && !input_nodes.contains(&input) {
                    frontier.push(input);
                }
            }

            mapped_nodes.push(NodeIndex::new(cut.output));
            mapping.push(cut.clone());
        }

        if print_stats {
            println!("Mapped to {} LUTs", mapping.len());
            println!("Estimated area: {} units", mapping.iter().map(|cut| self.lut_area[cut.input_count()]).sum::<u32>());

            for i in 1..=self.max_inputs {
                println!("LUT{}: {}", i, mapping.iter().filter(|cut| cut.input_count() == i).count());
            }

            println!("Maximum delay: {}", self.max_depth);
        }

        for node in self.mig.graph().node_indices() {
            self.required[node.index()] = self.max_depth;
        }

        let mut required_dfs = petgraph::visit::DfsPostOrder::empty(self.mig.graph());
        let pis = self.mig.input_nodes();
        for pi in pis {
            required_dfs.move_to(pi);
            while let Some(node) = required_dfs.next(self.mig.graph()) {
                if let Some(cut) = self.cuts[node.index()].first() {
                    let required = self.required[node.index()] - self.wire_delay;
                    for (index, input) in cut.inputs().filter(|node| node.index() != 0).sorted_by_key(|node| self.depth[node.index()]).rev().enumerate() {
                        if input.index() != node.index() {
                            self.required[input.index()] = self.required[input.index()].min(required - self.lut_delay[cut.input_count()][index]);
                            assert!(self.required[input.index()] >= 0, "node {} has negative required time of {}", input.index(), self.required[input.index()]);
                        }
                    }
                }
            }
        }

        mapping
    }
}