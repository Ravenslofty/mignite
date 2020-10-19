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
    pub fn trivial(node: usize) -> Self {
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

    #[must_use]
    pub fn dominates(&self, rhs: &Self) -> bool {
        rhs.nodes.iter().all(|node| self.nodes.binary_search(node).is_ok())
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
    mig: &'a mig4::Mig,
    cuts: Vec<Vec<Cut>>,
    label: Vec<i32>,
}

impl<'a> Mapper<'a> {
    #[must_use]
    pub fn new(max_cuts: usize, max_inputs: usize, mig: &'a mig4::Mig) -> Self {
        let len = mig.node_count();
        Self {
            max_cuts,
            max_inputs,
            mig,
            cuts: vec![Vec::new(); len],
            label: vec![-1000; len],
        }
    }

    pub fn compute_cuts(&mut self) {
        let mut iter = petgraph::visit::Topo::new(self.mig.graph());

        let mut cut_count = 0;

        while let Some(node) = iter.next(&self.mig.graph()) {
            if let Some((x_edge, y_edge, z_edge)) = self.mig.try_unwrap_majority(node) {
                let x = self.mig.edge_source(x_edge);
                let y = self.mig.edge_source(y_edge);
                let z = self.mig.edge_source(z_edge);

                if self.cuts[x.index()].is_empty() {
                    self.cuts[x.index()] = vec![Cut::trivial(x.index())];
                    self.label[x.index()] = 0;
                }

                if self.cuts[y.index()].is_empty() {
                    self.cuts[y.index()] = vec![Cut::trivial(y.index())];
                    self.label[y.index()] = 0;
                }

                if self.cuts[z.index()].is_empty() {
                    self.cuts[z.index()] = vec![Cut::trivial(z.index())];
                    self.label[z.index()] = 0;
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
                .chain(Some(cut))
                .filter(|candidate| candidate.input_count() <= self.max_inputs)
                .collect::<Vec<Cut>>();

                // Check for dominated cuts.
                let cuts = cuts.iter()
                .filter(|candidate| !cuts.iter().any(|cut| cut != *candidate && cut.dominates(candidate)))
                .sorted_by_key(|cut| cut.inputs.iter().map(|node| self.label[*node]).max().unwrap() + 1)
                .take(self.max_cuts)
                .cloned()
                .collect::<Vec<Cut>>();

                cut_count += cuts.len();

                self.cuts[node.index()] = cuts;
                self.label[node.index()] = self.cuts[node.index()][0].inputs.iter().map(|node| self.label[*node]).max().unwrap() + 1;
            }
        }

        println!("Found {} cuts", cut_count);
    }

    pub fn map_luts(&mut self) -> Vec<Cut> {
        let mut frontier = self.mig.graph().externals(Outgoing).flat_map(|output| self.mig.graph().neighbors_directed(output, Incoming)).collect::<Vec<_>>();
        let mut mapping = Vec::new();
        let mut mapped_nodes = Vec::new();
        let input_nodes = self.mig.input_nodes();
        let mut max_label = 0;

        while let Some(node) = frontier.pop() {
            let cut = self.cuts[node.index()][0].clone();
            max_label = max_label.max(self.label[node.index()]);

            for input in cut.inputs() {
                if !mapped_nodes.contains(&input) && !input_nodes.contains(&input) {
                    frontier.push(input)
                }
            }

            mapped_nodes.push(NodeIndex::new(cut.output));
            mapping.push(cut);
        }

        println!("Mapped to {} LUTs", mapping.len());
        println!("Maximum label: {}", max_label);

        mapping
    }
}