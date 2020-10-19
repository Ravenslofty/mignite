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
    pub fn new(inputs: Vec<usize>, output: usize, nodes: Vec<usize>) -> Self {
        assert!((0..inputs.len() - 1).all(|i| inputs[i] <= inputs[i + 1]));
        assert!((0..nodes.len() - 1).all(|i| nodes[i] <= nodes[i + 1]));
        Self { inputs, output, nodes }
    }

    pub fn input_count(&self) -> usize {
        if self.inputs.contains(&0) {
            self.inputs.len() - 1
        } else {
            self.inputs.len()
        }
    }

    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

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

    /*
    pub fn expand(&self, node: u32) -> Cut {
        assert!(self.inputs.contains(node));
        let inputs = ();
        Self {
            inputs,
            output,
            nodes,
        }
    }*/

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
    cuts: Vec<Vec<(Cut, i32)>>,
}

impl<'a> Mapper<'a> {
    pub fn new(max_cuts: usize, max_inputs: usize, mig: &'a mig4::Mig) -> Self {
        let len = mig.node_count();
        Self {
            max_cuts,
            max_inputs,
            mig,
            cuts: vec![Vec::new(); len],
        }
    }

    pub fn compute_cuts(&mut self) {
        let mut iter = petgraph::visit::Topo::new(self.mig.graph());

        let mut cut_count = 0;

        while let Some(node) = iter.next(&self.mig.graph()) {
            match self.mig.node_type(node) {
                mig4::MigNode::Input(_) | mig4::MigNode::Zero => {
                    let cut = Cut::new(vec![node.index()], node.index(), vec![node.index()]);
                    self.cuts[node.index()].push((cut, 0));
                },
                mig4::MigNode::Output(_) => {
                    let mut cuts = Vec::with_capacity(self.max_cuts);
                    let mut inputs = self.mig.graph().neighbors_directed(node, Incoming).detach();
                    let mut input_list = Vec::new();
                    let mut max_label = 0;

                    while let Some((edge, input)) = inputs.next(self.mig.graph()) {
                        input_list.push(input.index());
                        for (cut, label) in &self.cuts[input.index()] {
                            let inputs = cut.inputs.clone();
                            let input = node.index();
                            let nodes = cut.nodes.iter().merge(&[cut.output]).dedup().copied().collect::<Vec<_>>();
                            let cut = Cut::new(inputs, input, nodes);
                            max_label = max_label.max(*label);
                            cuts.push((cut, *label + 1));
                        }
                    }

                    let nodes = input_list.iter().merge(&[node.index()]).dedup().copied().collect();
                    let cut = Cut::new(input_list, node.index(), nodes);
                    cuts.push((cut, max_label + 1));

                    self.cuts[node.index()] = cuts;
                },
                mig4::MigNode::Majority => {
                    let mut cuts: Vec<(Cut, i32)> = Vec::with_capacity(self.max_cuts);
                    let mut max_label = 0;

                    let (x_edge, y_edge, z_edge) = self.mig.try_unwrap_majority(node).unwrap();
                    let x = self.mig.edge_source(x_edge);
                    let y = self.mig.edge_source(y_edge);
                    let z = self.mig.edge_source(z_edge);

                    for (x_cut, x_label) in &self.cuts[x.index()] {
                        for (y_cut, y_label) in &self.cuts[y.index()] {
                            for (z_cut, z_label) in &self.cuts[z.index()] {
                                let candidate = Cut::union(x_cut, y_cut, z_cut, node.index());
                                let dominated = cuts.iter().any(|cut| cut.0.dominates(&candidate));
                                if candidate.input_count() <= self.max_inputs && !dominated {
                                    let label = x_label.max(y_label).max(z_label);
                                    cuts.push((candidate, label + 1));
                                    cut_count += 1;
                                    max_label = max_label.max(*label);
                                }
                            }
                        }
                    }

                    let cut = Cut::new(vec![x.index(), y.index(), z.index()], node.index(), vec![x.index(), y.index(), z.index(), node.index()]);
                    cuts.push((cut, max_label + 1));

                    cuts.sort_by(|lhs, rhs| lhs.1.cmp(&rhs.1));

                    self.cuts[node.index()] = cuts.iter().take(self.max_cuts).cloned().collect::<Vec<_>>();
                }
            }
        }

        println!("Found {} cuts", cut_count);
    }

    pub fn compute_cuts_taiga(&mut self) {
        todo!()
    }

    pub fn map_luts(&mut self) -> Vec<Cut> {
        let mut frontier = self.mig.graph().externals(Outgoing).collect::<Vec<_>>();
        let mut mapping = Vec::new();
        let mut mapped_nodes = Vec::new();
        let input_nodes = self.mig.input_nodes();
        let mut max_label = 0;

        while let Some(node) = frontier.pop() {
            let (cut, label) = self.cuts[node.index()][0].clone();

            max_label = max_label.max(label);

            //dbg!(&cut);

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