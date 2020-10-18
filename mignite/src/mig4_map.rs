use crate::mig4;

use itertools::Itertools;

#[derive(Clone, Debug, Hash, Eq, PartialEq)]
struct Cut {
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

    pub fn dominates(&self, rhs: &Self) -> bool {
        rhs.nodes.iter().all(|node| self.nodes.binary_search(node).is_ok())
    }
}

pub struct Mapper {
    max_cuts: usize,
    max_inputs: usize,
    mig: mig4::Mig,
    cuts: Vec<Vec<Cut>>,   
}

impl Mapper {
    pub fn new(max_cuts: usize, max_inputs: usize, mig: mig4::Mig) -> Self {
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
                    self.cuts[node.index()].push(Cut::new(vec![node.index()], node.index(), vec![node.index()]));
                }
                mig4::MigNode::Output(_) => {} // need to decide what to do here.
                mig4::MigNode::Majority => {
                    let mut cuts = Vec::new();
                    cuts.push(Cut::new(vec![node.index()], node.index(), vec![node.index()]));

                    let (x_edge, y_edge, z_edge) = self.mig.try_unwrap_majority(node).unwrap();
                    let x = self.mig.edge_source(x_edge);
                    let y = self.mig.edge_source(y_edge);
                    let z = self.mig.edge_source(z_edge);

                    for x_cut in &self.cuts[x.index()] {
                        for y_cut in &self.cuts[y.index()] {
                            for z_cut in &self.cuts[z.index()] {
                                let candidate = Cut::union(x_cut, y_cut, z_cut, node.index());
                                let dominated = cuts.iter().any(|cut| cut.dominates(&candidate));
                                if candidate.input_count() <= self.max_inputs && !dominated {
                                    cuts.push(candidate);
                                    cut_count += 1;
                                }

                                if cuts.len() == self.max_cuts {
                                    break;
                                }
                            }
                        }
                    }

                    self.cuts[node.index()] = cuts;
                }
            }
        }

        println!("Found {} cuts", cut_count);
    }
}