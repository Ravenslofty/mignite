use aiger::Literal;

/// Utilities for working with majority-inverter graphs.
///
/// Majority-inverter graphs represent boolean logic graphs as a combination of three-input majority gates and
/// inverters (NOT gates). These two gates are enough to represent any logic function (i.e. they are universal).
///
/// The choice of a three-input majority gate as a representation might seem odd, but it has useful properties.
/// A majority gate can be considered as an AND of two of its inputs if the third input is zero, since both inputs
/// would have to be true for the majority to be true. It can also be considered as an OR gate if the third gate is
/// one, since only one input needs to be true for the majority to be true. However, since it can compute the majority
/// of its inputs, it is more powerful than the combination of AND/OR.
///
/// Additionally, majority gates can be used for error tolerance. For example, a tree can be triplicated into three
/// segments connected to a majority gate, and each segment can make an overly-general assumption (a logic error).
/// Provided that these logic errors do not overlap (i.e. that only one segment produces a wrong result given the
/// inputs), the result of the majority gate will still be correct. This can provide major logic savings.
///
/// A three input majority gate will be notated as `M(x, y, z)`, and the inversion of `x` as `x'`.
///
/// Majority logic has five main axioms:
/// - Commutativity: permuting the inputs does not change the result, because majority gates are order-insensitive.
/// - Majority: if a gate has two identical input terms, the gate can be replaced with that term, because that term 
///   decides the gate output.
///   Likewise, if a gate has a term and its inversion as inputs, then the gate can be replaced with the third input,
///   because the third input term decides the gate output.
/// - Associativity: a term in a child gate can be swapped with a term in its parent without changing the result.
/// - Distributivity: input terms can be pushed down a level without changing the result.
/// - Inverter Propagation: a gate with three inverted input terms can move the inverter to its output.

/// A majority-inverter graph.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct Mig {
    pub graph: Vec<MigNode>,
    pub parents: Vec<Vec<usize>>,
    inputs: Vec<usize>,
    outputs: Vec<usize>,
    zero: usize,
    one: usize,
}

impl Mig {
    /// Create a new majority-inverter graph.
    #[must_use]
    pub fn new() -> Self {
        let graph = vec![
            MigNode::Zero(Zero()),
            MigNode::Inverter(Inverter(0))
        ];
        let parents = vec![
            vec![0],
            vec![],
        ];
        Self {
            graph,
            parents,
            inputs: Vec::new(),
            outputs: Vec::new(),
            zero: 0,
            one: 1,
        }
    }

    pub fn from_aiger(path: &str) -> Self {
        let file = std::fs::File::open(path).unwrap();
        let reader = aiger::Reader::from_reader(file).unwrap();
        let mut mig = Self::new();

        let header = reader.header();

        mig.graph.reserve_exact(header.m);

        for _ in 0..header.i {
            let _ = mig.push_input();
        }

        for _ in 0..header.l {
            todo!("AIG has flops");
        }

        for _ in 0..header.o {
            let _ = mig.push_output(mig.zero);
        }

        for _ in 0..header.a {
            let _ = mig.push_majority(mig.zero, mig.zero, mig.zero);
        }

        let mut outputs = Vec::new();

        for record in reader.records() {
            match record.unwrap() {
                aiger::Aiger::Input(Literal(input)) => {
                    mig.parents[input].clear();
                }
                aiger::Aiger::Latch { output: _, input: _ } => {
                    todo!("latches");
                }
                aiger::Aiger::Output(Literal(output)) => {
                    outputs.push(output);

                    mig.parents[output].clear();
                }
                aiger::Aiger::AndGate { output, inputs } => {
                    let Literal(output) = output;
                    let Literal(mut input0) = inputs[0];
                    let Literal(mut input1) = inputs[1];

                    match mig.graph[input0] {
                        MigNode::Input(_) => {}
                        MigNode::Output(Output(_index, input)) => {
                            input0 = input;
                        }
                        MigNode::Zero(_) => {}
                        MigNode::Inverter(_) => {}
                        MigNode::Majority(_) => {}
                    }

                    match mig.graph[input1] {
                        MigNode::Input(_) => {}
                        MigNode::Output(Output(_index, input)) => {
                            input1 = input;
                        }
                        MigNode::Zero(_) => {}
                        MigNode::Inverter(_) => {}
                        MigNode::Majority(_) => {}
                    }

                    match mig.graph[output] {
                        MigNode::Input(_) => panic!("overwrote input"),
                        MigNode::Output(Output(index, _input)) => {
                            let (x, x_bar) = mig.push_majority(input0, input1, mig.zero);
                            mig.parents[input0].push(x);
                            mig.parents[input1].push(x);
                            mig.graph[output] = MigNode::Output(Output(index, x));
                            mig.graph[output + 1] = MigNode::Output(Output(index, x_bar));
                        },
                        MigNode::Zero(_) => panic!("overwrote constant"),
                        MigNode::Inverter(_) => panic!("overwrote inverter"),
                        MigNode::Majority(_) => {
                            mig.graph[output] = MigNode::Majority(Majority(input0, input1, mig.zero));
                            mig.parents[input0].push(output);
                            mig.parents[input1].push(output);
                        }
                    }
                }
            }
        }

        mig.outputs = outputs;

        mig
    }

    pub fn count_nodes(&self) -> usize {
        fn count(graph: &[MigNode], visited: &mut [bool], root: usize) -> usize {
            match graph[root] {
                MigNode::Input(_) | MigNode::Zero(_) => 0,
                MigNode::Output(Output(_index, input)) => {
                    count(graph, visited, input)
                }
                MigNode::Inverter(Inverter(input)) => {
                    count(graph, visited, input)
                }
                MigNode::Majority(Majority(input0, input1, input2)) => {
                    if visited[root] {
                        0
                    } else {
                        visited[root] = true;
                        count(graph, visited, input0) +
                        count(graph, visited, input1) +
                        count(graph, visited, input2) + 1
                    }
                }
            }
        }

        let mut visited = vec![false; self.graph.len()];

        let sum = self.outputs
        .clone()
        .into_iter()
        .map(|output| {
            count(&self.graph, &mut visited, output)
        })
        .sum();

        sum
    }

    pub fn print_graph(&self) {
        fn count(graph: &[MigNode], visited: &mut [bool], root: usize) {
            match graph[root] {
                MigNode::Input(Input(index)) => {},
                MigNode::Zero(Zero()) => {},
                MigNode::Output(Output(_index, input)) => {
                    println!("{} -> {} {};", input & !1, root & !1, if input & 1 == 1 { "[dir=both, arrowtail=odot]" } else { "" });
                    count(graph, visited, input);
                }
                MigNode::Inverter(Inverter(input)) => {
                    if input & !1 != root & !1 {
                        println!("{} -> {} [dir=both, arrowtail=odot];", input & !1, root & !1);
                    }
                    count(graph, visited, input);
                }
                MigNode::Majority(Majority(input0, input1, input2)) => {
                    if !visited[root] {
                        println!("{} [label=\"Majority {0}\"];", root);
                        if input0 & !1 != 0 {
                            println!("{} -> {} {};", input0 & !1, root & !1, if input0 & 1 == 1 { "[dir=both, arrowtail=odot]" } else { "" });
                        } else {
                            println!("z{} [label=\"Zero\"]", root);
                            println!("z{} -> {} {};", root, root & !1, if input0 & 1 == 1 { "[dir=both, arrowtail=odot]" } else { "" });
                        }
                        if input1 & !1 != 0 {
                            println!("{} -> {} {};", input1 & !1, root & !1, if input1 & 1 == 1 { "[dir=both, arrowtail=odot]" } else { "" });
                        } else {
                            println!("z{} [label=\"Zero\"]", root);
                            println!("z{} -> {} {};", root, root & !1, if input1 & 1 == 1 { "[dir=both, arrowtail=odot]" } else { "" });
                        }
                        if input2 & !1 != 0 {
                            println!("{} -> {} {};", input2 & !1, root & !1, if input2 & 1 == 1 { "[dir=both, arrowtail=odot]" } else { "" });
                        } else {
                            println!("z{} [label=\"Zero\"]", root);
                            println!("z{} -> {} {};", root, root & !1, if input2 & 1 == 1 { "[dir=both, arrowtail=odot]" } else { "" });
                        }
                        visited[root] = true;
                        count(graph, visited, input0);
                        count(graph, visited, input1);
                        count(graph, visited, input2);
                    }
                }
            }
        }

        let mut visited = vec![false; self.graph.len()];

        println!("digraph {{");

        for input in self.inputs.iter() {
            println!("{} [shape=box,color=blue,label=\"Input {0}\"];", input);
        }

        for output in self.outputs.iter() {
            println!("{} [shape=box,color=green,label=\"Output {0}\"];", output)
        }

        self.outputs
        .clone()
        .into_iter()
        .for_each(|output| {
            count(&self.graph, &mut visited, output)
        });

        println!("}}");
    }

    /// Replace all references of `from` with references to `to`.
    pub fn replace_all(&mut self, from: usize, to: usize) {
        for parent in self.parents[from].clone() {
            match &mut self.graph[parent] {
                MigNode::Input(_) => panic!("input nodes cannot be parents"),
                MigNode::Output(Output(_index, input)) => {
                    *input = to;
                    self.parents[to].push(parent);
                },
                MigNode::Zero(_) => panic!("constant nodes cannot be parents"),
                MigNode::Inverter(Inverter(input)) => {
                    *input = to;
                    self.parents[to].push(parent);
                }
                MigNode::Majority(Majority(x, y, z)) => {
                    if *x == from {
                        *x = to;
                        self.parents[to].push(parent);
                    }
                    if *y == from {
                        *y = to;
                        self.parents[to].push(parent);
                    }
                    if *z == from {
                        *z = to;
                        self.parents[to].push(parent);
                    }
                }
            }
        }
        self.parents[from].clear();
    }

    /// Replace all references of `from` with references to `to` in the children of `node`.
    pub fn replace_children(&mut self, node: usize, from: usize, to: usize) -> bool {
        let mut did_something = false;
        match &mut self.graph[node] {
            MigNode::Input(Input(_index)) => {},
            MigNode::Output(Output(_index, input)) => {
                if *input == from {
                    *input = to;
                    did_something = true;
                }
            },
            MigNode::Zero(Zero()) => {},
            MigNode::Inverter(Inverter(input)) => {
                if *input == from {
                    *input = to;
                    did_something = true;
                }
            },
            MigNode::Majority(Majority(x, y, z)) => {
                if *x == from {
                    *x = to;
                    did_something = true;
                }
                if *y == from {
                    *y = to;
                    did_something = true;
                }
                if *z == from {
                    *z = to;
                    did_something = true;
                }
            }
        }

        match self.graph[node] {
            MigNode::Input(Input(_index)) => {},
            MigNode::Output(Output(_index, _input)) => {},
            MigNode::Zero(Zero()) => {},
            MigNode::Inverter(Inverter(input)) => {
                did_something |= self.replace_children(input, from, to);
            },
            MigNode::Majority(Majority(x, y, z)) => {
                did_something |= self.replace_children(x, from, to);
                did_something |= self.replace_children(y, from, to);
                did_something |= self.replace_children(z, from, to);
            }
        }
        did_something
    }

    /// Append an Input to the graph, returning an (input, input') pair.
    #[must_use]
    pub fn push_input(&mut self) -> (usize, usize) {
        self.graph.push(MigNode::Input(Input(self.inputs.len())));
        self.graph.push(MigNode::Inverter(Inverter(self.graph.len() - 1)));
        self.parents.push(Vec::new());
        self.parents.push(Vec::new());
        self.parents[self.graph.len() - 2].push(self.graph.len() - 1);
        self.inputs.push(self.graph.len() - 2);
        (self.graph.len() - 2, self.graph.len() - 1)
    }

    /// Append an Output to the graph. Returns (input, input') pair.
    #[must_use]
    pub fn push_output(&mut self, input: usize) -> (usize, usize) {
        self.graph.push(MigNode::Output(Output(self.outputs.len(), input)));
        self.graph.push(MigNode::Output(Output(self.outputs.len(), input ^ 1)));
        self.parents.push(Vec::new());
        self.parents.push(Vec::new());
        self.parents[input].push(self.graph.len() - 2);
        self.parents[self.graph.len() - 2].push(self.graph.len() - 1);
        self.outputs.push(self.graph.len() - 2);
        self.outputs.push(self.graph.len() - 1);
        (self.graph.len() - 2, self.graph.len() - 1)
    }

    /// Append a 3-input majority gate to the graph. Returns (output, output')
    #[must_use]
    pub fn push_majority(&mut self, input0: usize, input1: usize, input2: usize) -> (usize, usize) {
        self.graph.push(MigNode::Majority(Majority(input0, input1, input2)));
        self.graph.push(MigNode::Inverter(Inverter(self.graph.len() - 1)));
        self.parents.push(Vec::new());
        self.parents.push(Vec::new());
        self.parents[input0].push(self.graph.len() - 2);
        self.parents[input1].push(self.graph.len() - 2);
        self.parents[input2].push(self.graph.len() - 2);
        self.parents[self.graph.len() - 2].push(self.graph.len() - 1);
        (self.graph.len() - 2, self.graph.len() - 1)
    }

    /// Apply a function while traversing a tree left to right.
    pub fn visit_left_to_right<F: FnMut(&mut Mig, usize) + Copy>(&mut self, root: usize, mut f: F) {
        match self.graph[root] {
            MigNode::Input(_) | MigNode::Output(_) | MigNode::Zero(_) => {},
            MigNode::Inverter(Inverter(input)) => {
                self.visit_left_to_right(input, f);
                f(self, root);
            }
            MigNode::Majority(Majority(input0, input1, input2)) => {
                self.visit_left_to_right(input0, f);
                self.visit_left_to_right(input1, f);
                self.visit_left_to_right(input2, f);
                f(self, root);
            }
        }
    }

    /// Apply a function while traversing a tree right to left.
    pub fn visit_right_to_left(&mut self, root: usize, f: fn(&mut Mig, usize)) {
        match self.graph[root] {
            MigNode::Input(_) | MigNode::Output(_) | MigNode::Zero(_) => {},
            MigNode::Inverter(Inverter(input)) => {
                self.visit_right_to_left(input, f);
                f(self, root);
            }
            MigNode::Majority(Majority(input0, input1, input2)) => {
                self.visit_right_to_left(input2, f);
                self.visit_right_to_left(input1, f);
                self.visit_right_to_left(input0, f);
                f(self, root);
            }
        }
    }

    /// Transform `M(x, x, y)` to `x`, and `M(x, x', y)` to `y` using the majority axiom. Returns true if transformation succeeded.
    pub fn transform_majority(&mut self, root: usize) {
        // TODO: this rule can apply for "equivalent" nodes, rather than just "identical" nodes.
        let majority_same = |mig: &mut Mig, root: usize, x: usize, y: usize, z: usize| -> Option<()> {
            if x == y {
                mig.replace_all(root, x);
                eprintln!("{} as M({}, {}, {}) => {} (majority-same)", root, x, y, z, z);
                Some(())
            } else {
                None
            }
        };

        let majority_different = |mig: &mut Mig, root: usize, x: usize, y: usize, z: usize| -> Option<()> {
            let y = mig.graph[y].try_unwrap_inverter()?;
            if x == y {
                mig.replace_all(root, z);
                eprintln!("{} as M({}, {}, {}) => {} (majority-different)", root, x, y ^ 1, z, z);
                Some(())
            } else {
                None
            }
        };

        if let MigNode::Majority(node) = self.graph[root] {
            node.apply(root, self, majority_same);
            node.apply(root, self, majority_different);
        }
    }

    /// Transform `M(x, u, M(y, u, z))` to `M(z, u, M(y, u, x))`
    pub fn transform_associativity(&mut self, root: usize) {
        let associativity = |mig: &mut Mig, root: usize, x1: usize, u1: usize, b: usize| -> Option<()> {
            let (_y, u2, z) = mig.graph[b].try_unwrap_majority()?;

            if u1 == u2 {
                let (x, _u, _b) = mig.graph[root].try_unwrap_majority_mut()?;
                *x = z;
                
                let (_y, _u, z) = mig.graph[b].try_unwrap_majority_mut()?;
                *z = x1;

                Some(())
            } else {
                None
            }
        };

        if let MigNode::Majority(node) = self.graph[root] {
            node.apply(root, self, associativity);
        }
    }

    /// Transform `M(x, y, M(u, v, z))` into `M(M(x, y, u), M(x, y, v), z)`. Returns true if transformation succeeded.
    #[allow(clippy::many_single_char_names)] // I think the graphs make it clear enough.
    pub fn transform_distributivity(&mut self, root: usize) {
        let distributivity = |mig: &mut Mig, root: usize, x: usize, y: usize, b: usize| -> Option<()> {
            //    a
            //  / | \
            // x  y  b
            //     / | \
            //    u  v  z
            let (u, _v, z1) = mig.graph[b].try_unwrap_majority()?;
            let (c, _) = mig.push_majority(x, y, u);

            //   a
            // / | \     
            // x y b      c
            //   / | \  / | \
            //   u v z  x y u

            let (u, _v, z) = mig.graph[z1].try_unwrap_majority_mut()?;
            *u = x;
            *z = y;

            //   a
            // / | \     
            // x y b      c
            //   / | \  / | \
            //   x v y  x y u

            let (x, y, _b) = mig.graph[root].try_unwrap_majority_mut()?;
            *x = c;
            *y = z1;

            //      a
            //    / | \
            //   c  z  b
            // / | \ / | \
            // x y u x v y

            Some(())
        };

        if let MigNode::Majority(node) = self.graph[root] {
            node.apply(root, self, distributivity);
        }
    }

    /// Rename all instances of `x` with `y'` in `M(x, y, z)`
    pub fn transform_relevance(&mut self, root: usize) {
        let relevance = |mig: &mut Mig, _root: usize, x: usize, y: usize, z: usize| -> Option<()> {
            let y_bar = y ^ 1;
            mig.replace_children(z, x, y_bar);
            Some(())
        };

        if let MigNode::Majority(node) = self.graph[root] {
            node.apply(root, self, relevance);
        }
    }

    /// Transform `M(x, u, M(y, u', z))` to `M(x, u, M(y, x, z))`.
    pub fn transform_compassoc(&mut self, root: usize) {
        let complementary_associativity = |mig: &mut Mig, _root: usize, x: usize, u1: usize, b: usize| -> Option<()> {
            let (_y, u2, _z) = mig.graph[b].try_unwrap_majority()?;
            let u3 = mig.graph[u2].try_unwrap_inverter()?;
            if u1 == u3 {
                let (_y, u2, _z) = mig.graph[b].try_unwrap_majority_mut()?;
                *u2 = x;
                Some(())
            } else {
                None
            }
        };

        if let MigNode::Majority(node) = self.graph[root] {
            node.apply(root, self, complementary_associativity);
        }
    }

    pub fn transform_substitution(&mut self, root: usize) {
        let substitution = |mig: &mut Mig, root: usize, x: usize, y: usize, z: usize| -> Option<()> {
            todo!()
        };
    }

    pub fn optimise_size(&mut self, effort: usize) {
        let outputs = self.outputs.clone();
        eprintln!("node is {} bytes", std::mem::size_of::<MigNode>());
        for iter in 0..effort {
            for (n, output) in outputs.iter().enumerate() {
                eprintln!("iter {}.{}: graph has {} gates out of {} nodes", iter, n, self.count_nodes(), self.graph.len());
                // Eliminate nodes
                self.visit_left_to_right(*output, Self::transform_majority);
                /*self.visit_right_to_left(*output, Self::transform_distributivity);

                // Reshape tree
                self.transform_associativity(*output);
                self.transform_compassoc(*output);
                self.transform_relevance(*output);
                // TODO: Substitution

                // Eliminate nodes
                self.visit_left_to_right(*output, Self::transform_majority);
                self.visit_right_to_left(*output, Self::transform_distributivity);*/
            }
        }
    }

    pub fn optimise_depth(&mut self, effort: usize) {
        let outputs = self.outputs.clone();
        for iter in 0..effort {
            eprintln!("iter {}: graph has {} gates", iter, self.count_nodes());
            for output in &outputs {
                // Push up critical nodes
                self.visit_left_to_right(*output, Self::transform_majority);
                self.visit_left_to_right(*output, Self::transform_distributivity);
                self.transform_associativity(*output);
                self.transform_compassoc(*output);

                // Reshape tree
                self.transform_associativity(*output);
                self.transform_compassoc(*output);
                self.transform_relevance(*output);
                // TODO: Substitution

                // Push up critical nodes
                self.visit_left_to_right(*output, Self::transform_majority);
                self.visit_left_to_right(*output, Self::transform_distributivity);
                self.transform_associativity(*output);
                self.transform_compassoc(*output);
            }
        }
    }
}

pub enum EvaluateError {
    /// Primary inputs can't be evaluated.
    FoundPrimaryInput,
    /// Primary outputs can't be evaluated.
    FoundPrimaryOutput,
}

/// A majority-inverter graph node.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum MigNode {
    Input(Input),
    Output(Output),
    Zero(Zero),
    Inverter(Inverter),
    Majority(Majority),
}

impl MigNode {
    /// Evaluate the network to yield a possible constant value.
    pub fn evaluate(self, mig: &Mig) -> Result<bool, EvaluateError> {
        match self {
            Self::Input(_) => Err(EvaluateError::FoundPrimaryInput),
            Self::Output(_) => Err(EvaluateError::FoundPrimaryOutput),
            Self::Zero(_) => Ok(false),
            Self::Inverter(x) => x.evaluate(mig),
            Self::Majority(x) => x.evaluate(mig)
        }
    }

    /// Return the input nodes of this gate, if this node is a majority gate.
    pub fn try_unwrap_majority(self) -> Option<(usize, usize, usize)> {
        if let Self::Majority(Majority(x, y, z)) = self {
            Some((x, y, z))
        } else {
            None
        }
    }

    /// Return the input nodes of this gate, if this node is a majority gate.
    pub fn try_unwrap_majority_mut(&mut self) -> Option<(&mut usize, &mut usize, &mut usize)> {
        if let Self::Majority(Majority(x, y, z)) = self {
            Some((x, y, z))
        } else {
            None
        }
    }

    /// Return the input node of this gate, if this node is an inverter.
    pub fn try_unwrap_inverter(self) -> Option<usize> {
        if let Self::Inverter(Inverter(x)) = self {
            Some(x)
        } else {
            None
        }
    }

    /// Return the input node of this gate, if this node is an inverter.
    pub fn try_unwrap_inverter_mut(&mut self) -> Option<&mut usize> {
        if let Self::Inverter(Inverter(x)) = self {
            Some(x)
        } else {
            None
        }
    }
}

/// A logic network input.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Input(pub usize);

/// A logic network output, with index 0, and parent 1.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Output(pub usize, pub usize);

/// A zero-input, one-output gate that returns a constant zero.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Zero();

/// A one-input, one-output gate that inverts its child.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Inverter(pub usize);

impl Inverter {
    /// Evaluate an inverter to yield a possible constant value.
    pub fn evaluate(self, mig: &Mig) -> Result<bool, EvaluateError> {
        Ok(!(mig.graph[self.0].evaluate(mig)?))
    }
}

/// A three-input, one-output gate that outputs the majority value of its children.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Majority(pub usize, pub usize, pub usize);

impl Majority {
    /// Evaluate a majority node to yield a possible constant value.
    pub fn evaluate(self, mig: &Mig) -> Result<bool, EvaluateError> {
        let in0 = mig.graph[self.0].evaluate(mig)?;
        let in1 = mig.graph[self.1].evaluate(mig)?;
        let in2 = mig.graph[self.2].evaluate(mig)?;
        match (in0, in1, in2) {
            (true, true, _) => Ok(true),
            (true, _, true) => Ok(true),
            (_, true, true) => Ok(true),
            (_, _, _) => Ok(false),
        }
    }

    /// Commutatively apply a function to a majority node.
    ///
    /// This lets you write a function that matches against a tree pattern and `apply` it to manipulate the inputs.
    pub fn apply<F: FnMut(&mut Mig, usize, usize, usize, usize) -> Option<()>>(&self, root: usize, mig: &mut Mig, mut f: F) -> Option<()> {
                    f(mig, root, self.0,     self.1,     self.2)
        //.or_else(|| f(mig, root, self.0 ^ 1, self.1 ^ 1, self.2 ^ 1))
        .or_else(|| f(mig, root, self.0,     self.2,     self.1))
        //.or_else(|| f(mig, root, self.0 ^ 1, self.2 ^ 1, self.1 ^ 1))
        .or_else(|| f(mig, root, self.1,     self.0,     self.2))
        //.or_else(|| f(mig, root, self.1 ^ 1, self.0 ^ 1, self.2 ^ 1))
        .or_else(|| f(mig, root, self.1,     self.2,     self.0))
        //.or_else(|| f(mig, root, self.1 ^ 1, self.2 ^ 1, self.0 ^ 1))
        .or_else(|| f(mig, root, self.2,     self.0,     self.1))
        //.or_else(|| f(mig, root, self.2 ^ 1, self.0 ^ 1, self.1 ^ 1))
        .or_else(|| f(mig, root, self.2,     self.1,     self.0))
        //.or_else(|| f(mig, root, self.2 ^ 1, self.1 ^ 1, self.0 ^ 1))
    }

    /// Commutatively apply a function to a majority node, without caring about input order.
    ///
    /// This lets you write a function that matches against a tree pattern and `apply` it to manipulate the inputs.
    pub fn apply_unordered<F: FnMut(&mut Mig, usize, usize, usize, usize) -> Option<()>>(&self, root: usize, mig: &mut Mig, mut f: F) -> Option<()> {
        f(mig, root, self.0, self.1, self.2)
        .or_else(|| f(mig, root, self.1, self.2, self.0))
        .or_else(|| f(mig, root, self.2, self.0, self.1))
    }
}

#[cfg(test)]
mod tests {
    use super::{MigNode, Mig, Output, Majority};

    #[test]
    fn majority_noop() {
        // Test that a network that does not match the majority rule does not get transformed.
        // Before: M(x, y, z)
        // After: M(x, y, z)
        let mut mig = Mig::new();
        let (x, _) = mig.push_input();
        let (y, _) = mig.push_input();
        let (z, _) = mig.push_input();
        let (m, _) = mig.push_majority(x, y, z);

        let mig_before = mig.clone();

        mig.transform_majority(m);
        assert_eq!(mig_before, mig);
    }

    #[test]
    fn majority_same() {
        // Test that a network with a majority gate that has two identical input nodes is simplified to that input node.
        // Before: M(x, x, y)
        // After: x
        let mut mig = Mig::new();
        let (x, _) = mig.push_input();
        let (y, _) = mig.push_input();
        let (m, _) = mig.push_majority(x, x, y);
        let (o, _) = mig.push_output(m);

        let mig_before = mig.clone();

        mig.transform_majority(m);

        assert_ne!(mig_before, mig);
        assert_eq!(mig.graph[o], MigNode::Output(Output(0, x)));

        // Make sure it commutes.
        let mut mig = Mig::new();
        let (x, _) = mig.push_input();
        let (y, _) = mig.push_input();
        let (m, _) = mig.push_majority(x, y, x);
        let (o, _) = mig.push_output(m);

        let mig_before = mig.clone();

        mig.transform_majority(m);

        assert_ne!(mig_before, mig);
        assert_eq!(mig.graph[o], MigNode::Output(Output(0, x)));
    }

    #[test]
    fn majority_different() {
        // Test that a network with a majority gate that has two input nodes of opposite polarity is simplified to the remaining input.
        // Before: M(x, x', y)
        // After: y
        let mut mig = Mig::new();
        let (x, x_bar) = mig.push_input();
        let (y, _) = mig.push_input();
        let (m, _) = mig.push_majority(x, x_bar, y);
        let (o, _) = mig.push_output(m);

        let mig_before = mig.clone();

        mig.transform_majority(m);

        assert_ne!(mig_before, mig);
        assert_eq!(mig.graph[o], MigNode::Output(Output(0, y)));

        // Make sure it commutates.
        let mut mig = Mig::new();
        let (x, x_bar) = mig.push_input();
        let (y, _) = mig.push_input();
        let (m, _) = mig.push_majority(x, y, x_bar);
        let (o, _) = mig.push_output(m);

        let mig_before = mig.clone();

        mig.transform_majority(m);

        assert_ne!(mig_before, mig);
        assert_eq!(mig.graph[o], MigNode::Output(Output(0, y)));
    }

    #[test]
    fn distributivity_noop() {
        // Test that a network that does not match the distributivity axiom does not get transformed.
        // Before: M(x, y, z)
        // After: M(x, y, z)
        let mut mig = Mig::new();
        let (x, _) = mig.push_input();
        let (y, _) = mig.push_input();
        let (z, _) = mig.push_input();
        let (m, _) = mig.push_majority(x, y, z);

        let mig_before = mig.clone();

        mig.transform_distributivity(m);
        assert_eq!(mig_before, mig);
    }

    #[test]
    fn distributivity() {
        // Test that input terms can be pushed down into children nodes.
        // Before: M(x, y, M(u, v, z))
        // After: M(M(x, y, u), M(x, y, v), z)
        let mut mig = Mig::new();
        let (u, _) = mig.push_input();
        let (v, _) = mig.push_input();
        let (x, _) = mig.push_input();
        let (y, _) = mig.push_input();
        let (z, _) = mig.push_input();
        let (m1, _) = mig.push_majority(u, v, z);
        let (m0, _) = mig.push_majority(x, y, m1);

        let mig_before = mig.clone();

        mig.transform_distributivity(m0);
        assert_ne!(mig_before, mig);
        if let MigNode::Majority(Majority(in0, in1, in2)) = mig.graph[m0] {
            
        }
    }
}