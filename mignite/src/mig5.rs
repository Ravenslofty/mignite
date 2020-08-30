/// An index into the graph.
///
/// The least significant bit signifies inversion state.
pub struct Index(u32);

/// A graph node.
pub enum Node {
    /// A three-input majority gate.
    Majority {
        /// Input 1.
        input1: Index,
        /// Input 2. 
        input2: Index,
        /// Input 3.
        input3: Index
    },
    /// A two-input exclusive-or gate.
    Xor {
        /// Input 1.
        input1: Index,
        /// Input 2.
        input2: Index,
    },
    /// An input for a cell with possibly-known structure and associated data.
    BoxInput {
        /// Box index.
        index: u32,
        /// Box port index.
        port: u32,
    },
    /// An output for a cell with possibly-known structure and associated data.
    BoxOutput {
        /// Box index.
        index: u32,
        /// Box port index.
        port: u32,
    },
    /// A network data input.
    PrimaryInput {
        /// Input number.
        port: u32,
    },
    /// A network data output.
    PrimaryOutput {
        /// Output number.
        port: u32,
    },
    /// A zero constant.
    Zero,
}

/// A majority-inverter graph.
pub struct Mig {
    graph: Vec<Node>
}

