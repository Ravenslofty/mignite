/// A graph to be manipulated.
pub trait Graph: Default + Sized {
    /// A graph node.
    type Node: From<usize> + Into<usize>;

    /// Returns the inputs (fan-in) of a node.
    fn node_inputs(&self, node: &Self::Node) -> Vec<Self::Node>;
    /// Returns the outputs (fan-out) of a node.
    fn node_outputs(&self, node: &Self::Node) -> Vec<Self::Node>;
    /// Returns the largest node index in the graph.
    fn node_count(&self) -> usize;
    /// Returns true if this node is an input to the graph.
    fn node_is_input(&self, node: &Self::Node) -> bool;
    /// Returns true if this node is an output to the graph.
    fn node_is_output(&self, node: &Self::Node) -> bool;
    /// Returns true if this node is a majority gate.
    fn node_is_majority(&self, node: &Self::Node) -> bool;

    fn push_output

    /// Garbage-collect the graph, removing orphan nodes.
    fn sweep(self) -> Self {
        // This algorithm boils down to "stop and copy" garbage collection.
        let node_count = self.node_count();
        let mut index: Vec<Option<usize>> = vec![None; node_count];

        let mut graph = Self::default();

        // Scan through the node list.
        for node in 0..node_count {
            // If we've already visited this node, skip it.
            if index[node].is_some() {
                continue;
            }

            // If this node is an output, it is assumed referenced.
            if self.node_is_output(&node.into()) {
                referenced[node] = true;

                // Everything that fans into an output is also referenced, and everything that fans into those, etc.
                let mut visit_list = self.node_inputs(node);
                while let Some(node) = visit_list.pop() {
                    if referenced[node] {
                        continue;
                    }

                    referenced[node] = true;

                    visit_list.append(self.node_outputs(node))
                }
            }
        }

        // Now, all nodes where referenced[node] == false are orphan nodes, and can be ignored.

        todo!()
    }
}