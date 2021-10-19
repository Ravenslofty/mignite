use crate::mig4;
use mig4::MigNode;
use std::collections::HashSet;

use petgraph::{prelude::*, visit::EdgeRef};
use std::io;

fn to_symbol_and_bit(s: &str) -> (&str, u32) {
    let mut symbol = s;
    let mut bit = 0;

    if let Some(open_square_index) = s.find('[') {
        let (symbol2, rest) = s.split_at(open_square_index);
        symbol = symbol2;

        assert_eq!(
            rest.chars().rev().next(),
            Some(']'),
            "symbol had open square bracket but did not end with a closing square bracket"
        );

        // The 'rest' slice includes the open square bracket, so skip one
        // character forward to ignore it. Subtract 1 from the length to skip
        // over the closing bracket, too.
        let bit_str = &rest[1..rest.len() - 1];
        bit = bit_str.parse::<u32>().expect("symbol bit index was not an integer");
    }

    (symbol, bit)
}

impl mig4::Mig {
    #[allow(clippy::too_many_lines, clippy::missing_errors_doc)]
    pub fn to_rtlil<T: io::Write>(&self, mut writer: T) -> io::Result<()> {
        enum WireType {
            Input,
            Output,
        }

        writeln!(
            writer,
            "module \\majority
  wire input 1 \\A
  wire input 2 \\B
  wire input 3 \\C
  wire output 4 \\Y

  wire $and_output
  wire $or_output

  cell $_AND_ $and
    connect \\A \\A
    connect \\B \\B
    connect \\Y $and_output
  end

  cell $_OR_ $or
    connect \\A \\A
    connect \\B \\B
    connect \\Y $or_output
  end

  cell $_MUX_ $mux
    connect \\A $and_output
    connect \\B $or_output
    connect \\S \\C
    connect \\Y \\Y
  end
end
"
        )?;

        let wires = self
            .graph()
            .node_indices()
            .filter_map(|node| {
                let mig_node = &self.node_type(node);
                let (wire_type, index) = match mig_node {
                    MigNode::Input(index) => (WireType::Input, index),
                    MigNode::Output(index) => (WireType::Output, index),
                    _ => return None,
                };

                let ident = if let Some(symbol) = self.symbol(*index) {
                    let (symbol, bit) = to_symbol_and_bit(symbol);

                    (symbol.to_string(), bit)
                } else {
                    let wire_type_str = match wire_type {
                        WireType::Input => "i",
                        WireType::Output => "o",
                    };

                    (format!("${}{:02}", wire_type_str, node.index()), 0)
                };

                Some((node, ident, wire_type))
            })
            .collect::<Vec<_>>();

        writeln!(writer, "module \\top")?;
        writeln!(writer, "  wire $node$0")?;
        writeln!(writer, "  connect $node$0 1'0")?;
        for node in self.graph().node_indices() {
            let mig_node = &self.node_type(node);
            match mig_node {
                MigNode::Majority | MigNode::Output(_) => {
                    writeln!(writer, "  wire $node${}", node.index())?;
                }
                _ => {}
            }
        }
        let mut wires_written = HashSet::new();
        for (i, (_, (symbol, _), wire_type)) in wires.iter().enumerate() {
            if !wires_written.insert(symbol) {
                continue;
            }

            let components = wires
                .iter()
                .filter(|(_, (symbol2, _), _)| symbol2 == symbol);

            let max_bit = components
                .clone()
                .map(|(_, (_, bit), _)| bit)
                .max()
                .unwrap();
            let width = max_bit + 1;

            let wire_type_str = match wire_type {
                WireType::Input => "input",
                WireType::Output => "output",
            };

            writeln!(
                writer,
                "  wire width {} {} {} \\{}",
                width, wire_type_str, i, symbol
            )?;

            for (node, (_, bit), _) in components {
                match wire_type {
                    WireType::Input => {
                        writeln!(writer, "  wire width 1 $node${}", node.index())?;
                        writeln!(
                            writer,
                            "  connect $node${} \\{} [{}]",
                            node.index(),
                            symbol,
                            bit
                        )?;
                    }
                    WireType::Output => {
                        writeln!(
                            writer,
                            "  connect \\{} [{}] $node${}",
                            symbol,
                            bit,
                            node.index()
                        )?;
                    }
                }
            }
        }

        let mut node_inverter_hash: std::collections::HashMap<(NodeIndex, bool), String> = std::collections::HashMap::new();

        let mut uid = 0;
        let mut prep_edge = |writer: &mut T, edge| -> io::Result<String> {
            let from = self.edge_source(edge);

            let is_inverted = self.is_edge_inverted(edge);

            if let Some(ident) = node_inverter_hash.get(&(from, is_inverted)) {
                return Ok(ident.clone())
            }

            let mut ident = format!("$node${}", from.index());

            if is_inverted {
                let inv_ident = format!("{}${}$n", ident, uid);

                writeln!(writer, "  wire {}", inv_ident)?;
                writeln!(writer, "  cell $_NOT_ $not${}", uid)?;
                writeln!(writer, "    connect \\A {}", ident)?;
                writeln!(writer, "    connect \\Y {}", inv_ident)?;
                writeln!(writer, "  end")?;

                uid += 1;
                ident = inv_ident;
            }

            node_inverter_hash.insert((from, is_inverted), ident.clone());

            Ok(ident)
        };

        for node in self.graph().node_indices() {
            let mig_node = &self.node_type(node);
            match mig_node {
                MigNode::Majority => {
                    if let Some((a_edge, b_edge)) = self.try_unwrap_and(node) {
                        let a_ident = prep_edge(&mut writer, a_edge)?;
                        let b_ident = prep_edge(&mut writer, b_edge)?;

                        writeln!(writer, "  cell $_AND_ $majority${}", node.index())?;
                        writeln!(writer, "    connect \\A {}", a_ident)?;
                        writeln!(writer, "    connect \\B {}", b_ident)?;
                        writeln!(writer, "    connect \\Y $node${}", node.index())?;
                        writeln!(writer, "  end")?;
                    } else if let Some((a_edge, b_edge)) = self.try_unwrap_or(node) {
                        let a_ident = prep_edge(&mut writer, a_edge)?;
                        let b_ident = prep_edge(&mut writer, b_edge)?;

                        writeln!(writer, "  cell $_OR_ $majority${}", node.index())?;
                        writeln!(writer, "    connect \\A {}", a_ident)?;
                        writeln!(writer, "    connect \\B {}", b_ident)?;
                        writeln!(writer, "    connect \\Y $node${}", node.index())?;
                        writeln!(writer, "  end")?;
                    } else {
                        let (a_edge, b_edge, c_edge) = self.try_unwrap_majority(node).unwrap();
                        let a_ident = prep_edge(&mut writer, a_edge)?;
                        let b_ident = prep_edge(&mut writer, b_edge)?;
                        let c_ident = prep_edge(&mut writer, c_edge)?;

                        writeln!(writer, "  cell \\majority $majority${}", node.index())?;
                        writeln!(writer, "    connect \\A {}", a_ident)?;
                        writeln!(writer, "    connect \\B {}", b_ident)?;
                        writeln!(writer, "    connect \\C {}", c_ident)?;
                        writeln!(writer, "    connect \\Y $node${}", node.index())?;
                        writeln!(writer, "  end")?;
                    }
                }
                MigNode::Output(_) => {
                    let mut edges = self.graph().edges_directed(node, Incoming);
                    let edge_driver = edges.next().expect("output to be driven");
                    assert_eq!(edges.next(), None, "output driven by multiple nodes");

                    let ident = prep_edge(&mut writer, edge_driver.id())?;
                    let node_driver = edge_driver.target();

                    writeln!(writer, "  connect $node${} {}", node_driver.index(), ident)?;
                }
                _ => {}
            }
        }
        writeln!(writer, "end")?;

        Ok(())
    }
}
