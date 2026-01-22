use std::fmt::Debug;
use petgraph::{Graph, EdgeType, graph::NodeIndex};
use crate::{Circuit, CliffordBasis};

pub fn graph_to_dot<'a, N2: Debug, E2: Debug, N, E, Ty: EdgeType>(
    g: &'a Graph<N, E, Ty>,
    nlab: impl Fn(NodeIndex, &'a N) -> Option<N2>,
    elab: impl Fn(NodeIndex, NodeIndex, &'a E) -> Option<E2>
) -> String {
    use std::fmt::Write;
    use petgraph::visit::EdgeRef;

    let arr = if g.is_directed() { "->" } else { "--" };
    let mut dot = if g.is_directed() { String::from("digraph G {\n  rankdir=LR;\n") } else { String::from("graph G {\n  rankdir=LR;\n") };

    for node in g.node_indices() {
        if let Some(label) = nlab(node, &g[node]) {
            writeln!(&mut dot, "  n{} [label=\"{:?}\"];", node.index(), label).unwrap();
        } else {
            writeln!(&mut dot, "  n{};", node.index()).unwrap();
        }
    }

    for e in g.edge_references() {
        if let Some(label) = elab(e.source(), e.target(), e.weight()) {
            writeln!(&mut dot, "  n{} {} n{} [label=\"{:?}\"];", e.source().index(), arr, e.target().index(), label).unwrap();
        } else {
            writeln!(&mut dot, "  n{} {} n{};", e.source().index(), arr, e.target().index()).unwrap();
        }
    }

    dot.push_str("}\n");
    dot
}

/// Check if two Clifford circuits are equivalent.
/// Returns:
///   - Some(true) if the circuits are equivalent,
///   - Some(false) if the circuits are not equivalent,
///   - None if the two circuits are incomparable (e.g different number of qubits, or contains T gates)
#[must_use]
pub fn clifford_equiv(a: &Circuit, b: &Circuit) -> Option<bool> {
    if a.qubits != b.qubits { return None }
    let mut basis = CliffordBasis::from_circuit(a)?;
    basis.apply_gates(b.iter_inverse())?;
    Some(basis.is_identity())
}
