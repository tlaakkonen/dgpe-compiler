use std::fmt::{Debug, Write};
use petgraph::{visit::{GraphProp, IntoNodeReferences, NodeIndexable, IntoEdgeReferences, EdgeRef, NodeRef}};
use crate::{Circuit, CliffordBasis};

pub fn graph_to_dot<G: GraphProp + IntoNodeReferences + NodeIndexable + IntoEdgeReferences, N: Debug, E: Debug>(
    g: G,
    nlab: impl Fn(G::NodeId, &G::NodeWeight) -> Option<N>,
    elab: impl Fn(G::NodeId, G::NodeId, &G::EdgeWeight) -> Option<E>
) -> String {
    let arr = if g.is_directed() { "->" } else { "--" };
    let mut dot = if g.is_directed() { String::from("digraph G {\n  rankdir=LR;\n") } else { String::from("graph G {\n  rankdir=LR;\n") };

    for nref in g.node_references() {
        let node = nref.id();
        if let Some(label) = nlab(node, nref.weight()) {
            writeln!(&mut dot, "  n{} [label=\"{:?}\"];", g.to_index(node), label).unwrap();
        } else {
            writeln!(&mut dot, "  n{};", g.to_index(node)).unwrap();
        }
    }

    for e in g.edge_references() {
        if let Some(label) = elab(e.source(), e.target(), e.weight()) {
            writeln!(&mut dot, "  n{} {} n{} [label=\"{:?}\"];", g.to_index(e.source()), arr, g.to_index(e.target()), label).unwrap();
        } else {
            writeln!(&mut dot, "  n{} {} n{};", g.to_index(e.source()), arr, g.to_index(e.target())).unwrap();
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
