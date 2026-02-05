use std::{collections::{HashMap, HashSet}, fmt::{Debug, Write}};
use petgraph::{Direction, graph::{DiGraph, EdgeReference}, visit::{EdgeFiltered, EdgeRef, GraphProp, IntoEdgeReferences, IntoNodeReferences, NodeIndexable, NodeRef}};
use crate::{Circuit, CliffordBasis};

pub fn graph_to_dot<G: GraphProp + IntoNodeReferences + NodeIndexable + IntoEdgeReferences, N: Debug, E: Debug>(
    g: G,
    nlab: impl Fn(G::NodeId, &G::NodeWeight) -> Option<&N>,
    elab: impl Fn(G::NodeId, G::NodeId, &G::EdgeWeight) -> Option<&E>
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

pub fn trans_red<'a, N, E>(g: &'a DiGraph<N, E>) -> EdgeFiltered<&'a DiGraph<N, E>, impl Fn(EdgeReference<'a, E>) -> bool + 'a> {
    let mut sets = HashMap::new();
    let mut edges = HashSet::new();
    let mut ready = g.node_indices()
        .filter(|&n| g.neighbors_directed(n, Direction::Outgoing)
            .next().is_none())
        .collect::<Vec<_>>();
    let mut visited = HashSet::new();
    let mut order = Vec::new();
    while let Some(node) = ready.pop() {
        let mut set = HashSet::new();
        set.insert(node);
        for edge in order.iter().rev().filter_map(|&c| g.edges_connecting(node, c).next()) {
            if !set.contains(&edge.target()) {
                edges.insert(edge.id());
                set.extend(&sets[&edge.target()]);
            }
        }

        sets.insert(node, set);
        visited.insert(node);
        order.push(node);

        for parent in g.neighbors_directed(node, Direction::Incoming) {
            if g.neighbors_directed(parent, Direction::Outgoing).all(|c| visited.contains(&c)) {
                ready.push(parent);
            }
        }
    }

    EdgeFiltered::from_fn(g, move |edge: EdgeReference<'_, E>| edges.contains(&edge.id()))
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

#[cfg(feature="quizx")]
pub fn quizx_equiv(a: &Circuit, b: &Circuit) -> bool {
    let ca = quizx::circuit::Circuit::from_qasm(&a.qasm()).unwrap();
    let cb = quizx::circuit::Circuit::from_qasm(&b.qasm()).unwrap();
    let cb = { let mut c = quizx::circuit::Circuit::new(ca.num_qubits()); c.gates = cb.gates; c };
    quizx::equality::equal_circuit(&ca, &cb) == Some(true)
}

#[cfg(feature="quizx")]
pub fn quizx_equiv_tensor(a: &Circuit, b: &Circuit) -> bool {
    let ca = quizx::circuit::Circuit::from_qasm(&a.qasm()).unwrap();
    let cb = quizx::circuit::Circuit::from_qasm(&b.qasm()).unwrap();
    let cb = { let mut c = quizx::circuit::Circuit::new(ca.num_qubits()); c.gates = cb.gates; c };
    use quizx::tensor::CompareTensors;
    quizx::tensor::TensorF::scalar_compare(&ca, &cb)
}

/// Check if two circuits are equivalent using feynver.
/// Requires `feynver` to be in the PATH.
pub fn feynver_equiv(a: &Circuit, b: &Circuit) -> Option<bool> {
    use std::io::Write;

    let tmp = std::env::temp_dir();
    let p1 = tmp.join("circuit1.qc");
    let p2 = tmp.join("circuit2.qc");
    let mut f1 = std::fs::File::create(&p1).unwrap();
    let mut f2 = std::fs::File::create(&p2).unwrap();

    write!(&mut f1, "{}", a.qc()).unwrap();
    write!(&mut f2, "{}", b.qc()).unwrap();

    let output = std::process::Command::new("feynver")
        .arg("-ignore-global-phase")
        .arg(p1)
        .arg(p2)
        .output()
        .unwrap();
    let output = String::from_utf8_lossy(&output.stdout);
    
    if output.contains("Equal") {
        return Some(true)
    } else if output.contains("Not equal") {
        return Some(false)
    } else {
        return None
    }
}
