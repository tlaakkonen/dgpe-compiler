use std::fmt::Debug;
use petgraph::graph::{DiGraph, NodeIndex};
use crate::{GlobalArch, LocalQubit, PauliString};

#[derive(Clone, Copy, Debug)]
pub enum Gate {
    H(usize),
    CX(usize, usize),
    S(usize),
    Sdg(usize),
    X(usize),
    Z(usize),
    T(usize)
}

impl Gate {
    pub fn iter_inverse(self) -> impl Iterator<Item=Gate> {
        match self {
            Gate::H(_) | Gate::CX(_, _) | Gate::Z(_) | Gate::X(_) => Some(self).into_iter().chain(None),
            Gate::S(a) => Some(Gate::Sdg(a)).into_iter().chain(None),
            Gate::Sdg(a) => Some(Gate::S(a)).into_iter().chain(None),
            Gate::T(a) => Some(Gate::Sdg(a)).into_iter().chain(Some(Gate::T(a)))
        }
    }
}

#[derive(Clone)]
pub enum PauliExp {
    Phase(PhaseExp),
    Nonlocal(NonlocalExp)
}

impl PauliExp {
    pub fn commutes(&self, other: &PauliExp) -> bool {
        match (self, other) {
            (
                PauliExp::Phase(PhaseExp { idx: idx_s, string: string_s, .. }),
                PauliExp::Phase(PhaseExp { idx: idx_o, string: string_o, .. })
            ) => idx_s != idx_o || string_s.commutes(string_o),
            (
                PauliExp::Phase(PhaseExp { idx, string, .. }),
                PauliExp::Nonlocal(NonlocalExp { idx_a, idx_b, string_a, string_b, .. })
            ) | (
                PauliExp::Nonlocal(NonlocalExp { idx_a, idx_b, string_a, string_b, .. }),
                PauliExp::Phase(PhaseExp { idx, string, .. })
            ) => (idx != idx_a || string.commutes(string_a)) && (idx != idx_b || string.commutes(string_b)),
            (
                PauliExp::Nonlocal(NonlocalExp { idx_a: idx_a_s, idx_b: idx_b_s, string_a: string_a_s, string_b: string_b_s, .. }),
                PauliExp::Nonlocal(NonlocalExp { idx_a: idx_a_o, idx_b: idx_b_o, string_a: string_a_o, string_b: string_b_o, .. })
            ) => (idx_a_s != idx_a_o || string_a_s.commutes(string_a_o)) && (idx_a_s != idx_b_o || string_a_s.commutes(string_b_o)) 
                && (idx_b_s != idx_a_o || string_b_s.commutes(string_a_o)) && (idx_b_s != idx_b_o || string_b_s.commutes(string_b_o))
        }
    }

    pub fn cx(&mut self, i: LocalQubit, j: LocalQubit) {
        match self {
            PauliExp::Phase(phase) => phase.cx(i, j),
            PauliExp::Nonlocal(nonlocal) => nonlocal.cx(i, j)
        }
    }

    pub fn h(&mut self, i: LocalQubit) {
        match self {
            PauliExp::Phase(phase) => phase.h(i),
            PauliExp::Nonlocal(nonlocal) => nonlocal.h(i)
        }
    }

    pub fn s(&mut self, i: LocalQubit) {
        match self {
            PauliExp::Phase(phase) => phase.s(i),
            PauliExp::Nonlocal(nonlocal) => nonlocal.s(i)
        }
    }

    pub fn weight(&self) -> usize {
        match self {
            PauliExp::Phase(phase) => phase.weight(),
            PauliExp::Nonlocal(nonlocal) => nonlocal.weight()
        }
    }

    pub fn push_clifford(&mut self, cliff: &PhaseExp) {
        match self {
            PauliExp::Phase(p) => p.push_clifford(cliff),
            PauliExp::Nonlocal(n) => n.push_clifford(cliff)
        }
    }

    /// Find a naive set of gates that implement this PauliExp.
    /// Does not respect architecture constraints.
    pub fn to_gates_naive(&self, arch: &GlobalArch) -> Vec<Gate> {
        match self {
            PauliExp::Phase(p) => p.to_gates_naive(arch),
            PauliExp::Nonlocal(n) => n.to_gates_naive(arch)
        }
    }

    /// Checks if there is a *local* Clifford operation
    pub fn is_clifford(&self) -> bool {
        match self {
            PauliExp::Phase(p) => p.is_clifford(),
            PauliExp::Nonlocal(_) => false
        }
    }
}

impl Debug for PauliExp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PauliExp::Nonlocal(p) => write!(f, "{:?}", p),
            PauliExp::Phase(p) => write!(f, "{:?}", p)
        }
    }
}

#[derive(Clone)]
pub struct PhaseExp {
    pub idx: usize,
    pub phase: usize,
    pub string: PauliString
}

impl PhaseExp {
    pub fn cx(&mut self, i: LocalQubit, j: LocalQubit) {
        assert_eq!(i.idx, j.idx, "cannot apply non-local CNOT");
        if i.idx == self.idx {
            self.string.cx(i.offset, j.offset);
        }
    }

    pub fn h(&mut self, i: LocalQubit) {
        if i.idx == self.idx {
            self.string.h(i.offset);
        }
    }

    pub fn s(&mut self, i: LocalQubit) {
        if i.idx == self.idx {
            self.string.s(i.offset);
        }
    }

    pub fn weight(&self) -> usize {
        self.string.weight()
    }

    pub fn commutes(&self, other: &PhaseExp) -> bool {
        if self.idx != other.idx {
            return true
        }

        return self.string.commutes(&other.string)
    }

    pub fn is_clifford(&self) -> bool {
        self.phase % 2 == 0
    }

    /// Push a Clifford PhaseExp through this one, left to right
    pub fn push_clifford(&mut self, cliff: &PhaseExp) {
        assert!(cliff.is_clifford());

        if self.commutes(cliff) {
            return
        }
        
        if (cliff.phase / 2) % 2 == 1 {
            // We know that they anticommute, can ignore phase
            let _ = self.string.mul_from(&cliff.string);
            // self.string.sign = !self.string.sign;
        }

        if (cliff.phase / 4) % 2 == 1 {
            self.string.sign = !self.string.sign;
        }
    }

    /// Find a naive set of gates that implement this PhaseExp.
    /// Does not respect architecture constraints.
    pub fn to_gates_naive(&self, arch: &GlobalArch) -> Vec<Gate> {
        if self.string.is_identity() || (self.phase % 8) == 0 {
            return Vec::new()
        }

        let part = &arch.parts[self.idx];
        let mut s = self.string.clone();
        let diag = s.diagonalize(part);
        let mut gates = diag.clone();
        let qpivot = part.from_offset(s.zs.iter().position(|&z| z).unwrap());
        let phase = if s.sign { (8 - (self.phase % 8)) % 8 } else { self.phase % 8 };
        match phase {
            1 => gates.push(Gate::T(qpivot.global)),
            2 => gates.push(Gate::S(qpivot.global)),
            3 => {
                gates.push(Gate::S(qpivot.global));
                gates.push(Gate::T(qpivot.global));
            },
            4 => gates.push(Gate::Z(qpivot.global)),
            5 => {
                gates.push(Gate::Z(qpivot.global));
                gates.push(Gate::T(qpivot.global));
            },
            6 => gates.push(Gate::Sdg(qpivot.global)),
            7 => {
                gates.push(Gate::Sdg(qpivot.global));
                gates.push(Gate::T(qpivot.global));
            },
            _ => unreachable!()
        }
        gates.extend(diag.iter().rev().flat_map(|g| g.iter_inverse()));
        gates
    }
}

impl Debug for PhaseExp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{{}}}P({:?},{})", self.idx, self.string, self.phase)
    }
}

#[derive(Clone)]
pub struct NonlocalExp {
    pub idx_a: usize,
    pub idx_b: usize,
    pub string_a: PauliString,
    pub string_b: PauliString
}

impl NonlocalExp {
    pub fn cx(&mut self, i: LocalQubit, j: LocalQubit) {
        assert_eq!(i.idx, j.idx, "cannot apply non-local CNOT");
        if i.idx == self.idx_a {
            self.string_a.cx(i.offset, j.offset);
        } else if i.idx == self.idx_b {
            self.string_b.cx(i.offset, j.offset);
        }
    }

    pub fn h(&mut self, i: LocalQubit) {
        if i.idx == self.idx_a {
            self.string_a.h(i.offset);
        } else if i.idx == self.idx_b {
            self.string_b.h(i.offset);
        }
    }

    pub fn s(&mut self, i: LocalQubit) {
        if i.idx == self.idx_a {
            self.string_a.s(i.offset);
        } else if i.idx == self.idx_b {
            self.string_b.s(i.offset);
        }
    }

    pub fn weight(&self) -> usize {
        self.string_a.weight() + self.string_b.weight()
    }

    pub fn commutes(&self, other: &NonlocalExp) -> bool {
        let aa = if self.idx_a == other.idx_a { self.string_a.commutes(&other.string_a) } else { true };
        let ab = if self.idx_a == other.idx_b { self.string_a.commutes(&other.string_b) } else { true };
        let ba = if self.idx_b == other.idx_a { self.string_b.commutes(&other.string_a) } else { true };
        let bb = if self.idx_b == other.idx_b { self.string_b.commutes(&other.string_b) } else { true };
        aa && ab && ba && bb
    }

    /// Push a Clifford NonlocalExp through this, left to right
    pub fn push_clifford(&mut self, cliff: &PhaseExp) {
        assert!(cliff.is_clifford());

        let str = if cliff.idx == self.idx_a {
            &mut self.string_a
        } else if cliff.idx == self.idx_b {
            &mut self.string_b
        } else {
            return
        };

        if str.commutes(&cliff.string) {
            return
        }

        if (cliff.phase / 2) % 2 == 1 {
            // We know that they anticommute, can ignore phase
            let _ = str.mul_from(&cliff.string);
        }

        if (cliff.phase / 4) % 2 == 1 {
            str.sign = !str.sign;
        }
    }

    /// Find a naive set of gates that implement this NonlocalExp.
    /// Does not respect architecture constraints.
    pub fn to_gates_naive(&self, arch: &GlobalArch) -> Vec<Gate> {
        let mut gates = Vec::new();

        let mut sa = self.string_a.clone();
        let da = sa.diagonalize(&arch.parts[self.idx_a]);
        gates.extend_from_slice(&da);

        let mut sb = self.string_b.clone();
        let db = sb.diagonalize(&arch.parts[self.idx_b]);
        gates.extend_from_slice(&db);

        let pa = sa.zs.iter().position(|&z| z).map(|p| arch.parts[self.idx_a].from_offset(p));
        let pb = sb.zs.iter().position(|&z| z).map(|p| arch.parts[self.idx_b].from_offset(p));
        match (pa, pb) {
            (None, None) => (),
            (Some(qa), None) => if sb.sign { gates.push(Gate::Z(qa.global)) },
            (None, Some(qb)) => if sa.sign { gates.push(Gate::Z(qb.global)) },
            (Some(qa), Some(qb)) => {
                if sb.sign { gates.push(Gate::Z(qa.global)) }
                if sa.sign { gates.push(Gate::Z(qb.global)) }
                gates.push(Gate::H(qb.global));
                gates.push(Gate::CX(qa.global, qb.global));
                gates.push(Gate::H(qb.global));
            }
        }

        gates.extend(da.iter().rev().flat_map(|g| g.iter_inverse()));
        gates.extend(db.iter().rev().flat_map(|g| g.iter_inverse()));

        gates
    }
}

impl Debug for NonlocalExp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{{},{}}}C({:?},{:?})", self.idx_a, self.idx_b, self.string_a, self.string_b)
    }
}

#[derive(Debug, Clone)]
pub struct Circuit {
    pub gates: Vec<Gate>,
    pub qubits: usize
}

impl Circuit {
    pub fn new(qubits: usize) -> Circuit {
        Circuit { qubits, gates: Vec::new() }
    }

    pub fn iter_inverse(&self) -> impl Iterator<Item=Gate> {
        self.gates.iter().rev().map(|g| g.iter_inverse()).flatten()
    }

    pub fn inverse(&self) -> Circuit {
        Circuit { qubits: self.qubits, gates: self.iter_inverse().collect() }
    }

    pub fn random_clifford(qubits: usize, ngates: usize, p_h: f32, p_s: f32) -> Circuit {
        let mut gates = Vec::new();
        for _ in 0..ngates {
            let r = rand::random::<f32>();
            let q = rand::random_range(0..qubits);
            if r < p_h {
                gates.push(Gate::H(q));
            } else if r < p_s + p_h {
                gates.push(Gate::S(q));
            } else {
                let mut t = rand::random_range(0..qubits-1);
                if t >= q { t += 1; }
                gates.push(Gate::CX(q, t));
            }
        }
        Circuit { gates, qubits }
    }

    pub fn random_cnot(qubits: usize, ngates: usize) -> Circuit {
        let mut gates = Vec::new();
        for _ in 0..ngates {
            let a = rand::random_range(0..qubits);
            let mut b = rand::random_range(0..qubits - 1);
            if b >= a { b += 1; }
            gates.push(Gate::CX(a, b));
        }
        Circuit { gates, qubits }
    }

    pub fn random_clifford_t(qubits: usize, ngates: usize, p_t: f32, p_h: f32, p_s: f32) -> Circuit {
        let mut gates = Vec::new();
        for _ in 0..ngates {
            let r = rand::random::<f32>();
            let q = rand::random_range(0..qubits);
            if r < p_t {
                gates.push(Gate::T(q));
            } else if r < p_t + p_h {
                gates.push(Gate::H(q));
            } else if r < p_t + p_h + p_s {
                gates.push(Gate::S(q));
            } else {
                let mut t = rand::random_range(0..qubits-1);
                if t >= q { t += 1; }
                gates.push(Gate::CX(q, t));
            }
        }
        Circuit { gates, qubits }
    }

    pub fn append(&mut self, other: &Circuit) {
        assert_eq!(self.qubits, other.qubits);
        self.gates.extend_from_slice(&other.gates);
    }

    pub fn s(&mut self, i: usize) {
        self.gates.push(Gate::S(i));
    }

    pub fn sdg(&mut self, i: usize) {
        self.gates.push(Gate::Sdg(i));
    }

    pub fn z(&mut self, i: usize) {
        self.gates.push(Gate::Z(i));
    }

    pub fn x(&mut self, i: usize) {
        self.gates.push(Gate::X(i));
    }

    pub fn t(&mut self, i: usize) {
        self.gates.push(Gate::T(i));
    }

    pub fn h(&mut self, i: usize) {
        self.gates.push(Gate::H(i));
    }

    pub fn cx(&mut self, i: usize, j: usize) {
        self.gates.push(Gate::CX(i, j));
    }

    pub fn qasm(&self) -> String {
        use std::fmt::Write;
        let mut buffer = String::new();
        writeln!(&mut buffer, "OPENQASM 2.0;\ninclude \"qelib1.inc\";").unwrap();
        writeln!(&mut buffer, "qreg q[{}];", self.qubits).unwrap();
        for gate in &self.gates {
            match &gate {
                Gate::CX(i, j) => writeln!(&mut buffer, "cx q[{}], q[{}];", i, j),
                Gate::H(i) => writeln!(&mut buffer, "h q[{}];", i),
                Gate::S(i) => writeln!(&mut buffer, "s q[{}];", i),
                Gate::Sdg(i) => writeln!(&mut buffer, "sdg q[{}];", i),
                Gate::Z(i) => writeln!(&mut buffer, "z q[{}];", i),
                Gate::X(i) => writeln!(&mut buffer, "x q[{}];", i),
                Gate::T(i) => writeln!(&mut buffer, "t q[{}];", i)
            }.unwrap();
        }
        buffer
    }

    pub fn qc(&self) -> String {
        use std::fmt::Write;
        let mut out = String::new();
        for &g in &self.gates {
            match g {
                Gate::X(q) => writeln!(&mut out, "X p{q}"),
                Gate::CX(c, t) => writeln!(&mut out, "cnot p{c} p{t}"),
                Gate::T(q) => writeln!(&mut out, "T p{q}"),
                Gate::S(q) => writeln!(&mut out, "S p{q}"),
                Gate::Z(q) => writeln!(&mut out, "Z p{q}"),
                Gate::Sdg(q) => writeln!(&mut out, "Z p{q}\nS p{q}"),
                Gate::H(q) => writeln!(&mut out, "H p{q}")
            }.unwrap()
        }
        let qs = (0..=self.qubits)
                .map(|i| format!("p{}", i))
                .collect::<Vec<_>>()
                .join(" ");
        format!(".v {}\n.i {}\nBEGIN\n{}\nEND", qs, qs, out)
    }

    pub fn partition(&self, arch: &GlobalArch) -> PartitionedCircuit {
        let mut exps = Vec::new();
        let mut gates = Vec::new();
        for &gate in self.gates.iter().rev() {
            match gate {
                Gate::CX(i, j) => {
                    let i = arch.to_local(i);
                    let j = arch.to_local(j);
                    if i.idx == j.idx {
                        for exp in &mut exps {
                            match exp {
                                PauliExp::Phase(exp) if exp.idx == i.idx => exp.string.cx(i.offset, j.offset),
                                PauliExp::Nonlocal(exp) if exp.idx_a == i.idx => exp.string_a.cx(i.offset, j.offset),
                                PauliExp::Nonlocal(exp) if exp.idx_b == i.idx => exp.string_b.cx(i.offset, j.offset),
                                _ => ()
                            }
                        }
                        gates.push(gate);
                    } else {
                        if i.idx < j.idx {
                            let string_a = PauliString::identity(arch.part_size(i.idx)).with_z(i.offset);
                            let string_b = PauliString::identity(arch.part_size(j.idx)).with_x(j.offset);
                            exps.push(PauliExp::Nonlocal(NonlocalExp { idx_a: i.idx, string_a, idx_b: j.idx, string_b }));
                        } else {
                            let string_a = PauliString::identity(arch.part_size(j.idx)).with_x(j.offset);
                            let string_b = PauliString::identity(arch.part_size(i.idx)).with_z(i.offset);
                            exps.push(PauliExp::Nonlocal(NonlocalExp { idx_a: j.idx, string_a, idx_b: i.idx, string_b }));
                        }
                    }
                },
                Gate::T(q) => {
                    let q = arch.to_local(q);
                    let mut string = PauliString::identity(arch.part_size(q.idx));
                    string.zs[q.offset] = true;
                    exps.push(PauliExp::Phase(PhaseExp { idx: q.idx, phase: 1, string }));
                },
                Gate::H(q) | Gate::S(q) | Gate::Sdg(q) | Gate::Z(q) | Gate::X(q) => {
                    let q = arch.to_local(q);
                    for exp in &mut exps {
                        let string = match exp {
                            PauliExp::Phase(exp) if exp.idx == q.idx => &mut exp.string,
                            PauliExp::Nonlocal(exp) if exp.idx_a == q.idx => &mut exp.string_a,
                            PauliExp::Nonlocal(exp) if exp.idx_b == q.idx => &mut exp.string_b,
                            _ => continue
                        };
                        match gate {
                            Gate::H(_) => string.h(q.offset),
                            Gate::S(_) => string.sdg(q.offset),
                            Gate::Sdg(_) => string.s(q.offset),
                            Gate::Z(_) => string.z(q.offset),
                            Gate::X(_) => string.x(q.offset),
                            _ => unreachable!()
                        }
                    }
                    gates.push(gate);
                }
            }
        }
        gates.reverse();
        exps.reverse();

        PartitionedCircuit::new(arch.clone(), exps, Circuit { gates, qubits: self.qubits })
    }
}

#[derive(Debug, Clone)]
pub struct PartitionedCircuit {
    pub arch: GlobalArch,
    pub dag: DiGraph<PauliExp, ()>,
    pub tail: Circuit
}

impl PartitionedCircuit {
    pub fn new(arch: GlobalArch, exps: Vec<PauliExp>, tail: Circuit) -> PartitionedCircuit {
        let mut nodes = Vec::new();
        let mut dag = DiGraph::new();
        for (i, exp) in exps.into_iter().enumerate() {
            nodes.push(dag.add_node(exp));
            for j in 0..i {
                if !dag[nodes[j]].commutes(&dag[nodes[i]]) {
                    dag.add_edge(nodes[j], nodes[i], ());
                }
            }
        }

        PartitionedCircuit { arch, dag, tail }
    }

    pub fn tcount(&self) -> usize {
        self.dag.node_weights().filter(|&n| {
            matches!(n, PauliExp::Phase(p) if !p.is_clifford())
        }).count()
    }

    pub fn nlcount(&self) -> usize {
        self.dag.node_weights().filter(|&n| {
            matches!(n, PauliExp::Nonlocal(_))
        }).count()
    }

    /// Rebuild the DAG from a topological order
    pub fn rebuild(&mut self, order: &[NodeIndex]) {
        self.dag.clear_edges();
        for i in 0..order.len() {
            for j in 0..i {
                if !self.dag[order[j]].commutes(&self.dag[order[i]]) {
                    self.dag.add_edge(order[j], order[i], ());
                }
            }
        }
    }

    pub fn push(&mut self, exp: PauliExp) {
        let idx = self.dag.add_node(exp);
        for n in self.dag.node_indices() {
            if !self.dag[n].commutes(&self.dag[idx]) {
                self.dag.add_edge(n, idx, ());
            }
        }
    }

    pub fn iter(&self) -> impl Iterator<Item=&PauliExp> {
        let order = petgraph::algo::toposort(&self.dag, None).unwrap();
        order.into_iter().map(|idx| &self.dag[idx])
    }

    /// Resynthesize a Circuit VERY naively. Does not respect architecture constraints.
    pub fn naive_resynth(&self) -> Circuit {
        let mut gates = Vec::new();
        for exp in self.iter() {
            let mut ngates = exp.to_gates_naive(&self.arch);
            gates.append(&mut ngates);
        }
        gates.extend_from_slice(&self.tail.gates);

        Circuit { gates, qubits: self.arch.qubits() }
    }
}
