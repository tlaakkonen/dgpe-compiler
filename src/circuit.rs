use std::{collections::HashSet, fmt::Debug};
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
                            Gate::S(_) => string.s(q.offset),
                            Gate::Sdg(_) => string.sdg(q.offset),
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
pub struct Bin<S> {
    pub nodes: Vec<NodeIndex>,
    pub state: S
}

#[derive(Debug, Clone)]
pub struct PartitionedCircuit<S=()> {
    pub arch: GlobalArch,
    pub dag: DiGraph<PauliExp, ()>,
    pub bins: Vec<Bin<S>>,
    pub tail: Circuit
}

impl PartitionedCircuit {
    pub fn new(arch: GlobalArch, exps: Vec<PauliExp>, tail: Circuit) -> PartitionedCircuit {
        let mut sets = Vec::new();
        let mut nodes = Vec::new();
        let mut dag = DiGraph::new();
        for (i, exp) in exps.into_iter().rev().enumerate() {
            nodes.push(dag.add_node(exp));
            let mut set = HashSet::new();
            set.insert(i);
            for j in (0..i).rev() {
                if set.contains(&j) || dag[nodes[i]].commutes(&dag[nodes[j]]) { continue; }
                dag.add_edge(nodes[i], nodes[j], ());
                set.extend(&sets[j]);
            }
            sets.push(set);
        }

        nodes.reverse();
        let bin = Bin { state: (), nodes };

        PartitionedCircuit { arch, dag, tail, bins: vec![bin] }
    }
}
