use std::{collections::HashSet, fmt::Debug};
use crate::{Circuit, Gate};
use gf2_linalg::{LinearSpace, Matrix, ToGF2};
use petgraph::graph::UnGraph;

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Pauli {
    I = 0,
    Z = 1,
    X = 2,
    Y = 3
}

impl Pauli {
    pub fn new(z: bool, x: bool) -> Pauli {
        match (z, x) {
            (false, false) => Pauli::I,
            (true, false) => Pauli::Z,
            (false, true) => Pauli::X,
            (true, true) => Pauli::Y
        }
    }

    pub fn z(&self) -> bool {
        matches!(self, Pauli::Z | Pauli::Y)
    }

    pub fn x(&self) -> bool {
        matches!(self, Pauli::X | Pauli::Y)
    }

    pub fn commutes(&self, other: &Pauli) -> bool {
        !((self.x() & other.z()) ^ (self.z() & other.x()))
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PauliString {
    pub xs: Vec<bool>,
    pub zs: Vec<bool>,
    pub sign: bool
}

impl std::fmt::Debug for PauliString {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.sign {
            write!(f, "-")?;
        }
        for i in 0..self.xs.len() {
            match (self.zs[i], self.xs[i]) {
                (false, false) => write!(f, "I")?,
                (false, true) => write!(f, "X")?,
                (true, false) => write!(f, "Z")?,
                (true, true) => write!(f, "Y")?
            }
        }
        Ok(())
    }
}

impl std::ops::MulAssign<&PauliString> for PauliString {
    fn mul_assign(&mut self, rhs: &PauliString) {
        let comm = self.commutes(rhs);
        self.sign ^= rhs.sign ^ !comm;
        for i in 0..self.zs.len() {
            self.zs[i] ^= rhs.zs[i];
            self.xs[i] ^= rhs.xs[i];
        }
    }
}

impl PauliString {
    pub fn random(n: usize) -> PauliString {
        let mut s = Self::identity(n);
        for i in 0..n {
            s.zs[i] = rand::random();
            s.xs[i] = rand::random();
        }
        s
    }

    pub fn random_nontrivial(n: usize) -> PauliString {
        loop {
            let s = Self::random(n);
            if !s.is_identity() { return s }
        }
    }

    pub fn identity(n: usize) -> PauliString {
        PauliString { xs: vec![false; n], zs: vec![false; n], sign: false }
    }

    pub fn is_identity(&self) -> bool {
        !(self.xs.iter().any(|&x| x) | self.zs.iter().any(|&z| z) | self.sign)
    }

    pub fn with_i(mut self, i: usize) -> Self {
        self.zs[i] = false;
        self.xs[i] = false;
        self
    }

    pub fn with_x(mut self, i: usize) -> Self {
        self.zs[i] = false;
        self.xs[i] = true;
        self
    }

    pub fn with_y(mut self, i: usize) -> Self {
        self.zs[i] = true;
        self.xs[i] = true;
        self
    }

    pub fn with_z(mut self, i: usize) -> Self {
        self.zs[i] = true;
        self.xs[i] = false;
        self
    }

    pub fn with(mut self, p: Pauli, i: usize) -> Self {
        self.zs[i] = p.z();
        self.xs[i] = p.x();
        self
    }

    pub fn get(&self, i: usize) -> Pauli {
        Pauli::new(self.zs[i], self.xs[i])
    }

    pub fn cx(&mut self, a: usize, b: usize) {
        self.sign ^= self.xs[a] & self.zs[b] & (self.xs[b] ^ self.zs[a] ^ true);
        self.xs[b] ^= self.xs[a];
        self.zs[a] ^= self.zs[b];
    }

    pub fn h(&mut self, a: usize) {
        self.sign ^= self.xs[a] & self.zs[a];
        std::mem::swap(&mut self.xs[a], &mut self.zs[a]);
    }

    pub fn s(&mut self, a: usize) {
        self.sign ^= self.xs[a] & self.zs[a];
        self.zs[a] ^= self.xs[a];
    }

    pub fn sdg(&mut self, a: usize) {
        self.z(a);
        self.s(a);
    }

    pub fn z(&mut self, a: usize) {
        self.s(a);
        self.s(a);
    }

    pub fn x(&mut self, a: usize) {
        self.h(a);
        self.z(a);
        self.h(a);
    }

    pub fn commutes(&self, other: &PauliString) -> bool {
        let t1 = self.xs.iter().zip(&other.zs)
            .map(|(&x, &z)| x & z)
            .fold(false, |a, b| a ^ b);
        let t2 = self.zs.iter().zip(&other.xs)
            .map(|(&x, &z)| x & z)
            .fold(false, |a, b| a ^ b);
        !(t1 ^ t2)
    }

    pub fn from_vector(matrix: &Matrix) -> Self {
        assert!(matrix.num_cols() == 1 && matrix.num_rows() % 2 == 0);
        let qubits = matrix.num_rows() / 2;
        let mut pauli = PauliString { xs: vec![false; qubits], zs: vec![false; qubits], sign: false };
        for i in 0..qubits {
            pauli.zs[i] = matrix[(i, 0)].into();
            pauli.xs[i] = matrix[(i+qubits, 0)].into();
        }
        pauli
    }

    pub fn to_vector(&self) -> Matrix {
        Matrix::from_data(self.zs.iter().copied().map(ToGF2::to_gf2)
            .chain(self.xs.iter().copied().map(ToGF2::to_gf2))
            .collect(), (2*self.xs.len(), 1))
    }

    pub fn weight(&self) -> usize {
        self.zs.iter().filter(|&&x| x).count() + self.xs.iter().filter(|&&x| x).count()
    }

    pub fn anticommutation_graph(strings: &[PauliString]) -> UnGraph<usize, ()> {
        let mut g = UnGraph::new_undirected();
        let mut nodes = Vec::new();
        for i in 0..strings.len() {
            nodes.push(g.add_node(i));
        }

        for i in 0..strings.len() {
            for j in i+1..strings.len() {
                if !strings[i].commutes(&strings[j]) {
                    g.add_edge(nodes[i], nodes[j], ());
                }
            }
        }

        g
    }

    pub fn qubits(&self) -> usize {
        self.zs.len()
    }
}

#[derive(Clone)]
pub struct CliffordBasis {
    pub qubits: usize,
    pub stabs: Vec<PauliString>,
    pub destabs: Vec<PauliString>,
    stab_space: LinearSpace,
    destab_space: LinearSpace,
    total_space: LinearSpace
}

impl Debug for CliffordBasis {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CliffordBasis")
            .field("qubits", &self.qubits)
            .field("stabs", &self.stabs)
            .field("destabs", &self.destabs)
            .finish_non_exhaustive()
    }
}

impl CliffordBasis {
    pub fn empty(qubits: usize) -> Self {
        CliffordBasis { 
            qubits, stabs: Vec::new(), destabs: Vec::new(), 
            stab_space: LinearSpace::empty(2*qubits),
            destab_space: LinearSpace::empty(2*qubits),
            total_space: LinearSpace::empty(2*qubits), 
        }
    }

    pub fn identity(qubits: usize) -> Self {
        let mut basis = CliffordBasis::empty(qubits);
        for i in 0..qubits {
            basis.add_stabilizer(PauliString::identity(qubits).with_z(i));
            basis.add_destabilizer(PauliString::identity(qubits).with_x(i));
        }
        basis
    }

    pub fn is_identity(&self) -> bool {
        if self.stabs.len() != self.qubits || self.destabs.len() != self.qubits { return false }
        for i in 0..self.qubits {
            let si = &self.stabs[i];
            let di = &self.destabs[i];
            if !si.zs[i] || si.xs[i] || !di.xs[i] || di.zs[i] { return false }
            if si.weight() != 1 || di.weight() != 1 { return false }
        }
        true
    }

    pub fn stabilizer_mat(&self) -> Matrix {
        if self.stabs.len() > 0 {
            Matrix::hstack(&self.stabs.iter().map(PauliString::to_vector).collect::<Vec<_>>())
        } else {
            Matrix::zeros(2*self.qubits, 0)
        }
    }

    pub fn destabilizer_mat(&self) -> Matrix {
        if self.destabs.len() > 0 {
            Matrix::hstack(&self.destabs.iter().map(PauliString::to_vector).collect::<Vec<_>>())
        } else {
            Matrix::zeros(2*self.qubits, 0)
        }
    }

    pub fn can_add_stabilizer(&self, pauli: &PauliString) -> bool {
        if self.stabs.iter().any(|s| !s.commutes(pauli)) {
            return false;
        }

        let pvec = pauli.to_vector().transpose();
        if self.stab_space.contains(&pvec) {
            return true;
        }

        !self.total_space.contains(&pvec)
    }

    pub fn add_stabilizer(&mut self, pauli: PauliString) {
        let pvec = pauli.to_vector().transpose();
        if !self.stab_space.contains(&pvec) {
            self.stabs.push(pauli);
            self.stab_space.push(&pvec);
            self.total_space.push(&pvec);
        }
    }

    pub fn can_add_destabilizer(&self, pauli: &PauliString) -> bool {
        if self.destabs.iter().any(|s| !s.commutes(pauli)) {
            return false;
        }

        let pvec = pauli.to_vector().transpose();
        if self.destab_space.contains(&pvec) {
            return true;
        }

        !self.total_space.contains(&pvec)
    }

    pub fn add_destabilizer(&mut self, pauli: PauliString) {
        let pvec = pauli.to_vector().transpose();
        if !self.destab_space.contains(&pvec) {
            self.destabs.push(pauli);
            self.destab_space.push(&pvec);
            self.total_space.push(&pvec);
        }
    }

    pub fn pairing_matrix(&self) -> Matrix {
        let mut pairings = Matrix::zeros(self.stabs.len(), self.destabs.len());
        for i in 0..self.stabs.len() {
            for j in 0..self.destabs.len() {
                pairings[(i, j)] = (!self.stabs[i].commutes(&self.destabs[j])).into();
            }
        }
        pairings
    }

    pub fn is_symplectic(&self) -> bool {
        let pairings = self.pairing_matrix();
        pairings.num_cols() == self.qubits && pairings.num_rows() == self.qubits && pairings.is_identity()
    }

    pub fn complete(&mut self) {
        let symp_form = Matrix::zeros(self.qubits, self.qubits).hconcat(&Matrix::eye(self.qubits))
            .vconcat(&Matrix::eye(self.qubits).hconcat(&Matrix::zeros(self.qubits, self.qubits)));
        let mut pairings = self.pairing_matrix();    

        struct Rec<'s>(&'s mut Vec<PauliString>);
        impl<'s> gf2_linalg::GaussRecorder for Rec<'s> {
            fn row_add(&mut self, s: usize, t: usize) {
                let [source, target] = self.0.get_disjoint_mut([s, t]).unwrap();
                *target *= source;
            }

            fn row_swap(&mut self, a: usize, b: usize) {
                self.0.swap(a, b);
            }

            fn col_add(&mut self, source: usize, target: usize) { self.row_add(source, target); }
            fn col_swap(&mut self, a: usize, b: usize) { self.row_swap(a, b); }
        }
        pairings.row_reduce_ext(true, Rec(&mut self.stabs));
        pairings.col_reduce_ext(true, Rec(&mut self.destabs));
        let (_, rank) = pairings.pivot_cols();

        if rank == self.qubits {
            assert!(self.is_symplectic());
            return
        }

        let nstab = self.stabs.len();
        let ndestab = self.destabs.len();

        for i in rank..nstab {
            let joint = self.stabilizer_mat().hconcat(&self.destabilizer_mat()).transpose().dot(&symp_form);
            let target = Matrix::basis_vector(self.stabs.len() + self.destabs.len(), i);
            let new = PauliString::from_vector(&joint.solve(&target).unwrap());
            self.destabs.push(new);
        }

        for i in rank..ndestab {
            let joint = self.destabilizer_mat().hconcat(&self.stabilizer_mat()).transpose().dot(&symp_form);
            let target = Matrix::basis_vector(self.destabs.len() + self.stabs.len(), i);
            let new = PauliString::from_vector(&joint.solve(&target).unwrap());
            self.stabs.push(new);
        }

        let mut pairings = self.pairing_matrix();
        pairings.row_reduce_ext(true, Rec(&mut self.stabs));
        pairings.col_reduce_ext(true, Rec(&mut self.destabs));

        let joint = self.destabilizer_mat().hconcat(&self.stabilizer_mat()).transpose().dot(&symp_form);
        let nsp = joint.null_space();
        let mut pool = (0..nsp.num_cols()).map(|i| PauliString::from_vector(&nsp.col(i))).collect::<Vec<_>>();
        for i in (0..pool.len()).step_by(2) {
            let j = (i+1..pool.len()).find(|&j| !pool[j].commutes(&pool[i])).unwrap();
            pool.swap(i + 1, j);
            for j in i+2..pool.len() {
                if !pool[j].commutes(&pool[i]) {
                    let [pj, pi] = pool.get_disjoint_mut([j, i+1]).unwrap();
                    *pj *= pi;
                }

                if !pool[j].commutes(&pool[i+1]) {
                    let [pj, pi] = pool.get_disjoint_mut([j, i]).unwrap();
                    *pj *= pi;
                }
            }
            self.stabs.push(pool[i].clone());
            self.destabs.push(pool[i+1].clone());
        }
        
        self.stab_space = LinearSpace::new(self.stabilizer_mat().transpose());
        self.destab_space = LinearSpace::new(self.destabilizer_mat().transpose());
        self.total_space = LinearSpace::new(self.stabilizer_mat().transpose().vconcat(&self.destabilizer_mat().transpose()));

        assert!(self.is_symplectic());
    }

    pub fn cx(&mut self, i: usize, j: usize) {
        for s in &mut self.stabs {
            s.cx(i, j);
        }

        for s in &mut self.destabs {
            s.cx(i, j);
        }
    }

    pub fn h(&mut self, i: usize) {
        for s in &mut self.stabs {
            s.h(i);
        }

        for s in &mut self.destabs {
            s.h(i);
        }
    }

    pub fn s(&mut self, i: usize) {
        for s in &mut self.stabs {
            s.s(i);
        }

        for s in &mut self.destabs {
            s.s(i);
        }
    }

    pub fn sdg(&mut self, i: usize) {
        for s in &mut self.stabs {
            s.sdg(i);
        }

        for s in &mut self.destabs {
            s.sdg(i);
        }
    }

    pub fn z(&mut self, i: usize) {
        for s in &mut self.stabs {
            s.z(i);
        }

        for s in &mut self.destabs {
            s.z(i);
        }
    }

    pub fn x(&mut self, i: usize) {
        for s in &mut self.stabs {
            s.x(i);
        }

        for s in &mut self.destabs {
            s.x(i);
        }
    }

    // This is the procedure from 2309.08972
    pub fn reduce_pair_simplified(&mut self, row: usize, col: usize, rec: &mut (impl CliffordRecorder + ?Sized)) {
        use Pauli::{I, X, Y, Z};

        // Make all the stabilizer Paulis Zs
        for i in 0..self.qubits {
            match self.stabs[col].get(i) {
                X => { self.h(i); rec.h(i) },
                Y => { self.sdg(i); rec.sdg(i); self.h(i); rec.h(i) },
                I | Z => ()
            }
        }

        // If the target is not a Z, then make it one
        if self.stabs[col].get(row) == I {
            let pivot = self.stabs[col].zs.iter().position(|&z| z == true).unwrap();
            self.cx(row, pivot); rec.cx(row, pivot);
        }

        // Eliminate all non-target qubits in the stabilizer
        for i in 0..self.qubits {
            if i == row { continue }
            if self.stabs[col].get(i) == Z { self.cx(i, row); rec.cx(i, row); }
        }

        // Make all the destabilizer Paulis Xs 
        // (this works on the target since the stabilizer is a Z and 
        // it anticommutes with the destabilizer, so it can only be X or Y)
        for i in 0..self.qubits {
            match self.destabs[col].get(i) {
                Z => { self.h(i); rec.h(i) },
                Y => { self.sdg(i); rec.sdg(i); },
                I | X => ()
            }
        }

        // Eliminate all non-target qubits in the destabilizer
        for i in 0..self.qubits {
            if i == row { continue }
            if self.destabs[col].get(i) == X { self.cx(row, i); rec.cx(row, i); }
        }

        // Fix signs
        if self.stabs[col].sign { self.x(row); rec.x(row); }
        if self.destabs[col].sign { self.z(row); rec.z(row); }
    }

    pub fn reduce_pair(&mut self, row: usize, col: usize, rec: &mut (impl CliffordRecorder + ?Sized)) {
        use Pauli::{I, X, Y, Z};

        // Make only one qubit anticommute, try to make it the target
        let mut idx = 0;
        while idx < self.qubits {
            let a = &self.stabs[col];
            let b = &self.destabs[col];
            let Some(i) = (idx..self.qubits).find(|&i| i != row && !a.get(i).commutes(&b.get(i))) else { break; };
            let Some(j) = (i+1..self.qubits).find(|&i| i != row && !a.get(i).commutes(&b.get(i))) else { break; };
            idx = j + 1;
            match (a.get(i), b.get(i), a.get(j), b.get(j)) {
                (Z, X, X, Y) | (Z, Y, X, Z) | (X, Z, Y, X) | (X, Y, Y, Z) | (Y, Z, Z, X) | (Y, X, Z, Y) => { 
                    self.cx(j, i); rec.cx(j, i);
                },
                (Z, X, X, Z) | (Z, Y, X, Y) | (X, Z, Z, X) | (X, Y, Z, Y) | (Y, Z, Y, X) | (Y, X, Y, Z) => { 
                    self.h(j); rec.h(j); self.cx(i, j); rec.cx(i, j);
                },
                _ => { self.cx(i, j); rec.cx(i, j) }
            }
        }

        // Move it to the target qubit, if it's not already there
        let a = &self.stabs[col];
        let b = &self.destabs[col];
        let pivot = (0..self.qubits).find(|&i| !a.get(i).commutes(&b.get(i))).unwrap();
        if pivot != row {
            self.cx(pivot, row);
            rec.cx(pivot, row);
            self.cx(row, pivot);
            rec.cx(row, pivot);
            self.cx(pivot, row);
            rec.cx(pivot, row);
        }

        // Make all non-pivot vars ZI, IX, or ZZ
        for i in 0..self.qubits {
            if i == row { continue }
            if self.stabs[col].get(i) == Y || self.destabs[col].get(i) == Y {
                self.sdg(i); rec.sdg(i);
            }
            if self.stabs[col].get(i) == X || (self.stabs[col].get(i) == I && self.destabs[col].get(i) == Z) {
                self.h(i); rec.h(i);
            }
        }

        // Map pivot to (Z, X)
        match self.stabs[col].get(row) {
            Z => (),
            X => { self.h(row); rec.h(row); },
            Y => { self.sdg(row); rec.sdg(row); self.h(row); rec.h(row); },
            I => unreachable!()
        }
        if self.destabs[col].get(row) == Y { self.sdg(row); rec.sdg(row); }

        // Eliminate ZI and IX
        for i in 0..self.qubits {
            if i == row { continue; }
            match (self.stabs[col].get(i), self.destabs[col].get(i)) {
                (Z, I) => { self.cx(i, row); rec.cx(i, row); },
                (I, X) => { self.cx(row, i); rec.cx(row, i); },
                _ => ()
            }
        }

        // Eliminate ZZ
        let has_zz = self.stabs[col].weight() > 1;
        if has_zz { self.sdg(row); rec.sdg(row); }
        for i in 0..self.qubits {
            if i == row { continue; }
            if self.stabs[col].get(i) == Z { self.cx(i, row); rec.cx(i, row); }
        }
        if has_zz { self.s(row); rec.s(row); }
        
        // Fix signs
        if self.stabs[col].sign { self.x(row); rec.x(row); }
        if self.destabs[col].sign { self.z(row); rec.z(row); }
    }

    pub fn synthesize(&mut self, rec: &mut (impl CliffordRecorder + ?Sized)) {
        assert!(self.is_symplectic());

        let mut visited = HashSet::new();
        for _ in 0..self.qubits {
            let pivot = (0..self.qubits)
                .filter(|i| !visited.contains(i))
                .min_by_key(|&i| self.stabs[i].weight() + self.destabs[i].weight())
                .unwrap();
            self.reduce_pair(pivot, pivot, rec);
            visited.insert(pivot);
        }
    }

    pub fn inverse(&self) -> CliffordBasis {
        assert!(self.is_symplectic());
        let mut inv = CliffordBasis::identity(self.qubits);
        self.clone().synthesize(&mut inv);
        inv
    }

    #[must_use]
    pub fn apply_gates(&mut self, gates: impl Iterator<Item=Gate>) -> Option<()> {
        for gate in gates {
            match gate {
                Gate::CX(a, b) => self.cx(a, b),
                Gate::H(a) => self.h(a),
                Gate::S(a) => self.s(a),
                Gate::Sdg(a) => self.sdg(a),
                Gate::Z(a) => self.z(a),
                Gate::X(a) => self.x(a),
                Gate::T(_) => return None
            }
        }
        Some(())
    }
    
    pub fn from_circuit(circ: &Circuit) -> Option<CliffordBasis> {
        let mut basis = Self::identity(circ.qubits);
        basis.apply_gates(circ.gates.iter().copied())?;
        Some(basis)
    }
}

pub trait CNOTRecorder {
    fn cx(&mut self, i: usize, j: usize);
}

pub trait CliffordRecorder: CNOTRecorder {
    fn h(&mut self, i: usize);
    fn s(&mut self, i: usize);

    fn sdg(&mut self, i: usize) {
        self.z(i);
        self.s(i);
    }

    fn z(&mut self, i: usize) {
        self.s(i);
        self.s(i);
    }

    fn x(&mut self, i: usize) {
        self.h(i);
        self.z(i);
        self.h(i);
    }
}

impl CNOTRecorder for () {
    fn cx(&mut self, _i: usize, _j: usize) {}
}

impl CliffordRecorder for () {
    fn h(&mut self, _i: usize) {}
    fn s(&mut self, _i: usize) {}
}

impl CNOTRecorder for CliffordBasis {
    fn cx(&mut self, i: usize, j: usize) {
        self.cx(i, j);
    }
}

impl CliffordRecorder for CliffordBasis {
    fn h(&mut self, i: usize) {
        self.h(i);
    }

    fn s(&mut self, i: usize) {
        self.s(i);
    }
}

impl CNOTRecorder for PauliString {
    fn cx(&mut self, i: usize, j: usize) {
        self.cx(i, j);
    }
}

impl CliffordRecorder for PauliString {
    fn h(&mut self, i: usize) {
        self.h(i);
    }

    fn s(&mut self, i: usize) {
        self.s(i);
    }
}

impl<R: CNOTRecorder> CNOTRecorder for [R] {
    fn cx(&mut self, i: usize, j: usize) {
        for e in self {
            e.cx(i, j);
        }
    }
}

impl<R: CliffordRecorder> CliffordRecorder for [R] {
    fn h(&mut self, i: usize) {
        for e in self {
            e.h(i);
        }
    }

    fn s(&mut self, i: usize) {
        for e in self {
            e.s(i);
        }
    }
}

impl<A: CNOTRecorder + ?Sized, B: CNOTRecorder + ?Sized> CNOTRecorder for (&mut A, &mut B) {
    fn cx(&mut self, i: usize, j: usize) {
        self.0.cx(i, j);
        self.1.cx(i, j);
    }
}

impl<A: CliffordRecorder + ?Sized, B: CliffordRecorder + ?Sized> CliffordRecorder for (&mut A, &mut B) {
    fn h(&mut self, i: usize) {
        self.0.h(i);
        self.1.h(i);
    }

    fn s(&mut self, i: usize) {
        self.0.s(i);
        self.1.s(i);
    }
}

impl CNOTRecorder for Circuit {
    fn cx(&mut self, i: usize, j: usize) {
        self.gates.push(Gate::CX(i, j));
    }
}

impl CliffordRecorder for Circuit {
    fn h(&mut self, i: usize) {
        self.gates.push(Gate::H(i));
    }

    fn s(&mut self, i: usize) {
        self.gates.push(Gate::S(i));
    }

    fn sdg(&mut self, i: usize) {
        self.gates.push(Gate::Sdg(i));
    }

    fn x(&mut self, i: usize) {
        self.gates.push(Gate::X(i));
    }

    fn z(&mut self, i: usize) {
        self.gates.push(Gate::Z(i));
    }
}
