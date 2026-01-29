use std::{collections::HashSet, fmt::Debug};
use crate::{Circuit, Gate, LocalArch};
use gf2_linalg::{LinearSpace, Matrix, ToGF2};
use petgraph::graph::UnGraph;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
        } else if f.sign_plus() {
            write!(f, "+")?;
        } else if f.sign_minus() {
            write!(f, " ")?;
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

    /// NB: This function does not check for a sign!
    pub fn is_identity(&self) -> bool {
        !(self.xs.iter().any(|&x| x) | self.zs.iter().any(|&z| z))
    }

    pub fn is_signed_identity(&self) -> bool {
        !self.sign && self.is_identity()
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

    pub fn with_sign(mut self, sign: bool) -> Self {
        self.sign = sign;
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

    pub fn swap_zx(mut self) -> Self {
        std::mem::swap(&mut self.zs, &mut self.xs);
        self
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

    /// Multiply a Pauli string into this one.
    /// Returns true if an extra i phase was produced, because they anticommute.
    /// Marked must_use because you should justify ignoring the phase!
    #[must_use]
    pub fn mul_from(&mut self, rhs: &PauliString) -> bool {
        self.sign ^= rhs.sign;
        let mut phase = false;
        for i in 0..self.zs.len() {
            let anti = self.zs[i] & rhs.xs[i] ^ self.xs[i] & rhs.zs[i];
            let extra = (!self.zs[i] & !rhs.xs[i]) | (self.zs[i] & rhs.xs[i] & rhs.zs[i]) | (self.zs[i] & rhs.xs[i] & self.xs[i]);
            if anti { 
                phase = !phase;
                if !phase ^ extra { self.sign = !self.sign; }
            }

            self.zs[i] ^= rhs.zs[i];
            self.xs[i] ^= rhs.xs[i];
        }
        phase
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

    // Try to find a single-qubit Pauli string which anticommutes with this one
    pub fn qubit_anticommuting(&self) -> Option<PauliString> {
        (0..self.qubits()).filter_map(|i| match self.get(i) {
            Pauli::I => None,
            Pauli::X | Pauli::Y => Some(PauliString::identity(self.qubits()).with_z(i)),
            Pauli::Z => Some(PauliString::identity(self.qubits()).with_x(i))
        }).next()
    }

    // Try to find a Pauli string which anticommutes with this one and commutes with the other
    pub fn paired_anticommuting(&self, other: &PauliString) -> Option<PauliString> {
        (0..self.qubits()).filter_map(|i| match (self.get(i), other.get(i)) {
            (Pauli::Z, Pauli::I | Pauli::X) => Some(PauliString::identity(self.qubits()).with_x(i)),
            (Pauli::Z, Pauli::Y) => Some(PauliString::identity(self.qubits()).with_y(i)),
            (Pauli::X, Pauli::I | Pauli::Z) => Some(PauliString::identity(self.qubits()).with_z(i)),
            (Pauli::X, Pauli::Y) => Some(PauliString::identity(self.qubits()).with_y(i)),
            (Pauli::Y, Pauli::I | Pauli::Z) => Some(PauliString::identity(self.qubits()).with_z(i)),
            (Pauli::Y, Pauli::X) => Some(PauliString::identity(self.qubits()).with_x(i)),
            _ => None
        }).next()
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
        writeln!(f, "CliffordBasis(qubits={},stabs={},destabs={}):", self.qubits, self.stabs.len(), self.destabs.len())?;
        if self.stabs.len() == 0 && self.destabs.len() == 0 { return Ok(()) }
        for i in 0..self.stabs.len().max(self.destabs.len()) {
            if i < self.stabs.len() && i < self.destabs.len() {
                write!(f, "{:-?} | {:-?}", self.stabs[i], self.destabs[i])?;
            } else if i < self.stabs.len() {
                write!(f, "{:-?} |", self.stabs[i])?;
            } else {
                write!(f, "{: <1$} | {2:-?}", "", self.qubits + 1, self.destabs[i])?;
            }
            if i < self.stabs.len().max(self.destabs.len()) - 1 {
                writeln!(f)?;
            }
        }
        Ok(())
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
                // Phases are irrelevant for finding a completion
                let _ = target.mul_from(&source);
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
                    // Phases are irrelevant for finding a completion
                    let _ = pj.mul_from(pi);
                }

                if !pool[j].commutes(&pool[i+1]) {
                    let [pj, pi] = pool.get_disjoint_mut([j, i]).unwrap();
                    // Phases are irrelevant for finding a completion
                    let _ = pj.mul_from(pi);
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
    pub fn reduce_pair_sweep(&mut self, arch: Option<&LocalArch>, row: usize, col: usize, rec: &mut (impl CliffordRecorder + ?Sized)) {
        use Pauli::{I, X, Y, Z};

        // Make all the stabilizer Paulis Zs
        for i in 0..self.qubits {
            match self.stabs[col].get(i) {
                X => { self.h(i); rec.h(i) },
                Y => { self.sdg(i); rec.sdg(i); self.h(i); rec.h(i) },
                I | Z => ()
            }
        }

        if let Some(arch) = arch {
            // Constrained case
            // Find a Steiner tree connecting the target and the non-identity qubits in the stabilizer
            let leaves = (0..self.qubits)
                .filter(|&i| self.stabs[col].zs[i])
                .map(|i| arch.qubits[i]);
            let tree = arch.topo.steiner_forest(leaves, [arch.qubits[row]]);

            // Fill the Steiner points and target
            for (_, parent, child) in tree.edges_postorder(arch.qubits[row], false) {
                let parent = arch.topo[parent].offset;
                let child = arch.topo[child].offset;
                if !self.stabs[col].zs[parent] {
                    self.cx(parent, child); rec.cx(parent, child);
                }
            }

            // Clear the non-target qubits
            for (_, parent, child) in tree.edges_postorder(arch.qubits[row], false) {
                let parent = arch.topo[parent].offset;
                let child = arch.topo[child].offset;
                self.cx(child, parent); rec.cx(child, parent);
            }
        } else {
            // All-to-all case
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

        if let Some(arch) = arch {
            // Constrained case
            // Find a Steiner tree connecting the target and the non-identity qubits in the destabilizer
            let leaves = (0..self.qubits)
                .filter(|&i| self.destabs[col].xs[i])
                .map(|i| arch.qubits[i]);
            let tree = arch.topo.steiner_forest(leaves, [arch.qubits[row]]);

            // Fill the Steiner points and target
            for (_, parent, child) in tree.edges_postorder(arch.qubits[row], false) {
                let parent = arch.topo[parent].offset;
                let child = arch.topo[child].offset;
                if !self.destabs[col].xs[parent] {
                    self.cx(child, parent); rec.cx(child, parent);
                }
            }

            // Clear the non-target qubits
            for (_, parent, child) in tree.edges_postorder(arch.qubits[row], false) {
                let parent = arch.topo[parent].offset;
                let child = arch.topo[child].offset;
                self.cx(parent, child); rec.cx(parent, child);
            }
        } else {
            // All-to-all case
            // Eliminate all non-target qubits in the destabilizer
            for i in 0..self.qubits {
                if i == row { continue }
                if self.destabs[col].get(i) == X { self.cx(row, i); rec.cx(row, i); }
            }
        }

        // Fix signs
        if self.stabs[col].sign { self.x(row); rec.x(row); }
        if self.destabs[col].sign { self.z(row); rec.z(row); }
    }

    // This is (a version of) the procedure from 2105.02291
    pub fn reduce_pair_match(&mut self, row: usize, col: usize, rec: &mut (impl CliffordRecorder + ?Sized)) {
        use Pauli::{I, X, Y, Z};

        // Map all qubits to ZI, IX, ZZ, or ZX
        for i in 0..self.qubits {
            if self.stabs[col].get(i) == Y { self.sdg(i); rec.sdg(i); }
            if self.stabs[col].get(i) == X { self.h(i); rec.h(i); }
            if self.destabs[col].get(i) == Y { self.sdg(i); rec.sdg(i); }
            if self.stabs[col].get(i) == I && self.destabs[col].get(i) == Z { self.h(i); rec.h(i); }
        }

        // Unconstrained case
        // Find the anticommuting qubits that are not the target
        let anticommuting = (0..self.qubits)
            .filter(|&i| i != row && !self.stabs[col].get(i).commutes(&self.destabs[col].get(i)))
            .collect::<Vec<_>>();
        // Eliminate as many as possible by pairing them up
        for (&i, &j) in anticommuting.iter().zip(anticommuting.iter().skip(1)).step_by(2) {
            self.cx(i, j); rec.cx(i, j);
        }
        // If the target does not anticommute, make it so:
        if anticommuting.len() % 2 == 1 {
            // The last anticommuting qubit must have been unmatched
            let pivot = anticommuting[anticommuting.len() - 1];
            match (self.stabs[col].get(row), self.destabs[col].get(row)) {
                (Z, I) => { self.cx(pivot, row); rec.cx(pivot, row); },
                (I, X) => { self.cx(row, pivot); rec.cx(row, pivot); },
                (Z, Z) => { 
                    self.cx(pivot, row); rec.cx(pivot, row); 
                    self.sdg(row); rec.sdg(row); 
                    self.sdg(pivot); rec.sdg(pivot); 
                },
                (I, I) => {
                    self.cx(pivot, row); rec.cx(pivot, row);
                    self.cx(row, pivot); rec.cx(row, pivot);
                },
                _ => unreachable!()
            }
        }

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
        let has_zz = self.destabs[col].zs.iter().any(|&z| z);
        if has_zz { self.sdg(row); rec.sdg(row); }
        for i in 0..self.qubits {
            if i == row { continue; }
            if self.stabs[col].get(i) == Z && self.destabs[col].get(i) == Z { self.cx(i, row); rec.cx(i, row); }
        }
        if has_zz { self.s(row); rec.s(row); }
        
        // Fix signs
        if self.stabs[col].sign { self.x(row); rec.x(row); }
        if self.destabs[col].sign { self.z(row); rec.z(row); }
    }

    pub fn synthesize(&mut self, method: SynthesisMethod, rec: &mut (impl CliffordRecorder + ?Sized)) {
        assert!(self.is_symplectic());

        let mut visited = HashSet::new();
        for _ in 0..self.qubits {
            let pivot = (0..self.qubits)
                .filter(|i| !visited.contains(i))
                .min_by_key(|&i| self.stabs[i].weight() + self.destabs[i].weight())
                .unwrap();

            match method {
                SynthesisMethod::Match => self.reduce_pair_match(pivot, pivot, rec),
                SynthesisMethod::Sweep => self.reduce_pair_sweep(None, pivot, pivot, rec)
            }

            visited.insert(pivot);
        }
    }

    pub fn synthesize_constrained(&mut self, arch: &LocalArch, rec: &mut (impl CliffordRecorder + ?Sized)) {
        assert!(self.is_symplectic());

        let mut visited = HashSet::new();
        let mut arch = arch.clone();
        for _ in 0..self.qubits {
            let cost_fn = |r: usize| {
                (0..self.qubits).map(|i| {
                    let s = (self.stabs[r].get(i) != Pauli::I) as usize;
                    let d = (self.destabs[r].get(i) != Pauli::I) as usize;
                    if s + d == 0 { 0 } else {
                        arch.topo.distance_between(arch.qubits[r], arch.qubits[i]).unwrap() * (s + d)
                    }
                }).sum::<usize>()
            };

            let pivot = (0..self.qubits)
                .filter(|i| !visited.contains(i))
                .filter(|&i| !arch.topo.is_cutting(arch.qubits[i]))
                .min_by_key(|&i| cost_fn(i))
                .unwrap();

            self.reduce_pair_sweep(Some(&arch), pivot, pivot, rec);

            visited.insert(pivot);
            arch.topo.delete_vertex(arch.qubits[pivot]);
        }
    }

    pub fn inverse(&self) -> CliffordBasis {
        assert!(self.is_symplectic());
        let mut inv = CliffordBasis::identity(self.qubits);
        self.clone().synthesize(SynthesisMethod::Match, &mut inv);
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

    /// Finds the parity matrix of a CNOT circuit which would generate this tableau, if one exists
    pub fn to_parity_matrix(&self) -> Option<Matrix> {
        if self.stabs.iter().any(|s| s.sign || s.xs.iter().any(|&x| x)) 
            || self.destabs.iter().any(|s| s.sign || s.zs.iter().any(|&z| z))
            || !self.is_symplectic() {
            None
        } else {
            Some(self.destabilizer_mat().slice(self.qubits.., ..))
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum SynthesisMethod {
    Sweep,
    Match
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
