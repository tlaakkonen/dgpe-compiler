use gf2_linalg::{GF2, LinearSpace};

use crate::{CliffordBasis, GlobalArch, NonlocalExp, PauliString};

#[derive(Clone)]
pub struct BlockTableau {
    pub indices: Vec<usize>,
    pub stabs: Vec<Vec<PauliString>>,
    pub destabs: Vec<Vec<PauliString>>,
    pub qubits: usize,
    pub parts: usize
}

impl std::fmt::Debug for BlockTableau {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "BlockTableau(qubits={}, parts={}):", self.qubits, self.parts)?;
        for row in 0..self.parts {
            let qbs = self.stabs[row][0].qubits();
            for i in 0..qbs {
                for col in 0..self.parts {
                    for j in self.indices[col]..self.indices[col + 1] {
                        write!(f, "{:?}", self.stabs[row][j].get(i))?;
                        write!(f, "{:?}", self.destabs[row][j].get(i))?;
                    }
                    if col != self.parts - 1 { write!(f, "|")?; }
                }

                if f.sign_plus() {
                    write!(f, " | ")?;
                    for col in 0..self.parts {
                        for j in self.indices[col]..self.indices[col + 1] {
                            write!(f, "{}", if i == (qbs-1)/2 { if self.stabs[row][j].sign { "-" } else { "+" } } else { " " })?;
                            write!(f, "{}", if i == (qbs-1)/2 { if self.destabs[row][j].sign { "-" } else { "+" } } else { " " })?;
                        }
                        if col != self.parts - 1 { write!(f, "|")?; }
                    }
                }

                if i != qbs - 1 { writeln!(f)?; }
            }
            if row != self.parts - 1 {
                writeln!(f)?;
                for col in 0..self.parts {
                    write!(f, "{:-<1$}", "", 2*(self.indices[col + 1] - self.indices[col]))?;
                    if col != self.parts - 1 { write!(f, "+")?; }
                }
                if f.sign_plus() {
                    write!(f, " | ")?;
                    for col in 0..self.parts {
                        write!(f, "{:-<1$}", "", 2*(self.indices[col + 1] - self.indices[col]))?;
                        if col != self.parts - 1 { write!(f, "+")?; }
                    }
                }
                writeln!(f)?;
            }
        }
        Ok(())
    }
}

impl BlockTableau {
    pub fn new(basis: &CliffordBasis, arch: &GlobalArch) -> BlockTableau {
        assert!(basis.is_symplectic());
        assert_eq!(arch.qubits(), basis.qubits);

        let mut stabs = vec![Vec::new(); arch.num_parts()];
        let mut destabs = vec![Vec::new(); arch.num_parts()];
        let mut indices = vec![0];
        for p in 0..arch.num_parts() {
            indices.push(indices[indices.len() - 1] + arch.part_size(p));
            for i in (0..arch.num_parts()).map(|j| arch.range(j)).flatten() {
                let i = i.global;
                stabs[p].push(arch.range(p)
                    .map(|q| (q, basis.stabs[i].get(q.global)))
                    .fold(PauliString::identity(arch.part_size(p)), |s, (q, p)| {
                        s.with(p, q.offset)
                    })
                    .with_sign(if p == 0 { basis.stabs[i].sign } else { false }));
                destabs[p].push(arch.range(p)
                    .map(|q| (q, basis.destabs[i].get(q.global)))
                    .fold(PauliString::identity(arch.part_size(p)), |s, (q, p)| {
                        s.with(p, q.offset)
                    })
                    .with_sign(if p == 0 { basis.destabs[i].sign } else { false }));
            }
        }

        BlockTableau { indices, stabs, destabs, qubits: arch.qubits(), parts: arch.num_parts() }
    }

    pub fn local_cx(&mut self, p: usize, i: usize, j: usize) {
        for s in &mut self.stabs[p] {
            s.cx(i, j);
        }

        for s in &mut self.destabs[p] {
            s.cx(i, j);
        }
    }

    pub fn local_h(&mut self, p: usize, i: usize) {
        for s in &mut self.stabs[p] {
            s.h(i);
        }

        for s in &mut self.destabs[p] {
            s.h(i);
        }
    }

    pub fn local_s(&mut self, p: usize, i: usize) {
        for s in &mut self.stabs[p] {
            s.s(i);
        }

        for s in &mut self.destabs[p] {
            s.s(i);
        }
    }

    fn nonlocal_exp_ref(&mut self, idx_a: usize, idx_b: usize, string_a: &PauliString, string_b: &PauliString) {
        let [stabs_a, stabs_b] = self.stabs.get_disjoint_mut([idx_a, idx_b]).unwrap();
        let [destabs_a, destabs_b] = self.destabs.get_disjoint_mut([idx_a, idx_b]).unwrap();
        let pairs = stabs_a.into_iter().chain(destabs_a).zip(stabs_b.into_iter().chain(destabs_b));
        for (sa, sb) in pairs {
            match (sa.commutes(string_a), sb.commutes(string_b)) {
                (true, true) => (),
                (false, true) => {
                    // No i phase because they commute
                    let _ = sb.mul_from(string_b);
                }, 
                (true, false) => {
                    // No i phase because they commute
                    let _ = sa.mul_from(string_a);
                },
                (false, false) => {
                    // Both i phases because they anticommute.
                    // The phases multiply and cancel out with -1
                    let _ = sa.mul_from(string_a);
                    let _ = sb.mul_from(string_b);
                }
            }
        }
    }

    pub fn nonlocal_exp(&mut self, exp: &NonlocalExp) {
        self.nonlocal_exp_ref(exp.idx_a, exp.idx_b, &exp.string_a, &exp.string_b);
        // println!("{:?}\n{:?}\n", exp, self);
    }

    pub fn reduce_pair_sweep(&mut self, row: usize, col: usize, rec: &mut (impl NonlocalRecorder + ?Sized)) {
        let mut comm_space = LinearSpace::empty(2*self.stabs[row][0].qubits());
        for col_q in self.indices[col]..self.indices[col+1] {
            // Ensure that the target stabilizer is not contained in comm_space
            if comm_space.contains(&self.stabs[row][col_q].to_vector().transpose()) {
                let pivot = (0..self.parts).find(|&p| p != row && !self.stabs[p][col_q].is_identity()).unwrap();
                let string_a = self.stabs[pivot][col_q].qubit_anticommuting().unwrap();
                // Find a non-identity string that commutes with comm_space - by definition it is not contained within it
                let string_b = PauliString::from_vector(&comm_space.basis().null_space().col(0)).swap_zx();
                assert!(!comm_space.contains(&string_b.to_vector().transpose()));
                let exp = NonlocalExp { idx_a: pivot, idx_b: row, string_a, string_b };
                self.nonlocal_exp(&exp); rec.nonlocal_exp(&exp);
            }

            // Now reduce all non-target stabilizer strings to the identity 
            // Find string that commutes with comm_space and anticommutes with the target stabilizer
            let nsp = comm_space.basis().null_space();
            let comms = self.stabs[row][col_q].to_vector().transpose().dot(&nsp);
            let pivot = (0..nsp.num_cols()).find(|&i| comms[(0, i)] != GF2::ZERO).unwrap();
            let string_a = PauliString::from_vector(&nsp.col(pivot)).swap_zx();
            assert!(!string_a.commutes(&self.stabs[row][col_q]));
            for p in 0..self.parts {
                if p == row || self.stabs[p][col_q].is_identity() { continue }
                let exp = NonlocalExp { idx_a: row, idx_b: p, string_a: string_a.clone(), string_b: self.stabs[p][col_q].clone() };
                self.nonlocal_exp(&exp); rec.nonlocal_exp(&exp);
            }

            // At this point we must have self.stabs[row][col_q] and self.destabs[row][col_q] 
            // anticommuting, hence self.destabs[row][col_q] cannot be the identity.
            assert!(!self.stabs[row][col_q].commutes(&self.destabs[row][col_q]));
            // Use stabs to eliminate all the non-target destabs
            for p in 0..self.parts {
                if p == row || self.destabs[p][col_q].is_identity() { continue }
                let exp = NonlocalExp { idx_a: row, idx_b: p, string_a: self.stabs[row][col_q].clone(), string_b: self.destabs[p][col_q].clone() };
                self.nonlocal_exp(&exp); rec.nonlocal_exp(&exp);
            }

            // Fix signs
            for p in 0..self.parts {
                if p == row { continue }
                self.stabs[row][col_q].sign ^= self.stabs[p][col_q].sign;
                self.stabs[p][col_q].sign = false;
                self.destabs[row][col_q].sign ^= self.destabs[p][col_q].sign;
                self.destabs[p][col_q].sign = false;
            }
            
            // Add the stabilizer and destabilizer to the commuting subspace
            comm_space.push(&self.stabs[row][col_q].to_vector().transpose());
            comm_space.push(&self.destabs[row][col_q].to_vector().transpose());
        }

        for p in 0..self.parts {
            if p != row {
                for col_q in self.indices[col]..self.indices[col+1] {
                    assert!(self.stabs[p][col_q].is_identity());
                    assert!(self.destabs[p][col_q].is_identity());
                }
            } else {
                for i in self.indices[col]..self.indices[col+1] {
                    assert!(!self.stabs[p][i].commutes(&self.destabs[p][i]));
                    for j in self.indices[col]..self.indices[col+1] {
                        if i == j { continue }
                        assert!(self.stabs[p][i].commutes(&self.stabs[p][j]));
                        assert!(self.stabs[p][i].commutes(&self.destabs[p][j]));
                        assert!(self.destabs[p][i].commutes(&self.stabs[p][j]));
                        assert!(self.destabs[p][i].commutes(&self.destabs[p][j]));
                    }
                }
            }
        }
    }

    pub fn synthesize(&mut self, rec: &mut (impl NonlocalRecorder + ?Sized)) {
        // println!("{:?}\n", self);
        for row in 0..self.parts {
            self.reduce_pair_sweep(row, row, rec);
        }
    }
}

pub trait NonlocalRecorder {
    fn nonlocal_exp(&mut self, exp: &NonlocalExp);
}

impl NonlocalRecorder for () {
    fn nonlocal_exp(&mut self, _: &NonlocalExp) {}
}

impl NonlocalRecorder for BlockTableau {
    fn nonlocal_exp(&mut self, exp: &NonlocalExp) {
        self.nonlocal_exp(exp);
    }
}

impl NonlocalRecorder for Vec<NonlocalExp> {
    fn nonlocal_exp(&mut self, exp: &NonlocalExp) {
        self.push(exp.clone());
    }
}
