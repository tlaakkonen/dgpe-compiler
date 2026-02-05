use std::collections::HashSet;
use gf2_linalg::{GF2, Matrix};
use crate::{GlobalArch, LocalArch, NonlocalExp, PauliString, dist::NonlocalRecorder};

#[derive(Clone)]
pub struct BlockMatrix {
    pub indices: Vec<usize>,
    pub qubits: usize,
    pub parts: usize,
    pub perm: Vec<Option<usize>>,
    pub mat: Matrix,
    pub itmat: Matrix
}

impl std::fmt::Debug for BlockMatrix {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "BlockMatrix(qubits={},parts={},perm={:?}):", self.qubits, self.parts, self.perm)?;
        for row in 0..self.parts {
            let qbs = self.indices[row+1]-self.indices[row];
            for i in 0..qbs {
                for col in 0..self.parts {
                    for j in self.indices[col]..self.indices[col + 1] {
                        write!(f, "{}", self.mat[(self.indices[row] + i, j)])?;
                    }
                    if col != self.parts - 1 { write!(f, "|")?; }
                }

                if i != qbs - 1 { writeln!(f)?; }
            }
            if row != self.parts - 1 {
                writeln!(f)?;
                for col in 0..self.parts {
                    write!(f, "{:-<1$}", "", (self.indices[col + 1] - self.indices[col]))?;
                    if col != self.parts - 1 { write!(f, "+")?; }
                }
                writeln!(f)?;
            }
        }
        Ok(())
    }
}

impl BlockMatrix {
    pub fn new(parity: &Matrix, arch: &GlobalArch) -> BlockMatrix {
        assert!(parity.is_invertible());
        assert_eq!(arch.qubits(), parity.num_rows());

        let qubits = arch.qubits();
        let parts = arch.num_parts();
        
        let mut indices = vec![0];
        for p in 0..parts {
            indices.push(indices[indices.len() - 1] + arch.part_size(p));
        }

        let mut mat = Matrix::zeros(qubits, qubits);
        for i in (0..parts).map(|k| arch.range(k)).flatten() {
            for j in (0..parts).map(|k| arch.range(k)).flatten() {
                mat[(indices[i.idx] + i.offset, indices[j.idx] + j.offset)] = parity[(i.global, j.global)];
            }
        }

        BlockMatrix { indices, qubits, parts, itmat: mat.inverse().unwrap().transpose(), mat, perm: vec![None; parts] }
    }

    pub fn row_add(&mut self, i: usize, j: usize) {
        self.mat.row_add(i, j);
        self.itmat.row_add(j, i);
    }

    pub fn block(&self, i: usize, j: usize) -> Matrix {
        self.mat.slice(self.indices[i]..self.indices[i+1], self.indices[j]..self.indices[j+1])
    }

    pub fn itblock(&self, i: usize, j: usize) -> Matrix {
        self.itmat.slice(self.indices[i]..self.indices[i+1], self.indices[j]..self.indices[j+1])
    }

    #[must_use]
    pub fn nonlocal_exp(&mut self, exp: &NonlocalExp) -> Option<()> {
        if exp.string_b.zs.iter().any(|&z| z) || exp.string_a.xs.iter().any(|&x| x) {
            return None
        }

        for i in 0..exp.string_b.qubits() {
            for j in 0..exp.string_a.qubits() {
                if exp.string_b.xs[i] && exp.string_a.zs[j] {
                    self.row_add(self.indices[exp.idx_a] + j, self.indices[exp.idx_b] + i);
                }
            }
        }
        Some(())
    }

    pub fn block_row_add(&mut self, row1: usize, row2: usize, mat: &Matrix, rec: &mut (impl NonlocalRecorder + ?Sized)) {
        let decomp = mat.rank_decomposition();
        for r in 0..decomp.c.num_cols() {
            let mut string_a = PauliString::identity(self.indices[row1+1]-self.indices[row1]);
            for j in 0..mat.shape.1 {
                if decomp.f[(r, j)] == GF2::ONE { string_a = string_a.with_z(j); }
            }
            let mut string_b = PauliString::identity(self.indices[row2+1]-self.indices[row2]);
            for i in 0..mat.shape.0 {
                if decomp.c[(i, r)] == GF2::ONE { string_b = string_b.with_x(i); }
            }
            let exp = NonlocalExp { idx_a: row1, idx_b: row2, string_a, string_b };
            rec.nonlocal_exp(&exp);
            let _ = self.nonlocal_exp(&exp);
        }
    }

    // Given A and B, find C with minimal rank such that (A + CB) >= B
    pub fn ensure_image(&mut self, b1: Matrix, b2: Matrix) -> Matrix {
        let mut red = b1.vconcat(&b2);
        red.col_reduce();
        let (pivots, rank) = red.pivot_rows();
        let npivots = pivots[rank..].iter().copied()
            .filter(|&p| p < b1.shape.0);
        let epivots = pivots[..rank].iter().copied()
            .filter(|&p| p >= b1.shape.0).map(|p| p - b1.shape.0);
        let mut mat = Matrix::zeros(b1.shape.0, b2.shape.0);
        for (n, e) in npivots.zip(epivots) {
            mat[(n, e)] = GF2::ONE;
        }
        mat
    }

    // Given A and B so that A >= B, find C with minimal rank so that B + CA = 0
    pub fn block_eliminate(&mut self, b1: Matrix, b2: Matrix) -> Matrix {
        let mut red = b1.vconcat(&b2);
        red.col_reduce();
        let (pivots, rank) = red.pivot_rows();
        let mut mat = Matrix::zeros(b2.shape.0, b1.shape.0);
        for i in 0..b2.shape.0 {
            for j in 0..rank {
                if red[(b1.shape.0 + i, j)] == GF2::ONE {
                    mat[(i, pivots[j])] = GF2::ONE;
                }
            }
        }
        mat
    }

    pub fn eliminate_col(&mut self, arch: Option<&GlobalArch>, row: usize, col: usize, rec: &mut (impl NonlocalRecorder + ?Sized)) {
        if let Some(arch) = arch {
            let leaves = (0..self.parts)
                .filter(|&i| i != row && !self.block(i, col).is_zeros())
                .map(|i| arch.parts[i].idx);
            let tree = arch.topo.steiner_forest(leaves, [arch.parts[row].idx]);
            
            for (_, parent, child) in tree.edges_postorder(arch.parts[row].idx, false) {
                let (parent, child) = (arch.topo[parent], arch.topo[child]);
                let b1 = self.block(parent, col);
                let b2 = self.block(child, col);
                let c = self.ensure_image(b1, b2);
                if c.is_zeros() { continue }
                self.block_row_add(child, parent, &c, rec);
            }

            assert!(self.block(row, col).is_invertible());
            
            for (_, parent, child) in tree.edges_postorder(arch.parts[row].idx, false) {
                let (parent, child) = (arch.topo[parent], arch.topo[child]);
                let b1 = self.block(parent, col);
                let b2 = self.block(child, col);
                let c = self.block_eliminate(b1, b2);
                self.block_row_add(parent, child, &c, rec);
                assert!(self.block(child, col).is_zeros());
            }
        } else {
            for i in 0..self.parts {
                if i == row { continue }
                
                let b2 = self.block(i, col);
                if b2.is_zeros() { continue }

                let b1 = self.block(row, col);
                let c = self.ensure_image(b1, b2);
                if !c.is_zeros() { self.block_row_add(i, row, &c, rec); }

                let b1 = self.block(row, col);
                let b2 = self.block(i, col);
                let c = self.block_eliminate(b1, b2);
                self.block_row_add(row, i, &c, rec);
            }
        }
    }

    pub fn eliminate_row(&mut self, arch: Option<&GlobalArch>, row: usize, col: usize, rec: &mut (impl NonlocalRecorder + ?Sized)) {
        if let Some(arch) = arch {
            let leaves = (0..self.parts)
                .filter(|&i| i != row && !self.itblock(i, col).is_zeros())
                .map(|i| arch.parts[i].idx);
            let tree = arch.topo.steiner_forest(leaves, [arch.parts[row].idx]);

            for (_, parent, child) in tree.edges_postorder(arch.parts[row].idx, false) {
                let (parent, child) = (arch.topo[parent], arch.topo[child]);
                let b1 = self.itblock(parent, col);
                let b2 = self.itblock(child, col);
                let c = self.ensure_image(b1, b2);
                if c.is_zeros() { continue }
                self.block_row_add(parent, child, &c.transpose(), rec);
            }

            assert!(self.itblock(row, col).is_invertible());

            for (_, parent, child) in tree.edges_postorder(arch.parts[row].idx, false) {
                let (parent, child) = (arch.topo[parent], arch.topo[child]);
                let b1 = self.itblock(parent, col);
                let b2 = self.itblock(child, col);
                let c = self.block_eliminate(b1, b2);
                self.block_row_add(child, parent, &c.transpose(), rec);
                assert!(self.itblock(child, col).is_zeros());
            }
        } else {
            for i in 0..self.parts {
                if i == row { continue }
                
                let b2 = self.itblock(i, col);
                if b2.is_zeros() { continue }

                let b1 = self.itblock(row, col);
                let c = self.ensure_image(b1, b2);
                if !c.is_zeros() { self.block_row_add(row, i, &c.transpose(), rec); }

                let b1 = self.itblock(row, col);
                let b2 = self.itblock(i, col);
                let c = self.block_eliminate(b1, b2);
                self.block_row_add(i, row, &c.transpose(), rec);
            }
        }
    }

    pub fn verify_solved(&self) {
        for i in 0..self.parts {
            for j in 0..self.parts {
                if self.perm[j] == Some(i) {
                    assert!(self.block(i, j).is_invertible());
                } else {
                    assert!(self.block(i, j).is_zeros());
                }
            }
        }
    }

    pub fn synthesize(&mut self, rec: &mut (impl NonlocalRecorder + ?Sized)) {
        let mut visited = HashSet::new();
        for _ in 0..self.parts {
            let cost_fn = |r: usize| {
                (0..self.parts).map(|i| {
                    let s = self.block(i, r).rank();
                    let d = self.itblock(i, r).rank();
                    s + d
                }).sum::<usize>()
            };

            let row = (0..self.parts)
                .filter(|&idx| !visited.contains(&idx))
                .min_by_key(|&idx| cost_fn(idx))
                .unwrap();
            self.eliminate_col(None, row, row, rec);
            self.eliminate_row(None, row, row, rec);
            visited.insert(row);
            self.perm[row] = Some(row);
        }

        self.verify_solved();
    }

    pub fn synthesize_constrained(&mut self, arch: &GlobalArch, rec: &mut (impl NonlocalRecorder + ?Sized)) {
        let mut arch = arch.clone();
        let mut visited = HashSet::new();
        for _ in 0..self.parts {
            let cost_fn = |r: usize| {
                (0..self.parts).map(|i| {
                    let s = self.block(i, r).rank();
                    let d = self.itblock(i, r).rank();
                    if s + d == 0 { 0 } else {
                        arch.topo.distance_between(arch.parts[r].idx, arch.parts[i].idx).unwrap() * (s + d)
                    }
                }).sum::<usize>()
            };

            let row = (0..self.parts)
                .filter(|&idx| !visited.contains(&idx))
                .filter(|&idx| !arch.topo.is_cutting(arch.parts[idx].idx))
                .min_by_key(|&idx| cost_fn(idx))
                .unwrap();
            self.eliminate_col(Some(&arch), row, row, rec);
            self.eliminate_row(Some(&arch), row, row, rec);
            arch.topo.delete_vertex(arch.parts[row].idx);
            visited.insert(row);
            self.perm[row] = Some(row);
        }

        self.verify_solved();
    }

    pub fn synthesize_perm(&mut self, rec: &mut (impl NonlocalRecorder + ?Sized)) {
        let mut visited = HashSet::new();
        for _ in 0..self.parts {
            let row_cost_fn = |r| (0..self.parts).map(|i| {
                let s = self.block(r, i).rank();
                let d = self.itblock(r, i).rank();
                s + d
            }).sum::<usize>();

            let col_cost_fn = |c, r| (0..self.parts).map(|i| {
                    let bs = self.block(i, c);
                    let bd = self.itblock(i, c);
                    let n = bs.num_rows().min(bs.num_cols());
                    let s = if i == r { n - bs.rank() } else { bs.rank() };
                    let d = if i == r { n - bd.rank() } else { bd.rank() };
                    s + d
                }).sum::<usize>();

            let row = (0..self.parts)
                .filter(|&idx| !visited.contains(&idx))
                .min_by_key(|&idx| row_cost_fn(idx))
                .unwrap();
            let col = (0..self.parts)
                .filter(|&idx| self.perm[idx].is_none())
                .min_by_key(|&idx| col_cost_fn(idx, row))
                .unwrap();

            self.eliminate_col(None, row, col, rec);
            self.eliminate_row(None, row, col, rec);

            visited.insert(row);
            self.perm[col] = Some(row);
        }

        self.verify_solved();
    }

    pub fn synthesize_perm_constrained(&mut self, arch: &GlobalArch, rec: &mut (impl NonlocalRecorder + ?Sized)) {
        let mut arch = arch.clone();
        let mut visited = HashSet::new();
        for _ in 0..self.parts {
            let row_cost_fn = |r| (0..self.parts).map(|i| {
                let s = self.block(r, i).rank();
                let d = self.itblock(r, i).rank();
                s + d
            }).sum::<usize>();

            let col_cost_fn = |c, r| (0..self.parts).map(|i| {
                    let bs = self.block(i, c);
                    let bd = self.itblock(i, c);
                    let n = bs.num_rows().min(bs.num_cols());
                    let s = if i == r { n - bs.rank() } else { bs.rank() };
                    let d = if i == r { n - bd.rank() } else { bd.rank() };
                    if s + d == 0 { 0 } else {
                        let part: &LocalArch = &arch.parts[r];
                        arch.topo.distance_between(part.idx, arch.parts[i].idx).unwrap() * (s + d)
                    }
                }).sum::<usize>();

            let row = (0..self.parts)
                .filter(|&idx| !visited.contains(&idx))
                .filter(|&idx| !arch.topo.is_cutting(arch.parts[idx].idx))
                .min_by_key(|&idx| row_cost_fn(idx))
                .unwrap();
            let col = (0..self.parts)
                .filter(|&idx| self.perm[idx].is_none())
                .min_by_key(|&idx| col_cost_fn(idx, row))
                .unwrap();

            self.eliminate_col(Some(&arch), row, col, rec);
            self.eliminate_row(Some(&arch), row, col, rec);

            arch.topo.delete_vertex(arch.parts[row].idx);
            visited.insert(row);
            self.perm[col] = Some(row);
        }

        self.verify_solved();
    }
}

impl NonlocalRecorder for BlockMatrix {
    fn nonlocal_exp(&mut self, exp: &NonlocalExp) {
        self.nonlocal_exp(exp).expect("cannot apply non-CNOT NonlocalExp to BlockMatrix")
    }
}
