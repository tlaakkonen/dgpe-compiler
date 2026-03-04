use petgraph::{Direction, graph::{DiGraph, NodeIndex}};

use crate::{Circuit, CliffordBasis, GlobalArch, NonlocalExp, PauliExp, PauliString, PhaseExp, SteinerForest, dist::BlockTableau};

#[derive(Clone)]
pub struct NLPhaseExp {
    pub phase: usize,
    pub strings: Vec<PauliString>
}

impl std::fmt::Debug for NLPhaseExp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "P({:?},{})", self.strings, self.phase)
    }
}

impl NLPhaseExp {
    pub fn from_global_string(phase: usize, string: &PauliString, arch: &GlobalArch) -> NLPhaseExp {
        let mut did_sign = false;
        NLPhaseExp {
            phase, strings: (0..arch.num_parts()).map(|p| {
                let part = &arch.parts[p];
                let mut pstring = PauliString::identity(part.qubits.len());
                for &q in &arch.parts[p].qubits {
                    let q = part.topo[q];
                    pstring.set(q.offset, string.get(q.global))
                }
                let sign = if !did_sign && (!pstring.is_identity() || p == arch.num_parts() - 1) {
                    did_sign = true;
                    string.sign
                } else { false };
                pstring.with_sign(sign)
            }).collect()
        }
    }

    pub fn nonlocal_exp(&mut self, exp: &NonlocalExp) {
        match (self.strings[exp.idx_a].commutes(&exp.string_a), self.strings[exp.idx_b].commutes(&exp.string_b)) {
            (true, true) => (),
            (false, true) => {
                // They commute
                let _ = self.strings[exp.idx_b].mul_from(&exp.string_b);
            },
            (true, false) => {
                // They commute
                let _ = self.strings[exp.idx_a].mul_from(&exp.string_a);
            },
            (false, false) => {
                // They both anti-commute
                let _ = self.strings[exp.idx_a].mul_from(&exp.string_a);
                let _ = self.strings[exp.idx_b].mul_from(&exp.string_b);
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct NLPhaseCircuit {
    pub dag: DiGraph<NLPhaseExp, ()>,
    pub arch: GlobalArch,
    pub tail: BlockTableau
}

impl NLPhaseCircuit {
    pub fn from_circuit(circ: &Circuit, arch: &GlobalArch) -> NLPhaseCircuit {
        let aa_arch = GlobalArch::all_to_all(1, circ.qubits);
        let phase_circ = circ.partition_naive(&aa_arch);
        let tableau = CliffordBasis::from_circuit(&phase_circ.tail.inverse()).unwrap();
        let dtab = BlockTableau::new(&tableau, arch);

        NLPhaseCircuit { 
            dag: phase_circ.dag.map_owned(|_, pe| {
                let PauliExp::Phase(pe) = pe else { unreachable!() };
                NLPhaseExp::from_global_string(pe.phase, &pe.string, arch)
            }, |_, _| ()),
            arch: arch.clone(), tail: dtab
        }
    }

    pub fn nonlocal_exp(&mut self, exp: &NonlocalExp) {
        for pe in self.dag.node_weights_mut() {
            pe.nonlocal_exp(exp);
        }
        self.tail.nonlocal_exp(exp);
    }

    pub fn cost_vector(&self) -> Vec<(usize, NodeIndex, SteinerForest)> {
        let mut costs = Vec::new();
        for node in self.dag.node_indices() {
            if self.dag.neighbors_directed(node, Direction::Incoming).next().is_some() {
                continue
            }

            let phase = &self.dag[node];
            let mut leaf_count = 0;
            let leaves = (0..self.arch.num_parts()).filter(|&p| {
                !phase.strings[p].is_identity()
            }).inspect(|_| { leaf_count += 1; }).map(|p| self.arch.parts[p].idx);
            let forest = self.arch.topo.steiner_forest(leaves, []);

            let score = 2*forest.size() - leaf_count - 1;
            costs.push((score, node, forest));
        }

        costs.sort_by_key(|&(score, _, _)| score);
        costs
    }

    /// A simplified version of 2104.00934
    pub fn synthesize(&mut self, exps: &mut Vec<PauliExp>) -> Circuit {
        while self.dag.node_count() > 0 {
            let cvec = self.cost_vector();
            let (_, node, forest) = cvec.into_iter().min_by_key(|&(score, _, _)| score).unwrap();

            // Fill in the tree
            for (_, parent, child) in forest.edges_postorder(forest.arbitrary_node().unwrap(), false) {
                let parent = self.arch.topo[parent];
                let child = self.arch.topo[child];
                let pe = &self.dag[node];
                if !pe.strings[parent].is_identity() { continue }
                let string_a = pe.strings[child].qubit_anticommuting().unwrap();
                let exp = NonlocalExp { idx_a: child, idx_b: parent, string_b: string_a.clone(), string_a };
                self.nonlocal_exp(&exp);
                exps.push(PauliExp::Nonlocal(exp));
            }

            assert!(forest.nodes().all(|n| !self.dag[node].strings[self.arch.topo[n]].is_identity()));

            // Pick the pivot in the tree which minimizes a heuristic.
            // The heuristic is min-fill-in assuming that any exp between a non-identity
            // and an identity string will increase the number of non-identity strings
            // (i.e it assumes that there is no cancellation, the equivalent for parity
            // tables would be row operations in the boolean semiring instead of F2)
            // While this would not work well for parity tables, it is likely to be 
            // pretty accurate for non-tiny block sizes, because cancellation then
            // becomes exponentially unlikely.
            let pivot = forest.nodes().min_by_key(|&p| {
                forest.edges_postorder(p, false)
                    .map(|(_, parent, child)| {
                        let parent = self.arch.topo[parent];
                        let child = self.arch.topo[child];
                        self.dag.node_weights().filter(|&pe| {
                            pe.strings[parent].is_identity() ^ pe.strings[child].is_identity()
                        }).count()
                    }).sum::<usize>()
            }).unwrap();
            
            // Clear the tree from the pivot
            for (_, parent, child) in forest.edges_postorder(pivot, false) {
                let parent = self.arch.topo[parent];
                let child = self.arch.topo[child];
                let pe = &self.dag[node];
                let string_a = pe.strings[parent].qubit_anticommuting().unwrap();
                let string_b = pe.strings[child].clone();
                let exp = NonlocalExp { idx_a: parent, idx_b: child, string_a, string_b  };
                self.nonlocal_exp(&exp);
                exps.push(PauliExp::Nonlocal(exp));
            }

            assert!(forest.nodes().all(|n| n == pivot || self.dag[node].strings[self.arch.topo[n]].is_identity()));
            assert!(!self.dag[node].strings[self.arch.topo[pivot]].is_identity());

            let pivot = self.arch.topo[pivot];
            let pstring = self.dag[node].strings[pivot].clone();
            let sign = self.dag[node].strings.iter().map(|s| s.sign).reduce(|a, b| a ^ b).unwrap();
            let phase_exp = PauliExp::Phase(PhaseExp {
                idx: pivot, 
                phase: self.dag[node].phase,
                string: pstring.with_sign(sign)
            });
            exps.push(phase_exp);

            self.dag.remove_node(node);
        }

        self.tail.synthesize_constrained(&self.arch, exps);
        self.tail.to_local_circuit(&self.arch)
    }
}
