use crate::{PartitionedCircuit, PauliExp, PauliString, PhaseExp, opt::{OptimizationPass, PassMetrics}};

/// Merge the phases of PhaseExps where possible.
#[derive(Debug, Default, Clone, Copy)]
pub struct PhaseTeleportationPass;

impl OptimizationPass for PhaseTeleportationPass {
    fn run_with_metrics(&self, mut circ: PartitionedCircuit, metrics: &mut PassMetrics) -> (PartitionedCircuit, bool) {
        metrics.name("PhaseTeleportation");

        let sort = petgraph::algo::toposort(&circ.dag, None).unwrap();
        let (res, revmap) = petgraph::algo::tred::dag_to_toposorted_adjacency_list::<_, u32>(&circ.dag, &sort);
        let (_, closure) = petgraph::algo::tred::dag_transitive_reduction_closure(&res);

        let mut progress = false;
        for na in circ.dag.node_indices() {
            for nb in circ.dag.node_indices() {
                if na >= nb { continue }

                {   
                    let (PauliExp::Phase(a), PauliExp::Phase(b)) = circ.dag.index_twice_mut(na, nb) else { continue };
                    if a.idx != b.idx || !a.string.unsigned_eq(&b.string) || a.phase == 0 || b.phase == 0 { continue }
                }

                if closure.contains_edge(revmap[na.index()], revmap[nb.index()]) 
                    || closure.contains_edge(revmap[nb.index()], revmap[na.index()]) {
                    continue
                }

                let (PauliExp::Phase(a), PauliExp::Phase(b)) = circ.dag.index_twice_mut(na, nb) else { unreachable!() };
                if a.string.sign == b.string.sign {
                    a.phase = (a.phase + b.phase) % 8;
                } else {
                    a.phase = (a.phase + (8 - b.phase)) % 8;
                }
                b.phase = 0;
                progress = true;
            }
        }
        (circ, progress)
    }
}

/// Merge compatible NonlocalExps where possible
#[derive(Debug, Default, Clone, Copy)]
pub struct NonlocalMergePass;

impl OptimizationPass for NonlocalMergePass {
    fn run_with_metrics(&self, mut circ: PartitionedCircuit, metrics: &mut PassMetrics) -> (PartitionedCircuit, bool) {
        metrics.name("NonlocalMerge");

        let mut sort = petgraph::algo::toposort(&circ.dag, None).unwrap();

        let mut progress = false;
        for i in 0..sort.len() {
            if !matches!(&circ.dag[sort[i]], PauliExp::Nonlocal(_)) { continue }

            // For each i, try to find a j to merge it with
            for j in i+1..sort.len() {
                // Check if these are mergeable and record which strings are to be merged
                let PauliExp::Nonlocal(ni) = &circ.dag[sort[i]] else { continue };
                let PauliExp::Nonlocal(nj) = &circ.dag[sort[j]] else { continue };
                let (i_match_a, j_match_a) = if ni.idx_a == nj.idx_a && ni.idx_b == nj.idx_b && ni.string_a == nj.string_a {
                    (true, true)
                } else if ni.idx_a == nj.idx_b && ni.idx_b == nj.idx_a && ni.string_a == nj.string_b {
                    (true, false)
                } else if ni.idx_b == nj.idx_a && ni.idx_a == nj.idx_b && ni.string_b == nj.string_a {
                    (false, true)
                } else if ni.idx_b == nj.idx_b && ni.idx_a == nj.idx_a && ni.string_b == nj.string_b {
                    (false, false)
                } else {
                    continue
                };

                // How far can j move down towards i?
                let mut v = j;
                while v > i + 1 {
                    if !circ.dag[sort[j]].commutes(&circ.dag[sort[v - 1]]) { break }
                    v -= 1;
                }
                // How far can i move up towards j?
                let mut u = i;
                while u < v - 1 {
                    if !circ.dag[sort[i]].commutes(&circ.dag[sort[u + 1]]) { break }
                    u += 1;
                }

                // If we couldn't move them together, keep looking
                if u != v - 1 { continue }              

                // Reindex for the borrow checker
                let (pi, pj) = circ.dag.index_twice_mut(sort[i], sort[j]);
                let PauliExp::Nonlocal(ni) = pi else { continue };
                let PauliExp::Nonlocal(nj) = pj else { continue };

                // Do the merge: multiply i into j in the unmatched string
                match (i_match_a, j_match_a) {
                    (true, true) => { let _ = nj.string_b.mul_from(&ni.string_b); },
                    (true, false) => { let _ = nj.string_a.mul_from(&ni.string_b); },
                    (false, true) => { let _ = nj.string_b.mul_from(&ni.string_a); },
                    (false, false) => { let _ = nj.string_a.mul_from(&ni.string_a); },
                }

                // If they don't commute we want to replace i with a P(A, pi/2) phase
                // otherwise a P(I, pi/2) phase, on the matching string. 
                let str_i = if i_match_a { &ni.string_a } else { &ni.string_b };
                let phase = PauliExp::Phase(PhaseExp {
                    idx: if i_match_a { ni.idx_a } else { ni.idx_b },
                    phase: 2,
                    string: if ni.commutes(&nj) { PauliString::identity(str_i.qubits()) } else { str_i.clone() }
                });
                circ.dag[sort[i]] = phase;

                // Update the sort to reflect the new position of j
                if v < j {
                    sort[v..=j].reverse();
                    sort[v+1..=j].reverse();
                }

                // We found a merge for i, now continue with i+1
                progress = true;
                break
            }
        }

        // If we made progress, a rebuild is probably needed
        if progress { circ.rebuild(&sort); }
    
        (circ, progress)
    }
}

/// Deletes all trivial operations
#[derive(Debug, Default, Clone, Copy)]
pub struct DeleteTrivialPass;

impl OptimizationPass for DeleteTrivialPass {
    fn run_with_metrics(&self, mut circ: PartitionedCircuit, metrics: &mut PassMetrics) -> (PartitionedCircuit, bool) {
        metrics.name("DeleteTrivial");
        let mut progress = false;

        // Delete P(A, 0), P(+-I, theta), C(A, I), C(I, B), C(+-I, +-I) 
        circ.dag.retain_nodes(|g, n| {
            let delete = match &g[n] {
                PauliExp::Phase(p) => p.phase == 0 || p.string.is_identity(),
                PauliExp::Nonlocal(n) => n.string_a.is_signed_identity() 
                    || n.string_b.is_signed_identity() 
                    || (n.string_a.is_identity() && n.string_b.is_identity())
            };
            progress |= delete;
            !delete
        });

        // Transform C(P, -I) into P(P, pi). 
        // Commutation and hence edges remains the same because -I commutes with everything.
        circ.dag.node_weights_mut().for_each(|p| {
            let PauliExp::Nonlocal(n) = p else { return };
            if n.string_a.is_identity() {
                assert!(n.string_a.sign && !n.string_b.is_identity());
                *p = PauliExp::Phase(PhaseExp { idx: n.idx_b, phase: 4, string: n.string_b.clone() });
                progress = true;
            } else if n.string_b.is_identity() {
                assert!(n.string_b.sign && !n.string_a.is_identity());
                *p = PauliExp::Phase(PhaseExp { idx: n.idx_a, phase: 4, string: n.string_a.clone() });
                progress = true;
            }
        });

        (circ, progress)
    }
}

/// Pushes all local Clifford operations into the tail.
#[derive(Debug, Default, Clone, Copy)]
pub struct CliffordPushPass;

impl OptimizationPass for CliffordPushPass {
    fn run_with_metrics(&self, mut circ: PartitionedCircuit, metrics: &mut PassMetrics) -> (PartitionedCircuit, bool) {
        metrics.name("CliffordPush");

        // Early return if there are no non-trivial Clifford operations.
        if !circ.dag.node_weights().any(|p| p.is_clifford()) {
            return (circ, false)
        }

        // Push Clifford PhaseExps to the right side of the circuit right-to-left
        let mut progress = false;
        let order = petgraph::algo::toposort(&circ.dag, None).unwrap();
        let mut tail = Vec::new();
        for i in (0..order.len()).rev() {
            let PauliExp::Phase(p) = &circ.dag[order[i]] else { continue };
            if !p.is_clifford() { continue };
            let mut gates = p.to_gates_naive(&circ.arch);
            gates.reverse();
            tail.append(&mut gates);
            progress = true;

            for j in i+1..order.len() {
                // Reindex for the borrow checker:
                let (PauliExp::Phase(p), e) = 
                    circ.dag.index_twice_mut(order[i], order[j]) else { unreachable!() };
                // If j is Clifford, we are actually about to delete it
                if e.is_clifford() { continue }
                // Otherwise push i through j
                e.push_clifford(&*p);
            }
        }
        tail.reverse();
        tail.append(&mut circ.tail.gates);
        circ.tail.gates = tail;

        // Rebuild the edges in the DAG to reflect the new circuit.
        // The original order must be a valid ordering of the new DAG so we reuse it.
        // There is probably a quicker way to do this.
        circ.rebuild(&order);

        // Delete the Clifford nodes
        circ.dag.retain_nodes(|g, n| !g[n].is_clifford());
        
        (circ, progress)
    }
}
