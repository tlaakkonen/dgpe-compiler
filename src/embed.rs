use std::collections::HashMap;

use dag_bin_packing::BinState;
use petgraph::{graph::DiGraph, visit::EdgeRef};

use crate::{Circuit, GlobalArch, NonlocalExp, PartitionedCircuit, PauliExp, PauliString, opt::PassMetrics};

#[derive(Clone)]
enum EmbedBinState {
    Empty,
    Phase,
    NonEmpty {
        idx_a: usize,
        idx_b: usize,
        a_strs: Option<(PauliString, Option<PauliString>)>,
        b_strs: Option<(PauliString, Option<PauliString>)>,
        count: usize
    }
}

impl dag_bin_packing::BinState for EmbedBinState {
    type Node = PauliExp;
    type Context = ();

    fn new_empty(_c: &Self::Context) -> Self {
        EmbedBinState::Empty
    }

    fn try_add(&mut self, node: &Self::Node, _c: &Self::Context) -> bool {
        match (&mut *self, node) {
            (EmbedBinState::Empty, PauliExp::Phase(_)) => {
                *self = EmbedBinState::Phase;
                true
            },
            (EmbedBinState::Phase, _) => false,
            (EmbedBinState::Empty, PauliExp::Nonlocal(node)) => {
                *self = EmbedBinState::NonEmpty { 
                    idx_a: node.idx_a,
                    idx_b: node.idx_b, 
                    a_strs: Some((node.string_a.clone(), None)), 
                    b_strs: Some((node.string_b.clone(), None)),
                    count: 1
                }; 
                true
            },
            (EmbedBinState::NonEmpty { .. }, PauliExp::Phase(_)) => false,
            (EmbedBinState::NonEmpty { idx_a, idx_b, a_strs, b_strs, count }, PauliExp::Nonlocal(node)) => {
                if !((node.idx_a == *idx_a && node.idx_b == *idx_b) || (node.idx_b == *idx_a && node.idx_a == *idx_b)) { 
                    return false 
                }

                if let Some(aa_strs) = a_strs {
                    if node.idx_a == *idx_a {
                        if node.string_a == aa_strs.0 || Some(&node.string_a) == aa_strs.1.as_ref() {
                            ()
                        } else if aa_strs.1.is_none() && !node.string_a.commutes(&aa_strs.0) {
                            aa_strs.1 = Some(node.string_a.clone());
                        } else {
                            *a_strs = None;
                        }
                    } else if node.idx_b == *idx_a {
                        if node.string_b == aa_strs.0 || Some(&node.string_b) == aa_strs.1.as_ref() {
                            ()
                        } else if aa_strs.1.is_none() && !node.string_b.commutes(&aa_strs.0) {
                            aa_strs.1 = Some(node.string_b.clone());
                        } else {
                            *a_strs = None;
                        }
                    }
                }

                if let Some(bb_strs) = b_strs {
                    if node.idx_a == *idx_b {
                        if node.string_a == bb_strs.0 || Some(&node.string_a) == bb_strs.1.as_ref() {
                            ()
                        } else if bb_strs.1.is_none() && !node.string_a.commutes(&bb_strs.0) {
                            bb_strs.1 = Some(node.string_a.clone());
                        } else {
                            *b_strs = None;
                        }
                    } else if node.idx_b == *idx_b {
                        if node.string_b == bb_strs.0 || Some(&node.string_b) == bb_strs.1.as_ref() {
                            ()
                        } else if bb_strs.1.is_none() && !node.string_b.commutes(&bb_strs.0) {
                            bb_strs.1 = Some(node.string_b.clone());
                        } else {
                            *b_strs = None;
                        }
                    }
                }

                if a_strs.is_some() || b_strs.is_some() {
                    *count += 1;
                    true
                } else {
                    false
                }
            }
        }
    }

    fn score(&self, _: &Self::Context) -> i32 {
        match self {
            EmbedBinState::Empty => -1,
            EmbedBinState::Phase => 0,
            EmbedBinState::NonEmpty { count, .. } => *count as i32 - 1
        }
    }

    fn try_add_score(&self, _node: &Self::Node, _context: &Self::Context) -> Option<i32> {
        Some(self.score(_context) + 1)   
    }
}

#[derive(Debug, Clone)]
pub enum EmbeddingBin {
    Single(PauliExp),
    Binned {
        idx_a: usize,
        idx_b: usize,
        stab: PauliString,
        destab: Option<PauliString>,
        exps: Vec<(bool, PauliString)>
    }
}

pub fn trivial_embedding(part: PartitionedCircuit) -> EmbeddedCircuit {
    EmbeddedCircuit { 
        arch: part.arch,
        tail: part.tail,
        dag: part.dag.map_owned(|_, n| EmbeddingBin::Single(n), |_, _| ())
    }
}

pub fn beam_search_embedding(part: PartitionedCircuit, beam_width: usize) -> (EmbeddedCircuit, PassMetrics) {
    let mut metrics = PassMetrics::new();
    metrics.name("BeamSearchEmbedding");

    // Find bins
    let mut pm = PassMetrics::new();
    pm.name("DAGBinPackingSolver");
    let mut solver = dag_bin_packing::Solver::<EmbedBinState>::new(&(), &part.dag, dag_bin_packing::Objective::SumMaxMin, beam_width, None);
    let sol = solver.solve_progress().unwrap();
    pm.end();
    metrics.child(pm);

    // Construct bin DAG
    let mut dag = DiGraph::<EmbeddingBin, ()>::new();
    let mut nodes = HashMap::new();
    for bin in sol.bins {
        if bin.len() == 0 { continue }
        // Check that each bin is already toposorted (this should be true)
        assert!((0..bin.len()).all(|j| (0..j).all(|i| !part.dag.contains_edge(bin[j], bin[i]))));

        // Reconstruct the bin state
        let mut state = EmbedBinState::Empty;
        for &el in &bin {
            assert!(state.try_add(&part.dag[el], &()));
        }

        // Map the bin state to an EmbeddingBin
        let data = match state {
            EmbedBinState::Empty => unreachable!(),
            EmbedBinState::Phase => EmbeddingBin::Single(part.dag[bin[0]].clone()),
            EmbedBinState::NonEmpty { 
                idx_a, idx_b, count,
                a_strs, b_strs, 
            } => if count == 1 {
                // If there is only one string, don't bother doing the complicated thing
                EmbeddingBin::Single(part.dag[bin[0]].clone())
            } else if let Some(((stab, destab), is_a)) 
                = a_strs.zip(Some(true)).or(b_strs.zip(Some(false))) {
                // At least one of a_strs and b_strs must be non-None for try_add to have succeeded
                // Pick one to be the embedded qubit, with preference to a_strs.
                    
                // Now map all of the bin elements to this choice
                let mut exps = Vec::new();
                for &el in &bin {
                    let PauliExp::Nonlocal(n) = &part.dag[el] else { panic!() };

                    // Is this exp A-B or B-A?
                    let n_is_ab = if n.idx_a == idx_a && n.idx_b == idx_b {
                        true
                    } else if n.idx_a == idx_b && n.idx_b == idx_a {
                        false
                    } else { unreachable!() };

                    // Does n.string_a match a stabilizer/destabilizer?
                    let na_is_stab = if n.string_a == stab {
                        Some(true)
                    } else if Some(&n.string_a) == destab.as_ref() {
                        Some(false)
                    } else { None };

                    // Does n.string_b match a stabilizer/destabilizer?
                    let nb_is_stab = if n.string_b == stab {
                        Some(true)
                    } else if Some(&n.string_b) == destab.as_ref() {
                        Some(false)
                    } else { None };

                    // Does the embedded-side match the stabilizer or destabilizer?
                    // is_a == n_is_ab is true iff we are matching A in an A-B or B in a B-A
                    let is_stab = if is_a == n_is_ab {
                        na_is_stab.unwrap()
                    } else {
                        nb_is_stab.unwrap()
                    };

                    // Get the string for the non-embedded side
                    let string = if is_a == n_is_ab {
                        n.string_b.clone()
                    } else {
                        n.string_a.clone()
                    };

                    exps.push((is_stab, string))
                }

                EmbeddingBin::Binned {
                    stab, destab, exps,
                    idx_a: if is_a { idx_a } else { idx_b },
                    idx_b: if is_a { idx_b } else { idx_a }
                }
            } else { unreachable!() }
        };

        let node = dag.add_node(data);
        for &idx in &bin {
            nodes.insert(idx, node);
        }
    }

    // Add edges to bin DAG
    for edge in part.dag.edge_references() {
        let ns = nodes[&edge.source()];
        let nt = nodes[&edge.target()];
        if ns == nt { continue }
        dag.update_edge(ns, nt, ());
    }

    // Check that the bin DAG is actually a DAG
    assert!(!petgraph::algo::is_cyclic_directed(&dag));

    metrics.end();
    (EmbeddedCircuit { dag, arch: part.arch, tail: part.tail }, metrics)
}

#[derive(Debug, Clone)]
pub struct EmbeddedCircuit {
    pub dag: DiGraph<EmbeddingBin, ()>,
    pub arch: GlobalArch,
    pub tail: Circuit
}

impl EmbeddedCircuit {
    pub fn tcount(&self) -> usize {
        self.dag.node_weights().filter(|&n| {
            matches!(n, EmbeddingBin::Single(PauliExp::Phase(p)) if !p.is_clifford())
        }).count()
    }

    pub fn nlcount(&self) -> usize {
        self.dag.node_weights().filter(|&n| {
            matches!(n, EmbeddingBin::Single(PauliExp::Nonlocal(_)) | EmbeddingBin::Binned { .. })
        }).count()
    }

    pub fn iter(&self) -> impl Iterator<Item=&EmbeddingBin> {
        let order = petgraph::algo::toposort(&self.dag, None).unwrap();
        order.into_iter().map(|idx| &self.dag[idx])
    }

    /// Resynthesize a Circuit VERY naively. Does not respect architecture constraints.
    pub fn naive_resynth(&self) -> Circuit {
        let mut gates = Vec::new();
        for bin in self.iter() {
            match bin {
                EmbeddingBin::Single(exp) => gates.append(&mut exp.to_gates_naive(&self.arch)),
                EmbeddingBin::Binned { idx_a, idx_b, stab, destab, exps } => {
                    for (is_stab, string) in exps {
                        let exp = NonlocalExp { 
                            idx_a: *idx_a, idx_b: *idx_b,
                            string_a: if *is_stab { stab.clone() } else { destab.clone().unwrap() },
                            string_b: string.clone()
                        };
                        gates.append(&mut exp.to_gates_naive(&self.arch))
                    }
                }
            }            
        }
        gates.extend_from_slice(&self.tail.gates);

        Circuit { gates, qubits: self.arch.qubits() }
    }
}
