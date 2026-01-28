use std::collections::{HashMap, HashSet};

use petgraph::{graph::UnGraph, stable_graph::{IndexType, NodeIndex, StableDiGraph, StableUnGraph, WalkNeighbors}, visit::{EdgeRef, IntoEdgeReferences, NodeFiltered}};

use crate::{Circuit, Gate, NonlocalExp};

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocalQubit {
    pub idx: usize,
    pub offset: usize,
    pub global: usize
}

impl std::fmt::Debug for LocalQubit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}/{}", self.idx, self.offset, self.global)
    }
}

pub type QubitIndex = NodeIndex;
pub type PartIndex = NodeIndex;

#[derive(Debug, Clone)]
pub struct LocalArch {
    pub idx: PartIndex, 
    pub qubits: Vec<QubitIndex>, 
    pub topo: APSP<LocalQubit, ()>
}

#[derive(Debug, Clone)]
pub struct GlobalArch {
    pub local: Vec<LocalQubit>,
    pub parts: Vec<LocalArch>,
    pub topo: APSP<usize, (LocalQubit, LocalQubit)>,
}

impl GlobalArch {
    pub fn to_local(&self, q: usize) -> LocalQubit {
        self.local[q]
    }

    pub fn part_size(&self, idx: usize) -> usize {
        self.parts[idx].qubits.len()
    }

    pub fn num_parts(&self) -> usize {
        self.parts.len()
    }

    pub fn qubits(&self) -> usize {
        self.local.len()
    }

    pub fn range(&self, idx: usize) -> impl Iterator<Item=LocalQubit> {
        let part = &self.parts[idx];
        part.qubits.iter().map(|&i| part.topo[i])
    }

    pub fn is_circuit_valid(&self, circuit: &Circuit) -> bool {
        if circuit.qubits != self.qubits() { return false }

        for &gate in &circuit.gates {
            if let Gate::CX(i, j) = gate {
                let i = self.local[i];
                let j = self.local[j];
                if i.idx == j.idx {
                    let local = &self.parts[i.idx];
                    if !local.topo.graph.contains_edge(local.qubits[i.offset], local.qubits[j.offset]) {
                        return false
                    }
                } else {
                    if !self.topo.graph.edges_connecting(self.parts[i.idx].idx, self.parts[j.idx].idx)
                        .any(|e| *e.weight() == (i, j) || *e.weight() == (j, i)) {
                        return false
                    }
                }
            }
        }

        true
    }

    pub fn is_exps_valid(&self, exps: &[NonlocalExp]) -> bool {
        exps.iter()
            .all(|exp| {
                self.topo.graph
                    .find_edge_undirected(self.parts[exp.idx_a].idx, self.parts[exp.idx_b].idx)
                    .is_some()
            })
    }

    pub fn all_to_all(k: usize, q: usize) -> GlobalArch {
        let mut local = Vec::new();
        let mut parts = Vec::new();
        let mut nonlocal = StableUnGraph::default();
        for p in 0..k {
            let idx = nonlocal.add_node(p);
            let mut topo = StableUnGraph::default();
            let mut qubits = Vec::new();
            for i in 0..q {
                let lq = LocalQubit { idx: p, offset: i, global: local.len() };
                qubits.push(topo.add_node(lq));
                local.push(lq);
            }

            for a in 0..q {
                for b in 0..q{
                    if a >= b { continue }
                    topo.add_edge(qubits[a], qubits[b], ());
                }
            }

            parts.push(LocalArch { idx, qubits, topo: APSP::build(topo) });
        }

        for ia in 0..k {
            for ib in 0..k {
                if ia >= ib { continue }
                for i in 0..q {
                    for j in 0..q {
                        nonlocal.add_edge(parts[ia].idx, parts[ib].idx, (parts[ia].topo[parts[ia].qubits[i]], parts[ib].topo[parts[ib].qubits[j]]));
                    }
                }
            }
        }

        GlobalArch { local, parts, topo: APSP::build(nonlocal) }
    }

    pub fn linear_nearest_neighbor(k: usize, q: usize) -> GlobalArch {
        let mut local = Vec::new();
        let mut parts = Vec::new();
        let mut nonlocal = StableUnGraph::default();
        for p in 0..k {
            let idx = nonlocal.add_node(p);
            let mut topo = StableUnGraph::default();
            let mut qubits = Vec::new();
            for i in 0..q {
                let lq = LocalQubit { idx: p, offset: i, global: local.len() };
                qubits.push(topo.add_node(lq));
                local.push(lq);
            }

            for i in 0..q-1 {
                topo.add_edge(qubits[i], qubits[i + 1], ());
            }

            parts.push(LocalArch { idx, qubits, topo: APSP::build(topo) });
        }

        for i in 0..k-1 {
            nonlocal.add_edge(parts[i].idx, parts[i+1].idx, (
                parts[i].topo[parts[i].qubits[q - 1]],
                parts[i+1].topo[parts[i+1].qubits[0]]
            ));
        }

        GlobalArch { local, parts, topo: APSP::build(nonlocal) }
    }
}

#[derive(Clone, Debug)]
pub struct APSP<N, E> {
    pub graph: StableUnGraph<N, E>,
    pub dist: StableDiGraph<(), (usize, NodeIndex)>,
    pub cutpoints: HashSet<NodeIndex>
}

impl<N, E> std::ops::Index<NodeIndex> for APSP<N, E> {
    type Output = N;

    fn index(&self, index: NodeIndex) -> &Self::Output {
        &self.graph[index]
    }
}

impl<N, E> APSP<N, E> {
    pub fn build(graph: StableUnGraph<N, E>) -> APSP<N, E> {
        let mut dist = graph
            .filter_map(|_, _| Some(()), |_, _| None)
            .into_edge_type();

        for v in graph.node_indices() {
            dist.add_edge(v, v, (0, v));
        }

        for e in graph.edge_references() {
            dist.update_edge(e.source(), e.target(), (1, e.target()));
            dist.update_edge(e.target(), e.source(), (1, e.source()));
        }

        for k in graph.node_indices() {
            for i in graph.node_indices() {
                for j in graph.node_indices() {
                    let Some((dik, pik)) = dist.find_edge(i, k).map(|e| dist[e]) else { continue };
                    let Some((dkj, _)) = dist.find_edge(k, j).map(|e| dist[e]) else { continue };
                    if let Some((dij, pij)) = dist.find_edge(i, j).map(|e| &mut dist[e]) {
                        if *dij > dik + dkj {
                            *dij = dik + dkj;
                            *pij = pik;
                        }
                    } else {
                        dist.add_edge(i, j, (dik + dkj, pik));
                    }
                }
            }
        }

        let cutpoints = find_cut_vertices(&graph);

        let mut edges = dist.edge_references().map(|e| (e.source(), e.target(), *e.weight())).collect::<Vec<_>>();
        edges.sort_by_key(|&(_, _, (d, _))| d);
        dist.clear_edges();
        edges.into_iter().for_each(|(a, b, w)| { dist.add_edge(a, b, w); });
        APSP { graph, dist, cutpoints }
    }

    pub fn delete_vertex(&mut self, v: NodeIndex) {
        // TODO: improve this with some incremental computation
        let mut graph = std::mem::take(&mut self.graph);
        graph.remove_node(v);
        *self = APSP::build(graph);
    }

    pub fn is_cutting(&self, v: NodeIndex) -> bool {
        self.cutpoints.contains(&v)
    }

    pub fn distance_between(&self, source: NodeIndex, target: NodeIndex) -> Option<usize> {
        Some(self.dist[self.dist.find_edge(source, target)?].0)
    }

    pub fn shortest_path(&self, source: NodeIndex, target: NodeIndex) -> Option<impl Iterator<Item=NodeIndex>> {
        if self.dist.find_edge(source, target).is_none() { return None };
        
        let mut current = source;
        Some(std::iter::from_fn(move || {
            if current == target {
                return None
            }

            current = self.dist[self.dist.find_edge(current, target).unwrap()].1;
            Some(current)
        }))
    }

    pub fn matching(&self, terms: impl IntoIterator<Item=NodeIndex>) -> Vec<Vec<NodeIndex>> {
        let terms = terms.into_iter().collect::<HashSet<_>>();
        let mut subgraph = UnGraph::new_undirected();
        let terms = terms.into_iter().map(|n| (n, subgraph.add_node(n))).collect::<HashMap<_, _>>();
        for (&i, &ci) in &terms {
            for (&j, &cj) in &terms {
                if i == j { continue }
                let Some(dist) = self.distance_between(i, j) else { continue };
                subgraph.update_edge(ci, cj, -(dist as i32));
            }
        }
        let edges = subgraph.edge_references()
            .map(|e| (e.source().index(), e.target().index(), *e.weight()))
            .collect::<Vec<_>>();

        let mut matching = mwmatching::Matching::new(edges);
        matching.max_cardinality();
        let mates = matching.solve();

        let mut result = Vec::new();
        for i in 0..mates.len() {
            if mates[i] == usize::MAX || i >= mates[i] { continue }
            let j = subgraph[NodeIndex::new(mates[i])];
            let i = subgraph[NodeIndex::new(i)];
            let mut path = vec![i];
            path.extend(self.shortest_path(i, j).unwrap());
            result.push(path)
        }

        result
    }

    /// Construct an approximate Steiner forest which covers all the leaves and the roots,
    /// such that each connected component contains exactly one of the roots.
    pub fn steiner_forest(&self, leaves: impl IntoIterator<Item=NodeIndex>, roots: impl IntoIterator<Item=NodeIndex>) -> SteinerForest {
        let roots = roots.into_iter().collect::<HashSet<_>>();
        let terms = leaves.into_iter().chain(roots.iter().copied()).collect::<HashSet<_>>();
        let terms = terms.into_iter().enumerate().map(|(i, n)| (n, i)).collect::<HashMap<_, _>>();

        let mut nodes = terms.clone();
        let mut ds = disjoint::DisjointSet::with_len(terms.len());
        let filtered = NodeFiltered::from_fn(&self.dist, |n| terms.contains_key(&n));
        let mut count = 0;
        let mut marked = roots.iter().map(|r| ds.root_of(terms[r])).collect::<HashSet<_>>();
        for edge in filtered.edge_references() {
            if count == terms.len() - 1 { break }
            
            let root_s = ds.root_of(terms[&edge.source()]);
            let root_t = ds.root_of(terms[&edge.target()]);
            let marked_s = marked.contains(&root_s);
            let marked_t = marked.contains(&root_t);
            if (!marked_s || !marked_t) && root_s != root_t {
                ds.join(terms[&edge.source()], terms[&edge.target()]);
                let root = ds.root_of(terms[&edge.source()]);
                if marked_s || marked_t { marked.insert(root);}
                count += 1;

                let idx = nodes.len();
                nodes.entry(edge.source()).or_insert(idx);
                for node in self.shortest_path(edge.source(), edge.target()).unwrap() {
                    let idx = nodes.len();
                    nodes.entry(node).or_insert(idx);
                }
            }
        }

        let mut tree = self.dist
            .filter_map(|n, _| Some(n), |_, _| None::<()>)
            .into_edge_type();
        let mut ds = disjoint::DisjointSet::with_len(nodes.len());
        let filtered = NodeFiltered::from_fn(&self.graph, |n| nodes.contains_key(&n));
        let mut marked = roots.iter().map(|r| ds.root_of(nodes[r])).collect::<HashSet<_>>();
        for edge in filtered.edge_references() {
            let root_s = ds.root_of(nodes[&edge.source()]);
            let root_t = ds.root_of(nodes[&edge.target()]);
            let marked_s = marked.contains(&root_s);
            let marked_t = marked.contains(&root_t);
            if (!marked_s || !marked_t) && root_s != root_t {
                ds.join(nodes[&edge.source()], nodes[&edge.target()]);
                let root = ds.root_of(nodes[&edge.source()]);
                if marked_s || marked_t { marked.insert(root);}
                tree.add_edge(edge.source(), edge.target(), ());
            }
        }

        loop {
            let mut found = false;
            tree.retain_nodes(|g, idx| {
                if terms.contains_key(&g[idx]) { return true }
                let mut neighs = g.neighbors_undirected(idx);
                if neighs.next().is_none() || neighs.next().is_none() {
                    found = true;
                    false
                } else { true }
            });
            if !found { break }
        }

        SteinerForest { forest: tree }
    }
}

// Tarjan's algorithm for finding articulation points. 
// This is necessary because petgraph::algo::articulation_points does not support StableGraph.
fn find_cut_vertices<N, E>(graph: &StableUnGraph<N, E>) -> HashSet<NodeIndex> {
    #[derive(Default)]
    struct CutNodeData {
        visited: bool,
        low: usize, 
        depth: usize, 
        parent: Option<NodeIndex>, 
        cut: bool
    }

    fn find_cut_vertices_helper(graph: &mut StableUnGraph<CutNodeData, ()>, i: NodeIndex, d: usize) {
        graph[i].visited = true;
        graph[i].depth = d;
        graph[i].low = d;
        let mut child_count = 0;
        let mut is_articulation = false;

        let mut neighs = graph.neighbors_undirected(i).detach();
        while let Some(ni) = neighs.next_node(graph) {
            if !graph[ni].visited {
                graph[ni].parent = Some(i);
                find_cut_vertices_helper(graph, ni, d + 1);
                child_count += 1;
                if graph[ni].low >= graph[i].depth {
                    is_articulation = true;
                }
                graph[i].low = graph[i].low.min(graph[ni].low);
            } else if  Some(ni) != graph[i].parent {
                graph[i].low = graph[i].low.min(graph[ni].depth)
            }
        }
        
        if (graph[i].parent.is_some() && is_articulation) || (graph[i].parent.is_none() && child_count > 1) {
            graph[i].cut = true;
        }
    }

    let mut mapped = graph.map(|_, _| CutNodeData::default(), |_, _| ());
    while let Some(root) = mapped.node_indices().find(|&n| !mapped[n].visited) {
        find_cut_vertices_helper(&mut mapped, root, 0);
    }
    mapped.node_indices().filter(|&n| mapped[n].cut).collect()
}

pub struct SteinerForest {
    pub forest: StableUnGraph<NodeIndex, ()>
}

impl SteinerForest {
    pub fn edges_postorder(&self, root: NodeIndex, twice: bool) -> impl Iterator<Item=(Option<NodeIndex>, NodeIndex, NodeIndex)> {
        let root = self.forest.node_indices().find(|&r| self.forest[r] == root).unwrap();
        TreeEdgesPostorder::new(&self.forest, root, twice)
    }
}

/// Iterator to traverse the edges of a tree in post-order from a root. 
/// Assumes that the tree is undirected and has no parallel edges, 
/// and will panic or return incorrect results if this is not true.
struct TreeEdgesPostorder<'a, N, E, Ix> {
    stack: Vec<(NodeIndex<Ix>, WalkNeighbors<Ix>)>,
    node: NodeIndex<Ix>,
    walker: WalkNeighbors<Ix>,
    tree: &'a StableUnGraph<N, E, Ix>,
    flag: bool,
    twice: bool
}

impl<'a, N, E, Ix: IndexType> TreeEdgesPostorder<'a, N, E, Ix> {
    fn new(tree: &'a StableUnGraph<N, E, Ix>, root: NodeIndex<Ix>, twice: bool) -> Self {
        TreeEdgesPostorder { stack: Vec::new(), node: root, walker: tree.neighbors_undirected(root).detach(), tree, twice, flag: false }
    }

    fn next_child(&mut self) -> Option<NodeIndex<Ix>> {
        let parent = self.stack.last().map(|&(p, _)| p);
        let node = self.walker.next_node(&self.tree)?;
        if Some(node) != parent {
            Some(node)
        } else {
            self.walker.next_node(&self.tree)
        }
    }
}

impl<'a, N: Clone, E, Ix: IndexType> Iterator for TreeEdgesPostorder<'a, N, E, Ix> {
    type Item = (Option<N>, N, N);

    fn next(&mut self) -> Option<Self::Item> {
        if !self.flag {
            let mut depth = 0;
            while let Some(child) = self.next_child() {
                self.stack.push((
                    std::mem::replace(&mut self.node, child), 
                    std::mem::replace(&mut self.walker, self.tree.neighbors_undirected(child).detach())
                ));

                depth += 1;
                if depth > self.tree.node_count() {
                    // Avoid blowing up the heap :)
                    panic!("cycle detected");
                }
            }

            self.flag = true;
            if self.twice {
                self.walker = self.tree.neighbors_undirected(self.node).detach();
            }
        }

        let (parent, child) = if let Some(child) = self.next_child() {
            (self.node, child)
        } else {
            let (parent, walker) = self.stack.pop()?;
            let child = self.node;
            self.node = parent;
            self.walker = walker;
            self.flag = false;
            (parent, child)
        };
        
        Some((
            self.stack.last().map(|&(grandparent, _)| self.tree[grandparent].clone()), 
            self.tree[parent].clone(), 
            self.tree[child].clone()
        ))
    }
}

