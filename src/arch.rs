use std::collections::HashMap;

use petgraph::{graph::{IndexType, DiGraph, NodeIndex, UnGraph, WalkNeighbors}, visit::{EdgeRef, IntoEdgeReferences, NodeFiltered}};

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocalQubit {
    pub idx: usize,
    pub offset: usize,
    pub global: usize
}

pub type QubitIndex = NodeIndex;
pub type PartIndex = NodeIndex;

#[derive(Debug, Clone)]
pub struct Part {
    pub idx: PartIndex, 
    pub qubits: Vec<QubitIndex>, 
    pub topo: APSP<LocalQubit, ()>
}

#[derive(Debug, Clone)]
pub struct Architecture {
    pub local: Vec<LocalQubit>,
    pub parts: Vec<Part>,
    pub nonlocal: APSP<usize, (usize, usize)>,
}

impl Architecture {
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

    pub fn range(&self, idx: usize) -> impl Iterator<Item=usize> {
        let part = &self.parts[idx];
        part.qubits.iter().map(|&i| part.topo.graph[i].global)
    }
}

impl Architecture {
    pub fn all_to_all(k: usize, q: usize) -> Architecture {
        let mut local = Vec::new();
        let mut parts = Vec::new();
        let mut nonlocal = UnGraph::new_undirected();
        for p in 0..k {
            let idx = nonlocal.add_node(p);
            let mut topo = UnGraph::new_undirected();
            let mut qubits = Vec::new();
            for i in 0..q {
                let lq = LocalQubit { idx: p, offset: i, global: local.len() };
                qubits.push(topo.add_node(lq));
                local.push(lq);
            }

            for a in topo.node_indices() {
                for b in topo.node_indices() {
                    if a >= b { continue }
                    topo.add_edge(a, b, ());
                }
            }

            parts.push(Part { idx, qubits, topo: APSP::build(topo) });
        }

        for a in nonlocal.node_indices() {
            for b in nonlocal.node_indices() {
                if a >= b { continue }
                for i in 0..q {
                    for j in 0..q {
                        nonlocal.add_edge(a, b, (i, j));
                    }
                }
            }
        }

        Architecture { local, parts, nonlocal: APSP::build(nonlocal) }
    }
}

#[derive(Clone, Debug)]
pub struct APSP<N, E> {
    pub graph: UnGraph<N, E>,
    pub dist: DiGraph<(), (usize, NodeIndex)>
}

impl<N, E> APSP<N, E> {
    pub fn build(graph: UnGraph<N, E>) -> APSP<N, E> {
        let mut dist = graph
            .filter_map(|_, _| Some(()), |_, _| None)
            .into_edge_type();

        for v in graph.node_indices() {
            dist.add_edge(v, v, (0, v));
        }

        for e in graph.edge_references() {
            dist.update_edge(e.source(), e.target(), (1, e.target()));
            if !graph.is_directed() {
                dist.update_edge(e.target(), e.source(), (1, e.source()));
            }
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

        let mut edges = dist.edge_references().map(|e| (e.source(), e.target(), *e.weight())).collect::<Vec<_>>();
        edges.sort_by_key(|&(_, _, (d, _))| d);
        dist.clear_edges();
        edges.into_iter().for_each(|(a, b, w)| { dist.add_edge(a, b, w); });

        APSP { graph, dist }
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

    pub fn steiner_tree(&self, terms: impl IntoIterator<Item=NodeIndex>) -> SteinerTree {
        let terms = terms.into_iter().enumerate().map(|(i, n)| (n, i)).collect::<HashMap<_, _>>();

        let mut nodes = HashMap::new();
        let mut ds = disjoint::DisjointSet::with_len(terms.len());
        let filtered = NodeFiltered::from_fn(&self.dist, |n| terms.contains_key(&n));
        let mut count = 0;
        for edge in filtered.edge_references() {
            if count == terms.len() - 1 { break }
            if ds.join(terms[&edge.source()], terms[&edge.target()]) {
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
        for edge in filtered.edge_references() {
            if tree.edge_count() == nodes.len() - 1 { break }
            if ds.join(nodes[&edge.source()], nodes[&edge.target()]) {
                tree.add_edge(edge.source(), edge.target(), ());
            }
        }

        loop {
            let mut found = false;
            for idx in tree.node_indices().rev() {
                if terms.contains_key(&tree[idx]) { continue }
                let mut neighs = tree.neighbors(idx);
                if neighs.next().is_none() || neighs.next().is_none() {
                    found = true;
                    tree.remove_node(idx);
                }
            }
            if !found { break }
        }

        SteinerTree { tree }
    }
}

pub struct SteinerTree {
    pub tree: UnGraph<NodeIndex, ()>
}

impl SteinerTree {
    pub fn edges_postorder(&self, root: NodeIndex) -> impl Iterator<Item=(NodeIndex, NodeIndex)> {
        let root = self.tree.node_indices().find(|&r| self.tree[r] == root).unwrap();
        TreeEdgesPostorder::new(&self.tree, root)
    }
}

/// Iterator to traverse the edges of a tree in post-order from a root. 
/// Assumes that the tree is undirected and has no parallel edges, 
/// and will panic or return incorrect results if this is not true.
struct TreeEdgesPostorder<'a, N, E, Ix> {
    stack: Vec<(NodeIndex<Ix>, WalkNeighbors<Ix>)>,
    node: NodeIndex<Ix>,
    walker: WalkNeighbors<Ix>,
    tree: &'a UnGraph<N, E, Ix>
}

impl<'a, N, E, Ix: IndexType> TreeEdgesPostorder<'a, N, E, Ix> {
    fn new(tree: &'a UnGraph<N, E, Ix>, root: NodeIndex<Ix>) -> Self {
        TreeEdgesPostorder { stack: Vec::new(), node: root, walker: tree.neighbors(root).detach(), tree }
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
    type Item = (N, N);

    fn next(&mut self) -> Option<Self::Item> {
        let mut depth = 0;
        while let Some(child) = self.next_child() {
            self.stack.push((
                std::mem::replace(&mut self.node, child), 
                std::mem::replace(&mut self.walker, self.tree.neighbors(child).detach())
            ));

            depth += 1;
            if depth > self.tree.node_count() {
                // Avoid blowing up the heap :)
                panic!("cycle detected");
            }
        }

        let (parent, walker) = self.stack.pop()?;
        let child = self.node;
        self.node = parent;
        self.walker = walker;
        Some((self.tree[parent].clone(), self.tree[child].clone()))
    }
}

