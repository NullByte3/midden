use std::collections::HashMap;

use super::*;
use crate::dump::{Class, FastMap, Kind, ObjectTable, Packing, Shapes, Symbols};
use crate::graph::ARRAY_ELEMENT;
use crate::hprof::Header;
use crate::sizes::{SizeMode, Sizing};

fn fixture(edges: &[Vec<u32>], roots: &[u32], shallow: u32) -> (Dump, Graph) {
    let classes = vec![Class { shallow, ..Class::default() }];
    let sizing = Sizing::resolve(SizeMode::Mat, 8, 0);
    let packing = Packing::new(classes.len());
    let ids: Vec<u64> = (0..edges.len()).map(|object| (object as u64 + 1) * 8).collect();
    let shapes = Shapes::new(
        (0..edges.len()).map(|_| packing.pack(0, Kind::Instance, 0).0).collect(),
        packing,
        Vec::new(),
    );
    let objects = ObjectTable::from_columns(&classes, sizing, &ids, shapes);
    let dump = Dump {
        path: String::new(),
        file_size: 0,
        gzip: false,
        member: None,
        header: Header { format: String::new(), id_size: 8, timestamp_ms: 0 },
        truncated: false,
        sizing,
        chunks: Vec::new(),
        pieces: Vec::new(),
        names: Vec::new(),
        symbols: Symbols::default(),
        classes,
        objects,
        array_hashes: None,
        boxed_values: None,
        roots: Vec::new(),
        dangling_roots: 0,
        marked_unreachable: 0,
        threads: Vec::new(),
        traces: HashMap::new(),
        frames: FastMap::default(),
        class_by_serial: HashMap::new(),
        class_class: NONE,
        string_class: NONE,
        value_label: NONE,
        name_label: NONE,
    };
    let mut offsets = Column::zeroed(edges.len() + 1);
    for (object, targets) in edges.iter().enumerate() {
        offsets[object + 1] = offsets[object] + targets.len() as u64;
    }
    let graph = Graph::from_parts(
        offsets,
        edges.iter().flatten().copied().collect(),
        edges.iter().flat_map(|edges| (0..edges.len() as u32).map(|i| ARRAY_ELEMENT | i)).collect(),
        &dump,
        Vec::new(),
        0,
        roots.to_vec(),
    );
    (dump, graph)
}

/// Ordinary queue BFS, optionally removing a vertex or edges.
fn reference_parents(edges: &[Vec<u32>], roots: &[u32], removed: u32, blocked: &[(u32, u32)]) -> Vec<u32> {
    let mut parent = vec![NONE; edges.len()];
    let mut queue = Vec::new();
    for &root in roots {
        if root != removed && parent[root as usize] == NONE {
            parent[root as usize] = edges.len() as u32;
            queue.push(root);
        }
    }
    let mut head = 0;
    while head < queue.len() {
        let from = queue[head];
        head += 1;
        for &to in &edges[from as usize] {
            if to != removed && parent[to as usize] == NONE && !blocked.contains(&(from, to)) {
                parent[to as usize] = from;
                queue.push(to);
            }
        }
    }
    parent
}

/// Removing a dominator makes every object in its subtree unreachable. This checks both the tree
/// and retained sizes independently of DFS numbering and the semidominator algorithm.
fn check_dominators(edges: &[Vec<u32>], roots: &[u32], shallow: u32) {
    let (dump, graph) = fixture(edges, roots, shallow);
    let tree = dominators(&graph, &dump);
    let parents = reference_parents(edges, roots, NONE, &[]);
    let subtrees: Vec<Vec<u32>> = (0..edges.len() as u32)
        .map(|removed| {
            let without = reference_parents(edges, roots, removed, &[]);
            (0..edges.len() as u32)
                .filter(|&object| parents[object as usize] != NONE && without[object as usize] == NONE)
                .collect()
        })
        .collect();
    for object in 0..edges.len() as u32 {
        let reachable = parents[object as usize] != NONE;
        let expected = if reachable {
            (0..edges.len() as u32)
                .filter(|&candidate| candidate != object && subtrees[candidate as usize].contains(&object))
                .min_by_key(|&candidate| subtrees[candidate as usize].len())
                .unwrap_or(graph.root)
        } else {
            NONE
        };
        assert_eq!(tree.idom[object as usize], expected, "idom of {object}, edges {edges:?}");
        assert_eq!(
            tree.retained(object),
            subtrees[object as usize].len().max(1) as u64 * u64::from(shallow),
            "retained size of {object}"
        );
        let mut actual = tree.subtree(object).to_vec();
        actual.sort_unstable();
        assert_eq!(actual, subtrees[object as usize], "subtree of {object}");
        assert_eq!(tree.preorder_index[object as usize] != NONE, reachable);
    }
    let reachable = parents.iter().filter(|&&parent| parent != NONE).count();
    assert_eq!(tree.preorder.len(), reachable);
    for (pos, &object) in tree.preorder.iter().enumerate() {
        assert_eq!(tree.preorder_index[object as usize] as usize, pos);
    }
}

#[test]
fn dominators_match_vertex_removal() {
    check_dominators(&[], &[], 16);
    check_dominators(&[vec![], vec![], vec![]], &[0, 1, 1], 16);
    check_dominators(&[vec![1], vec![0], vec![]], &[], 16);
    check_dominators(&[vec![1, 2, 2, 4], vec![3], vec![3], vec![1], vec![], vec![]], &[0, 4], 16);
    // Sizes beyond four bytes must survive batched leaf accounting.
    check_dominators(&[vec![1, 2, 3, 4], vec![], vec![], vec![], vec![]], &[0], 1 << 30);
    let mut seed = 1u64;
    for case in 0..40 {
        let mut next = || {
            seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            (seed >> 32) as u32
        };
        let edges: Vec<Vec<u32>> = (0..16).map(|_| (0..next() % 6).map(|_| next() % 16).collect()).collect();
        let roots = if case % 2 == 0 { vec![0] } else { vec![0, 5, 12] };
        check_dominators(&edges, &roots, 16);
    }
}

#[test]
fn leaf_runs_cross_worker_boundaries() {
    let count = 100_000u32;
    let mut edges = vec![Vec::new(); count as usize];
    edges[0] = (1..count - 1).collect();
    let (dump, graph) = fixture(&edges, &[0], 16);
    let tree = dominators(&graph, &dump);
    assert_eq!(tree.retained(0), u64::from(count - 1) * 16);
    assert_eq!(tree.subtree(0).len(), count as usize - 1);
    assert_eq!(tree.idom[count as usize - 1], NONE);
    assert!(tree.subtree(count - 1).is_empty());
    for object in 1..count - 1 {
        assert_eq!(tree.idom[object as usize], 0);
        assert_eq!(tree.retained(object), 16);
        assert_eq!(tree.subtree(object), &[object]);
    }
    for (pos, &object) in tree.preorder.iter().enumerate() {
        assert_eq!(tree.preorder_index[object as usize] as usize, pos);
    }
}

#[test]
fn deep_chain_preserves_parents_and_retained_sizes() {
    let count = 100_000u32;
    let edges: Vec<Vec<u32>> =
        (0..count).map(|object| if object + 1 < count { vec![object + 1] } else { Vec::new() }).collect();
    let (dump, graph) = fixture(&edges, &[0], 16);
    let tree = dominators(&graph, &dump);
    assert_eq!(tree.idom[0], graph.root);
    for object in 0..count {
        if object != 0 {
            assert_eq!(tree.idom[object as usize], object - 1);
        }
        assert_eq!(tree.retained(object), u64::from(count - object) * 16);
        assert_eq!(tree.preorder[object as usize], object);
        assert_eq!(tree.subtree_end[object as usize], count);
    }
}

#[test]
fn filtered_children_keep_order_and_hidden_totals() {
    let edges = vec![vec![1, 2, 3, 4], vec![5], vec![6, 7], vec![], vec![], vec![], vec![], vec![]];
    let (dump, graph) = fixture(&edges, &[0], 16);
    let tree = dominators(&graph, &dump);
    let mut hidden = (0, 0);
    let shown = tree.children_matching(0, |child| {
        let bytes = tree.retained(child);
        if bytes < 32 {
            hidden.0 += 1;
            hidden.1 += bytes;
            false
        } else {
            true
        }
    });
    assert_eq!(shown, [2, 1]);
    assert_eq!(hidden, (2, 32));
    assert_eq!(tree.children(0), [2, 1, 3, 4]);
}

#[test]
fn reachability_matches_queue_across_parallel_levels() {
    let width = PARALLEL_LEVEL as u32 + 1;
    let first_leaf = width + 2;
    let mut edges = vec![Vec::new(); first_leaf as usize + 128];
    edges[0] = (2..first_leaf).collect();
    edges[1] = (2..first_leaf).step_by(2).collect();
    for object in 2..first_leaf {
        edges[object as usize] = vec![first_leaf + object % 128, first_leaf, first_leaf];
    }
    let (dump, graph) = fixture(&edges, &[0, 1], 16);
    for blocked in [vec![], vec![(0, 2), (2, first_leaf + 2), (3, first_leaf)]] {
        let mut actual = reach_blocking(&graph, &dump, &blocked);
        let expected = reference_parents(&edges, &graph.roots, NONE, &blocked);
        assert_eq!(&actual.parent[..], expected);
        let count = expected.iter().filter(|&&parent| parent != NONE).count() as u64;
        assert_eq!(actual.count, count);
        assert_eq!(actual.bytes, count * 16);
        let tree = dominators(&graph, &dump);
        actual.keep_differing(&tree.idom);
        for (object, &parent) in expected.iter().enumerate() {
            assert_eq!(actual.parent(object as u32, &tree.idom), parent);
        }
    }
}
