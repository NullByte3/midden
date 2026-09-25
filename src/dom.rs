//! Reachability, root paths, the weakly-held set and the dominator tree. `d` dominates `o` when every
//! root path to `o` passes through `d`; the bytes under `d` are its retained size.

use std::sync::atomic::{AtomicU32, Ordering::Relaxed};

use super::dump::{Dump, NONE};
use super::graph::Graph;
use super::parallel;

/// Parent and dominator chains are cut at this length, so a corrupt tree cannot loop.
const MAX_CHAIN_LEN: usize = 50_000_000;

/// Breadth-first reachability. `parent` is the previous hop on a shortest
/// path from a root (`graph.root` for roots, `NONE` when unreachable).
pub struct Reachability {
    pub parent: Vec<u32>,
    pub count: u64,
    pub bytes: u64,
}

pub fn reach(graph: &Graph, dump: &Dump) -> Reachability {
    reach_blocking(graph, dump, &[])
}

/// Reachability that ignores the edges in `blocked`.
fn reach_blocking(graph: &Graph, dump: &Dump, blocked: &[(u32, u32)]) -> Reachability {
    let mut parent = vec![NONE; dump.objects.len()];
    let mut queue: Vec<u32> = Vec::new();
    for &root in &graph.roots {
        if parent[root as usize] == NONE {
            parent[root as usize] = graph.root;
            queue.push(root);
        }
    }
    let mut head = 0;
    while head < queue.len() {
        let object = queue[head];
        head += 1;
        for target in graph.edges(object).targets() {
            if parent[target as usize] == NONE && !blocked.contains(&(object, target)) {
                parent[target as usize] = object;
                queue.push(target);
            }
        }
    }
    let bytes = queue.iter().map(|&object| u64::from(dump.objects[object as usize].shallow)).sum();
    Reachability { parent, count: queue.len() as u64, bytes }
}

impl Reachability {
    /// Root-to-object path, the root end first. Empty when unreachable.
    pub fn path(&self, root: u32, mut object: u32) -> Vec<u32> {
        let mut path = Vec::new();
        if self.parent[object as usize] == NONE {
            return path;
        }
        while object != NONE && object != root {
            path.push(object);
            object = self.parent[object as usize];
            if path.len() > MAX_CHAIN_LEN {
                break;
            }
        }
        path.reverse();
        path
    }
}

/// Up to `limit` root paths to `target` that arrive through different referrers: each
/// search blocks the last edge of the paths found so far.
pub fn paths(graph: &Graph, dump: &Dump, first: &Reachability, target: u32, limit: usize) -> Vec<Vec<u32>> {
    let mut out = Vec::new();
    let mut blocked = Vec::new();
    let mut reach = None;
    for _ in 0..limit.max(1) {
        let path = reach.as_ref().unwrap_or(first).path(graph.root, target);
        if path.is_empty() {
            break;
        }
        if path.len() >= 2 {
            blocked.push((path[path.len() - 2], target));
        }
        out.push(path);
        if out.len() >= limit || blocked.is_empty() {
            break;
        }
        reach = Some(reach_blocking(graph, dump, &blocked));
    }
    out
}

/// Objects reachable only once weak referents count.
pub struct WeakSet {
    pub count: u64,
    pub bytes: u64,
    pub seen: Vec<bool>,
}

/// The weakly-held set: a search seeded by weak edges leaving the strongly reachable set.
pub fn weak_only(graph: &Graph, dump: &Dump, strong: &Reachability) -> WeakSet {
    weak_set(graph, dump, strong, |_| true)
}

/// Count and bytes of the weakly-held set reached through the weak edges `take` accepts.
pub fn weak_only_from(
    graph: &Graph,
    dump: &Dump,
    strong: &Reachability,
    take: impl Fn(u32) -> bool,
) -> (u64, u64) {
    let set = weak_set(graph, dump, strong, take);
    (set.count, set.bytes)
}

fn weak_set(graph: &Graph, dump: &Dump, strong: &Reachability, take: impl Fn(u32) -> bool) -> WeakSet {
    let mut seen = vec![false; dump.objects.len()];
    let mut queue: Vec<u32> = Vec::new();
    let visit = |object: u32, queue: &mut Vec<u32>, seen: &mut [bool]| {
        if strong.parent[object as usize] == NONE && !seen[object as usize] {
            seen[object as usize] = true;
            queue.push(object);
        }
    };
    for &(referrer, referent) in graph.weak_edges() {
        if strong.parent[referrer as usize] != NONE && take(referrer) {
            visit(referent, &mut queue, &mut seen);
        }
    }
    let mut head = 0;
    while head < queue.len() {
        let object = queue[head];
        head += 1;
        for target in graph.edges(object).targets() {
            visit(target, &mut queue, &mut seen);
        }
        for referent in graph.weak_referents(object) {
            visit(referent, &mut queue, &mut seen);
        }
    }
    let bytes = queue.iter().map(|&object| u64::from(dump.objects[object as usize].shallow)).sum();
    WeakSet { count: queue.len() as u64, bytes, seen }
}

/// The dominator tree over the reachable objects, plus retained sizes.
pub struct DominatorTree {
    /// Immediate dominator: `graph.root` for top-level objects, `NONE` if unreachable.
    pub idom: Vec<u32>,
    /// Shallow size plus everything dominated; unreachable objects keep their shallow size.
    pub retained: Vec<u64>,
    /// Objects dominated by the roots alone, biggest retained first.
    top_level: Vec<u32>,
    /// Reachable objects in tree preorder: what an object dominates runs from its place to its `subtree_end`.
    pub preorder: Vec<u32>,
    pub subtree_end: Vec<u32>,
    /// Each object's place in `preorder`, `NONE` if unreachable.
    pub preorder_index: Vec<u32>,
}

impl DominatorTree {
    pub fn top_level(&self) -> &[u32] {
        &self.top_level
    }

    /// Children, biggest retained first. Sorted on demand: the report opens a few hundred of millions.
    pub fn children(&self, object: u32) -> Vec<u32> {
        let mut children: Vec<u32> = self.preorder_children(object).collect();
        children.sort_unstable_by(|&a, &b| self.bigger(a, b));
        children
    }

    /// The child `children` lists first.
    pub fn biggest_child(&self, object: u32) -> Option<u32> {
        self.preorder_children(object).min_by(|&a, &b| self.bigger(a, b))
    }

    fn bigger(&self, a: u32, b: u32) -> std::cmp::Ordering {
        self.retained[b as usize].cmp(&self.retained[a as usize]).then(a.cmp(&b))
    }

    /// Children in preorder: each child's subtree ends where the next begins.
    fn preorder_children(&self, object: u32) -> impl Iterator<Item = u32> + '_ {
        // The virtual root, past the objects, holds the whole preorder.
        let (mut pos, stop) = match self.preorder_index.get(object as usize) {
            None => (0, self.preorder.len() as u32),
            Some(&NONE) => (0, 0),
            Some(&place) => (place + 1, self.subtree_end[place as usize]),
        };
        std::iter::from_fn(move || {
            (pos < stop).then(|| {
                let child = self.preorder[pos as usize];
                pos = self.subtree_end[pos as usize];
                child
            })
        })
    }

    /// `object` and everything it dominates; empty when `object` is unreachable.
    pub fn subtree(&self, object: u32) -> &[u32] {
        match self.preorder_index[object as usize] {
            NONE => &[],
            place => &self.preorder[place as usize..self.subtree_end[place as usize] as usize],
        }
    }

    /// The dominators above `object`, nearest first, stopping before the root.
    pub fn dominators_of(&self, root: u32, mut object: u32) -> Vec<u32> {
        let mut out = Vec::new();
        loop {
            object = self.idom[object as usize];
            if object == NONE || object == root || out.len() > MAX_CHAIN_LEN {
                return out;
            }
            out.push(object);
        }
    }
}

/// SEMI-NCA: Lengauer-Tarjan semidominators with simple link/eval over a DFS numbering, then idoms by
/// nearest common ancestor. Predecessor lists use DFS numbers so the hot loops walk contiguous memory.
pub fn dominators(graph: &Graph, dump: &Dump) -> DominatorTree {
    let object_count = dump.objects.len();
    let root = graph.root;

    let mut dfs_number = vec![NONE; object_count + 1];
    let mut vertex: Vec<u32> = vec![root];
    let mut parent: Vec<u32> = vec![NONE];
    dfs_number[object_count] = 0;
    let mut stack: Vec<(u32, u32)> = vec![(root, 0)];
    while let Some(&mut (node, ref mut cursor)) = stack.last_mut() {
        let next = if node == root {
            graph.roots.get(*cursor as usize).copied()
        } else {
            graph.edges(node).get(*cursor as usize)
        };
        let Some(successor) = next else {
            stack.pop();
            continue;
        };
        *cursor += 1;
        if dfs_number[successor as usize] == NONE {
            dfs_number[successor as usize] = vertex.len() as u32;
            parent.push(dfs_number[node as usize]);
            vertex.push(successor);
            stack.push((successor, 0));
        }
    }
    drop(stack);
    let vertex_count = vertex.len();

    // Predecessors in DFS numbers, in parallel: in-degrees first, then a scatter with a cursor per vertex.
    let in_degree = parallel::zeroed(vertex_count);
    for &gc_root in &graph.roots {
        in_degree[dfs_number[gc_root as usize] as usize].fetch_add(1, Relaxed);
    }
    parallel::ranges(vertex_count - 1, |lo, hi| {
        for &node in &vertex[(lo + 1)..=hi] {
            for target in graph.edges(node).targets() {
                in_degree[dfs_number[target as usize] as usize].fetch_add(1, Relaxed);
            }
        }
    });
    let mut pred_offsets = vec![0u64; vertex_count + 1];
    for i in 0..vertex_count {
        pred_offsets[i + 1] = pred_offsets[i] + u64::from(in_degree[i].load(Relaxed));
        in_degree[i].store(0, Relaxed);
    }
    let predecessors = parallel::zeroed(pred_offsets[vertex_count] as usize);
    let add_predecessor = |number: u32, from: u32| {
        let filled = in_degree[number as usize].fetch_add(1, Relaxed) as usize;
        predecessors[pred_offsets[number as usize] as usize + filled].store(from, Relaxed);
    };
    for &gc_root in &graph.roots {
        add_predecessor(dfs_number[gc_root as usize], 0);
    }
    parallel::ranges(vertex_count - 1, |lo, hi| {
        for &node in &vertex[(lo + 1)..=hi] {
            let node_number = dfs_number[node as usize];
            for target in graph.edges(node).targets() {
                add_predecessor(dfs_number[target as usize], node_number);
            }
        }
    });
    // The fill counted every in-degree back up, so the offsets can go: walking
    // down from the top, each vertex's list ends where the next one's starts.
    drop(pred_offsets);

    // Semidominators, as in Lengauer-Tarjan: process vertices in reverse
    // preorder, taking the smallest semi reachable through each predecessor.
    let mut semi: Vec<u32> = (0..vertex_count as u32).collect();
    let mut label: Vec<u32> = (0..vertex_count as u32).collect();
    let mut ancestor = vec![NONE; vertex_count];
    let mut path: Vec<u32> = Vec::new();
    let mut eval = |vertex: u32, ancestor: &mut [u32], label: &mut [u32], semi: &[u32]| -> u32 {
        if ancestor[vertex as usize] == NONE {
            return vertex;
        }
        path.clear();
        let mut current = vertex;
        while ancestor[ancestor[current as usize] as usize] != NONE {
            path.push(current);
            current = ancestor[current as usize];
        }
        for &node in path.iter().rev() {
            let above = ancestor[node as usize];
            if semi[label[above as usize] as usize] < semi[label[node as usize] as usize] {
                label[node as usize] = label[above as usize];
            }
            ancestor[node as usize] = ancestor[above as usize];
        }
        label[vertex as usize]
    };
    let mut hi = predecessors.len();
    for vertex in (1..vertex_count).rev() {
        let lo = hi - in_degree[vertex].load(Relaxed) as usize;
        for pred in predecessors[lo..hi].iter().map(|pred| pred.load(Relaxed)) {
            let best = eval(pred, &mut ancestor, &mut label, &semi);
            if semi[best as usize] < semi[vertex] {
                semi[vertex] = semi[best as usize];
            }
        }
        hi = lo;
        ancestor[vertex] = parent[vertex];
    }
    drop((label, ancestor, predecessors, in_degree));

    // Idoms (SEMI-NCA): nearest common ancestor of parent and semi in the tree so far, climbing idom
    // links, which are final for every smaller number.
    let mut dom = vec![0u32; vertex_count];
    for vertex in 1..vertex_count {
        let mut candidate = parent[vertex];
        while candidate > semi[vertex] {
            candidate = dom[candidate as usize];
        }
        dom[vertex] = candidate;
    }
    drop((semi, parent));

    // Retained and subtree sizes: reverse preorder visits children before parents.
    let mut subtree_bytes = vec![0u64; vertex_count];
    parallel::chunks(&mut subtree_bytes[1..], |start, part| {
        for (bytes, &object) in part.iter_mut().zip(&vertex[start + 1..]) {
            *bytes = u64::from(dump.objects[object as usize].shallow);
        }
    });
    let mut size = vec![1u32; vertex_count];
    for number in (1..vertex_count).rev() {
        let dominator = dom[number] as usize;
        subtree_bytes[dominator] += subtree_bytes[number];
        size[dominator] += size[number];
    }
    // Map each result back to object indices once final, so fewer arrays stand at once.
    // Unreachable objects keep their shallow size.
    let mut retained = vec![0u64; object_count];
    parallel::chunks(&mut retained, |start, part| {
        for ((bytes, &number), object) in
            part.iter_mut().zip(&dfs_number[start..]).zip(&dump.objects[start..])
        {
            *bytes = if number == NONE { u64::from(object.shallow) } else { subtree_bytes[number as usize] };
        }
    });
    drop(subtree_bytes);
    // A preorder in which each subtree is one range: an object takes its
    // dominator's next free place, and DFS numbers put dominators first.
    let (mut place, mut next_free) = (vec![0u32; vertex_count], vec![0u32; vertex_count]);
    for number in 1..vertex_count {
        let dominator = dom[number] as usize;
        place[number] = next_free[dominator];
        next_free[dominator] += size[number];
        next_free[number] = place[number] + 1;
    }
    drop(next_free);
    let (preorder, subtree_end) = (parallel::zeroed(vertex_count - 1), parallel::zeroed(vertex_count - 1));
    parallel::ranges(vertex_count - 1, |lo, hi| {
        for number in (lo + 1)..=hi {
            preorder[place[number] as usize].store(vertex[number], Relaxed);
            subtree_end[place[number] as usize].store(place[number] + size[number], Relaxed);
        }
    });
    drop(size);
    let mut idom = vec![0u32; object_count];
    parallel::chunks(&mut idom, |start, part| {
        for (dominator, &number) in part.iter_mut().zip(&dfs_number[start..]) {
            *dominator = if number == NONE { NONE } else { vertex[dom[number as usize] as usize] };
        }
    });
    drop((dom, vertex));
    // Last, turn DFS numbers into preorder places.
    dfs_number.truncate(object_count);
    parallel::chunks(&mut dfs_number, |_, part| {
        for number in part.iter_mut().filter(|number| **number != NONE) {
            *number = place[*number as usize];
        }
    });
    drop(place);
    let preorder_index = dfs_number;

    let preorder = preorder.into_iter().map(AtomicU32::into_inner).collect();
    let subtree_end = subtree_end.into_iter().map(AtomicU32::into_inner).collect();
    let mut tree =
        DominatorTree { idom, retained, top_level: Vec::new(), preorder, subtree_end, preorder_index };
    tree.top_level = tree.children(object_count as u32);
    tree
}
