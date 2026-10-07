//! Reachability, root paths, the weakly-held set and the dominator tree. `d` dominates `o` when every
//! root path to `o` passes through `d`; the bytes under `d` are its retained size.

use std::sync::atomic::Ordering::Relaxed;

use super::dump::{Dump, NONE};
use super::graph::Graph;
use super::parallel;
use super::store::{Bits, Column};

/// Parent and dominator chains are cut at this length, so a corrupt tree cannot loop.
const MAX_CHAIN_LEN: usize = 50_000_000;

/// A level this wide or wider is split over the workers; narrower ones run on the calling thread.
const PARALLEL_LEVEL: usize = 1 << 14;

/// Breadth-first reachability. An object's parent is the previous hop on a shortest path from a root
/// (`graph.root` for roots, `NONE` when unreachable).
pub struct Reachability {
    /// Every object's parent, until [`Reachability::keep_differing`] leaves only those in `differing`.
    parent: Column<u32>,
    /// Objects whose parent is not their idom, and the parent, by object.
    differing: Vec<(u32, u32)>,
    pub count: u64,
    pub bytes: u64,
}

pub fn reach(graph: &Graph, dump: &Dump) -> Reachability {
    reach_blocking(graph, dump, &[])
}

/// Reachability that ignores the edges in `blocked`. Wide levels run over the workers and give the
/// same parents and order as one queue: a target goes to the first frontier object, in queue order,
/// that has an edge to it.
fn reach_blocking(graph: &Graph, dump: &Dump, blocked: &[(u32, u32)]) -> Reachability {
    let object_count = dump.objects.len();
    // Parents plus one, so zeroed pages read back `NONE` for the unreached.
    let mut parent_column = Column::<u32>::zeroed(object_count);
    let mut seen_bits = Bits::new(object_count);
    let (parent, seen) = (parent_column.atomics(), seen_bits.atomics());
    let visit = |object: u32| {
        let bit = 1u64 << (object % 64);
        seen[object as usize / 64].fetch_or(bit, Relaxed) & bit == 0
    };
    let is_seen = |object: u32| seen[object as usize / 64].load(Relaxed) >> (object % 64) & 1 != 0;
    let allowed = |from: u32, to: u32| blocked.is_empty() || !blocked.contains(&(from, to));
    let mut order = Column::<u32>::with_capacity(object_count);
    for &root in &graph.roots {
        if visit(root) {
            parent[root as usize].store(graph.root + 1, Relaxed);
            order.push(root);
        }
    }
    // Claims hold `u32::MAX - position`, so the largest is the earliest frontier object.
    let mut claim_column: Option<Column<u32>> = None;
    let mut lo = 0;
    while lo < order.len() {
        let hi = order.len();
        if hi - lo < PARALLEL_LEVEL || parallel::threads() == 1 {
            for pos in lo..hi {
                let from = order[pos];
                for target in graph.edges(from).targets() {
                    if !is_seen(target) && allowed(from, target) && visit(target) {
                        parent[target as usize].store(from + 1, Relaxed);
                        order.push(target);
                    }
                }
            }
        } else {
            let claim = claim_column.get_or_insert_with(|| Column::zeroed(object_count)).atomics();
            let frontier = &order[lo..hi];
            let found = parallel::ranges(frontier.len(), |start, end| {
                let mut found: Vec<(u32, u32)> = Vec::new();
                for (pos, &from) in (lo + start..).zip(&frontier[start..end]) {
                    let key = u32::MAX - pos as u32;
                    for target in graph.edges(from).targets() {
                        if !is_seen(target)
                            && allowed(from, target)
                            && claim[target as usize].fetch_max(key, Relaxed) < key
                        {
                            found.push((target, key));
                        }
                    }
                }
                found
            });
            let kept = parallel::items(&found, |found| {
                let mut kept = Vec::new();
                for &(target, key) in found {
                    if claim[target as usize].load(Relaxed) == key && visit(target) {
                        let from = order[(u32::MAX - key) as usize];
                        parent[target as usize].store(from + 1, Relaxed);
                        kept.push(target);
                    }
                }
                kept
            });
            drop(found);
            for part in kept {
                order.extend_from_slice(&part);
            }
        }
        lo = hi;
    }
    drop(claim_column);
    drop(seen_bits);
    parallel::chunks(&mut parent_column, |_, part| {
        for stored in part {
            *stored = stored.wrapping_sub(1);
        }
    });
    let bytes = parallel::ranges(order.len(), |lo, hi| {
        order[lo..hi].iter().map(|&object| u64::from(dump.objects.shallow(object as usize))).sum::<u64>()
    })
    .into_iter()
    .sum();
    Reachability { parent: parent_column, differing: Vec::new(), count: order.len() as u64, bytes }
}

impl Reachability {
    /// An object's parent; `idom` answers for most once only the differing parents are kept.
    pub fn parent(&self, object: u32, idom: &[u32]) -> u32 {
        if !self.parent.is_empty() {
            return self.parent[object as usize];
        }
        match self.differing.binary_search_by_key(&object, |&(differs, _)| differs) {
            Ok(i) => self.differing[i].1,
            Err(_) => idom[object as usize],
        }
    }

    /// Whether a root reaches `object`: it has a parent, or once only the differing ones are kept, an idom.
    pub fn reached(&self, object: u32, idom: &[u32]) -> bool {
        let source = if self.parent.is_empty() { idom } else { &self.parent };
        source[object as usize] != NONE
    }

    /// Drop every parent that equals the object's idom. An object with one referrer has it as both, so
    /// few parents stay.
    pub fn keep_differing(&mut self, idom: &[u32]) {
        let parent = &self.parent;
        self.differing = parallel::ranges(parent.len(), |lo, hi| {
            (lo as u32..hi as u32)
                .filter(|&object| parent[object as usize] != idom[object as usize])
                .map(|object| (object, parent[object as usize]))
                .collect::<Vec<_>>()
        })
        .concat();
        self.parent = Column::with_capacity(0);
    }

    /// Root-to-object path, the root end first. Empty when unreachable.
    pub fn path(&self, root: u32, mut object: u32, idom: &[u32]) -> Vec<u32> {
        let mut path = Vec::new();
        if !self.reached(object, idom) {
            return path;
        }
        while object != NONE && object != root {
            path.push(object);
            object = self.parent(object, idom);
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
pub fn paths(
    graph: &Graph,
    dump: &Dump,
    (first, idom): (&Reachability, &[u32]),
    target: u32,
    limit: usize,
) -> Vec<Vec<u32>> {
    let mut out = Vec::new();
    let mut blocked = Vec::new();
    let mut reach = None;
    for _ in 0..limit.max(1) {
        let path = reach.as_ref().unwrap_or(first).path(graph.root, target, idom);
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
    pub seen: Bits,
}

/// The weakly-held set: a search seeded by weak edges leaving the strongly reachable set.
pub fn weak_only(graph: &Graph, dump: &Dump, strong: &Reachability) -> WeakSet {
    weak_set(graph, dump, (strong, &[]), |_| true)
}

/// Count and bytes of the weakly-held set reached through the weak edges `take` accepts.
pub fn weak_only_from(
    graph: &Graph,
    dump: &Dump,
    strong: (&Reachability, &[u32]),
    take: impl Fn(u32) -> bool,
) -> (u64, u64) {
    let set = weak_set(graph, dump, strong, take);
    (set.count, set.bytes)
}

fn weak_set(
    graph: &Graph,
    dump: &Dump,
    (strong, idom): (&Reachability, &[u32]),
    take: impl Fn(u32) -> bool,
) -> WeakSet {
    let mut seen = Bits::new(dump.objects.len());
    let mut queue: Vec<u32> = Vec::new();
    let visit = |object: u32, queue: &mut Vec<u32>, seen: &mut Bits| {
        if !strong.reached(object, idom) && !seen.get(object as usize) {
            seen.set(object as usize);
            queue.push(object);
        }
    };
    for &(referrer, referent) in graph.weak_edges() {
        if strong.reached(referrer, idom) && take(referrer) {
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
    let bytes = queue.iter().map(|&object| u64::from(dump.objects.shallow(object as usize))).sum();
    WeakSet { count: queue.len() as u64, bytes, seen }
}

/// The dominator tree over the reachable objects, plus retained sizes.
pub struct DominatorTree {
    /// Immediate dominator: `graph.root` for top-level objects, `NONE` if unreachable.
    pub idom: Column<u32>,
    /// Shallow size plus everything dominated; unreachable objects keep their shallow size. Four bytes: an
    /// object retaining 4 GiB or more reads `u32::MAX` here and has its size in `big`.
    retained: Column<u32>,
    big: Vec<(u32, u64)>,
    /// Objects dominated by the roots alone, biggest retained first.
    top_level: Vec<u32>,
    /// Reachable objects in tree preorder: what an object dominates runs from its place to its `subtree_end`.
    pub preorder: Column<u32>,
    pub subtree_end: Column<u32>,
    /// Each object's place in `preorder`, `NONE` if unreachable.
    pub preorder_index: Column<u32>,
}

impl DominatorTree {
    /// No tree yet.
    pub fn empty() -> DominatorTree {
        let none = || Column::with_capacity(0);
        DominatorTree {
            idom: none(),
            retained: Column::with_capacity(0),
            big: Vec::new(),
            top_level: Vec::new(),
            preorder: none(),
            subtree_end: none(),
            preorder_index: none(),
        }
    }

    pub fn retained(&self, object: u32) -> u64 {
        match self.retained[object as usize] {
            u32::MAX => self.big.binary_search_by_key(&object, |&(big, _)| big).map_or(0, |i| self.big[i].1),
            bytes => u64::from(bytes),
        }
    }

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
        self.retained(b).cmp(&self.retained(a)).then(a.cmp(&b))
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

/// Lengauer-Tarjan `eval` with path compression over `ancestor`, keeping the smallest `semi` in `label`.
struct Forest {
    semi: Column<u32>,
    label: Column<u32>,
    ancestor: Column<u32>,
    path: Vec<u32>,
}

impl Forest {
    fn new(vertex_count: usize) -> Forest {
        Forest {
            semi: parallel::iota(vertex_count),
            label: parallel::iota(vertex_count),
            ancestor: parallel::filled(vertex_count, NONE),
            path: Vec::new(),
        }
    }

    fn eval(&mut self, vertex: u32) -> u32 {
        let (ancestor, label, semi) = (&mut self.ancestor, &mut self.label, &self.semi);
        if ancestor[vertex as usize] == NONE {
            return vertex;
        }
        self.path.clear();
        let mut current = vertex;
        while ancestor[ancestor[current as usize] as usize] != NONE {
            self.path.push(current);
            current = ancestor[current as usize];
        }
        for &node in self.path.iter().rev() {
            let above = ancestor[node as usize];
            if semi[label[above as usize] as usize] < semi[label[node as usize] as usize] {
                label[node as usize] = label[above as usize];
            }
            ancestor[node as usize] = ancestor[above as usize];
        }
        label[vertex as usize]
    }
}

/// A leaf in the DFS numbering: reachable or not, an object with no references out.
const LEAF: u32 = NONE - 1;
/// In-degree marker for a vertex with one referrer.
const SINGLE: u32 = NONE;

/// SEMI-NCA: Lengauer-Tarjan semidominators with simple link/eval over a DFS numbering, then idoms by
/// nearest common ancestor. Predecessor lists use DFS numbers so the hot loops walk contiguous memory.
/// Leaves never enter it: they dominate nothing, so a leaf's idom is the nearest common ancestor of its
/// referrers, met once the rest of the tree is known.
pub fn dominators(graph: &Graph, dump: &Dump) -> DominatorTree {
    let object_count = dump.objects.len();
    let root = graph.root;

    let mut dfs_number = Column::<u32>::zeroed(object_count + 1);
    parallel::chunks(&mut dfs_number[..object_count], |start, part| {
        for (number, object) in part.iter_mut().zip(start as u32..) {
            *number = if graph.edges(object).len() == 0 { LEAF } else { NONE };
        }
    });
    let mut vertex = Column::<u32>::with_capacity(object_count + 1);
    let mut parent = Column::<u32>::with_capacity(object_count + 1);
    vertex.push(root);
    parent.push(NONE);
    dfs_number[object_count] = 0;
    // Vertices not yet numbered, a bit each: the walk tests these, which stay in cache, not the numbers.
    let mut unvisited = parallel::bits(object_count, |object| graph.edges(object as u32).len() != 0);
    // Each frame: its number, then its next and end edge as places in the target array (the root's
    // edges are its GC roots).
    let targets = graph.all_targets();
    let mut stack: Vec<(u32, usize, usize)> = vec![(0, 0, graph.roots.len())];
    while let Some(frame) = stack.last_mut() {
        let (number, next, end) = *frame;
        if next == end {
            stack.pop();
            continue;
        }
        frame.1 += 1;
        let successor = if number == 0 { graph.roots[next] } else { targets[next] };
        if unvisited.take(successor as usize) {
            let successor_number = vertex.len() as u32;
            parent.push(number);
            vertex.push(successor);
            let span = graph.span(successor);
            stack.push((successor_number, span.start, span.end));
        }
    }
    drop((stack, unvisited));
    let vertex_count = vertex.len();
    // Numbers go in after the walk, in parallel, keeping a random write out of it.
    {
        let numbers = dfs_number.atomics();
        parallel::ranges(vertex_count - 1, |lo, hi| {
            for number in (lo + 1)..=hi {
                numbers[vertex[number] as usize].store(number as u32, Relaxed);
            }
        });
    }

    // Predecessors in DFS numbers, in parallel: in-degrees first, then a scatter with a cursor per vertex.
    let number_of = |object: u32| Some(dfs_number[object as usize]).filter(|&number| number != LEAF);
    let mut in_degree_column = Column::<u32>::zeroed(vertex_count);
    let mut pred_offsets = Column::<u64>::zeroed(vertex_count + 1);
    {
        let in_degree = in_degree_column.atomics();
        for number in graph.roots.iter().filter_map(|&gc_root| number_of(gc_root)) {
            in_degree[number as usize].fetch_add(1, Relaxed);
        }
        parallel::ranges(vertex_count - 1, |lo, hi| {
            for &node in &vertex[(lo + 1)..=hi] {
                for number in graph.edges(node).targets().filter_map(number_of) {
                    in_degree[number as usize].fetch_add(1, Relaxed);
                }
            }
        });
        // A vertex with one referrer has it as its DFS parent and needs no list: it is marked instead.
        for i in 0..vertex_count {
            let degree = in_degree[i].load(Relaxed);
            let listed = if degree == 1 { 0 } else { degree };
            pred_offsets[i + 1] = pred_offsets[i] + u64::from(listed);
            in_degree[i].store(if degree == 1 { SINGLE } else { 0 }, Relaxed);
        }
    }
    let mut predecessor_column = Column::<u32>::zeroed(pred_offsets[vertex_count] as usize);
    {
        let (in_degree, predecessors) = (in_degree_column.atomics(), predecessor_column.atomics());
        let add_predecessor = |number: u32, from: u32| {
            if in_degree[number as usize].load(Relaxed) == SINGLE {
                return;
            }
            let filled = in_degree[number as usize].fetch_add(1, Relaxed) as usize;
            predecessors[pred_offsets[number as usize] as usize + filled].store(from, Relaxed);
        };
        for number in graph.roots.iter().filter_map(|&gc_root| number_of(gc_root)) {
            add_predecessor(number, 0);
        }
        parallel::ranges(vertex_count - 1, |lo, hi| {
            for &node in &vertex[(lo + 1)..=hi] {
                let node_number = dfs_number[node as usize];
                for number in graph.edges(node).targets().filter_map(number_of) {
                    add_predecessor(number, node_number);
                }
            }
        });
    }
    // The fill counted every in-degree back up, so the offsets can go: walking
    // down from the top, each vertex's list ends where the next one's starts.
    drop(pred_offsets);

    // Semidominators, as in Lengauer-Tarjan: process vertices in reverse
    // preorder, taking the smallest semi reachable through each predecessor.
    let mut forest = Forest::new(vertex_count);
    let mut hi = predecessor_column.len();
    for vertex in (1..vertex_count).rev() {
        if in_degree_column[vertex] == SINGLE {
            forest.semi[vertex] = parent[vertex];
            forest.ancestor[vertex] = parent[vertex];
            continue;
        }
        let lo = hi - in_degree_column[vertex] as usize;
        for &pred in &predecessor_column[lo..hi] {
            let best = forest.eval(pred);
            if forest.semi[best as usize] < forest.semi[vertex] {
                forest.semi[vertex] = forest.semi[best as usize];
            }
        }
        hi = lo;
        forest.ancestor[vertex] = parent[vertex];
    }
    let semi = forest.semi;
    drop((forest.label, forest.ancestor, predecessor_column, in_degree_column));

    // Idoms (SEMI-NCA): nearest common ancestor of parent and semi in the tree so far, climbing idom
    // links, which are final for every smaller number.
    let mut dom = Column::<u32>::zeroed(vertex_count);
    for vertex in 1..vertex_count {
        let mut candidate = parent[vertex];
        while candidate > semi[vertex] {
            candidate = dom[candidate as usize];
        }
        dom[vertex] = candidate;
    }
    drop((semi, parent));

    // Each leaf meets its referrers at their nearest common ancestor, by DFS number plus one (zero: not
    // reached), kept where its idom goes. The meet does not depend on the order referrers arrive in.
    let mut idom = Column::<u32>::zeroed(object_count);
    {
        let leaf = idom.atomics();
        let ancestor = |mut a: u32, mut b: u32| {
            while a != b {
                if a > b {
                    a = dom[a as usize];
                } else {
                    b = dom[b as usize];
                }
            }
            a
        };
        let meet = |object: u32, number: u32| {
            let slot = &leaf[object as usize];
            let mut current = slot.load(Relaxed);
            loop {
                let next = if current == 0 { number } else { ancestor(current - 1, number) };
                if next + 1 == current {
                    return;
                }
                match slot.compare_exchange_weak(current, next + 1, Relaxed, Relaxed) {
                    Ok(_) => return,
                    Err(seen) => current = seen,
                }
            }
        };
        for &gc_root in graph.roots.iter().filter(|&&gc_root| dfs_number[gc_root as usize] == LEAF) {
            meet(gc_root, 0);
        }
        parallel::ranges(vertex_count - 1, |lo, hi| {
            for number in lo + 1..=hi {
                for target in graph.edges(vertex[number]).targets() {
                    if dfs_number[target as usize] == LEAF {
                        meet(target, number as u32);
                    }
                }
            }
        });
    }

    // Retained and subtree sizes: leaves first, then reverse preorder visits children before parents.
    let mut subtree_bytes = Column::<u64>::zeroed(vertex_count);
    parallel::chunks(&mut subtree_bytes[1..], |start, part| {
        for (bytes, &object) in part.iter_mut().zip(&vertex[start + 1..]) {
            *bytes = u64::from(dump.objects.shallow(object as usize));
        }
    });
    let mut size = parallel::filled(vertex_count, 1u32);
    {
        let (bytes, counts) = (subtree_bytes.atomics(), size.atomics());
        parallel::ranges(object_count, |lo, hi| {
            for (object, (&leaf, &number)) in (lo..hi).zip(idom[lo..hi].iter().zip(&dfs_number[lo..hi])) {
                if number == LEAF && leaf != 0 {
                    bytes[leaf as usize - 1].fetch_add(u64::from(dump.objects.shallow(object)), Relaxed);
                    counts[leaf as usize - 1].fetch_add(1, Relaxed);
                }
            }
        });
    }
    for number in (1..vertex_count).rev() {
        let dominator = dom[number] as usize;
        subtree_bytes[dominator] += subtree_bytes[number];
        size[dominator] += size[number];
    }
    // Map each result back to object indices once final, so fewer arrays stand at once.
    // Leaves and unreachable objects keep their shallow size.
    let mut retained = Column::<u32>::zeroed(object_count);
    let big = parallel::chunks(&mut retained, |start, part| {
        let mut big = Vec::new();
        for (((bytes, &number), shallow), object) in part
            .iter_mut()
            .zip(&dfs_number[start..])
            .zip(dump.objects.shallow_range(start, dump.objects.len()))
            .zip(start as u32..)
        {
            let total = if number >= LEAF { u64::from(shallow) } else { subtree_bytes[number as usize] };
            *bytes = u32::try_from(total).unwrap_or(u32::MAX);
            if *bytes == u32::MAX {
                big.push((object, total));
            }
        }
        big
    })
    .concat();
    drop(subtree_bytes);
    // Idoms as objects, in place: a leaf's slot held its dominator's number plus one.
    parallel::chunks(&mut idom, |start, part| {
        for (dominator, &number) in part.iter_mut().zip(&dfs_number[start..]) {
            *dominator = match number {
                NONE => NONE,
                LEAF if *dominator == 0 => NONE,
                LEAF => vertex[*dominator as usize - 1],
                number => vertex[dom[number as usize] as usize],
            };
        }
    });
    // A preorder in which each subtree is one range: an object takes its dominator's next free place,
    // and DFS numbers put dominators first. Places go where the dominators were, and next free places
    // where the sizes were, each read before it is overwritten.
    let reachable = size[0] as usize - 1;
    let mut place = dom;
    let mut free = size;
    free[0] = 0;
    for number in 1..vertex_count {
        let (dominator, size) = (place[number] as usize, free[number]);
        place[number] = free[dominator];
        free[dominator] += size;
        free[number] = place[number] + 1;
    }
    let (mut preorder, mut subtree_end) =
        (Column::<u32>::zeroed(reachable), Column::<u32>::zeroed(reachable));
    {
        let preorder = preorder.atomics();
        parallel::ranges(vertex_count - 1, |lo, hi| {
            for number in (lo + 1)..=hi {
                preorder[place[number] as usize].store(vertex[number], Relaxed);
            }
        });
    }
    drop((place, vertex));
    // Leaves take what is left of their dominator's range. A leaf's dominator is a vertex, whose entry
    // still holds its number.
    dfs_number.truncate(object_count + 1);
    {
        let (preorder, subtree_end) = (preorder.atomics(), subtree_end.atomics());
        let (free, numbers) = (free.atomics(), dfs_number.atomics());
        parallel::ranges(object_count, |lo, hi| {
            for object in lo..hi {
                if numbers[object].load(Relaxed) != LEAF {
                    continue;
                }
                match idom[object] {
                    NONE => numbers[object].store(NONE, Relaxed),
                    dominator => {
                        let at =
                            free[numbers[dominator as usize].load(Relaxed) as usize].fetch_add(1, Relaxed);
                        preorder[at as usize].store(object as u32, Relaxed);
                        subtree_end[at as usize].store(at + 1, Relaxed);
                    }
                }
            }
        });
    }
    // Last, every placed object's number becomes its place; a vertex's range ends where its next free
    // place stopped.
    {
        let numbers = dfs_number.atomics();
        parallel::chunks(&mut subtree_end, |start, part| {
            for (end, (pos, &object)) in part.iter_mut().zip((start as u32..).zip(&preorder[start..])) {
                let number = numbers[object as usize].load(Relaxed);
                if number != LEAF {
                    *end = free[number as usize];
                }
                numbers[object as usize].store(pos, Relaxed);
            }
        });
    }
    drop(free);
    dfs_number.truncate(object_count);
    let preorder_index = dfs_number;
    let mut tree =
        DominatorTree { idom, retained, big, top_level: Vec::new(), preorder, subtree_end, preorder_index };
    tree.top_level = tree.children(object_count as u32);
    tree
}
