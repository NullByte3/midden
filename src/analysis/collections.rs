//! Collection sizing: entries against capacity for the JDK collections, sparse arrays,
//! empty collections and hash collisions, plus the key/value walk the inspector uses.

use super::{Heap, Objects};
use crate::dump::{Dump, Kind, NONE};
use crate::graph::ARRAY_ELEMENT;
use crate::parallel;

/// How a collection class stores its elements; labels are field name ids.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Shape {
    /// Elements sit in an array field (`ArrayList`, `ArrayDeque`, `PriorityQueue`).
    Array(u32),
    /// Buckets of nodes chained by a field (`HashMap`, Hashtable, `ConcurrentHashMap`).
    Hash { table: u32, next: u32 },
    /// Alternating key/value slots (`IdentityHashMap`).
    Identity(u32),
    /// A red-black tree (`TreeMap`).
    Tree { root: u32, left: u32, right: u32 },
    /// A node list (`LinkedList`, the linked queues).
    Linked { head: u32, next: u32 },
    /// Wraps another collection (`HashSet` over a `HashMap`).
    Delegate(u32),
}

const KNOWN: [(&str, &[&str]); 21] = [
    ("java.util.ArrayList", &["array", "elementData"]),
    ("java.util.Vector", &["array", "elementData"]),
    ("java.util.ArrayDeque", &["array", "elements"]),
    ("java.util.PriorityQueue", &["array", "queue"]),
    ("java.util.concurrent.CopyOnWriteArrayList", &["array", "array"]),
    ("java.util.EnumMap", &["array", "vals"]),
    ("java.util.HashMap", &["hash", "table", "next"]),
    ("java.util.Hashtable", &["hash", "table", "next"]),
    ("java.util.WeakHashMap", &["hash", "table", "next"]),
    ("java.util.concurrent.ConcurrentHashMap", &["hash", "table", "next"]),
    ("java.util.IdentityHashMap", &["identity", "table"]),
    ("java.util.TreeMap", &["tree", "root", "left", "right"]),
    ("java.util.LinkedList", &["linked", "first", "next"]),
    ("java.util.concurrent.ConcurrentLinkedQueue", &["linked", "head", "next"]),
    ("java.util.concurrent.ConcurrentLinkedDeque", &["linked", "head", "next"]),
    ("java.util.concurrent.LinkedBlockingQueue", &["linked", "head", "next"]),
    ("java.util.concurrent.LinkedBlockingDeque", &["linked", "first", "next"]),
    ("java.util.HashSet", &["delegate", "map"]),
    ("java.util.TreeSet", &["delegate", "m"]),
    ("java.util.Properties", &["delegate", "map"]),
    ("java.util.concurrent.CopyOnWriteArraySet", &["delegate", "al"]),
];

/// The shape of every class: its own if known, else the nearest known
/// superclass that actually has the fields.
pub fn shapes(dump: &Dump) -> Vec<Option<Shape>> {
    let mut own: Vec<Option<Shape>> = vec![None; dump.classes.len()];
    for (name, spec) in KNOWN {
        let Some(class) = dump.class_named(name) else { continue };
        let label = |field: &str| dump.field_offset(class, field).and(dump.name_id(field));
        let shape = match spec {
            ["array", field] => label(field).map(Shape::Array),
            ["hash", table_field, next_field] => label(table_field)
                .zip(dump.name_id(next_field))
                .map(|(table, next)| Shape::Hash { table, next }),
            ["identity", field] => label(field).map(Shape::Identity),
            ["tree", root_field, left_field, right_field] => label(root_field)
                .zip(dump.name_id(left_field))
                .zip(dump.name_id(right_field))
                .map(|((root, left), right)| Shape::Tree { root, left, right }),
            ["linked", head_field, next_field] => label(head_field)
                .zip(dump.name_id(next_field))
                .map(|(head, next)| Shape::Linked { head, next }),
            ["delegate", field] => label(field).map(Shape::Delegate),
            _ => None,
        };
        own[class as usize] = shape;
    }
    (0..dump.classes.len() as u32)
        .map(|class| dump.ancestry(class).find_map(|ancestor| own[ancestor as usize]))
        .collect()
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CollectionStats {
    pub entries: u64,
    pub capacity: u64,
    /// Non-empty buckets, for hash tables.
    pub used_buckets: u64,
    /// The backing array, or `NONE`.
    pub backing: u32,
}

/// One collection class, summed over its reachable instances.
#[derive(Default)]
pub struct CollectionRow {
    pub class: u32,
    pub instances: u64,
    pub entries: u64,
    pub capacity: u64,
    pub wasted: u64,
    pub empty: u64,
    pub collisions: u64,
}

/// An under-filled collection or array.
pub struct Sparse {
    pub object: u32,
    pub stats: CollectionStats,
    pub wasted: u64,
}

#[derive(Default)]
pub struct Collections {
    pub rows: Vec<CollectionRow>,
    /// Under-filled collections and plain arrays, most waste first.
    pub sparse: Vec<Sparse>,
    /// Hash tables with the most chained entries: `(object, stats)`.
    pub colliding: Vec<(u32, CollectionStats)>,
    /// Empty collections and the bytes they and their private arrays take.
    pub empty: Objects,
}

const MAX_STEPS: usize = 1 << 24;
/// Wrappers (a `HashSet` over its `HashMap` and the like) followed to the collection inside.
const MAX_DELEGATE_DEPTH: usize = 4;
/// Object arrays at least this long and half empty, owned by no collection, count as sparse.
const SPARSE_ARRAY_MIN_LEN: u32 = 1024;
/// Collections this big and half empty count as sparse.
const SPARSE_MIN_CAPACITY: u64 = 64;
/// Hash tables with this many entries in under half as many buckets count as colliding.
const COLLIDING_MIN_ENTRIES: u64 = 64;
/// Sparse and colliding collections kept, largest first.
const MAX_LISTED: usize = 100;

impl Heap<'_> {
    pub fn shape_of(&self, object: u32) -> Option<Shape> {
        self.shapes[self.class(object) as usize]
    }

    /// Walk a collection's elements: `(key or None, value)`, at most `limit`.
    pub fn entries(&self, collection: u32, limit: usize) -> Vec<(Option<u32>, u32)> {
        let mut out = Vec::new();
        self.walk(collection, 0, &mut |key, value| {
            out.push((key, value));
            out.len() < limit
        });
        out
    }

    /// A collection another one wraps (a `HashSet`'s map): counted under the wrapper.
    fn wrapped(&self, collection: u32) -> bool {
        let dominator = self.dominators.idom[collection as usize];
        dominator != self.graph.root
            && matches!(self.shape_of(dominator), Some(Shape::Delegate(field)) if self.graph.field(dominator, field) == Some(collection))
    }

    pub fn measure(&self, collection: u32) -> Option<CollectionStats> {
        self.measure_depth(collection, 0)
    }

    fn measure_depth(&self, collection: u32, depth: usize) -> Option<CollectionStats> {
        let graph = self.graph;
        let mut stats = CollectionStats { backing: NONE, ..CollectionStats::default() };
        let mut nodes = 0u64;
        let mut count = |_| {
            nodes += 1;
            true
        };
        match self.shape_of(collection)? {
            Shape::Array(field) => {
                let array = graph.field(collection, field)?;
                stats.backing = array;
                stats.capacity = u64::from(self.dump.objects[array as usize].len);
                stats.entries = graph.edges(array).len() as u64;
            }
            Shape::Identity(field) => {
                let array = graph.field(collection, field)?;
                stats.backing = array;
                stats.capacity = u64::from(self.dump.objects[array as usize].len) / 2;
                stats.entries = graph
                    .edges(array)
                    .labels()
                    .filter(|label| (label & !ARRAY_ELEMENT).is_multiple_of(2))
                    .count() as u64;
            }
            Shape::Hash { table, next } => {
                let Some(buckets) = graph.field(collection, table) else { return Some(stats) };
                stats.backing = buckets;
                stats.capacity = u64::from(self.dump.objects[buckets as usize].len);
                stats.used_buckets = graph.edges(buckets).len() as u64;
                self.hash_nodes(buckets, next, &mut count);
                stats.entries = nodes;
            }
            Shape::Tree { root, left, right } => {
                if let Some(root_node) = graph.field(collection, root) {
                    self.tree_nodes(root_node, left, right, &mut count);
                }
                (stats.entries, stats.capacity) = (nodes, nodes);
            }
            Shape::Linked { head, next } => {
                if let Some(head_node) = graph.field(collection, head) {
                    self.chain(head_node, next, &mut count);
                }
                (stats.entries, stats.capacity) = (nodes, nodes);
            }
            Shape::Delegate(field) => {
                if depth > MAX_DELEGATE_DEPTH {
                    return None;
                }
                return self.measure_depth(graph.field(collection, field)?, depth + 1);
            }
        }
        Some(stats)
    }

    /// Visit each `(key, value)` until `f` returns false.
    fn walk(&self, collection: u32, depth: usize, f: &mut dyn FnMut(Option<u32>, u32) -> bool) {
        let graph = self.graph;
        let (key, item) = (self.labels.get("key"), self.labels.get("item"));
        // HashMap nodes call it `value`, ConcurrentHashMap nodes `val`.
        let value_of = |node: u32| ["value", "val"].iter().find_map(|name| self.field(node, name));
        let Some(shape) = self.shape_of(collection) else { return };
        match shape {
            Shape::Array(field) | Shape::Identity(field) => {
                let Some(array) = graph.field(collection, field) else { return };
                if matches!(shape, Shape::Array(_)) {
                    for element in graph.edges(array).targets() {
                        if !f(None, element) {
                            return;
                        }
                    }
                } else {
                    let mut pending: Option<u32> = None;
                    for (element, label) in graph.edges(array).iter() {
                        if (label & !ARRAY_ELEMENT).is_multiple_of(2) {
                            pending = Some(element);
                        } else if !f(pending.take(), element) {
                            return;
                        }
                    }
                }
            }
            Shape::Hash { table, next } => {
                let Some(buckets) = graph.field(collection, table) else { return };
                self.hash_nodes(buckets, next, &mut |node| {
                    let node_key =
                        key.and_then(|label| graph.field(node, label)).or_else(|| self.referent_of(node));
                    value_of(node).is_none_or(|value| f(node_key, value))
                });
            }
            Shape::Tree { root, left, right } => {
                let Some(root_node) = graph.field(collection, root) else { return };
                self.tree_nodes(root_node, left, right, &mut |node| {
                    value_of(node)
                        .is_none_or(|value| f(key.and_then(|label| graph.field(node, label)), value))
                });
            }
            Shape::Linked { head, next } => {
                let Some(head_node) = graph.field(collection, head) else { return };
                self.chain(head_node, next, &mut |node| {
                    item.and_then(|label| graph.field(node, label)).is_none_or(|value| f(None, value))
                });
            }
            Shape::Delegate(field) => {
                if let Some(inner) = graph.field(collection, field).filter(|_| depth <= MAX_DELEGATE_DEPTH) {
                    self.walk(inner, depth + 1, f);
                }
            }
        }
    }

    /// Every node off a hash table: bucket heads, their `next` chains, tree bins via `first`.
    fn hash_nodes(&self, table: u32, next: u32, f: &mut dyn FnMut(u32) -> bool) -> bool {
        let graph = self.graph;
        let first = self.labels.get("first");
        for head in graph.edges(table).targets() {
            let start = first.and_then(|label| graph.field(head, label)).unwrap_or(head);
            if !self.chain(start, next, f) {
                return false;
            }
        }
        true
    }

    /// Follow `next` from `node`, bounded against corrupt cycles. A `WeakHashMap` entry is also
    /// a Reference whose own `next`, after `queue`, is its queue link, not the chain.
    fn chain(&self, mut node: u32, next: u32, f: &mut dyn FnMut(u32) -> bool) -> bool {
        let queue = self.labels.get("queue");
        for _ in 0..MAX_STEPS {
            if !f(node) {
                return false;
            }
            let reference = self.dump.class_of(node).ref_kind.is_some();
            let mut own =
                self.graph.edges(node).iter().take_while(|&(_, label)| !reference || Some(label) != queue);
            match own.find(|&(_, label)| label == next) {
                Some((target, _)) => node = target,
                None => return true,
            }
        }
        true
    }

    fn tree_nodes(&self, root: u32, left: u32, right: u32, f: &mut dyn FnMut(u32) -> bool) {
        let graph = self.graph;
        let mut stack = vec![root];
        let mut steps = 0;
        while let Some(node) = stack.pop() {
            steps += 1;
            if steps > MAX_STEPS || !f(node) {
                return;
            }
            stack.extend(graph.field(node, right));
            stack.extend(graph.field(node, left));
        }
    }

    /// Measure every reachable collection and under-filled array.
    pub fn collections(&self) -> Collections {
        let class_count = self.dump.classes.len();
        let parts = parallel::ranges(self.dump.objects.len(), |lo, hi| self.collections_in(lo, hi));
        let mut rows: Vec<Option<CollectionRow>> = (0..class_count).map(|_| None).collect();
        let mut out = Collections::default();
        for part in parts {
            for part_row in part.rows {
                let row = rows[part_row.class as usize]
                    .get_or_insert(CollectionRow { class: part_row.class, ..CollectionRow::default() });
                row.instances += part_row.instances;
                row.entries += part_row.entries;
                row.capacity += part_row.capacity;
                row.wasted += part_row.wasted;
                row.empty += part_row.empty;
                row.collisions += part_row.collisions;
            }
            out.sparse.extend(part.sparse);
            out.colliding.extend(part.colliding);
            out.empty.count += part.empty.count;
            out.empty.bytes += part.empty.bytes;
        }
        out.rows = rows.into_iter().flatten().filter(|row| !self.excluded(row.class)).collect();
        out.rows.sort_by(|a, b| {
            b.wasted.cmp(&a.wasted).then(b.instances.cmp(&a.instances)).then(a.class.cmp(&b.class))
        });
        trim(&mut out.sparse, |sparse| sparse.wasted);
        trim(&mut out.colliding, |(_, stats)| stats.entries - stats.used_buckets);
        out
    }

    /// One worker's share of `collections`: the objects `lo..hi`.
    fn collections_in(&self, lo: usize, hi: usize) -> Collections {
        let dump = self.dump;
        let ref_size = u64::from(dump.sizing.ref_size);
        let mut rows: Vec<Option<CollectionRow>> = (0..dump.classes.len()).map(|_| None).collect();
        let mut part = Collections::default();
        for object in lo as u32..hi as u32 {
            if !self.reachable(object) {
                continue;
            }
            let record = &dump.objects[object as usize];
            if record.kind == Kind::ObjectArray {
                part.sparse.extend(self.sparse_array(object, ref_size));
                continue;
            }
            let Some(stats) = self.measure(object) else { continue };
            if self.wrapped(object) {
                continue;
            }
            let row = rows[record.class as usize]
                .get_or_insert(CollectionRow { class: record.class, ..CollectionRow::default() });
            let used =
                if stats.used_buckets > 0 { stats.used_buckets } else { stats.entries.min(stats.capacity) };
            let wasted = (stats.capacity - used) * ref_size;
            row.instances += 1;
            row.entries += stats.entries;
            row.capacity += stats.capacity;
            row.wasted += wasted;
            if stats.used_buckets > 0 {
                row.collisions += stats.entries.saturating_sub(stats.used_buckets);
            }
            if stats.entries == 0 {
                row.empty += 1;
                part.empty.count += 1;
                let private = stats.backing != NONE && self.dominators.idom[stats.backing as usize] == object;
                part.empty.bytes +=
                    self.shallow(object) + if private { self.shallow(stats.backing) } else { 0 };
            }
            if stats.capacity >= SPARSE_MIN_CAPACITY && used * 2 < stats.capacity {
                part.sparse.push(Sparse { object, stats, wasted });
            }
            if stats.used_buckets > 0
                && stats.entries >= COLLIDING_MIN_ENTRIES
                && stats.used_buckets * 2 < stats.entries
            {
                part.colliding.push((object, stats));
            }
        }
        part.rows = rows.into_iter().flatten().collect();
        trim(&mut part.sparse, |sparse| sparse.wasted);
        trim(&mut part.colliding, |(_, stats)| stats.entries - stats.used_buckets);
        part
    }

    /// A big plain object array, owned by no collection, under half filled.
    fn sparse_array(&self, object: u32, ref_size: u64) -> Option<Sparse> {
        let record = &self.dump.objects[object as usize];
        let filled = self.graph.edges(object).len() as u64;
        let idom = self.dominators.idom[object as usize];
        let backs_collection = idom != self.graph.root && self.shape_of(idom).is_some();
        if record.len < SPARSE_ARRAY_MIN_LEN || filled * 2 >= u64::from(record.len) || backs_collection {
            return None;
        }
        let stats = CollectionStats {
            entries: filled,
            capacity: u64::from(record.len),
            used_buckets: 0,
            backing: NONE,
        };
        Some(Sparse { object, stats, wasted: (stats.capacity - filled) * ref_size })
    }
}

/// Keep the `MAX_LISTED` largest by `key`.
fn trim<T>(items: &mut Vec<T>, key: impl Fn(&T) -> u64) {
    items.sort_by_key(|item| std::cmp::Reverse(key(item)));
    items.truncate(MAX_LISTED);
}
