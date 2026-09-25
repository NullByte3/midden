//! Analyses over the graph and dominator tree, in object indices; `report/` renders them.
//! This file holds the shared parts: retained sizes, the histogram, referrers, root paths.

pub mod baseline;
pub mod collections;
pub mod duplicates;
pub mod garbage;
pub mod loaders;
pub mod native;
pub mod references;
pub mod suspects;
pub mod system;
pub mod threads;

use std::cmp::Reverse;
use std::collections::HashMap;
use std::hash::Hash;

use super::dom::{self, DominatorTree, Reachability};
use super::dump::{Dump, FastMap, Kind, NONE, package_of};
use super::graph::{ARRAY_ELEMENT, Graph, LOADER};
use super::hprof::RootKind;
use super::parallel;
use super::pattern::{Pattern, short};

/// Referrer label flag: the source is a class object, the field a static.
pub const STATIC: u32 = 1 << 30;

/// Field names the analyses look up, resolved to label ids once.
pub struct Labels(HashMap<&'static str, u32>);

const LABEL_NAMES: [&str; 21] = [
    "referent",
    "key",
    "value",
    "val",
    "next",
    "first",
    "item",
    "table",
    "threadLocals",
    "inheritableThreadLocals",
    "att",
    "cleaner",
    "fd",
    "plugin",
    "description",
    "map",
    "props",
    "queue",
    "name",
    "elementData",
    "head",
];

impl Labels {
    fn new(dump: &Dump) -> Labels {
        Labels(LABEL_NAMES.iter().filter_map(|&name| dump.name_id(name).map(|id| (name, id))).collect())
    }

    pub fn get(&self, name: &str) -> Option<u32> {
        self.0.get(name).copied()
    }
}

/// One analysed dump: the graph, liveness, dominators and derived tables.
pub struct Heap<'a> {
    pub dump: &'a Dump,
    pub graph: &'a Graph,
    pub reachability: Reachability,
    pub dominators: DominatorTree,
    /// Shallow bytes of every object in the dump.
    pub total: u64,
    /// Bytes reachable through strong references only: the live heap.
    pub live: u64,
    /// Reachable only through soft/weak/phantom referents.
    pub weak_only: Objects,
    pub unreachable: Objects,
    /// One per `dump.threads`, from the Thread objects' `name` fields.
    pub thread_names: Vec<String>,
    /// The class each class object stands for.
    pub class_objects: FastMap<u32, u32>,
    pub labels: Labels,
    pub shapes: Vec<Option<collections::Shape>>,
    /// Classes `--exclude` hides from suspects and tables.
    excluded: Vec<bool>,
    /// Per object: reachable only through weak referents.
    weakly_reachable: Vec<bool>,
}

/// A number of objects and their bytes.
#[derive(Clone, Copy, Default)]
pub struct Objects {
    pub count: u64,
    pub bytes: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClassRow {
    pub class: u32,
    pub instances: u64,
    pub shallow: u64,
    pub retained: u64,
}

/// Edges into something, grouped by source class and field.
pub struct Referrer {
    pub class: u32,
    /// Field label, or `ARRAY_ELEMENT` for array elements.
    pub label: u32,
    pub count: u64,
}

impl<'a> Heap<'a> {
    pub fn new(dump: &'a Dump, graph: &'a Graph) -> Heap<'a> {
        // The BFS and the dominators only read the graph: run them side by side.
        let (strong, dominators) = match parallel::threads() {
            1 => (dom::reach(graph, dump), dom::dominators(graph, dump)),
            _ => std::thread::scope(|scope| {
                let bfs = scope.spawn(|| dom::reach(graph, dump));
                let tree = dom::dominators(graph, dump);
                (bfs.join().expect("reachability"), tree)
            }),
        };
        let total = dump.total_shallow();
        let weak = dom::weak_only(graph, dump, &strong);
        let unreachable = Objects {
            count: dump.objects.len() as u64 - strong.count - weak.count,
            bytes: total - strong.bytes - weak.bytes,
        };
        let class_objects = dump
            .classes
            .iter()
            .enumerate()
            .filter(|(_, class)| class.dumped)
            .filter_map(|(i, class)| dump.lookup(class.id).map(|object| (object, i as u32)))
            .collect();
        Heap {
            dump,
            graph,
            live: strong.bytes,
            reachability: strong,
            dominators,
            total,
            weak_only: Objects { count: weak.count, bytes: weak.bytes },
            unreachable,
            thread_names: Vec::new(),
            class_objects,
            labels: Labels::new(dump),
            shapes: collections::shapes(dump),
            excluded: vec![false; dump.classes.len()],
            weakly_reachable: weak.seen,
        }
    }

    pub fn set_excludes(&mut self, patterns: &[Pattern]) {
        for (i, class) in self.dump.classes.iter().enumerate() {
            self.excluded[i] = patterns.iter().any(|pattern| pattern.matches(&class.name));
        }
    }

    pub fn excluded(&self, class: u32) -> bool {
        self.excluded[class as usize]
    }

    /// A thread's name in quotes, or its serial when unknown.
    pub fn thread_name(&self, serial: u32) -> String {
        let name = self
            .dump
            .threads
            .iter()
            .position(|thread| thread.serial == serial)
            .and_then(|i| self.thread_names.get(i));
        match name {
            Some(name) if !name.is_empty() => format!("\"{name}\""),
            _ => format!("thread #{serial}"),
        }
    }

    pub fn retained(&self, object: u32) -> u64 {
        self.dominators.retained[object as usize]
    }

    pub fn shallow(&self, object: u32) -> u64 {
        u64::from(self.dump.objects[object as usize].shallow)
    }

    pub fn reachable(&self, object: u32) -> bool {
        self.reachability.parent[object as usize] != NONE
    }

    /// Alive only through soft, weak or phantom references.
    pub fn weakly_reachable(&self, object: u32) -> bool {
        self.weakly_reachable[object as usize]
    }

    pub fn class(&self, object: u32) -> u32 {
        self.dump.objects[object as usize].class
    }

    pub fn is_string(&self, object: u32) -> bool {
        self.class(object) == self.dump.string_class
    }

    /// Share of the live heap, in percent.
    pub fn percent_of_live(&self, bytes: u64) -> f64 {
        if self.live == 0 { 0.0 } else { bytes as f64 * 100.0 / self.live as f64 }
    }

    /// Objects dominated by the roots alone, biggest first.
    pub fn top_level(&self) -> &[u32] {
        self.dominators.top_level()
    }

    pub fn field(&self, object: u32, name: &str) -> Option<u32> {
        self.graph.field(object, self.labels.get(name)?)
    }

    /// The referent of a Reference object, weak or strong.
    pub fn referent_of(&self, object: u32) -> Option<u32> {
        self.graph.referent(object, self.labels.get("referent").unwrap_or(NONE))
    }

    /// Retained bytes per group. An object dominated by another of its group is skipped,
    /// so a list's nodes are not counted once per node.
    pub fn grouped_retained(&self, group_of: impl Fn(u32) -> u32 + Sync, groups: usize) -> Vec<u64> {
        let tree = &self.dominators;
        // Each worker scans a preorder range, keeping `(end, group)` open for the topmost
        // object of each group above; climbing from the range's first object finds those.
        let parts = parallel::ranges(tree.preorder.len(), |lo, hi| {
            let (mut retained, mut inside) = (vec![0u64; groups], vec![false; groups]);
            let mut topmost: FastMap<u32, u32> = FastMap::default();
            let mut ancestor = tree.preorder.get(lo).map_or(NONE, |&object| tree.idom[object as usize]);
            while ancestor != NONE && ancestor != self.graph.root {
                topmost.insert(
                    group_of(ancestor),
                    tree.subtree_end[tree.preorder_index[ancestor as usize] as usize],
                );
                ancestor = tree.idom[ancestor as usize];
            }
            let mut open: Vec<(u32, u32)> = topmost.into_iter().map(|(group, end)| (end, group)).collect();
            open.sort_unstable_by(|a, b| b.cmp(a));
            for &(_, group) in &open {
                inside[group as usize] = true;
            }
            for pos in lo..hi {
                while let Some(&(_, group)) = open.last().filter(|entry| entry.0 as usize <= pos) {
                    inside[group as usize] = false;
                    open.pop();
                }
                let object = tree.preorder[pos];
                let group = group_of(object);
                if !inside[group as usize] {
                    retained[group as usize] += tree.retained[object as usize];
                    inside[group as usize] = true;
                    open.push((tree.subtree_end[pos], group));
                }
            }
            retained
        });
        (0..groups).map(|group| parts.iter().map(|part| part[group]).sum()).collect()
    }

    /// Per class: instances, shallow bytes and retained bytes, counted the way MAT does.
    pub fn histogram(&self) -> Vec<ClassRow> {
        let dump = self.dump;
        let retained =
            self.grouped_retained(|object| dump.objects[object as usize].class, dump.classes.len());
        let shallow = parallel::ranges(dump.objects.len(), |lo, hi| {
            let mut sums = vec![0u64; dump.classes.len()];
            for record in &dump.objects[lo..hi] {
                sums[record.class as usize] += u64::from(record.shallow);
            }
            sums
        });
        let mut rows: Vec<ClassRow> = (0..dump.classes.len() as u32)
            .filter(|&class| dump.classes[class as usize].instances > 0)
            .map(|class| ClassRow {
                class,
                instances: dump.classes[class as usize].instances,
                shallow: shallow.iter().map(|part| part[class as usize]).sum(),
                retained: retained[class as usize],
            })
            .collect();
        rows.sort_by(|a, b| {
            b.retained.cmp(&a.retained).then(b.shallow.cmp(&a.shallow)).then(a.class.cmp(&b.class))
        });
        rows
    }

    /// The histogram rolled up by package, retained counted once per package.
    pub fn packages(&self, histogram: &[ClassRow]) -> Vec<(String, ClassRow)> {
        let dump = self.dump;
        let (package_of_class, names) = dense_ids(dump.classes.iter().map(|class| package_of(&class.name)));
        let retained = self.grouped_retained(
            |object| package_of_class[dump.objects[object as usize].class as usize],
            names.len(),
        );
        let mut rows: Vec<(String, ClassRow)> = names
            .iter()
            .zip(retained)
            .map(|(name, retained)| {
                (name.to_string(), ClassRow { class: NONE, instances: 0, shallow: 0, retained })
            })
            .collect();
        for class_row in histogram {
            let row = &mut rows[package_of_class[class_row.class as usize] as usize].1;
            row.instances += class_row.instances;
            row.shallow += class_row.shallow;
        }
        rows.retain(|row| row.1.instances > 0);
        rows.sort_by(|a, b| b.1.retained.cmp(&a.1.retained).then(a.0.cmp(&b.0)));
        rows
    }

    /// The objects `object` dominates (itself included), by class, biggest first.
    pub fn retained_set(&self, object: u32) -> (Vec<ClassRow>, u64) {
        let dominated = match self.dominators.subtree(object) {
            [] => std::slice::from_ref(&object),
            subtree => subtree,
        };
        let parts = parallel::ranges(dominated.len(), |lo, hi| {
            let mut tally = Tally::new(self.dump.classes.len());
            for &member in &dominated[lo..hi] {
                tally.add(&self.dump.objects[member as usize]);
            }
            tally
        });
        parts.into_iter().reduce(Tally::merge).expect("one part at least").rows()
    }

    /// Who references what: for every edge from a live object into an object
    /// `slot` maps somewhere, count `(source class, field)` pairs.
    pub fn referrers(&self, slot: impl Fn(u32) -> Option<usize> + Sync) -> Vec<Vec<Referrer>> {
        let graph = self.graph;
        let parts = parallel::ranges(self.dump.objects.len(), |lo, hi| {
            let mut counts: Vec<FastMap<(u32, u32), u64>> = Vec::new();
            for source in lo as u32..hi as u32 {
                if !self.reachable(source) {
                    continue;
                }
                let record = &self.dump.objects[source as usize];
                // Only a class object can be in the map; the rest skip the lookup.
                let class_object =
                    if record.kind == Kind::Class { self.class_objects.get(&source) } else { None };
                let (class, flag) = match class_object {
                    Some(&class) => (class, STATIC),
                    None => (record.class, 0),
                };
                for (target, label) in graph.edges(source).iter() {
                    if let Some(index) = slot(target) {
                        while counts.len() <= index {
                            counts.push(FastMap::default());
                        }
                        let label = if label & ARRAY_ELEMENT != 0 { ARRAY_ELEMENT } else { label | flag };
                        *counts[index].entry((class, label)).or_default() += 1;
                    }
                }
            }
            counts
        });
        let slots = parts.iter().map(Vec::len).max().unwrap_or(0);
        (0..slots)
            .map(|index| {
                let mut merged: FastMap<(u32, u32), u64> = FastMap::default();
                for (key, count) in parts.iter().filter_map(|part| part.get(index)).flatten() {
                    *merged.entry(*key).or_default() += count;
                }
                let mut referrers: Vec<Referrer> = merged
                    .into_iter()
                    .map(|((class, label), count)| Referrer { class, label, count })
                    .collect();
                referrers.sort_by(|a, b| {
                    b.count.cmp(&a.count).then(a.class.cmp(&b.class)).then(a.label.cmp(&b.label))
                });
                referrers
            })
            .collect()
    }

    pub fn referrers_of(&self, object: u32) -> Vec<Referrer> {
        self.referrers(|target| (target == object).then_some(0)).into_iter().next().unwrap_or_default()
    }

    /// The live objects that reference `object`, biggest retained first: `(source, label)`.
    pub fn referrer_objects(&self, object: u32, limit: usize) -> Vec<(u32, u32)> {
        let graph = self.graph;
        let parts = parallel::ranges(self.dump.objects.len(), |lo, hi| {
            (lo as u32..hi as u32)
                .filter(|&source| self.reachable(source))
                .filter_map(|source| graph.edges(source).label_of(object).map(|label| (source, label)))
                .collect::<Vec<_>>()
        });
        let mut all = parts.concat();
        all.sort_by(|a, b| self.retained(b.0).cmp(&self.retained(a.0)).then(a.0.cmp(&b.0)));
        all.truncate(limit);
        all
    }

    /// Walk up the dominator tree keeping the class that owns the most bytes per level.
    /// Members dominated by their own class are skipped: "Object[] ← `ArrayList`", not "Node ← Node".
    pub fn owners_of(&self, members: &[u32]) -> Vec<(u32, u64, u64)> {
        let root = self.graph.root;
        let same_class = |object: u32| {
            let dominator = self.dominators.idom[object as usize];
            dominator != root && self.class(dominator) == self.class(object)
        };
        let mut current: Vec<u32> =
            members.iter().copied().filter(|&object| self.reachable(object) && !same_class(object)).collect();
        let mut out = Vec::new();
        for _ in 0..6 {
            // Bytes per owning class, `NONE` standing for the roots.
            let parts = parallel::ranges(current.len(), |lo, hi| {
                let mut bytes: FastMap<u32, u64> = FastMap::default();
                for &object in &current[lo..hi] {
                    let dominator = self.dominators.idom[object as usize];
                    let class = if dominator == root { NONE } else { self.class(dominator) };
                    *bytes.entry(class).or_default() += self.dominators.retained[object as usize];
                }
                bytes
            });
            let mut bytes_of: FastMap<u32, u64> = FastMap::default();
            for (class, bytes) in parts.into_iter().flatten() {
                *bytes_of.entry(class).or_default() += bytes;
            }
            let total = bytes_of.values().sum();
            let Some((class, bytes)) = bytes_of.into_iter().max_by_key(|&(class, bytes)| (bytes, class))
            else {
                break;
            };
            out.push((class, bytes, total));
            if class == NONE {
                break;
            }
            let mut next: Vec<u32> = parallel::ranges(current.len(), |lo, hi| {
                current[lo..hi]
                    .iter()
                    .map(|&object| self.dominators.idom[object as usize])
                    .filter(|&dominator| dominator != root && self.class(dominator) == class)
                    .collect::<Vec<_>>()
            })
            .concat();
            next.sort_unstable();
            next.dedup();
            current = next;
        }
        out
    }

    /// Root-to-object path with the label of the edge into each hop.
    pub fn root_path(&self, object: u32) -> Vec<(u32, Option<u32>)> {
        self.labelled(&self.reachability.path(self.graph.root, object))
    }

    /// Up to `limit` root paths arriving through different referrers.
    pub fn root_paths(&self, object: u32, limit: usize) -> Vec<Vec<(u32, Option<u32>)>> {
        dom::paths(self.graph, self.dump, &self.reachability, object, limit)
            .into_iter()
            .map(|path| self.labelled(&path))
            .collect()
    }

    fn labelled(&self, path: &[u32]) -> Vec<(u32, Option<u32>)> {
        path.iter()
            .enumerate()
            .map(|(i, &object)| {
                (object, if i == 0 { None } else { self.graph.label_of(path[i - 1], object) })
            })
            .collect()
    }

    /// An edge as text without indices: `static Owner.FIELD`, `.field`, `[]`.
    pub fn edge_text(&self, from: Option<u32>, label: u32) -> String {
        let dump = self.dump;
        match label {
            LOADER => "<classloader>".to_string(),
            label if label & ARRAY_ELEMENT != 0 => "[]".to_string(),
            label => {
                let name = &dump.names[label as usize];
                match from.and_then(|source| self.class_objects.get(&source)) {
                    Some(&class) => format!("static {}.{name}", short(&dump.classes[class as usize].name)),
                    None => format!(".{name}"),
                }
            }
        }
    }

    /// The object's shape without its address: class name, `class X`, `T[]`.
    pub fn kind_text(&self, object: u32) -> String {
        let dump = self.dump;
        let record = &dump.objects[object as usize];
        match self.class_objects.get(&object) {
            Some(&class) if record.kind == Kind::Class => {
                format!("class {}", dump.classes[class as usize].name)
            }
            _ => dump.classes[record.class as usize].name.clone(),
        }
    }

    /// Names a top-level structure across dumps: its root path without addresses or
    /// indices, plus the thread name for a thread.
    pub fn path_key(&self, object: u32) -> String {
        let path = self.root_path(object);
        let mut key = String::new();
        for (i, &(hop, label)) in path.iter().enumerate() {
            if let Some(label) = label {
                key.push_str(&self.edge_text(Some(path[i - 1].0), label));
                key.push(' ');
            }
            key.push_str(&self.kind_text(hop));
            let thread = self.dump.threads.iter().position(|thread| thread.object == hop);
            if let Some(name) =
                thread.and_then(|index| self.thread_names.get(index)).filter(|name| !name.is_empty())
            {
                key.extend([" \"", name.as_str(), "\""]);
            }
            key.push(' ');
        }
        key.trim_end().to_string()
    }

    /// Why `object` is a GC root, in words; empty when it is not one.
    pub fn root_note(&self, object: u32) -> String {
        let dump = self.dump;
        let mut roots: Vec<_> =
            dump.roots.iter().filter(|(rooted, _)| *rooted == object).map(|(_, root)| *root).collect();
        // A class object is a root because it is loaded; a frame holding it says less.
        let is_class = dump.objects[object as usize].kind == Kind::Class;
        roots.sort_by_key(|root| (is_class && root.kind != RootKind::StickyClass, root.kind));
        let Some(root) = roots.first() else { return String::new() };
        let thread = |serial: u32| self.thread_name(serial);
        let note = match root.kind {
            RootKind::JavaFrame | RootKind::JniLocal | RootKind::JniMonitor => {
                let what = if root.kind == RootKind::JavaFrame { "local" } else { root.kind.label() };
                let frame = dump.frame_of(root.thread_serial, root.frame).map(|frame| format!(" at {frame}"));
                format!("{what} in {}{}", thread(root.thread_serial), frame.unwrap_or_default())
            }
            RootKind::ThreadObject => format!("thread {}", thread(root.thread_serial)),
            RootKind::NativeStack | RootKind::ThreadBlock => {
                format!("{} of {}", root.kind.label(), thread(root.thread_serial))
            }
            RootKind::StickyClass => "system class".to_string(),
            kind => format!("{} root", kind.label()),
        };
        match roots.iter().filter(|other| other.kind != root.kind).count() {
            0 => note,
            others => format!("{note} (+{others} more root kinds)"),
        }
    }

    /// Classes with instances whose name matches, excluded ones left out.
    pub fn classes_matching(&self, pattern: &Pattern) -> Vec<u32> {
        (0..self.dump.classes.len() as u32)
            .filter(|&class| self.dump.classes[class as usize].instances > 0)
            .filter(|&class| pattern.matches(&self.dump.classes[class as usize].name))
            .collect()
    }

    /// Reachable instances of a class, in index order.
    pub fn members(&self, class: u32) -> Vec<u32> {
        self.members_of(&[class]).pop().unwrap_or_default()
    }

    /// Reachable instances of each class, in index order, from one scan.
    pub fn members_of(&self, classes: &[u32]) -> Vec<Vec<u32>> {
        let mut slot = vec![NONE; self.dump.classes.len()];
        for (i, &class) in classes.iter().enumerate() {
            slot[class as usize] = i as u32;
        }
        let parts = parallel::ranges(self.dump.objects.len(), |lo, hi| {
            let mut out = vec![Vec::new(); classes.len()];
            for object in (lo as u32..hi as u32).filter(|&object| self.reachable(object)) {
                let index = slot[self.class(object) as usize];
                if index != NONE {
                    out[index as usize].push(object);
                }
            }
            out
        });
        (0..classes.len()).map(|i| parts.iter().flat_map(|part| part[i].iter().copied()).collect()).collect()
    }

    /// Every instance of a class, biggest retained first.
    pub fn instances_of(&self, class: u32) -> Vec<u32> {
        let mut instances = parallel::ranges(self.dump.objects.len(), |lo, hi| {
            (lo as u32..hi as u32).filter(|&object| self.class(object) == class).collect::<Vec<_>>()
        })
        .concat();
        instances.sort_by(|&a, &b| self.retained(b).cmp(&self.retained(a)).then(a.cmp(&b)));
        instances
    }

    /// The largest reachable instance of every class: `(retained, object)`.
    pub fn biggest_per_class(&self) -> Vec<(u64, u32)> {
        let n = self.dump.classes.len();
        let parts = parallel::ranges(self.dump.objects.len(), |lo, hi| {
            let mut best = vec![(0u64, NONE); n];
            for object in lo as u32..hi as u32 {
                let retained = self.dominators.retained[object as usize];
                let class = self.class(object) as usize;
                if self.reachable(object) && retained > best[class].0 {
                    best[class] = (retained, object);
                }
            }
            best
        });
        let mut best = vec![(0u64, NONE); n];
        for part in parts {
            for (class, candidate) in part.into_iter().enumerate() {
                if (candidate.0, Reverse(candidate.1)) > (best[class].0, Reverse(best[class].1)) {
                    best[class] = candidate;
                }
            }
        }
        best
    }
}

/// Dense ids for `keys` in first-seen order: the id of each key, and the distinct keys.
pub fn dense_ids<K: Hash + Eq + Copy>(keys: impl Iterator<Item = K>) -> (Vec<u32>, Vec<K>) {
    let mut ids: FastMap<K, u32> = FastMap::default();
    let mut distinct = Vec::new();
    let index = keys
        .map(|key| {
            *ids.entry(key).or_insert_with(|| {
                distinct.push(key);
                distinct.len() as u32 - 1
            })
        })
        .collect();
    (index, distinct)
}

/// `(class, (instances, bytes))` pairs as rows, biggest first.
pub fn rows_of(by_class: impl IntoIterator<Item = (u32, (u64, u64))>) -> Vec<ClassRow> {
    let mut rows: Vec<ClassRow> = by_class
        .into_iter()
        .map(|(class, (instances, shallow))| ClassRow { class, instances, shallow, retained: shallow })
        .collect();
    rows.sort_by(|a, b| b.shallow.cmp(&a.shallow).then(a.class.cmp(&b.class)));
    rows
}

/// Instances and bytes per class over a set of objects, indexed by class so
/// a walk over millions of objects never hashes.
pub struct Tally {
    instances: Vec<u64>,
    shallow: Vec<u64>,
    pub objects: u64,
}

impl Tally {
    pub fn new(classes: usize) -> Tally {
        Tally { instances: vec![0; classes], shallow: vec![0; classes], objects: 0 }
    }

    pub fn add(&mut self, record: &super::dump::Object) {
        self.instances[record.class as usize] += 1;
        self.shallow[record.class as usize] += u64::from(record.shallow);
        self.objects += 1;
    }

    /// Two tallies over disjoint sets as one.
    pub fn merge(mut self, other: Tally) -> Tally {
        self.instances.iter_mut().zip(other.instances).for_each(|(a, b)| *a += b);
        self.shallow.iter_mut().zip(other.shallow).for_each(|(a, b)| *a += b);
        self.objects += other.objects;
        self
    }

    /// Rows for the classes seen, biggest first, with the object count.
    pub fn rows(self) -> (Vec<ClassRow>, u64) {
        let seen = (0..self.instances.len() as u32)
            .filter(|&class| self.instances[class as usize] > 0)
            .map(|class| (class, (self.instances[class as usize], self.shallow[class as usize])));
        (rows_of(seen), self.objects)
    }
}
