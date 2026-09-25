//! Comparing two dumps of one process. The baseline is reduced to a `Snapshot` and
//! dropped before the main dump loads, so memory peaks at one dump.

use std::collections::{BTreeSet, HashMap};

use super::duplicates::Duplicates;
use super::{ClassRow, Heap};

/// Top-level objects, biggest first, whose structures are compared with the baseline.
const STRUCTURES_COMPARED: usize = 10_000;

/// What a baseline dump is reduced to before it is dropped.
pub struct Snapshot {
    pub path: String,
    pub live: u64,
    pub objects: u64,
    pub total: u64,
    pub classes: HashMap<String, ClassSums>,
    /// Top-level structures by path key → retained.
    pub structures: HashMap<String, u64>,
    /// Thread name → retained plus pinned by its stack.
    pub threads: HashMap<String, u64>,
    /// Loader key → what its classes own.
    pub loaders: HashMap<String, u64>,
    /// Duplicate string content hash → `(copies, wasted)`.
    pub strings: HashMap<u64, (u64, u64)>,
}

/// A class name's histogram rows, summed.
#[derive(Clone, Copy, Default, PartialEq, Eq)]
pub struct ClassSums {
    pub instances: u64,
    pub shallow: u64,
    pub retained: u64,
}

/// One measure in two dumps.
pub struct Change {
    pub before: i64,
    pub after: i64,
}

/// One class in two dumps.
pub struct Delta {
    pub name: String,
    pub instances: Change,
    pub shallow: Change,
    pub retained: Change,
}

/// A structure's retained bytes in two dumps, matched by its root path key.
pub struct StructureChange {
    pub key: String,
    /// The object now, or `NONE`.
    pub object: u32,
    pub before: u64,
    pub after: u64,
}

/// A thread's retained or a loader's owned bytes in two dumps.
pub struct NamedChange {
    pub name: String,
    pub before: u64,
    pub after: u64,
}

/// A duplicate string content in two dumps.
pub struct StringChange {
    /// The string now, or `NONE`.
    pub string: u32,
    pub hash: u64,
    pub copies_before: u64,
    pub copies_after: u64,
    pub wasted_before: u64,
    pub wasted_after: u64,
}

/// The changes from a snapshot to the current dump.
pub struct Diff {
    pub path: String,
    /// Change in live bytes, object count, total bytes.
    pub live: i64,
    pub objects: i64,
    pub total: i64,
    pub classes: Vec<Delta>,
    pub structures: Vec<StructureChange>,
    pub threads: Vec<NamedChange>,
    pub loaders: Vec<NamedChange>,
    pub strings: Vec<StringChange>,
}

impl Heap<'_> {
    /// A loader key stable across dumps: its class and the first class name it loaded.
    fn loader_key(&self, loader: u32) -> String {
        let dump = self.dump;
        if loader == crate::dump::NONE {
            return "bootstrap".to_string();
        }
        let id = dump.objects[loader as usize].id;
        let first = dump
            .classes
            .iter()
            .filter(|class| class.loader == id)
            .map(|class| class.name.as_str())
            .min()
            .unwrap_or("");
        format!("{} {first}", dump.class_name(loader))
    }

    /// Reduce this dump to what a later one can diff against.
    pub fn snapshot(&self, histogram: &[ClassRow], duplicates: Option<&Duplicates>) -> Snapshot {
        let dump = self.dump;
        let mut classes: HashMap<String, ClassSums> = HashMap::new();
        for row in histogram {
            let sums = classes.entry(dump.classes[row.class as usize].name.clone()).or_default();
            sums.instances += row.instances;
            sums.shallow += row.shallow;
            sums.retained += row.retained;
        }
        let mut structures: HashMap<String, u64> = HashMap::new();
        for &object in self.top_level().iter().take(STRUCTURES_COMPARED) {
            *structures.entry(self.path_key(object)).or_default() += self.retained(object);
        }
        let threads = self
            .threads()
            .into_iter()
            .map(|row| {
                (self.thread_name(dump.threads[row.thread].serial), row.retained + row.locals_retained)
            })
            .collect();
        let loaders =
            self.loaders(histogram).into_iter().map(|row| (self.loader_key(row.object), row.owns)).collect();
        let strings = duplicates
            .map(|duplicates| {
                duplicates.groups.iter().map(|group| (group.hash, (group.count, group.wasted))).collect()
            })
            .unwrap_or_default();
        Snapshot {
            path: dump.path.clone(),
            live: self.live,
            objects: dump.objects.len() as u64,
            total: self.total,
            classes,
            structures,
            threads,
            loaders,
            strings,
        }
    }

    /// This dump against a baseline snapshot, biggest changes first.
    pub fn diff(&self, histogram: &[ClassRow], duplicates: Option<&Duplicates>, base: &Snapshot) -> Diff {
        let now = self.snapshot(histogram, duplicates);
        Diff {
            path: base.path.clone(),
            live: now.live as i64 - base.live as i64,
            objects: now.objects as i64 - base.objects as i64,
            total: now.total as i64 - base.total as i64,
            classes: class_deltas(&now, base),
            structures: self.structure_changes(&now, base),
            threads: named_changes(&now.threads, &base.threads),
            loaders: named_changes(&now.loaders, &base.loaders),
            strings: string_changes(&now, base, duplicates),
        }
    }

    fn structure_changes(&self, now: &Snapshot, base: &Snapshot) -> Vec<StructureChange> {
        let mut objects: HashMap<String, u32> = HashMap::new();
        for &object in self.top_level().iter().take(STRUCTURES_COMPARED) {
            objects.entry(self.path_key(object)).or_insert(object);
        }
        let mut structures: Vec<StructureChange> = all_keys(&now.structures, &base.structures)
            .into_iter()
            .map(|key| StructureChange {
                key: key.clone(),
                object: objects.get(key).copied().unwrap_or(crate::dump::NONE),
                before: base.structures.get(key).copied().unwrap_or(0),
                after: now.structures.get(key).copied().unwrap_or(0),
            })
            .filter(|row| row.before != row.after)
            .collect();
        structures.sort_by(|a, b| {
            b.before.abs_diff(b.after).cmp(&a.before.abs_diff(a.after)).then(a.key.cmp(&b.key))
        });
        structures
    }
}

/// The keys of both maps, in order.
fn all_keys<'m, K: Ord, V>(now: &'m HashMap<K, V>, base: &'m HashMap<K, V>) -> BTreeSet<&'m K> {
    now.keys().chain(base.keys()).collect()
}

fn class_deltas(now: &Snapshot, base: &Snapshot) -> Vec<Delta> {
    let mut classes: Vec<Delta> = all_keys(&now.classes, &base.classes)
        .into_iter()
        .filter_map(|name| {
            let before = base.classes.get(name).copied().unwrap_or_default();
            let after = now.classes.get(name).copied().unwrap_or_default();
            (before != after).then(|| Delta {
                name: name.clone(),
                instances: Change { before: before.instances as i64, after: after.instances as i64 },
                shallow: Change { before: before.shallow as i64, after: after.shallow as i64 },
                retained: Change { before: before.retained as i64, after: after.retained as i64 },
            })
        })
        .collect();
    let change = |delta: &Delta| {
        (
            delta.retained.before.abs_diff(delta.retained.after),
            delta.shallow.before.abs_diff(delta.shallow.after),
        )
    };
    classes.sort_by(|a, b| change(b).cmp(&change(a)).then(a.name.cmp(&b.name)));
    classes
}

/// Threads or loaders whose bytes changed, biggest change first.
fn named_changes(now: &HashMap<String, u64>, base: &HashMap<String, u64>) -> Vec<NamedChange> {
    let mut rows: Vec<NamedChange> = all_keys(now, base)
        .into_iter()
        .map(|name| NamedChange {
            name: name.clone(),
            before: base.get(name).copied().unwrap_or(0),
            after: now.get(name).copied().unwrap_or(0),
        })
        .filter(|row| row.before != row.after)
        .collect();
    rows.sort_by(|a, b| {
        b.before.abs_diff(b.after).cmp(&a.before.abs_diff(a.after)).then(a.name.cmp(&b.name))
    });
    rows
}

fn string_changes(now: &Snapshot, base: &Snapshot, duplicates: Option<&Duplicates>) -> Vec<StringChange> {
    let string_objects: HashMap<u64, u32> = duplicates
        .map(|duplicates| duplicates.groups.iter().map(|group| (group.hash, group.string)).collect())
        .unwrap_or_default();
    let mut strings: Vec<StringChange> = all_keys(&now.strings, &base.strings)
        .into_iter()
        .map(|&hash| {
            let (copies_before, wasted_before) = base.strings.get(&hash).copied().unwrap_or_default();
            let (copies_after, wasted_after) = now.strings.get(&hash).copied().unwrap_or_default();
            let string = string_objects.get(&hash).copied().unwrap_or(crate::dump::NONE);
            StringChange { string, hash, copies_before, copies_after, wasted_before, wasted_after }
        })
        .filter(|row| row.wasted_before != row.wasted_after)
        .collect();
    strings.sort_by(|a, b| {
        b.wasted_before
            .abs_diff(b.wasted_after)
            .cmp(&a.wasted_before.abs_diff(a.wasted_after))
            .then(a.hash.cmp(&b.hash))
    });
    strings
}
