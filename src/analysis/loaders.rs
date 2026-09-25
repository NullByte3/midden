//! Class loaders: what their classes hold, which look stale after a reload, and how to name one.

use super::{ClassRow, Heap, dense_ids};
use crate::dump::{FastMap, NONE};
use crate::parallel;

/// One class loader and what its classes amount to.
#[derive(Default)]
pub struct LoaderRow {
    /// The loader object, or `NONE` for the bootstrap loader.
    pub object: u32,
    pub classes: u64,
    pub instances: u64,
    /// Reachable instances of its classes.
    pub live: u64,
    pub shallow: u64,
    /// Retained by the loader object itself.
    pub retained: u64,
    /// Retained by the instances of its classes.
    pub owns: u64,
    /// Class names it shares with other loaders.
    pub duplicates: u64,
}

/// A loader that looks left over from a reload.
pub struct Stale {
    pub object: u32,
    pub classes: u64,
    pub live: u64,
    /// Shared class names where another loader has the live instances.
    pub lost: u64,
    pub owns: u64,
}

impl Heap<'_> {
    /// Loader index per class, and the loader objects in that order.
    fn loader_groups(&self) -> (Vec<u32>, Vec<u32>) {
        let dump = self.dump;
        dense_ids(
            dump.classes.iter().map(|class| {
                if class.loader == 0 { NONE } else { dump.lookup(class.loader).unwrap_or(NONE) }
            }),
        )
    }

    /// Reachable instances per class.
    fn live_per_class(&self) -> Vec<u64> {
        let classes = self.dump.classes.len();
        let parts = parallel::ranges(self.dump.objects.len(), |lo, hi| {
            let mut counts = vec![0u64; classes];
            for object in lo as u32..hi as u32 {
                if self.reachable(object) {
                    counts[self.class(object) as usize] += 1;
                }
            }
            counts
        });
        (0..classes).map(|class| parts.iter().map(|part| part[class]).sum()).collect()
    }

    /// Every loader with classes, by what its classes retain.
    pub fn loaders(&self, histogram: &[ClassRow]) -> Vec<LoaderRow> {
        let dump = self.dump;
        let (loader_index, loaders) = self.loader_groups();
        let owns = self.grouped_retained(|object| loader_index[self.class(object) as usize], loaders.len());
        let live = self.live_per_class();
        let by_class: FastMap<u32, &ClassRow> = histogram.iter().map(|row| (row.class, row)).collect();
        let mut rows: Vec<LoaderRow> = loaders
            .iter()
            .zip(owns)
            .map(|(&loader, owns)| LoaderRow {
                object: loader,
                retained: if loader == NONE { 0 } else { self.retained(loader) },
                owns,
                ..LoaderRow::default()
            })
            .collect();
        let mut by_name: FastMap<&str, Vec<u32>> = FastMap::default();
        for (class_idx, class) in dump.classes.iter().enumerate() {
            let row = &mut rows[loader_index[class_idx] as usize];
            row.live += live[class_idx];
            if !class.dumped {
                continue;
            }
            row.classes += 1;
            if let Some(class_row) = by_class.get(&(class_idx as u32)) {
                row.instances += class_row.instances;
                row.shallow += class_row.shallow;
            }
            by_name.entry(&class.name).or_default().push(loader_index[class_idx]);
        }
        for indices in by_name.values().filter(|indices| indices.len() > 1) {
            for &index in indices {
                rows[index as usize].duplicates += 1;
            }
        }
        rows.retain(|row| row.classes > 0);
        rows.sort_by(|a, b| {
            b.owns.cmp(&a.owns).then(b.classes.cmp(&a.classes)).then(a.object.cmp(&b.object))
        });
        rows
    }

    /// Loaders that share class names with another loader and lost the live
    /// instances to it, or whose classes (two or more) have no live instances.
    pub fn stale_loaders(&self, rows: &[LoaderRow]) -> Vec<Stale> {
        let dump = self.dump;
        let (loader_index, loaders) = self.loader_groups();
        // Per class name: the loader whose class has the most live instances.
        let live_of = self.live_per_class();
        let mut by_name: FastMap<&str, Vec<u32>> = FastMap::default();
        for (class_idx, class) in dump.classes.iter().enumerate().filter(|(_, class)| class.dumped) {
            by_name.entry(&class.name).or_default().push(class_idx as u32);
        }
        let mut lost = vec![0u64; loaders.len()];
        for classes in by_name.values().filter(|classes| classes.len() > 1) {
            let winner = classes
                .iter()
                .max_by_key(|&&class| (live_of[class as usize], dump.classes[class as usize].id))
                .copied()
                .expect("non-empty");
            for &class in classes {
                if class != winner {
                    lost[loader_index[class as usize] as usize] += 1;
                }
            }
        }
        let mut out: Vec<Stale> = rows
            .iter()
            .filter(|row| row.object != NONE && self.reachable(row.object))
            .filter_map(|row| {
                let lost = lost[loaders.iter().position(|&loader| loader == row.object)?];
                // One dead class alone is usually a JDK trampoline loader, not a leak.
                let stale = (lost > 0 && lost * 2 >= row.duplicates) || (row.live == 0 && row.classes >= 2);
                stale.then_some(Stale {
                    object: row.object,
                    classes: row.classes,
                    live: row.live,
                    lost,
                    owns: row.owns,
                })
            })
            .collect();
        out.sort_by(|a, b| b.owns.cmp(&a.owns).then(b.classes.cmp(&a.classes)).then(a.object.cmp(&b.object)));
        out
    }

    /// A String naming the loader: its `name`, or its plugin's description name.
    pub fn loader_name(&self, loader: u32) -> Option<u32> {
        if loader == NONE {
            return None;
        }
        let string_field =
            |object: u32, name: &str| self.field(object, name).filter(|&name| self.is_string(name));
        string_field(loader, "name")
            .or_else(|| string_field(self.field(self.field(loader, "plugin")?, "description")?, "name"))
    }
}
