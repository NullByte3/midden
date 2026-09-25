//! Soft, weak, phantom and final references: counts, referents, and what lives only through them.
//! Finalizers and Cleaners, the phantom-side leak vectors, get their own rows.

use super::{Heap, Objects};
use crate::dom::weak_only_from;
use crate::dump::{FastMap, NONE, RefKind};
use crate::parallel;

/// One reference kind.
pub struct ReferenceRow {
    pub kind: RefKind,
    /// Live Reference objects of this kind.
    pub references: u64,
    /// Of them, with a non-null referent.
    pub referents: u64,
    /// Objects and bytes reachable only through them.
    pub only: Objects,
    /// Referent classes, most referenced first.
    pub top: Vec<(u32, u64)>,
}

/// Objects with a `finalize()` still to run.
pub struct Finalizers {
    pub registered: u64,
    /// Of them, already queued for the finalizer thread.
    pub enqueued: u64,
    pub classes: Vec<(u32, u64)>,
}

impl Heap<'_> {
    fn ref_kind(&self, object: u32) -> Option<RefKind> {
        self.dump.classes[self.class(object) as usize].ref_kind
    }

    /// The reference kinds present, soft first.
    pub fn references(&self) -> Vec<ReferenceRow> {
        let parts = parallel::ranges(self.dump.objects.len(), |lo, hi| {
            let mut counts = [(0u64, 0u64); 4];
            let mut top: Vec<FastMap<u32, u64>> = (0..4).map(|_| FastMap::default()).collect();
            for object in lo as u32..hi as u32 {
                let Some(kind) = self.ref_kind(object).filter(|_| self.reachable(object)) else { continue };
                let i = kind as usize;
                counts[i].0 += 1;
                if let Some(referent) = self.referent_of(object) {
                    counts[i].1 += 1;
                    *top[i].entry(self.class(referent)).or_default() += 1;
                }
            }
            (counts, top)
        });
        RefKind::ALL
            .iter()
            .map(|&kind| {
                let i = kind as usize;
                let (references, referents) =
                    parts.iter().fold((0, 0), |sum, part| (sum.0 + part.0[i].0, sum.1 + part.0[i].1));
                let mut by_class: FastMap<u32, u64> = FastMap::default();
                for (class, count) in parts.iter().flat_map(|part| &part.1[i]) {
                    *by_class.entry(*class).or_default() += count;
                }
                let mut top: Vec<(u32, u64)> = by_class.into_iter().collect();
                top.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
                top.truncate(5);
                let (count, bytes) = weak_only_from(self.graph, self.dump, &self.reachability, |object| {
                    self.ref_kind(object) == Some(kind)
                });
                ReferenceRow { kind, references, referents, only: Objects { count, bytes }, top }
            })
            .filter(|row| row.references > 0)
            .collect()
    }

    /// Finalizable objects, when the dump has a Finalizer class.
    pub fn finalizers(&self) -> Option<Finalizers> {
        let dump = self.dump;
        let finalizer = dump.class_named("java.lang.ref.Finalizer")?;
        let enqueued_marker = dump
            .class_named("java.lang.ref.ReferenceQueue")
            .and_then(|queue_class| dump.static_value(queue_class, "ENQUEUED"))
            .and_then(|value| if let crate::hprof::Value::Ref(id) = value { dump.lookup(id) } else { None })
            .unwrap_or(NONE);
        let queue = self.labels.get("queue");
        let members = self.members(finalizer);
        let mut classes: FastMap<u32, u64> = FastMap::default();
        let mut enqueued = 0u64;
        for &member in &members {
            if let Some(referent) = self.referent_of(member) {
                *classes.entry(self.class(referent)).or_default() += 1;
            }
            if queue.and_then(|label| self.graph.field(member, label)) == Some(enqueued_marker) {
                enqueued += 1;
            }
        }
        let mut classes: Vec<(u32, u64)> = classes.into_iter().collect();
        classes.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
        classes.truncate(8);
        Some(Finalizers { registered: members.len() as u64, enqueued, classes })
    }

    /// Live Cleaner registrations (JDK 9+ `PhantomCleanable`, JDK 8 sun.misc.Cleaner).
    pub fn cleaners(&self) -> u64 {
        let dump = self.dump;
        let bases: Vec<u32> = ["jdk.internal.ref.PhantomCleanable", "sun.misc.Cleaner"]
            .iter()
            .filter_map(|name| dump.class_named(name))
            .collect();
        if bases.is_empty() {
            return 0;
        }
        let is_cleaner: Vec<bool> = (0..dump.classes.len() as u32)
            .map(|class| bases.iter().any(|&base| dump.extends(class, base)))
            .collect();
        let parts = parallel::ranges(dump.objects.len(), |lo, hi| {
            (lo as u32..hi as u32)
                .filter(|&object| self.reachable(object) && is_cleaner[self.class(object) as usize])
                .count()
        });
        parts.iter().sum::<usize>() as u64
    }
}
