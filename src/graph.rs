//! Pass two: the reference graph in CSR form, a label per edge (field name or array index). Edge slots
//! are atomics while building, so several threads can fill a plain file's chunks.

use std::io;
use std::sync::atomic::{AtomicU32, Ordering::Relaxed};

use super::dump::{Dump, Kind, RefKind};
use super::hprof::{self, Body, IO_BUFFER_SIZE, Sink, Ty, be_uint};
use super::index::References;
use super::parallel;
use super::source::Source;
use super::store::Column;
use crate::error::{Error, Result};

/// Label flag: the edge is an array element, the low bits are its index.
pub const ARRAY_ELEMENT: u32 = 1 << 31;
/// Label of the edge from a class object to its class loader.
pub const LOADER: u32 = ARRAY_ELEMENT - 1;

/// Which referents count as strongly held.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub struct ReferencePolicy {
    pub soft: bool,
    pub weak: bool,
}

impl ReferencePolicy {
    pub fn keeps(self, kind: RefKind) -> bool {
        match kind {
            RefKind::Soft => self.soft,
            _ => self.weak,
        }
    }
}

/// Offsets, targets, labels and weak edges, as the cache stores them.
pub type Parts<'a> = (&'a [u64], &'a [u32], &'a [u32], &'a [(u32, u32)]);

/// The object graph: out-edges per object, and the GC roots.
pub struct Graph {
    /// The virtual root every GC root hangs off; equals the object count.
    pub root: u32,
    offsets: Column<u64>,
    targets: Column<u32>,
    labels: Column<u32>,
    /// Referent edges left out of the graph proper, sorted by source.
    weak: Vec<(u32, u32)>,
    /// References to ids the dump does not contain.
    pub dangling: u64,
    /// Distinct GC root objects, sorted.
    pub roots: Vec<u32>,
}

/// One object's out-edges, read in place.
#[derive(Clone, Copy)]
pub struct Edges<'a> {
    targets: &'a [u32],
    labels: &'a [u32],
}

impl<'a> Edges<'a> {
    pub fn len(&self) -> usize {
        self.targets.len()
    }

    pub fn targets(&self) -> impl Iterator<Item = u32> + 'a {
        self.targets.iter().copied()
    }

    pub fn labels(&self) -> impl Iterator<Item = u32> + 'a {
        self.labels.iter().copied()
    }

    /// `(target, label)` pairs.
    pub fn iter(&self) -> impl Iterator<Item = (u32, u32)> + 'a {
        self.targets().zip(self.labels())
    }

    pub fn label_of(&self, target: u32) -> Option<u32> {
        self.iter().find(|&(to, _)| to == target).map(|(_, label)| label)
    }
}

impl Graph {
    /// Where `object`'s edges sit in [`Graph::all_targets`].
    pub fn span(&self, object: u32) -> std::ops::Range<usize> {
        self.offsets[object as usize] as usize..self.offsets[object as usize + 1] as usize
    }

    /// Every edge's target, object by object.
    pub fn all_targets(&self) -> &[u32] {
        &self.targets
    }

    pub fn edges(&self, object: u32) -> Edges<'_> {
        let (lo, hi) = (self.offsets[object as usize] as usize, self.offsets[object as usize + 1] as usize);
        Edges { targets: &self.targets[lo..hi], labels: &self.labels[lo..hi] }
    }

    pub fn edge_count(&self) -> u64 {
        self.targets.len() as u64
    }

    pub fn weak_referents(&self, object: u32) -> impl Iterator<Item = u32> + '_ {
        let lo = self.weak.partition_point(|edge| edge.0 < object);
        self.weak[lo..].iter().take_while(move |edge| edge.0 == object).map(|edge| edge.1)
    }

    pub fn weak_edges(&self) -> &[(u32, u32)] {
        &self.weak
    }

    pub fn label_of(&self, from: u32, to: u32) -> Option<u32> {
        self.edges(from).label_of(to)
    }

    /// The target of `object`'s edge labelled `label`.
    pub fn field(&self, object: u32, label: u32) -> Option<u32> {
        self.edges(object).iter().find(|&(_, edge_label)| edge_label == label).map(|(target, _)| target)
    }

    /// The referent of a Reference object, weak or strong.
    pub fn referent(&self, object: u32, referent_label: u32) -> Option<u32> {
        self.field(object, referent_label).or_else(|| self.weak_referents(object).next())
    }

    /// Reassemble a graph from cached parts.
    pub fn from_parts(
        offsets: Column<u64>,
        targets: Column<u32>,
        labels: Column<u32>,
        weak: Vec<(u32, u32)>,
        dangling: u64,
        roots: Vec<u32>,
    ) -> Graph {
        Graph { root: offsets.len() as u32 - 1, offsets, targets, labels, weak, dangling, roots }
    }

    /// The parts the cache writes.
    pub fn parts(&self) -> Parts<'_> {
        (&self.offsets, &self.targets, &self.labels, &self.weak)
    }
}

/// Every reference in the dump as a graph over object indices: from the ids the index pass copied, or
/// read from the dump when it could not copy them.
pub fn build(
    dump: &Dump,
    source: &Source,
    reference_policy: ReferencePolicy,
    references: Option<References>,
) -> Result<Graph> {
    let object_count = dump.objects.len();
    // offsets[i + 1] holds object i's out-degree until the prefix sum below.
    let mut offsets = Column::<u64>::zeroed(object_count + 1);
    parallel::chunks(&mut offsets[1..], |start, degrees| {
        for (degree, object) in degrees.iter_mut().zip(dump.objects.range(start, dump.objects.len())) {
            *degree = match object.kind {
                Kind::Instance => dump.classes[object.class as usize].slots.len() as u64,
                Kind::ObjectArray => u64::from(object.len),
                Kind::PrimitiveArray | Kind::Class => 0,
            };
        }
    });
    // Class objects: one edge per reference-typed static, plus the loader.
    let mut class_slots: Vec<(u32, u32)> = Vec::new();
    for (class_idx, class) in dump.classes.iter().enumerate() {
        if let Some(idx) = class.dumped.then(|| dump.lookup(class.id)).flatten() {
            let ref_count = class.statics.iter().filter(|field| field.ty == Ty::Object).count() as u64 + 1;
            class_slots.push((idx, class_idx as u32));
            offsets[idx as usize + 1] += ref_count;
        }
    }
    for i in 0..object_count {
        offsets[i + 1] += offsets[i];
    }
    let total = usize::try_from(offsets[object_count])
        .map_err(|_| Error::Dump("too many references for this machine".into()))?;
    // A target is stored plus one, leaving zero for a hole.
    let (mut target_column, mut label_column) = (Column::<u32>::zeroed(total), Column::<u32>::zeroed(total));
    let (targets, labels) = (target_column.atomics(), label_column.atomics());
    let mut dangling = 0u64;
    for (idx, class_idx) in class_slots {
        let class = &dump.classes[class_idx as usize];
        let mut slot = offsets[idx as usize] as usize;
        for field in class.statics.iter().filter(|field| field.ty == Ty::Object) {
            if let hprof::Value::Ref(id) = field.value {
                match (id, dump.lookup(id)) {
                    (0, _) => {}
                    (_, Some(target)) => set_edge(targets, labels, slot, target, field.name),
                    (_, None) => dangling += 1,
                }
            }
            slot += 1;
        }
        if let Some(target) = (class.loader != 0).then(|| dump.lookup(class.loader)).flatten() {
            set_edge(targets, labels, slot, target, LOADER);
        }
    }

    let found = match &references {
        Some(references) => resolve(dump, references, &offsets, targets, labels, reference_policy),
        None => source
            .scan(&dump.chunks, "reading references", || Filler {
                dump,
                offsets: &offsets,
                targets,
                labels,
                weak: Vec::new(),
                reference_policy,
                dangling: 0,
                next: 0,
            })?
            .into_iter()
            .map(|filler| (filler.weak, filler.dangling))
            .collect(),
    };
    drop(references);
    let mut weak: Vec<(u32, u32)> = Vec::new();
    for (part_weak, part_dangling) in found {
        dangling += part_dangling;
        weak.extend(part_weak);
    }
    weak.sort_unstable();

    // Squeeze out null and dangling holes: each worker packs its range to the front, then ranges close up.
    let mut packed = Column::<u64>::zeroed(object_count + 1);
    let blocks = parallel::chunks(&mut packed[1..], |start, ends| {
        let (from, mut dst) = (offsets[start] as usize, offsets[start] as usize);
        for (i, end) in (start..).zip(ends.iter_mut()) {
            for src in offsets[i] as usize..offsets[i + 1] as usize {
                let target = targets[src].load(Relaxed);
                if target != 0 {
                    targets[dst].store(target - 1, Relaxed);
                    labels[dst].store(labels[src].load(Relaxed), Relaxed);
                    dst += 1;
                }
            }
            *end = (dst - from) as u64;
        }
        (start + ends.len(), from, dst)
    });
    let (mut targets, mut labels) = (target_column, label_column);
    let (mut dst, mut start) = (0usize, 0usize);
    for (end, from, upto) in blocks {
        // Skip blocks already in place; a self-copy still costs.
        if from != dst {
            targets.copy_within(from..upto, dst);
            labels.copy_within(from..upto, dst);
        }
        if dst > 0 {
            packed[start + 1..=end].iter_mut().for_each(|offset| *offset += dst as u64);
        }
        (dst, start) = (dst + upto - from, end);
    }
    targets.truncate(dst);
    labels.truncate(dst);
    targets.shrink_to_fit();
    labels.shrink_to_fit();

    let mut roots: Vec<u32> = dump.roots.iter().map(|&(object, _)| object).collect();
    roots.sort_unstable();
    roots.dedup();
    Ok(Graph { root: object_count as u32, offsets: packed, targets, labels, weak, dangling, roots })
}

/// Turn the copied ids into edges, a range of objects per worker. The same rules as [`Filler`]: a referent
/// the policy does not keep goes to the weak list, an id the dump lacks is counted as dangling.
fn resolve(
    dump: &Dump,
    references: &References,
    offsets: &[u64],
    targets: &[AtomicU32],
    labels: &[AtomicU32],
    reference_policy: ReferencePolicy,
) -> Vec<(Vec<(u32, u32)>, u64)> {
    parallel::ranges(dump.objects.len(), |lo, hi| {
        let (mut weak, mut dangling) = (Vec::new(), 0u64);
        for (idx, object) in (lo as u32..).zip(dump.objects.range(lo, hi)) {
            let (start, base) = (references.starts[idx as usize] as usize, offsets[idx as usize] as usize);
            match object.kind {
                Kind::Instance => {
                    let class = &dump.classes[object.class as usize];
                    let kept_referent = reference_policy.keeps(class.ref_kind.unwrap_or(RefKind::Weak));
                    let ids = &references.ids[start..start + class.slots.len()];
                    for (k, (slot, &target)) in class.slots.iter().zip(ids).enumerate() {
                        if target == 0 {
                            continue;
                        }
                        match dump.lookup(target) {
                            Some(target_idx) if slot.weak && !kept_referent => weak.push((idx, target_idx)),
                            Some(target_idx) => set_edge(targets, labels, base + k, target_idx, slot.label),
                            None => dangling += 1,
                        }
                    }
                }
                Kind::ObjectArray => {
                    let ids = &references.ids[start..start + object.len as usize];
                    for (element, &target) in ids.iter().enumerate().filter(|&(_, &target)| target != 0) {
                        match dump.lookup(target) {
                            Some(target_idx) => {
                                let label = ARRAY_ELEMENT | element as u32;
                                set_edge(targets, labels, base + element, target_idx, label);
                            }
                            None => dangling += 1,
                        }
                    }
                }
                Kind::PrimitiveArray | Kind::Class => {}
            }
        }
        (weak, dangling)
    })
}

fn set_edge(targets: &[AtomicU32], labels: &[AtomicU32], slot: usize, target: u32, label: u32) {
    targets[slot].store(target + 1, Relaxed);
    labels[slot].store(label, Relaxed);
}

/// The reference-pass sink for one chunk: writes each object's slots, which
/// no other chunk touches, and keeps the weak edges it met.
struct Filler<'a> {
    dump: &'a Dump,
    offsets: &'a [u64],
    targets: &'a [AtomicU32],
    labels: &'a [AtomicU32],
    weak: Vec<(u32, u32)>,
    reference_policy: ReferencePolicy,
    dangling: u64,
    /// One past the last record's index. Records come in address order, so
    /// the next one's is usually here, or one on past a primitive array.
    next: usize,
}

impl Filler<'_> {
    fn index_of(&mut self, id: u64) -> Option<u32> {
        let near = self
            .dump
            .objects
            .ids()
            .get(self.next..)
            .and_then(|rest| rest.iter().take(2).position(|&next| next == id));
        let idx = near.map(|ahead| (self.next + ahead) as u32).or_else(|| self.dump.lookup(id));
        if let Some(i) = idx {
            self.next = i as usize + 1;
        }
        idx
    }
}

impl Sink for Filler<'_> {
    fn instance(&mut self, id: u64, _class_id: u64, body: Body) -> io::Result<()> {
        let Some(idx) = self.index_of(id) else { return Ok(()) };
        let class = self.dump.class_of(idx);
        if class.slots.is_empty() {
            return Ok(());
        }
        let id_size = self.dump.header.id_size as usize;
        let bytes = body.bytes()?;
        let base = self.offsets[idx as usize] as usize;
        for (k, slot) in class.slots.iter().enumerate() {
            let Some(raw) = bytes.get(slot.offset as usize..slot.offset as usize + id_size) else { break };
            let target = be_uint(raw);
            if target == 0 {
                continue;
            }
            let kept = !slot.weak || self.reference_policy.keeps(class.ref_kind.unwrap_or(RefKind::Weak));
            match self.dump.lookup(target) {
                Some(target_idx) if !kept => self.weak.push((idx, target_idx)),
                Some(target_idx) => set_edge(self.targets, self.labels, base + k, target_idx, slot.label),
                None => self.dangling += 1,
            }
        }
        Ok(())
    }

    fn object_array(&mut self, id: u64, _class_id: u64, len: u32, body: Body) -> io::Result<()> {
        let Some(idx) = self.index_of(id) else { return Ok(()) };
        if len == 0 {
            return Ok(());
        }
        let id_size = self.dump.header.id_size as usize;
        let base = self.offsets[idx as usize] as usize;
        let mut element_index = 0usize;
        body.chunks(IO_BUFFER_SIZE, |chunk| {
            for raw in chunk.chunks_exact(id_size) {
                let target = be_uint(raw);
                if target != 0 {
                    match self.dump.lookup(target) {
                        Some(target_idx) => set_edge(
                            self.targets,
                            self.labels,
                            base + element_index,
                            target_idx,
                            ARRAY_ELEMENT | element_index as u32,
                        ),
                        None => self.dangling += 1,
                    }
                }
                element_index += 1;
            }
            Ok(())
        })
    }
}
