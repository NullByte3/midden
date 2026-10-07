//! Pass two: the reference graph in CSR form, a label per edge (field name or array index). Edge slots
//! are atomics while building, so several threads can fill a plain file's chunks.

use std::io;
use std::sync::atomic::{AtomicU32, Ordering::Relaxed};

use super::dump::{Dump, Kind, RefKind, Slot};
use super::hprof::{self, Body, IO_BUFFER_SIZE, Sink, Ty, be_uint};
use super::index::References;
use super::parallel;
use super::source::Source;
use super::store::{Blocked, Column};
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

/// Targets and weak edges, as the cache stores them.
pub type Parts<'a> = (&'a [u32], &'a [(u32, u32)]);

/// Where each object's edges start, then the total: two bytes each above a base every block of objects.
struct Offsets(Blocked);

impl Offsets {
    // Takes the plain offsets so they are freed once packed.
    #[allow(clippy::needless_pass_by_value)]
    fn new(offsets: Column<u64>) -> Offsets {
        Offsets(Blocked::new(offsets.len(), |i| offsets[i]))
    }

    fn get(&self, i: usize) -> u64 {
        self.0.get(i)
    }

    fn len(&self) -> usize {
        self.0.len()
    }
}

/// A label code with this bit is an array element; the rest is the nulls since the previous element.
const ELEMENT: u16 = 1 << 15;
/// The low bits of a code whose label is kept whole in the escapes.
const ESCAPED: u16 = ELEMENT - 1;

/// Edge labels in two bytes each: a code for the field (the most used fields get one), or for an array
/// element the nulls since the previous one. A field without a code and a gap past fifteen bits leave
/// the low bits all ones, and the label is kept whole in `escapes`, by edge.
struct Labels {
    codes: Column<u16>,
    fields: Vec<u32>,
    escapes: Vec<(u64, u32)>,
    /// Per field name, then the loader: its code, or all ones.
    code_of: Vec<u16>,
    names: usize,
}

impl Labels {
    /// Code the labels of the edges `offsets` lays out, each object's from its offset to the next.
    // Takes the plain labels so they are freed once coded.
    #[allow(clippy::needless_pass_by_value)]
    fn new(offsets: &[u64], labels: Column<u32>, dump: &Dump) -> Labels {
        let names = dump.names.len();
        let slot = |label: u32| match label {
            LOADER => names,
            label if (label as usize) < names => label as usize,
            _ => names + 1,
        };
        // The fields the classes name: when they fit the codes, each gets one; else the most used do.
        let mut listed = vec![false; names + 2];
        listed[names] = true;
        for class in &dump.classes {
            for slot in &class.slots {
                listed[(slot.label as usize).min(names + 1)] = true;
            }
            for field in class.statics.iter().filter(|field| field.ty == Ty::Object) {
                listed[(field.name as usize).min(names + 1)] = true;
            }
        }
        listed[names + 1] = false;
        let label_at = |at: usize| if at == names { LOADER } else { at as u32 };
        let mut fields: Vec<u32> = (0..=names).filter(|&at| listed[at]).map(label_at).collect();
        if fields.len() > usize::from(ESCAPED) {
            let counts = parallel::ranges(labels.len(), |lo, hi| {
                let mut counts = vec![0u64; names + 2];
                for &label in labels[lo..hi].iter().filter(|&&label| label & ARRAY_ELEMENT == 0) {
                    counts[slot(label)] += 1;
                }
                counts
            });
            let mut used: Vec<(u64, u32)> = (0..=names)
                .map(|at| (counts.iter().map(|part| part[at]).sum::<u64>(), label_at(at)))
                .filter(|&(count, _)| count > 0)
                .collect();
            used.sort_unstable_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
            used.truncate(usize::from(ESCAPED));
            fields = used.iter().map(|&(_, label)| label).collect();
        }
        let mut code_of = vec![ESCAPED; names + 2];
        for (code, &label) in fields.iter().enumerate() {
            code_of[slot(label)] = code as u16;
        }
        // Workers take ranges of objects, each coding its own run of edges.
        let objects = offsets.len() - 1;
        let per = objects.div_ceil(parallel::threads()).max(1);
        let mut codes = Column::<u16>::zeroed(labels.len());
        let mut rest = &mut codes[..];
        let mut tasks = Vec::new();
        for lo in (0..objects).step_by(per) {
            let hi = (lo + per).min(objects);
            let (start, end) = (offsets[lo], offsets[hi]);
            let (part, tail) = std::mem::take(&mut rest).split_at_mut((end - start) as usize);
            rest = tail;
            let (labels, code_of) = (&labels, &code_of);
            tasks.push(move || {
                let mut escapes = Vec::new();
                for object in lo..hi {
                    let mut previous: Option<u32> = None;
                    for edge in offsets[object]..offsets[object + 1] {
                        let label = labels[edge as usize];
                        let code = if label & ARRAY_ELEMENT == 0 {
                            code_of[slot(label)]
                        } else {
                            let index = label & !ARRAY_ELEMENT;
                            let gap = index - previous.map_or(0, |previous| previous + 1);
                            previous = Some(index);
                            ELEMENT | u16::try_from(gap).unwrap_or(ESCAPED).min(ESCAPED)
                        };
                        if code & ESCAPED == ESCAPED {
                            escapes.push((edge, label));
                        }
                        part[(edge - start) as usize] = code;
                    }
                }
                escapes
            });
        }
        let escapes = parallel::run_all(tasks).concat();
        Labels { codes, fields, escapes, code_of, names }
    }

    /// The code of a field label, when it has one.
    fn code(&self, label: u32) -> Option<u16> {
        let at = match label {
            LOADER => self.names,
            label => (label as usize).min(self.names + 1),
        };
        self.code_of.get(at).copied().filter(|&code| code != ESCAPED)
    }
}

/// One object's labels, decoded in order.
#[derive(Clone, Copy)]
struct EdgeLabels<'a> {
    codes: &'a [u16],
    /// The first edge's place among all edges.
    start: u64,
    fields: &'a [u32],
    escapes: &'a [(u64, u32)],
}

impl<'a> EdgeLabels<'a> {
    /// Edge `k`'s field label, or just `ARRAY_ELEMENT` for an element.
    fn coarse(self, k: usize) -> u32 {
        let code = self.codes[k];
        if code & ELEMENT != 0 {
            ARRAY_ELEMENT
        } else if code == ESCAPED {
            self.escape(self.start + k as u64)
        } else {
            self.fields[usize::from(code)]
        }
    }

    /// Edge `k`'s label; an element's index adds up the gaps before it.
    fn exact(self, k: usize) -> u32 {
        match self.codes[k] & ELEMENT {
            0 => self.coarse(k),
            _ => self.iter().nth(k).expect("k is an edge"),
        }
    }

    fn escape(self, edge: u64) -> u32 {
        self.escapes[self.escapes.partition_point(|&(at, _)| at < edge)].1
    }

    fn iter(self) -> impl Iterator<Item = u32> + 'a {
        let mut previous: Option<u32> = None;
        (self.start..).zip(self.codes).map(move |(edge, &code)| {
            let label = if code & ESCAPED == ESCAPED {
                self.escape(edge)
            } else if code & ELEMENT != 0 {
                ARRAY_ELEMENT | (previous.map_or(0, |previous| previous + 1) + u32::from(code & ESCAPED))
            } else {
                self.fields[usize::from(code)]
            };
            if label & ARRAY_ELEMENT != 0 {
                previous = Some(label & !ARRAY_ELEMENT);
            }
            label
        })
    }
}

/// The object graph: out-edges per object, and the GC roots.
pub struct Graph {
    /// The virtual root every GC root hangs off; equals the object count.
    pub root: u32,
    offsets: Offsets,
    targets: Column<u32>,
    labels: Labels,
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
    labels: EdgeLabels<'a>,
}

impl<'a> Edges<'a> {
    pub fn len(&self) -> usize {
        self.targets.len()
    }

    pub fn targets(&self) -> impl Iterator<Item = u32> + use<'a> {
        self.targets.iter().copied()
    }

    pub fn labels(&self) -> impl Iterator<Item = u32> + use<'a> {
        self.labels.iter()
    }

    /// `(target, label)` pairs.
    pub fn iter(&self) -> impl Iterator<Item = (u32, u32)> + use<'a> {
        self.targets().zip(self.labels())
    }

    /// Edge `k`'s field label, or just `ARRAY_ELEMENT` for an element: no gaps to add up.
    pub fn coarse(&self, k: usize) -> u32 {
        self.labels.coarse(k)
    }

    /// `(target, label)` pairs with every element's label just `ARRAY_ELEMENT`.
    pub fn iter_coarse(&self) -> impl Iterator<Item = (u32, u32)> + use<'a> {
        let labels = self.labels;
        self.targets().enumerate().map(move |(k, target)| (target, labels.coarse(k)))
    }

    pub fn label_of(&self, target: u32) -> Option<u32> {
        let k = self.targets.iter().position(|&to| to == target)?;
        Some(self.labels.exact(k))
    }
}

impl Graph {
    /// Where `object`'s edges sit in [`Graph::all_targets`].
    pub fn span(&self, object: u32) -> std::ops::Range<usize> {
        self.offsets.get(object as usize) as usize..self.offsets.get(object as usize + 1) as usize
    }

    /// Every edge's target, object by object.
    pub fn all_targets(&self) -> &[u32] {
        &self.targets
    }

    pub fn edges(&self, object: u32) -> Edges<'_> {
        let (lo, hi) =
            (self.offsets.get(object as usize) as usize, self.offsets.get(object as usize + 1) as usize);
        let labels = &self.labels;
        let (codes, start) = (&labels.codes[lo..hi], lo as u64);
        Edges {
            targets: &self.targets[lo..hi],
            labels: EdgeLabels { codes, start, fields: &labels.fields, escapes: &labels.escapes },
        }
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
        let edges = self.edges(object);
        match self.labels.code(label) {
            Some(code) => edges.labels.codes.iter().position(|&at| at == code).map(|k| edges.targets[k]),
            None => {
                edges.iter_coarse().find(|&(_, edge_label)| edge_label == label).map(|(target, _)| target)
            }
        }
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
        dump: &Dump,
        weak: Vec<(u32, u32)>,
        dangling: u64,
        roots: Vec<u32>,
    ) -> Graph {
        let labels = Labels::new(&offsets, labels, dump);
        let offsets = Offsets::new(offsets);
        Graph { root: offsets.len() as u32 - 1, labels, offsets, targets, weak, dangling, roots }
    }

    /// The parts the cache writes.
    pub fn parts(&self) -> Parts<'_> {
        (&self.targets, &self.weak)
    }

    /// Every edge's label, object by object.
    pub fn all_labels(&self) -> impl Iterator<Item = u32> + '_ {
        (0..self.root).flat_map(|object| self.edges(object).labels())
    }

    /// Where each object's edges start, then the total, as the cache stores them.
    pub fn offsets(&self) -> impl ExactSizeIterator<Item = u64> + '_ {
        (0..self.offsets.len()).map(|i| self.offsets.get(i))
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
    // offsets[i + 1] holds object i's out-degree until the prefix sum below. Read from the dump, every slot
    // gets a place and the holes are squeezed out after; copied ids are counted first, so only dangling
    // ones leave holes.
    let mut offsets = Column::<u64>::zeroed(object_count + 1);
    parallel::chunks(&mut offsets[1..], |start, degrees| {
        for ((degree, object), idx) in
            degrees.iter_mut().zip(dump.objects.range(start, dump.objects.len())).zip(start..)
        {
            *degree = match (object.kind, &references) {
                (Kind::Instance, None) => dump.classes[object.class as usize].slots.len() as u64,
                (Kind::ObjectArray, None) => u64::from(object.len),
                (Kind::Instance, Some(references)) => {
                    let class = &dump.classes[object.class as usize];
                    let kept_referent = reference_policy.keeps(class.ref_kind.unwrap_or(RefKind::Weak));
                    let start = references.starts[idx] as usize;
                    let copied = &references.copied.ids[start..start + class.slots.len()];
                    let edge = |(slot, &id): (&Slot, &u32)| id != 0 && (kept_referent || !slot.weak);
                    class.slots.iter().zip(copied).filter(|&pair| edge(pair)).count() as u64
                }
                (Kind::ObjectArray, Some(references)) => {
                    let start = references.starts[idx] as usize;
                    let copied = &references.copied.ids[start..start + object.len as usize];
                    copied.iter().filter(|&&id| id != 0).count() as u64
                }
                (Kind::PrimitiveArray | Kind::Class, _) => 0,
            };
        }
    });
    // Class objects: one edge per reference-typed static, plus the loader.
    let exact = references.is_some();
    let static_edge = |id: u64| !exact || (id != 0 && dump.lookup(id).is_some());
    let mut class_slots: Vec<(u32, u32)> = Vec::new();
    for (class_idx, class) in dump.classes.iter().enumerate() {
        if let Some(idx) = class.dumped.then(|| dump.lookup(class.id)).flatten() {
            let statics = class.statics.iter().filter(|field| field.ty == Ty::Object);
            let edges = statics.filter(|field| static_edge(field.value.bits())).count() as u64;
            class_slots.push((idx, class_idx as u32));
            offsets[idx as usize + 1] += edges + u64::from(static_edge(class.loader));
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
            slot += usize::from(static_edge(field.value.bits()));
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
    // Read from the dump every null is a hole; counted from copied ids only dangling ones are.
    let mut holes = !exact;
    for (part_weak, part_dangling) in found {
        dangling += part_dangling;
        holes |= part_dangling > 0;
        weak.extend(part_weak);
    }
    weak.sort_unstable();
    let mut roots: Vec<u32> = dump.roots.iter().map(|&(object, _)| object).collect();
    roots.sort_unstable();
    roots.dedup();
    if !holes {
        let (mut targets, labels) = (target_column, label_column);
        parallel::chunks(&mut targets, |_, part| part.iter_mut().for_each(|target| *target -= 1));
        let labels = Labels::new(&offsets, labels, dump);
        let offsets = Offsets::new(offsets);
        return Ok(Graph { root: object_count as u32, offsets, targets, labels, weak, dangling, roots });
    }

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
    drop(offsets);
    let labels = Labels::new(&packed, labels, dump);
    let offsets = Offsets::new(packed);
    Ok(Graph { root: object_count as u32, offsets, targets, labels, weak, dangling, roots })
}

/// Turn the copied ids into edges, a range of objects per worker, packed as counted. The same rules as
/// [`Filler`]: a referent the policy does not keep goes to the weak list, an id the dump lacks is dangling.
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
                    let mut place = base;
                    for (k, slot) in class.slots.iter().enumerate() {
                        let target = references.copied.id(start + k);
                        if target == 0 {
                            continue;
                        }
                        let kept = kept_referent || !slot.weak;
                        match dump.lookup(target) {
                            Some(target_idx) if !kept => weak.push((idx, target_idx)),
                            Some(target_idx) => set_edge(targets, labels, place, target_idx, slot.label),
                            None => dangling += 1,
                        }
                        place += usize::from(kept);
                    }
                }
                Kind::ObjectArray => {
                    let mut place = base;
                    for element in 0..object.len as usize {
                        let target = references.copied.id(start + element);
                        if target == 0 {
                            continue;
                        }
                        match dump.lookup(target) {
                            Some(target_idx) => {
                                let label = ARRAY_ELEMENT | element as u32;
                                set_edge(targets, labels, place, target_idx, label);
                            }
                            None => dangling += 1,
                        }
                        place += 1;
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
        let objects = &self.dump.objects;
        let near = (self.next..objects.len().min(self.next + 2)).find(|&next| objects.id(next) == id);
        let idx = near.map(|next| next as u32).or_else(|| self.dump.lookup(id));
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
