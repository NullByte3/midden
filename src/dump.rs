//! The indexed dump: classes with their layouts, the object table, roots,
//! threads and stacks. Built by `index.rs`, read by everything after.

use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};

use super::hash::GOLDEN_RATIO;
use super::hprof::{Frame, Header, Piece, Root, Ty, Value};
use super::sizes::Sizing;
use super::store::{BLOCK, Bits, Blocked, Column};

pub const NONE: u32 = u32::MAX;

/// Superclass walks stop at this depth, so a cycle in a corrupt dump cannot loop.
pub const MAX_CLASS_DEPTH: usize = 64;

/// Multiply-fold hash for id-keyed maps: ids are addresses, `SipHash` is waste.
#[derive(Default, Clone, Copy)]
pub struct FastHash(u64);

/// Folds the well-mixed high bits of the product back into the low bits a table indexes by.
const FAST_HASH_FOLD: u32 = 29;

impl Hasher for FastHash {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        for &byte in bytes {
            self.write_u64(u64::from(byte));
        }
    }

    fn write_u64(&mut self, value: u64) {
        let hash = (self.0 ^ value).wrapping_mul(GOLDEN_RATIO);
        self.0 = hash ^ (hash >> FAST_HASH_FOLD);
    }

    fn write_u32(&mut self, value: u32) {
        self.write_u64(u64::from(value));
    }
}

pub type FastMap<K, V> = HashMap<K, V, BuildHasherDefault<FastHash>>;

/// Symbol texts back to back in one string, found by id: no allocation per symbol.
#[derive(Default)]
pub struct Symbols {
    text: String,
    spans: FastMap<u64, (usize, usize)>,
}

impl Symbols {
    pub fn insert(&mut self, id: u64, text: &[u8]) {
        let start = self.text.len();
        self.text.push_str(&String::from_utf8_lossy(text));
        self.spans.insert(id, (start, self.text.len()));
    }

    pub fn get(&self, id: u64) -> Option<&str> {
        self.spans.get(&id).map(|&(start, end)| &self.text[start..end])
    }

    pub fn len(&self) -> usize {
        self.spans.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = (u64, &str)> {
        self.spans.iter().map(|(&id, &(start, end))| (id, &self.text[start..end]))
    }

    /// Only the symbols `keep` names, in a fresh string.
    pub fn only(&self, keep: impl IntoIterator<Item = u64>) -> Symbols {
        let mut kept = Symbols::default();
        for id in keep {
            if let Some(text) = self.get(id) {
                kept.insert(id, text.as_bytes());
            }
        }
        kept
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum Kind {
    Instance,
    ObjectArray,
    PrimitiveArray,
    Class,
}

impl Kind {
    pub const ALL: [Kind; 4] = [Kind::Instance, Kind::ObjectArray, Kind::PrimitiveArray, Kind::Class];
}

/// One heap object. `len` is the elements of an array, zero for anything else.
#[derive(Clone, Copy, Debug)]
pub struct Object {
    pub id: u64,
    pub class: u32,
    pub len: u32,
    pub shallow: u32,
    pub kind: Kind,
}

/// Class index and kind in one word: the kind in the low bits.
pub const KIND_BITS: u32 = 2;
/// Classes the packed word leaves room for.
pub const MAX_CLASSES: usize = 1 << (u32::BITS - KIND_BITS);

/// Object ids, ascending: 8-byte steps above the first (the lowest), blocked, while every id has one in
/// four bytes; else whole.
pub enum TableIds {
    Steps(u64, Blocked),
    Wide(Column<u64>),
}

impl TableIds {
    pub fn steps(base: u64, steps: &[u32]) -> TableIds {
        TableIds::Steps(base, Blocked::new(steps.len(), |object| u64::from(steps[object])))
    }
}

/// How a shape word splits: the kind in the low bits, `class_bits` of class, then the length.
#[derive(Clone, Copy)]
pub struct Packing {
    class_bits: u32,
}

impl Packing {
    /// Room for classes `0..classes`.
    pub fn new(classes: usize) -> Packing {
        Packing { class_bits: usize::BITS - classes.saturating_sub(1).leading_zeros() }
    }

    fn len_shift(self) -> u32 {
        KIND_BITS + self.class_bits
    }

    /// All ones in the length bits: the length is in the long list.
    fn marker(self) -> u32 {
        u32::MAX.checked_shr(self.len_shift()).unwrap_or(0)
    }

    /// One object's word, and its length again when that goes in the long list.
    pub fn pack(self, class: u32, kind: Kind, len: u32) -> (u32, Option<u32>) {
        let marker = self.marker();
        let inline = len.min(marker).checked_shl(self.len_shift()).unwrap_or(0);
        (inline | class << KIND_BITS | kind as u32, (len >= marker && len != 0).then_some(len))
    }
}

/// Class, kind and length of each object in one word. The length is an array's elements or a class
/// object's shallow size; an instance's size comes from its class. A length too long for its bits is
/// kept in `long`, by object.
pub struct Shapes {
    words: Column<u32>,
    packing: Packing,
    long: Vec<(u32, u32)>,
}

impl Shapes {
    pub fn new(words: Column<u32>, packing: Packing, long: Vec<(u32, u32)>) -> Shapes {
        Shapes { words, packing, long }
    }

    pub fn words(&self) -> &[u32] {
        &self.words
    }

    pub fn long(&self) -> &[(u32, u32)] {
        &self.long
    }

    fn class(&self, word: u32) -> u32 {
        ((u64::from(word) >> KIND_BITS) & ((1 << self.packing.class_bits) - 1)) as u32
    }

    fn kind(word: u32) -> Kind {
        Kind::ALL[(word & ((1 << KIND_BITS) - 1)) as usize]
    }

    fn len(&self, object: usize, word: u32) -> u32 {
        let inline = (u64::from(word) >> self.packing.len_shift()) as u32;
        if inline != self.packing.marker() {
            return inline;
        }
        let found = self.long.binary_search_by_key(&(object as u32), |&(object, _)| object);
        found.map_or(0, |at| self.long[at].1)
    }
}

/// The object table, sorted by id, as columns: ids, and the shape words. Shallow sizes are worked out on
/// read from the class and length.
pub struct ObjectTable {
    ids: TableIds,
    lookup: Buckets,
    shapes: Shapes,
    /// Per class: an instance's shallow size, and an array element's footprint.
    instance_shallow: Vec<u32>,
    element_size: Vec<u32>,
    sizing: Sizing,
}

impl ObjectTable {
    /// An empty table for these classes and sizes.
    fn new(classes: &[Class], sizing: Sizing) -> ObjectTable {
        ObjectTable {
            ids: TableIds::Wide(Column::with_capacity(0)),
            lookup: Buckets::empty(),
            shapes: Shapes::new(Column::with_capacity(0), Packing::new(classes.len()), Vec::new()),
            instance_shallow: classes.iter().map(|class| class.shallow).collect(),
            element_size: classes
                .iter()
                .map(|class| class.element_type.map_or(1, |ty| sizing.field_size(ty)))
                .collect(),
            sizing,
        }
    }

    /// A table from merged columns.
    pub fn from_steps(classes: &[Class], sizing: Sizing, ids: TableIds, shapes: Shapes) -> ObjectTable {
        let mut table = ObjectTable::new(classes, sizing);
        (table.ids, table.shapes) = (ids, shapes);
        table.index();
        table
    }

    /// A table from cached columns.
    pub fn from_columns(classes: &[Class], sizing: Sizing, ids: &[u64], shapes: Shapes) -> ObjectTable {
        let mut table = ObjectTable::new(classes, sizing);
        let base = ids.first().copied().unwrap_or(0);
        let steps: Option<Column<u32>> = ids.iter().map(|&id| step_of(base, id)).collect();
        table.ids = match steps {
            Some(steps) => TableIds::steps(base, &steps),
            None => TableIds::Wide(ids.iter().copied().collect()),
        };
        table.shapes = shapes;
        table.index();
        table
    }

    /// The shape words, as the cache stores them.
    pub fn shapes(&self) -> &Shapes {
        &self.shapes
    }

    /// Bucket the ids for lookups, once they are all in.
    fn index(&mut self) {
        self.lookup = Buckets::build(self);
    }

    pub fn len(&self) -> usize {
        self.shapes.words.len()
    }

    pub fn is_empty(&self) -> bool {
        self.shapes.words.is_empty()
    }

    pub fn id(&self, object: usize) -> u64 {
        match &self.ids {
            TableIds::Steps(base, steps) => base + (steps.get(object) << 3),
            TableIds::Wide(wide) => wide[object],
        }
    }

    /// The index of the object with this id.
    pub fn lookup(&self, id: u64) -> Option<u32> {
        let (lo, hi) = self.lookup.range(id)?;
        let at = match &self.ids {
            TableIds::Steps(base, steps) => {
                let step = u64::from(step_of(*base, id)?);
                // Within one block the two-byte parts ascend too, the long ones last.
                if hi > lo && (hi - 1) / BLOCK == lo / BLOCK {
                    let wanted =
                        step.checked_sub(steps.base(lo)).and_then(|wanted| u16::try_from(wanted).ok());
                    if let Some(wanted) = wanted.filter(|&wanted| wanted != u16::MAX) {
                        return steps.above(lo, hi).binary_search(&wanted).ok().map(|at| (lo + at) as u32);
                    }
                }
                let (mut at, mut end) = (lo, hi);
                while at < end {
                    let mid = at + (end - at) / 2;
                    if steps.get(mid) < step {
                        at = mid + 1;
                    } else {
                        end = mid;
                    }
                }
                (at < hi && steps.get(at) == step).then_some(at)
            }
            TableIds::Wide(wide) => wide[lo..hi].binary_search(&id).ok().map(|i| lo + i),
        };
        at.map(|at| at as u32)
    }

    pub fn class(&self, object: usize) -> u32 {
        self.shapes.class(self.shapes.words[object])
    }

    pub fn kind(&self, object: usize) -> Kind {
        Shapes::kind(self.shapes.words[object])
    }

    pub fn shallow(&self, object: usize) -> u32 {
        self.shallow_of(object, self.shapes.words[object])
    }

    fn shallow_of(&self, object: usize, word: u32) -> u32 {
        let class = self.shapes.class(word) as usize;
        match Shapes::kind(word) {
            Kind::Instance => self.instance_shallow[class],
            Kind::ObjectArray => {
                self.sizing.array_size(u64::from(self.shapes.len(object, word)), self.sizing.ref_size)
            }
            Kind::PrimitiveArray => {
                self.sizing.array_size(u64::from(self.shapes.len(object, word)), self.element_size[class])
            }
            Kind::Class => self.shapes.len(object, word),
        }
    }

    /// Everything about one object.
    pub fn get(&self, object: usize) -> Object {
        let word = self.shapes.words[object];
        let kind = Shapes::kind(word);
        let len = match kind {
            Kind::ObjectArray | Kind::PrimitiveArray => self.shapes.len(object, word),
            Kind::Instance | Kind::Class => 0,
        };
        Object {
            id: self.id(object),
            class: self.shapes.class(word),
            len,
            shallow: self.shallow_of(object, word),
            kind,
        }
    }

    /// Objects `start..end`, in order.
    pub fn range(&self, start: usize, end: usize) -> impl Iterator<Item = Object> + '_ {
        (start..end).map(|object| self.get(object))
    }

    /// Shallow sizes of objects `start..end`, in order.
    pub fn shallow_range(&self, start: usize, end: usize) -> impl Iterator<Item = u32> + '_ {
        (start..).zip(&self.shapes.words[start..end]).map(|(object, &word)| self.shallow_of(object, word))
    }
}

/// Both hashes of every primitive array, in table order, as the index pass took them: the String hash
/// (zero when not taken) and the grouping hash. A bit per object marks the arrays and a count per 64
/// objects finds an array's pair.
pub struct ArrayHashes {
    arrays: Bits,
    before: Column<u32>,
    values: Column<[u64; 2]>,
}

impl ArrayHashes {
    /// One pair per primitive array in `objects`, in order; `None` when the counts disagree.
    pub fn new(objects: &ObjectTable, values: Column<[u64; 2]>) -> Option<ArrayHashes> {
        let mut arrays =
            super::parallel::bits(objects.len(), |object| objects.kind(object) == Kind::PrimitiveArray);
        let mut before = Column::with_capacity(arrays.words().len());
        let mut count = 0;
        for &word in arrays.words().iter() {
            before.push(count);
            count += word.count_ones();
        }
        (count as usize == values.len()).then_some(ArrayHashes { arrays, before, values })
    }

    pub fn get(&self, object: u32) -> Option<[u64; 2]> {
        let (word, bit) = (object as usize / 64, object % 64);
        let bits = self.arrays.word(word);
        (bits >> bit & 1 != 0)
            .then(|| self.values[(self.before[word] + (bits & ((1 << bit) - 1)).count_ones()) as usize])
    }

    pub fn values(&self) -> &[[u64; 2]] {
        &self.values
    }
}

pub struct Field {
    pub name: u32,
    pub ty: Ty,
}

pub struct Static {
    pub name: u32,
    pub ty: Ty,
    pub value: Value,
}

/// A reference-typed field in an instance's data, by byte offset.
#[derive(Clone, Copy, Debug)]
pub struct Slot {
    pub offset: u32,
    /// Index into [`Dump::names`].
    pub label: u32,
    /// The `referent` of a `java.lang.ref.Reference`: not an owning edge.
    pub weak: bool,
}

/// The `java.lang.ref.Reference` family a class belongs to.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum RefKind {
    Soft,
    Weak,
    Phantom,
    Final,
}

impl RefKind {
    pub const ALL: [RefKind; 4] = [RefKind::Soft, RefKind::Weak, RefKind::Phantom, RefKind::Final];

    pub fn label(self) -> &'static str {
        match self {
            RefKind::Soft => "soft",
            RefKind::Weak => "weak",
            RefKind::Phantom => "phantom",
            RefKind::Final => "final",
        }
    }

    pub fn class_name(self) -> &'static str {
        match self {
            RefKind::Soft => "java.lang.ref.SoftReference",
            RefKind::Weak => "java.lang.ref.WeakReference",
            RefKind::Phantom => "java.lang.ref.PhantomReference",
            RefKind::Final => "java.lang.ref.FinalReference",
        }
    }
}

#[derive(Default)]
pub struct Class {
    pub id: u64,
    pub name: String,
    pub superclass: u32,
    pub loader: u64,
    /// Declared instance fields in layout order: own fields first, then up the chain.
    pub fields: Vec<Field>,
    pub statics: Vec<Static>,
    /// Bytes of field data an instance carries, whole chain.
    pub data_len: u32,
    /// Shallow size of one instance; arrays are sized per object.
    pub shallow: u32,
    /// Field bytes under the size convention, whole chain.
    pub footprint: u32,
    pub slots: Vec<Slot>,
    /// Element type of an array class.
    pub element_type: Option<Ty>,
    /// Had a class dump record, so its layout is known.
    pub dumped: bool,
    pub instances: u64,
    /// Set on `java.lang.ref.Reference` subclasses.
    pub ref_kind: Option<RefKind>,
}

impl Class {
    /// A class with nothing known yet beyond its name and id.
    pub fn placeholder(name: String, id: u64) -> Class {
        Class { id, name, superclass: NONE, ..Class::default() }
    }
}

/// A stack trace, as frame ids.
pub struct Trace {
    pub frames: Vec<u64>,
}

/// A thread root with its stack.
pub struct Thread {
    pub object: u32,
    pub serial: u32,
    pub trace_serial: u32,
}

/// Everything pass one learned about the file.
pub struct Dump {
    pub path: String,
    pub file_size: u64,
    pub gzip: bool,
    /// The archive member the dump was read from, when it was one.
    pub member: Option<String>,
    pub header: Header,
    pub truncated: bool,
    pub sizing: Sizing,
    /// Heap sub-record byte ranges, for parallel passes over a plain file.
    pub chunks: Vec<(u64, u64)>,
    /// The same records in smaller pieces, with the ids in each.
    pub pieces: Vec<Piece>,
    /// Interned field names, referenced by `Slot::label` and `Field::name`.
    pub names: Vec<String>,
    pub symbols: Symbols,
    pub classes: Vec<Class>,
    pub objects: ObjectTable,
    /// Primitive array hashes and boxed value tallies from the index pass; `None` when it did not take them.
    pub array_hashes: Option<ArrayHashes>,
    pub boxed_values: Option<FastMap<(u32, u64), u64>>,
    pub roots: Vec<(u32, Root)>,
    pub dangling_roots: u64,
    /// Objects ART marked unreachable: counted, never roots.
    pub marked_unreachable: u64,
    pub threads: Vec<Thread>,
    pub traces: HashMap<u32, Trace>,
    pub frames: FastMap<u64, Frame>,
    pub class_by_serial: HashMap<u32, u32>,
    /// `java.lang.Class`, `java.lang.String`, and the `value` / `name` labels.
    pub class_class: u32,
    pub string_class: u32,
    pub value_label: u32,
    pub name_label: u32,
}

/// An id's 8-byte steps above `base`, if it is aligned and within four bytes of them.
fn step_of(base: u64, id: u64) -> Option<u32> {
    let distance = id.checked_sub(base).filter(|distance| distance.trailing_zeros() >= 3)?;
    u32::try_from(distance >> 3).ok()
}

/// Buckets widen until the id span needs at most this many.
const MAX_BUCKETS: u64 = 1 << 22;

/// The object table bucketed by address range: a short binary search per id, not a hash lookup.
struct Buckets {
    min: u64,
    max: u64,
    shift: u32,
    starts: Vec<u32>,
}

impl Buckets {
    fn empty() -> Buckets {
        Buckets { min: 1, max: 0, shift: 0, starts: vec![0, 0] }
    }

    fn build(table: &ObjectTable) -> Buckets {
        let Some(last) = table.len().checked_sub(1) else { return Buckets::empty() };
        let (min, max) = (table.id(0), table.id(last));
        let span = max - min + 1;
        let mut shift = 0;
        while (span >> shift) > MAX_BUCKETS {
            shift += 1;
        }
        let bucket_count = ((span - 1) >> shift) as usize + 1;
        let mut starts = vec![0u32; bucket_count + 1];
        for object in 0..table.len() {
            starts[((table.id(object) - min) >> shift) as usize + 1] += 1;
        }
        for i in 0..bucket_count {
            starts[i + 1] += starts[i];
        }
        Buckets { min, max, shift, starts }
    }

    /// The table range an id would be in.
    fn range(&self, id: u64) -> Option<(usize, usize)> {
        if id < self.min || id > self.max {
            return None;
        }
        let bucket = ((id - self.min) >> self.shift) as usize;
        Some((self.starts[bucket] as usize, self.starts[bucket + 1] as usize))
    }
}

/// The class with exactly this name that has a layout, else any with the name.
pub fn class_named(classes: &[Class], name: &str) -> Option<u32> {
    let named = |class: &Class| class.name == name;
    let dumped = classes.iter().position(|class| named(class) && class.dumped);
    dumped.or_else(|| classes.iter().position(named)).map(|i| i as u32)
}

/// A class and its superclasses, nearest first.
pub fn ancestry(classes: &[Class], class: u32) -> impl Iterator<Item = u32> + '_ {
    let known = |class: u32| (class != NONE).then_some(class);
    std::iter::successors(known(class), move |&current| known(classes[current as usize].superclass))
        .take(MAX_CLASS_DEPTH)
}

/// Instance field layout for `class`: `(name, type, offset)` up the chain.
pub fn field_layout(classes: &[Class], id_size: u32, class: u32) -> Vec<(u32, Ty, u32)> {
    let mut out = Vec::new();
    let mut offset = 0u32;
    for ancestor in ancestry(classes, class) {
        for field in &classes[ancestor as usize].fields {
            out.push((field.name, field.ty, offset));
            offset += field.ty.size(id_size);
        }
    }
    out
}

/// Offset and type of the instance field called `name`, if `class` has one.
pub fn field_offset(
    classes: &[Class],
    names: &[String],
    id_size: u32,
    class: u32,
    name: &str,
) -> Option<(u32, Ty)> {
    let id = names.iter().position(|interned| interned == name)? as u32;
    field_layout(classes, id_size, class)
        .into_iter()
        .find(|&(field_id, _, _)| field_id == id)
        .map(|(_, ty, offset)| (offset, ty))
}

/// `java/util/Map$Entry`, `[I`, `[Ljava/lang/String;` as source spells them.
pub fn pretty_class_name(raw: &str) -> String {
    match raw.strip_prefix('[') {
        None => raw.replace('/', "."),
        Some(rest) => {
            let dims = 1 + rest.bytes().take_while(|&c| c == b'[').count();
            let base = &rest[dims - 1..];
            let element = match base.as_bytes().first().copied() {
                Some(b'L') => base[1..].trim_end_matches(';').replace('/', "."),
                first => {
                    first.and_then(Ty::from_descriptor).map_or("?".to_string(), |ty| ty.name().to_string())
                }
            };
            format!("{element}{}", "[]".repeat(dims))
        }
    }
}

/// The element type an array class holds, from either name form.
pub fn array_element_type(raw: &str, pretty: &str) -> Option<Ty> {
    if let Some(rest) = raw.strip_prefix('[') {
        return Some(match rest.as_bytes().first() {
            Some(b'[' | b'L') => Ty::Object,
            Some(&descriptor) => Ty::from_descriptor(descriptor)?,
            None => return None,
        });
    }
    let base = pretty.strip_suffix("[]")?;
    if base.ends_with("[]") {
        return Some(Ty::Object);
    }
    Some(
        [Ty::Bool, Ty::Char, Ty::Float, Ty::Double, Ty::Byte, Ty::Short, Ty::Int, Ty::Long]
            .into_iter()
            .find(|ty| ty.name() == base)
            .unwrap_or(Ty::Object),
    )
}

/// The package part of a class name; arrays and default-package classes give "".
pub fn package_of(name: &str) -> &str {
    let base = name.trim_end_matches("[]");
    base.rfind('.').map_or("", |i| &base[..i])
}

impl Dump {
    pub fn lookup(&self, id: u64) -> Option<u32> {
        self.objects.lookup(id)
    }

    pub fn class_of(&self, object: u32) -> &Class {
        &self.classes[self.objects.class(object as usize) as usize]
    }

    pub fn class_name(&self, object: u32) -> &str {
        &self.class_of(object).name
    }

    pub fn class_by_serial(&self, serial: u32) -> Option<u32> {
        self.class_by_serial.get(&serial).copied()
    }

    /// The class with exactly this name that has a layout, else any with the name.
    pub fn class_named(&self, name: &str) -> Option<u32> {
        class_named(&self.classes, name)
    }

    /// Whether `class` is `base` or extends it.
    pub fn extends(&self, class: u32, base: u32) -> bool {
        self.ancestry(class).any(|ancestor| ancestor == base)
    }

    /// A class and its superclasses, nearest first.
    pub fn ancestry(&self, class: u32) -> impl Iterator<Item = u32> + '_ {
        ancestry(&self.classes, class)
    }

    /// Index of an interned field name.
    pub fn name_id(&self, name: &str) -> Option<u32> {
        self.names.iter().position(|interned| interned == name).map(|i| i as u32)
    }

    /// Instance field layout for `class`: `(name, type, offset)` up the chain.
    pub fn field_layout(&self, class: u32) -> Vec<(u32, Ty, u32)> {
        field_layout(&self.classes, self.header.id_size, class)
    }

    /// Offset and type of the instance field called `name`, if `class` has one.
    pub fn field_offset(&self, class: u32, name: &str) -> Option<(u32, Ty)> {
        field_offset(&self.classes, &self.names, self.header.id_size, class, name)
    }

    /// The label a class-object edge carries for its `k`-th static field.
    pub fn static_name(&self, class: u32, index: usize) -> &str {
        &self.names[self.classes[class as usize].statics[index].name as usize]
    }

    pub fn static_value(&self, class: u32, name: &str) -> Option<Value> {
        let statics = &self.classes[class as usize].statics;
        statics.iter().find(|field| self.names[field.name as usize] == name).map(|field| field.value)
    }

    /// A thread's stack, top frame first.
    pub fn stack(&self, trace_serial: u32) -> Vec<String> {
        let Some(trace) = self.traces.get(&trace_serial) else { return Vec::new() };
        trace.frames.iter().map(|id| self.frame_text(*id)).collect()
    }

    /// `Class.method(File.java:12)` for a frame id.
    pub fn frame_text(&self, frame_id: u64) -> String {
        let Some(frame) = self.frames.get(&frame_id) else { return format!("<frame 0x{frame_id:x}>") };
        let class = self
            .class_by_serial(frame.class_serial)
            .map_or("?", |idx| self.classes[idx as usize].name.as_str());
        let method = self.symbols.get(frame.method_id).unwrap_or("?");
        let source = self.symbols.get(frame.source_id).unwrap_or("");
        let line = match frame.line {
            n if n > 0 => format!(":{n}"),
            -2 => " compiled".to_string(),
            -3 => " native".to_string(),
            _ => String::new(),
        };
        if source.is_empty() {
            format!("{class}.{method}")
        } else {
            format!("{class}.{method}({source}{line})")
        }
    }

    /// The method holding a java-frame root's local.
    pub fn frame_of(&self, thread_serial: u32, frame: u32) -> Option<String> {
        let thread = self.threads.iter().find(|thread| thread.serial == thread_serial)?;
        let trace = self.traces.get(&thread.trace_serial)?;
        trace.frames.get(frame as usize).map(|id| self.frame_text(*id))
    }

    pub fn total_shallow(&self) -> u64 {
        super::parallel::ranges(self.objects.len(), |lo, hi| {
            self.objects.shallow_range(lo, hi).map(u64::from).sum::<u64>()
        })
        .into_iter()
        .sum()
    }
}
