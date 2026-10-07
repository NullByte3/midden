//! Pass one: everything in one read of the heap. Symbols, classes and their layouts, the object table
//! with shallow sizes, GC roots and thread stacks, and each object's references as raw ids for the graph.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::io;
use std::sync::Arc;

use super::analysis::duplicates::boxed_classes;
use super::detail::ArrayHash;
use super::dump::{
    self, ArrayHashes, Class, Dump, FastMap, Field, Kind, MAX_CLASS_DEPTH, MAX_CLASSES, NONE, ObjectTable,
    RefKind, Slot, Static,
};
use super::graph::LOADER;
use super::hprof::{
    self, Body, ClassDump, Frame, Header, IO_BUFFER_SIZE, Reader, Root, RootKind, Sink, Ty, Value, View,
    Walked, be_uint,
};
use super::parallel;
use super::sizes::{SizeMode, Sizing};
use super::source::Progress;
use super::store::Column;
use crate::error::{Error, Result};

/// An object as the walk meets it: id, then class and kind above the length, then where its references
/// start in the copied ids, or for a primitive array where its hashes are (`raw`).
type Raw = [u64; 3];

fn raw(id: u64, class: u32, kind: Kind, len: u32, references: usize) -> Raw {
    [id, u64::from(class) << 34 | (kind as u64) << 32 | u64::from(len), references as u64]
}

fn raw_class(record: Raw) -> u32 {
    (record[1] >> 34) as u32
}

fn raw_kind(record: Raw) -> Kind {
    Kind::ALL[(record[1] >> 32 & 3) as usize]
}

/// Byte and char arrays up to this long get the String hash as the walk reads them; a String's longer
/// array is hashed by the detail read.
const STRING_HASH_MAX_BYTES: u64 = 64 << 10;

/// Primitive array classes by `Ty as usize`; room for every HPROF basic-type tag (long, the largest, is 11).
const BASIC_TYPE_SLOTS: usize = 12;

/// Every object's reference slots as the walk copied them, and where each object's start, by object index.
/// The graph resolves them without reading the dump again.
pub struct References {
    pub copied: Copied<Column<u32>>,
    pub starts: Column<u32>,
}

/// A copied id too far from the base to fit in four bytes; the whole id is in `escapes`.
const ESCAPED: u32 = u32::MAX;

/// Reference ids as the walk copies them, four bytes each: the id's distance above `base` in 8-byte steps
/// plus one, zero for null, and [`ESCAPED`] for one that does not fit, kept whole in `escapes` by place.
pub struct Copied<C> {
    pub ids: C,
    pub escapes: Vec<(u64, u64)>,
    pub base: u64,
}

impl<C: Ids> Copied<C> {
    fn new(ids: C, base: u64) -> Copied<C> {
        Copied { ids, escapes: Vec::new(), base }
    }

    pub fn len(&self) -> usize {
        self.ids.count()
    }
}

impl Copied<Column<u32>> {
    /// The id copied at `at`, zero for null.
    pub fn id(&self, at: usize) -> u64 {
        match self.ids[at] {
            0 => 0,
            ESCAPED => self
                .escapes
                .binary_search_by_key(&(at as u64), |&(place, _)| place)
                .map_or(0, |i| self.escapes[i].1),
            steps => self.base + (u64::from(steps - 1) << 3),
        }
    }
}

impl<C: Ids> Extend<u64> for Copied<C> {
    fn extend<I: IntoIterator<Item = u64>>(&mut self, ids: I) {
        for id in ids {
            let steps = id
                .checked_sub(self.base)
                .filter(|distance| distance.trailing_zeros() >= 3)
                .and_then(|distance| u32::try_from((distance >> 3) + 1).ok())
                .filter(|&steps| steps != ESCAPED)
                .unwrap_or(ESCAPED);
            let value = if id == 0 { 0 } else { steps };
            if value == ESCAPED {
                self.escapes.push((self.ids.count() as u64, id));
            }
            self.ids.put(value);
        }
    }
}

/// Where copied ids go: a column for the whole walk, a `Vec` for a worker's part.
pub trait Ids {
    fn count(&self) -> usize;
    fn put(&mut self, value: u32);
}

impl Ids for Column<u32> {
    fn count(&self) -> usize {
        self.len()
    }

    fn put(&mut self, value: u32) {
        self.push(value);
    }
}

impl Ids for Vec<u32> {
    fn count(&self) -> usize {
        self.len()
    }

    fn put(&mut self, value: u32) {
        self.push(value);
    }
}

pub struct Indexer {
    id_size: u32,
    symbols: FastMap<u64, String>,
    classes: Vec<Class>,
    class_by_id: FastMap<u64, u32>,
    class_by_serial: HashMap<u32, u32>,
    class_dumps: Vec<ClassDump>,
    /// Field names, interned by text: one `value` label whatever symbol ids the file used.
    names: Vec<String>,
    name_by_text: HashMap<String, u32>,
    name_by_id: FastMap<u64, u32>,
    objects: Column<Raw>,
    references: Copied<Column<u32>>,
    hashes: Column<[u64; 2]>,
    /// Per class: where a boxed class keeps its value.
    boxed: Vec<Option<(u32, Ty)>>,
    boxed_values: FastMap<(u32, u64), u64>,
    /// Layouts are fixed and the walk copies references from here on.
    frozen: bool,
    /// A class dump came after the layouts were fixed: the references are read in a second pass.
    late: bool,
    roots: Vec<Root>,
    traces: HashMap<u32, dump::Trace>,
    frames: FastMap<u64, Frame>,
    prim_array_classes: [u32; BASIC_TYPE_SLOTS],
    last_class: (u64, u32),
}

impl Indexer {
    pub fn new(id_size: u32) -> Indexer {
        Indexer {
            id_size,
            symbols: FastMap::default(),
            classes: Vec::new(),
            class_by_id: FastMap::default(),
            class_by_serial: HashMap::new(),
            class_dumps: Vec::new(),
            names: Vec::new(),
            name_by_text: HashMap::new(),
            name_by_id: FastMap::default(),
            objects: Column::with_capacity(0),
            references: Copied::new(Column::with_capacity(0), 0),
            hashes: Column::with_capacity(0),
            boxed: Vec::new(),
            boxed_values: FastMap::default(),
            frozen: false,
            late: false,
            roots: Vec::new(),
            traces: HashMap::new(),
            frames: FastMap::default(),
            prim_array_classes: [NONE; BASIC_TYPE_SLOTS],
            last_class: (0, NONE),
        }
    }

    /// The class index for an id, minting a placeholder when the load record is missing (Android).
    fn class_index(&mut self, id: u64) -> u32 {
        if self.last_class.0 == id && self.last_class.1 != NONE {
            return self.last_class.1;
        }
        let idx = if let Some(&idx) = self.class_by_id.get(&id) {
            idx
        } else {
            let idx = self.classes.len() as u32;
            self.classes.push(Class::placeholder(format!("<class 0x{id:x}>"), id));
            self.class_by_id.insert(id, idx);
            idx
        };
        self.last_class = (id, idx);
        idx
    }

    fn primitive_array_class(&mut self, ty: Ty) -> u32 {
        let ty_idx = ty as usize;
        if self.prim_array_classes[ty_idx] == NONE {
            let name = format!("{}[]", ty.name());
            let idx = class_named(&self.classes, &name)
                .unwrap_or_else(|| push(&mut self.classes, Class::placeholder(name, 0)));
            self.classes[idx as usize].element_type = Some(ty);
            self.prim_array_classes[ty_idx] = idx;
        }
        self.prim_array_classes[ty_idx]
    }

    /// Fix the layouts once the class dumps before the first object are in (`HotSpot` writes them all
    /// first), so the walk can copy references as it goes. A dump naming a class the file never loaded
    /// would mint placeholders out of their usual order, so then the references wait for a second pass.
    fn freeze(&mut self) {
        self.frozen = true;
        let known = |id: u64| id == 0 || self.class_by_id.contains_key(&id);
        if !self.class_dumps.iter().all(|class_dump| known(class_dump.id) && known(class_dump.super_id)) {
            self.late = true;
            return;
        }
        // Class mirrors sit in the heap, so the lowest is a good base for the copied ids.
        self.references.base = self.class_by_id.keys().copied().filter(|&id| id != 0).min().unwrap_or(0) & !7;
        self.resolve_class_dumps();
        // Reference slots do not depend on the size convention; `finish` lays out again with the real one.
        self.lay_out_classes(&Sizing::resolve(SizeMode::Mat, self.id_size, 0));
        self.boxed = vec![None; self.classes.len()];
        for (class, _, offset, ty) in boxed_classes(&self.classes, &self.names, self.id_size) {
            self.boxed[class as usize] = Some((offset, ty));
        }
    }

    /// Whether the walk copies references: the layouts are fixed and no class dump came after them.
    fn copies(&mut self) -> bool {
        if !self.frozen {
            self.freeze();
        }
        !self.late
    }
}

/// What the walk takes from an instance's body: its reference slots, an id each and zero for null or past
/// a short body, and a boxed class's value.
fn copy_instance(
    (class, slots, boxed): (u32, &[Slot], Option<(u32, Ty)>),
    id_size: u32,
    body: Body,
    references: &mut impl Extend<u64>,
    boxed_values: &mut FastMap<(u32, u64), u64>,
) -> io::Result<()> {
    if slots.is_empty() && boxed.is_none() {
        return Ok(());
    }
    let bytes = body.bytes()?;
    let width = id_size as usize;
    references.extend(
        slots
            .iter()
            .map(|slot| bytes.get(slot.offset as usize..slot.offset as usize + width).map_or(0, be_uint)),
    );
    let value = boxed.and_then(|(offset, ty)| Value::decode(ty, bytes.get(offset as usize..)?, id_size));
    if let Some(value) = value {
        *boxed_values.entry((class, value.bits())).or_default() += 1;
    }
    Ok(())
}

/// A primitive array's hashes, the String one only for a byte or char array of up to
/// [`STRING_HASH_MAX_BYTES`]; zero stands for not taken.
fn hash_array(ty: Ty, len: u32, body: Body) -> io::Result<[u64; 2]> {
    let string = matches!(ty, Ty::Byte | Ty::Char) && body.len() <= STRING_HASH_MAX_BYTES;
    let mut hash = ArrayHash::new();
    body.chunks(IO_BUFFER_SIZE, |chunk| {
        if string {
            hash.string(chunk);
        }
        hash.content(chunk);
        Ok(())
    })?;
    let [string_hash, content_hash] = hash.finish(len);
    Ok([if string { string_hash } else { 0 }, content_hash])
}

/// Copy an object array's elements: an id each, zero for null.
fn copy_elements(id_size: usize, body: Body, out: &mut impl Extend<u64>) -> io::Result<()> {
    body.chunks(IO_BUFFER_SIZE, |chunk| {
        out.extend(chunk.chunks_exact(id_size).map(be_uint));
        Ok(())
    })
}

/// The object callbacks: the same code for the sequential walk and a worker's part.
macro_rules! object_callbacks {
    () => {
        fn instance(&mut self, id: u64, class_id: u64, body: Body) -> io::Result<()> {
            let class = self.class_index(class_id);
            let (len, start) = (body.len() as u32, self.references.len());
            if self.copies() && class != NONE {
                let boxed = self.boxed.get(class as usize).copied().flatten();
                let copied = (class, &self.classes[class as usize].slots[..], boxed);
                copy_instance(copied, self.id_size, body, &mut self.references, &mut self.boxed_values)?;
            }
            self.objects.push(raw(id, class, Kind::Instance, len, start));
            Ok(())
        }

        fn object_array(&mut self, id: u64, class_id: u64, len: u32, body: Body) -> io::Result<()> {
            let class = self.class_index(class_id);
            let start = self.references.len();
            if self.copies() {
                copy_elements(self.id_size as usize, body, &mut self.references)?;
            }
            self.objects.push(raw(id, class, Kind::ObjectArray, len, start));
            Ok(())
        }

        fn primitive_array(&mut self, id: u64, ty: Ty, len: u32, body: Body) -> io::Result<()> {
            let class = self.primitive_array_class(ty);
            let at = self.hashes.len();
            self.hashes.push(hash_array(ty, len, body)?);
            self.objects.push(raw(id, class, Kind::PrimitiveArray, len, at));
            Ok(())
        }
    };
}

impl Sink for Indexer {
    fn utf8(&mut self, id: u64, text: &[u8]) {
        self.symbols.insert(id, String::from_utf8_lossy(text).into_owned());
    }

    fn load_class(&mut self, serial: u32, id: u64, name_id: u64) {
        let raw_name = self.symbols.get(&name_id).map_or("", String::as_str);
        let name =
            if raw_name.is_empty() { format!("<class 0x{id:x}>") } else { dump::pretty_class_name(raw_name) };
        let element_type = dump::array_element_type(raw_name, &name);
        let idx = if let Some(&idx) = self.class_by_id.get(&id) {
            self.classes[idx as usize].name = name;
            idx
        } else {
            let idx = push(&mut self.classes, Class::placeholder(name, id));
            self.class_by_id.insert(id, idx);
            idx
        };
        self.classes[idx as usize].element_type = element_type;
        self.class_by_serial.insert(serial, idx);
    }

    fn frame(&mut self, frame: Frame) {
        self.frames.insert(frame.id, frame);
    }

    fn trace(&mut self, serial: u32, _thread_serial: u32, frames: &[u64]) {
        self.traces.insert(serial, dump::Trace { frames: frames.to_vec() });
    }

    fn root(&mut self, root: Root) {
        self.roots.push(root);
    }

    fn class(&mut self, class: ClassDump) {
        self.late |= self.frozen;
        self.class_index(class.id);
        self.class_dumps.push(class);
    }

    object_callbacks!();
}

/// One run of heap segments, read on a worker. A class whose load record is not seen yet is left
/// to the sequential walk, which mints placeholders in file order.
struct Part<'a> {
    id_size: u32,
    class_by_id: &'a FastMap<u64, u32>,
    classes: &'a [Class],
    boxed: &'a [Option<(u32, Ty)>],
    prim_array_classes: [u32; BASIC_TYPE_SLOTS],
    missed: bool,
    /// Copy references: false once a class dump turned up after the layouts were fixed.
    copying: bool,
    class_dumps: Vec<ClassDump>,
    objects: Vec<Raw>,
    references: Copied<Vec<u32>>,
    hashes: Vec<[u64; 2]>,
    boxed_values: FastMap<(u32, u64), u64>,
    roots: Vec<Root>,
}

impl Part<'_> {
    fn class_index(&mut self, id: u64) -> u32 {
        let idx = self.class_by_id.get(&id).copied();
        self.missed |= idx.is_none();
        idx.unwrap_or(NONE)
    }

    fn primitive_array_class(&mut self, ty: Ty) -> u32 {
        let class = self.prim_array_classes[ty as usize];
        self.missed |= class == NONE;
        class
    }

    fn copies(&self) -> bool {
        self.copying
    }
}

impl Sink for Part<'_> {
    fn root(&mut self, root: Root) {
        self.roots.push(root);
    }

    fn class(&mut self, class: ClassDump) {
        self.copying = false;
        self.class_dumps.push(class);
    }

    object_callbacks!();
}

/// What a worker's part brought back.
struct Parsed {
    class_dumps: Vec<ClassDump>,
    objects: Vec<Raw>,
    references: Copied<Vec<u32>>,
    hashes: Vec<[u64; 2]>,
    boxed_values: FastMap<(u32, u64), u64>,
    copied: bool,
    roots: Vec<Root>,
    walked: Walked,
}

impl Indexer {
    /// Read the stepped-over segments, a run of adjacent ones per worker, merged in file order. False
    /// sends the file back to the sequential walk: segments were also walked in place, one runs past
    /// the end, a part fails to parse, or a class needs a placeholder only file order can mint. The
    /// class dumps and roots before the first object are read first, here, to fix the layouts.
    pub fn read_segments(&mut self, view: &View, walked: &mut Walked, progress: &Arc<Progress>) -> bool {
        let segments = std::mem::take(&mut walked.segments);
        if !walked.chunks.is_empty() || segments.last().is_some_and(|&(_, end)| end > view.len) {
            return false;
        }
        let mut runs: Vec<(u64, u64)> = Vec::new();
        for &(start, end) in &segments {
            match runs.last_mut() {
                // A record header apart: only the next segment's header is between.
                Some(run)
                    if run.1 + hprof::RECORD_HEADER_LEN == start && run.1 - run.0 < hprof::CHUNK_SIZE =>
                {
                    run.1 = end;
                }
                _ => runs.push((start, end)),
            }
        }
        let Some(first) = runs.first_mut() else { return true };
        let objects_start = Reader::open_at(view, first.0, self.id_size)
            .and_then(|mut reader| hprof::prelude(&mut reader, first.1, self));
        let Ok(objects_start) = objects_start else { return false };
        first.0 = objects_start;
        runs.retain(|&(start, end)| start < end);
        self.freeze();
        let mut prim_array_classes = [NONE; BASIC_TYPE_SLOTS];
        for ty in [Ty::Bool, Ty::Char, Ty::Float, Ty::Double, Ty::Byte, Ty::Short, Ty::Int, Ty::Long] {
            let name = format!("{}[]", ty.name());
            prim_array_classes[ty as usize] = class_named(&self.classes, &name).unwrap_or(NONE);
        }
        progress.begin("indexing objects", runs.iter().map(|&(start, end)| end - start).sum());
        let (id_size, class_by_id, classes, boxed, copying, base) =
            (self.id_size, &self.class_by_id, &self.classes, &self.boxed, !self.late, self.references.base);
        let (mut complete, mut class_dumps) = (true, Vec::new());
        parallel::ordered(
            &runs,
            |&(start, end)| {
                let mut reader = Reader::open_at(view, start, id_size).ok()?;
                reader.progress = progress.counter(start);
                let mut part = Part {
                    id_size,
                    class_by_id,
                    classes,
                    boxed,
                    prim_array_classes,
                    missed: false,
                    copying,
                    class_dumps: Vec::new(),
                    objects: Vec::new(),
                    references: Copied::new(Vec::new(), base),
                    hashes: Vec::new(),
                    boxed_values: FastMap::default(),
                    roots: Vec::new(),
                };
                let mut part_walked = Walked::default();
                hprof::heap(&mut reader, Some(end), &mut part, &mut part_walked).ok()?;
                (!part.missed).then_some(Parsed {
                    class_dumps: part.class_dumps,
                    objects: part.objects,
                    references: part.references,
                    hashes: part.hashes,
                    boxed_values: part.boxed_values,
                    copied: part.copying,
                    roots: part.roots,
                    walked: part_walked,
                })
            },
            |part| {
                let Some(part) = part else {
                    complete = false;
                    return false;
                };
                class_dumps.extend(part.class_dumps);
                self.late |= !part.copied;
                // Starts are the part's own: move them past what earlier parts copied.
                let (reference_base, hash_base) = (self.references.len() as u64, self.hashes.len() as u64);
                if !self.late {
                    let escapes = part.references.escapes.iter().map(|&(at, id)| (at + reference_base, id));
                    self.references.escapes.extend(escapes);
                    self.references.ids.extend_from_slice(&part.references.ids);
                }
                self.hashes.extend_from_slice(&part.hashes);
                for (key, count) in part.boxed_values {
                    *self.boxed_values.entry(key).or_default() += count;
                }
                self.objects.reserve(part.objects.len());
                for &record in &part.objects {
                    let base =
                        if raw_kind(record) == Kind::PrimitiveArray { hash_base } else { reference_base };
                    self.objects.push([record[0], record[1], record[2] + base]);
                }
                self.roots.extend(part.roots);
                walked.chunks.extend(part.walked.chunks);
                walked.pieces.extend(part.walked.pieces);
                true
            },
        );
        // Class dumps can mint placeholders, which the workers must not see change.
        for class_dump in class_dumps {
            self.class(class_dump);
        }
        complete
    }

    /// Resolve layouts, size every object, sort the table, resolve the roots. Also hands back the
    /// references the walk copied, unless a late class dump means the graph must read them itself.
    pub fn finish(
        mut self,
        path: &str,
        reader: &Reader,
        header: Header,
        walked: Walked,
        mode: SizeMode,
    ) -> Result<(Dump, Option<References>)> {
        self.resolve_class_dumps();
        // Class and field names are copied out by now: only stack frames still look symbols up.
        let framed: HashSet<u64> =
            self.frames.values().flat_map(|frame| [frame.method_id, frame.source_id]).collect();
        self.symbols.retain(|id, _| framed.contains(id));
        self.symbols.shrink_to_fit();
        let value_label = intern_str(&mut self.names, "value");
        let name_label = intern_str(&mut self.names, "name");

        // Sizes depend on the address range.
        let max_id = self.objects.iter().map(|record| record[0]).max().unwrap_or(0);
        let sizing = Sizing::resolve(mode, self.id_size, max_id);
        self.lay_out_classes(&sizing);
        // Starts are four bytes: a walk that copied more ids than that reads the references again.
        let keep = self.frozen && !self.late && self.references.len() < u32::MAX as usize;
        let (mut objects, class_class, starts, array_hashes) = self.size_objects(sizing, keep);
        objects.index();
        // u32 indices keep NONE free and the graph root one past the objects; labels stay below LOADER.
        let counts = [
            ("objects", objects.len(), NONE as usize - 1),
            ("classes", self.classes.len(), MAX_CLASSES - 1),
            ("field names", self.names.len(), LOADER as usize),
        ];
        for (what, count, limit) in counts {
            if count > limit {
                return Err(Error::Dump(format!("too many {what} for midden ({count}, limit {limit})")));
            }
        }
        let string_class = class_named(&self.classes, "java.lang.String").unwrap_or(NONE);
        let references = keep.then(|| References {
            copied: std::mem::replace(&mut self.references, Copied::new(Column::with_capacity(0), 0)),
            starts,
        });

        let mut dump = Dump {
            path: path.to_string(),
            file_size: reader.file_size,
            gzip: reader.gzip,
            member: reader.member.clone(),
            header,
            truncated: walked.truncated,
            sizing,
            chunks: walked.chunks,
            pieces: walked.pieces,
            names: self.names,
            symbols: self.symbols,
            classes: self.classes,
            objects,
            array_hashes: Some(array_hashes),
            boxed_values: keep.then_some(self.boxed_values),
            roots: Vec::new(),
            dangling_roots: 0,
            marked_unreachable: 0,
            threads: Vec::new(),
            traces: self.traces,
            frames: self.frames,
            class_by_serial: self.class_by_serial,
            class_class,
            string_class,
            value_label,
            name_label,
        };
        resolve_roots(&mut dump, self.roots);
        Ok((dump, references))
    }

    /// Apply the class dumps read so far to their classes, interning their field names.
    fn resolve_class_dumps(&mut self) {
        for class_dump in std::mem::take(&mut self.class_dumps) {
            let idx = self.class_index(class_dump.id) as usize;
            let superclass =
                if class_dump.super_id == 0 { NONE } else { self.class_index(class_dump.super_id) };
            let fields = class_dump
                .fields
                .iter()
                .map(|&(name_id, ty)| Field { name: self.intern(name_id), ty })
                .collect();
            let statics = class_dump
                .statics
                .iter()
                .map(|&(name_id, ty, value)| Static { name: self.intern(name_id), ty, value })
                .collect();
            let class = &mut self.classes[idx];
            class.superclass = superclass;
            class.loader = class_dump.loader_id;
            class.dumped = true;
            class.fields = fields;
            class.statics = statics;
        }
    }

    /// The label for a field name symbol.
    fn intern(&mut self, id: u64) -> u32 {
        if let Some(&label) = self.name_by_id.get(&id) {
            return label;
        }
        let text = self.symbols.get(&id).cloned().unwrap_or_else(|| format!("<0x{id:x}>"));
        let label = if let Some(&label) = self.name_by_text.get(&text) {
            label
        } else {
            let label = push(&mut self.names, text.clone());
            self.name_by_text.insert(text, label);
            label
        };
        self.name_by_id.insert(id, label);
        label
    }

    fn lay_out_classes(&mut self, sizing: &Sizing) {
        let reference = class_named(&self.classes, "java.lang.ref.Reference");
        let referent = self.names.iter().position(|name| name == "referent").map(|i| i as u32);
        let class_count = self.classes.len();
        let mut laid_out = vec![false; class_count];
        for i in 0..class_count {
            layout(&mut self.classes, i as u32, &mut laid_out, self.id_size, sizing, reference, referent, 0);
        }
        mark_reference_kinds(&mut self.classes);
    }

    /// The object table: the walk's records and the class objects merged by id, one of each id kept,
    /// instances counted. Also returns the `java.lang.Class` class, where each kept object's copied
    /// references start when `keep`, and the primitive arrays' hashes by object index.
    fn size_objects(&mut self, sizing: Sizing, keep: bool) -> (ObjectTable, u32, Column<u32>, ArrayHashes) {
        // Class objects live in the object table too: statics are edges and
        // sticky-class roots point at them.
        let class_class = class_named(&self.classes, "java.lang.Class")
            .unwrap_or_else(|| push(&mut self.classes, Class::placeholder("java.lang.Class".to_string(), 0)));
        let mut class_objects: Vec<Raw> = Vec::new();
        for class in self.classes.iter().filter(|class| class.dumped) {
            let statics_size: u64 =
                class.statics.iter().map(|field| u64::from(sizing.field_size(field.ty))).sum();
            class_objects.push(raw(
                class.id,
                class_class,
                Kind::Class,
                sizing.instance_size(statics_size),
                0,
            ));
        }
        class_objects.sort_by_key(|record| record[0]);
        let records = std::mem::replace(&mut self.objects, Column::with_capacity(0));
        // HotSpot writes by address in runs: merge the runs, earlier ones first on equal ids, which is
        // a stable sort. The first record of each id is kept.
        let mut runs: Vec<&[Raw]> = Vec::new();
        let mut start = 0;
        for i in 1..=records.len() {
            if i == records.len() || records[i][0] < records[i - 1][0] {
                runs.push(&records[start..i]);
                start = i;
            }
        }
        runs.push(&class_objects);
        runs.retain(|run| !run.is_empty());
        let capacity = records.len() + class_objects.len();
        let mut table = ObjectTable::new(&self.classes, sizing, capacity);
        let mut starts = Column::with_capacity(if keep { capacity } else { 0 });
        let hashes = std::mem::replace(&mut self.hashes, Column::with_capacity(0));
        let mut array_hashes = ArrayHashes {
            objects: Column::with_capacity(hashes.len()),
            values: Column::with_capacity(hashes.len()),
        };
        let mut last = None;
        let mut instances = vec![0u64; self.classes.len()];
        merge_runs(&mut runs, |record| {
            if last != Some(record[0]) {
                last = Some(record[0]);
                let (class, kind) = (raw_class(record), raw_kind(record));
                instances[class as usize] += 1;
                if kind == Kind::PrimitiveArray {
                    array_hashes.objects.push(table.len() as u32);
                    array_hashes.values.push(hashes[record[2] as usize]);
                }
                table.push(record[0], class, kind, record[1] as u32);
                if keep {
                    starts.push(record[2] as u32);
                }
            }
        });
        for (class, count) in self.classes.iter_mut().zip(instances) {
            class.instances = count;
        }
        (table, class_class, starts, array_hashes)
    }
}

/// Feed the records of sorted runs to `emit` in id order, an earlier run first on equal ids. Emits a
/// stretch of the run with the smallest head at once, up to the next head.
fn merge_runs(runs: &mut [&[Raw]], mut emit: impl FnMut(Raw)) {
    let head = |runs: &[&[Raw]], run: usize| runs[run].first().map(|record| Reverse((record[0], run)));
    let mut heads: BinaryHeap<Reverse<(u64, usize)>> =
        (0..runs.len()).filter_map(|run| head(runs, run)).collect();
    while let Some(Reverse((_, run))) = heads.pop() {
        let stretch = match heads.peek() {
            None => runs[run].len(),
            Some(&Reverse(next)) => runs[run].partition_point(|record| (record[0], run) < next).max(1),
        };
        let (taken, rest) = runs[run].split_at(stretch);
        for &record in taken {
            emit(record);
        }
        runs[run] = rest;
        heads.extend(head(runs, run));
    }
}

/// Resolve the roots against the object table and list each thread once.
fn resolve_roots(dump: &mut Dump, roots: Vec<Root>) {
    for root in roots {
        if root.kind == RootKind::Unreachable {
            dump.marked_unreachable += 1;
            continue;
        }
        match dump.lookup(root.id) {
            Some(idx) => dump.roots.push((idx, root)),
            None => dump.dangling_roots += 1,
        }
    }
    let mut seen_threads = HashSet::new();
    for &(object, root) in &dump.roots {
        if root.kind == RootKind::ThreadObject && seen_threads.insert(root.thread_serial) {
            let (serial, trace_serial) = (root.thread_serial, root.trace_serial);
            dump.threads.push(dump::Thread { object, serial, trace_serial });
        }
    }
    dump.threads.sort_by_key(|thread| thread.serial);
}

fn intern_str(names: &mut Vec<String>, name: &str) -> u32 {
    let found = names.iter().position(|existing| existing == name).map(|i| i as u32);
    found.unwrap_or_else(|| push(names, name.to_string()))
}

/// The index of the first class with this name.
fn class_named(classes: &[Class], name: &str) -> Option<u32> {
    classes.iter().position(|class| class.name == name).map(|i| i as u32)
}

/// Append an item, returning its index.
fn push<T>(items: &mut Vec<T>, item: T) -> u32 {
    items.push(item);
    items.len() as u32 - 1
}

/// A class's data length, shallow size and reference slots, after its
/// superclass's. Depth-capped so a corrupt cyclic chain cannot recurse forever.
#[allow(clippy::too_many_arguments)]
fn layout(
    classes: &mut [Class],
    idx: u32,
    laid_out: &mut [bool],
    id_size: u32,
    sizing: &Sizing,
    reference: Option<u32>,
    referent: Option<u32>,
    depth: usize,
) {
    let i = idx as usize;
    if laid_out[i] {
        return;
    }
    laid_out[i] = true;
    let super_idx = classes[i].superclass;
    let (mut own_len, mut own_footprint, mut slots) = (0u32, 0u64, Vec::new());
    for field in &classes[i].fields {
        if field.ty == Ty::Object {
            let weak = Some(idx) == reference && Some(field.name) == referent;
            slots.push(Slot { offset: own_len, label: field.name, weak });
        }
        own_len += field.ty.size(id_size);
        own_footprint += u64::from(sizing.field_size(field.ty));
    }
    let (mut data_len, mut footprint) = (own_len, own_footprint);
    if super_idx != NONE && depth < MAX_CLASS_DEPTH {
        layout(classes, super_idx, laid_out, id_size, sizing, reference, referent, depth + 1);
        let superclass = &classes[super_idx as usize];
        data_len += superclass.data_len;
        footprint += u64::from(superclass.footprint);
        slots.extend(superclass.slots.iter().map(|slot| Slot { offset: slot.offset + own_len, ..*slot }));
    }
    let class = &mut classes[i];
    class.data_len = data_len;
    class.footprint = footprint.min(u64::from(u32::MAX)) as u32;
    class.shallow = sizing.instance_size(footprint);
    class.slots = slots;
}

/// Tag every `Reference` subclass with its family.
fn mark_reference_kinds(classes: &mut [Class]) {
    let bases: Vec<(u32, RefKind)> = RefKind::ALL
        .iter()
        .filter_map(|&kind| class_named(classes, kind.class_name()).map(|i| (i, kind)))
        .collect();
    let reference = class_named(classes, "java.lang.ref.Reference");
    if bases.is_empty() && reference.is_none() {
        return;
    }
    for i in 0..classes.len() {
        let mut current = i as u32;
        let mut kind = None;
        for _ in 0..MAX_CLASS_DEPTH {
            if current == NONE {
                break;
            }
            if let Some(&(_, base_kind)) = bases.iter().find(|(base, _)| *base == current) {
                kind = Some(base_kind);
                break;
            }
            if Some(current) == reference && current != i as u32 {
                kind = Some(RefKind::Weak);
                break;
            }
            current = classes[current as usize].superclass;
        }
        classes[i].ref_kind = kind;
    }
}
