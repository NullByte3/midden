//! Pass one: everything in one read of the heap. Symbols, classes and their layouts, the object table
//! with shallow sizes, GC roots and thread stacks, and each object's references as raw ids for the graph.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap, HashSet};
use std::io;
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
use std::sync::{Arc, Mutex};

use super::analysis::duplicates::boxed_classes;
use super::detail::ArrayHash;
use super::dump::{
    self, ArrayHashes, Class, Dump, FastMap, Field, Kind, MAX_CLASS_DEPTH, MAX_CLASSES, NONE, ObjectTable,
    Packing, RefKind, Shapes, Slot, Static, Symbols, TableIds,
};
use super::graph::LOADER;
use super::hprof::{
    self, Body, ClassDump, Frame, Header, IO_BUFFER_SIZE, Reader, Root, RootKind, Sink, Ty, Value, View,
    Walked, be_uint,
};
use super::parallel;
use super::sizes::{SizeMode, Sizing};
use super::source::Progress;
use super::store::{Blocked, Column};
use crate::error::{Error, Result};

/// An object as the walk meets it, beside its id: class and kind above the length. Its start is where
/// its references are in the copied ids, or for a primitive array where its hashes are.
fn word(class: u32, kind: Kind, len: u32) -> u64 {
    u64::from(class) << 34 | (kind as u64) << 32 | u64::from(len)
}

fn word_class(word: u64) -> u32 {
    (word >> 34) as u32
}

fn word_kind(word: u64) -> Kind {
    Kind::ALL[(word >> 32 & 3) as usize]
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
    symbols: Symbols,
    classes: Vec<Class>,
    class_by_id: FastMap<u64, u32>,
    class_by_serial: HashMap<u32, u32>,
    class_dumps: Vec<ClassDump>,
    /// Field names, interned by text: one `value` label whatever symbol ids the file used.
    names: Vec<String>,
    name_by_text: HashMap<String, u32>,
    name_by_id: FastMap<u64, u32>,
    /// The sequential walk's records: each one's id and word.
    objects: Column<[u64; 2]>,
    /// Per record, where its copied references start, or a primitive array's hash slot. Four bytes: the
    /// references are only kept while they fit.
    starts: Column<u32>,
    /// The workers' parts in file order, kept as read.
    parts: Vec<Kept>,
    /// The highest object id met, which picks the size convention.
    max_id: u64,
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
            symbols: Symbols::default(),
            classes: Vec::new(),
            class_by_id: FastMap::default(),
            class_by_serial: HashMap::new(),
            class_dumps: Vec::new(),
            names: Vec::new(),
            name_by_text: HashMap::new(),
            name_by_id: FastMap::default(),
            objects: Column::with_capacity(0),
            starts: Column::with_capacity(0),
            parts: Vec::new(),
            max_id: 0,
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

    /// Keep an object's id and word, paired: one array to fill as the walk goes.
    fn keep(&mut self, id: u64, word: u64) {
        self.objects.push([id, word]);
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
            self.max_id = self.max_id.max(id);
            self.keep(id, word(class, Kind::Instance, len));
            self.starts.push(start as u32);
            Ok(())
        }

        fn object_array(&mut self, id: u64, class_id: u64, len: u32, body: Body) -> io::Result<()> {
            let class = self.class_index(class_id);
            let start = self.references.len();
            if self.copies() {
                copy_elements(self.id_size as usize, body, &mut self.references)?;
            }
            self.max_id = self.max_id.max(id);
            self.keep(id, word(class, Kind::ObjectArray, len));
            self.starts.push(start as u32);
            Ok(())
        }

        fn primitive_array(&mut self, id: u64, ty: Ty, len: u32, body: Body) -> io::Result<()> {
            let class = self.primitive_array_class(ty);
            let at = self.hashes.len();
            self.hashes.push(hash_array(ty, len, body)?);
            self.max_id = self.max_id.max(id);
            self.keep(id, word(class, Kind::PrimitiveArray, len));
            self.starts.push(at as u32);
            Ok(())
        }
    };
}

impl Sink for Indexer {
    fn utf8(&mut self, id: u64, text: &[u8]) {
        self.symbols.insert(id, text);
    }

    fn load_class(&mut self, serial: u32, id: u64, name_id: u64) {
        let raw_name = self.symbols.get(name_id).unwrap_or("");
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
    ids: Vec<u64>,
    words: Vec<u64>,
    starts: Vec<u32>,
    max_id: u64,
    references: Copied<Vec<u32>>,
    hashes: Vec<[u64; 2]>,
    boxed_values: FastMap<(u32, u64), u64>,
    roots: Vec<Root>,
    last_class: (u64, u32),
}

impl Part<'_> {
    fn class_index(&mut self, id: u64) -> u32 {
        if self.last_class.0 == id {
            return self.last_class.1;
        }
        let idx = self.class_by_id.get(&id).copied();
        self.missed |= idx.is_none();
        let idx = idx.unwrap_or(NONE);
        self.last_class = (id, idx);
        idx
    }

    fn primitive_array_class(&mut self, ty: Ty) -> u32 {
        let class = self.prim_array_classes[ty as usize];
        self.missed |= class == NONE;
        class
    }

    fn copies(&self) -> bool {
        self.copying
    }

    /// Keep an object's id and word, apart: the ids can go once they are sorted.
    fn keep(&mut self, id: u64, word: u64) {
        self.ids.push(id);
        self.words.push(word);
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

/// A part's records (ids, words and starts), copied ids and hashes. The starts are the part's own: a hash
/// slot is a place in `hashes`, and `reference_base` moves a reference start past what earlier parts copied.
struct Kept {
    ids: Vec<u64>,
    words: Vec<u64>,
    starts: Vec<u32>,
    references: Vec<u32>,
    hashes: Vec<[u64; 2]>,
    reference_base: u32,
}

/// What a worker's part brought back.
struct Parsed {
    class_dumps: Vec<ClassDump>,
    ids: Vec<u64>,
    words: Vec<u64>,
    starts: Vec<u32>,
    max_id: u64,
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
        // Each part's references go after those copied before it: the walk's own first, if any.
        let mut copied = self.references.len() as u64;
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
                    ids: Vec::new(),
                    words: Vec::new(),
                    starts: Vec::new(),
                    max_id: 0,
                    references: Copied::new(Vec::new(), base),
                    hashes: Vec::new(),
                    boxed_values: FastMap::default(),
                    roots: Vec::new(),
                    last_class: (0, NONE),
                };
                let mut part_walked = Walked::default();
                hprof::heap(&mut reader, Some(end), &mut part, &mut part_walked).ok()?;
                (!part.missed).then_some(Parsed {
                    class_dumps: part.class_dumps,
                    ids: part.ids,
                    words: part.words,
                    starts: part.starts,
                    max_id: part.max_id,
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
                let reference_base = copied;
                if !self.late {
                    let escapes = part.references.escapes.iter().map(|&(at, id)| (at + reference_base, id));
                    self.references.escapes.extend(escapes);
                    copied += part.references.ids.len() as u64;
                }
                for (key, count) in part.boxed_values {
                    *self.boxed_values.entry(key).or_default() += count;
                }
                self.max_id = self.max_id.max(part.max_id);
                // The records stay where the worker put them; the merge reads them in place.
                self.parts.push(Kept {
                    ids: part.ids,
                    words: part.words,
                    starts: part.starts,
                    references: part.references.ids,
                    hashes: part.hashes,
                    reference_base: reference_base as u32,
                });
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
        // The copied ids in one column, each part's after the one before, moved by the workers.
        if complete && !self.late {
            let mut ids = Column::<u32>::zeroed(copied as usize);
            let (own, mut rest) = ids.split_at_mut(self.references.len());
            own.copy_from_slice(&self.references.ids);
            let mut moves = Vec::with_capacity(self.parts.len());
            for part in &mut self.parts {
                let (to, tail) = std::mem::take(&mut rest).split_at_mut(part.references.len());
                rest = tail;
                moves.push(Mutex::new((to, std::mem::take(&mut part.references))));
            }
            parallel::items(&moves, |pair| {
                let mut pair = pair.lock().expect("worker panicked");
                let from = std::mem::take(&mut pair.1);
                pair.0.copy_from_slice(&from);
            });
            drop(moves);
            self.references.ids = ids;
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
        self.symbols =
            self.symbols.only(self.frames.values().flat_map(|frame| [frame.method_id, frame.source_id]));
        let value_label = intern_str(&mut self.names, "value");
        let name_label = intern_str(&mut self.names, "name");

        // Sizes depend on the address range.
        let sizing = Sizing::resolve(mode, self.id_size, self.max_id);
        // Fixed layouts only need their sizes for the real convention; a late class dump lays out again.
        if self.frozen && !self.late {
            size_classes(&mut self.classes, &sizing);
        } else {
            self.lay_out_classes(&sizing);
        }
        // Starts are four bytes: a walk that copied more ids than that reads the references again.
        let keep = self.frozen && !self.late && self.references.len() < u32::MAX as usize;
        let (objects, class_class, starts, array_hashes) = self.size_objects(sizing, keep);
        let array_hashes = ArrayHashes::new(&objects, array_hashes);
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
            array_hashes,
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
        let text = self.symbols.get(id).map_or_else(|| format!("<0x{id:x}>"), str::to_string);
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
    /// references start when `keep`, and the primitive arrays' hashes in table order.
    fn size_objects(
        &mut self,
        sizing: Sizing,
        keep: bool,
    ) -> (ObjectTable, u32, Column<u32>, Column<[u64; 2]>) {
        // Class objects live in the object table too: statics are edges and
        // sticky-class roots point at them.
        let class_class = class_named(&self.classes, "java.lang.Class")
            .unwrap_or_else(|| push(&mut self.classes, Class::placeholder("java.lang.Class".to_string(), 0)));
        let mut class_objects: Vec<(u64, u64)> = Vec::new();
        for class in self.classes.iter().filter(|class| class.dumped) {
            let statics_size: u64 =
                class.statics.iter().map(|field| u64::from(sizing.field_size(field.ty))).sum();
            class_objects
                .push((class.id, word(class_class, Kind::Class, sizing.instance_size(statics_size))));
        }
        class_objects.sort_by_key(|&(id, _)| id);
        let (class_ids, class_words): (Vec<u64>, Vec<u64>) = class_objects.into_iter().unzip();
        let class_starts = vec![0u32; class_ids.len()];
        let objects = std::mem::replace(&mut self.objects, Column::with_capacity(0));
        let starts = std::mem::replace(&mut self.starts, Column::with_capacity(0));
        let mut parts = std::mem::take(&mut self.parts);
        let hashes = std::mem::replace(&mut self.hashes, Column::with_capacity(0));
        let walked = (Records::Paired(&objects), &starts[..], &hashes[..], 0);
        let class_run = (Records::Apart(&class_ids, &class_words), &class_starts[..], &[][..], 0);
        let read = runs_read(walked, &parts, class_run);
        // The collectors that walk regions (G1, Parallel, Serial) write by address in runs: merge the runs,
        // earlier ones first on equal ids, which is a stable sort. The first record of each id is kept. A
        // collector that walks the graph (ZGC, Shenandoah) writes in no order, and its records are sorted.
        let total: usize = read.iter().map(|run| run.0.len()).sum();
        let most_runs = (total / FRAGMENTED_RUN_LEN).max(MIN_FRAGMENTED_RUNS);
        let mut runs: Vec<Run> = Vec::new();
        'read: for &(records, starts, hashes, reference_base) in &read {
            let mut start = 0;
            for i in 1..=records.len() {
                if i == records.len() || records.id(i) < records.id(i - 1) {
                    runs.push((records.range(start, i), &starts[start..i], hashes, reference_base));
                    start = i;
                    if runs.len() > most_runs {
                        break 'read;
                    }
                }
            }
        }
        let merged = if runs.len() > most_runs {
            drop(runs);
            let order = Order::new(&read);
            drop(read);
            // The order holds every id: the ids the workers read can go before the table is filled.
            for part in &mut parts {
                part.ids = Vec::new();
            }
            merge_sorted(&order, &runs_read(walked, &parts, class_run), self.classes.len(), keep)
        } else {
            let merged = merge_runs(&runs, self.classes.len(), keep);
            drop((runs, read));
            merged
        };
        // Freeing what the walk read takes a while, and nothing waits for it.
        std::thread::spawn(move || drop((parts, objects, starts, hashes)));
        let table = ObjectTable::from_steps(&self.classes, sizing, merged.ids, merged.shapes);
        for (class, count) in self.classes.iter_mut().zip(merged.instances) {
            class.instances = count;
        }
        (table, class_class, merged.starts, merged.hashes)
    }
}

/// Records as the walk kept them: each one's id and word, paired by the sequential walk, apart in a
/// worker's part. The words give the count: a part's ids go once they are sorted.
#[derive(Clone, Copy)]
enum Records<'a> {
    Paired(&'a [[u64; 2]]),
    Apart(&'a [u64], &'a [u64]),
}

impl<'a> Records<'a> {
    fn len(self) -> usize {
        match self {
            Records::Paired(records) => records.len(),
            Records::Apart(_, words) => words.len(),
        }
    }

    #[inline]
    fn id(self, at: usize) -> u64 {
        match self {
            Records::Paired(records) => records[at][0],
            Records::Apart(ids, _) => ids[at],
        }
    }

    #[inline]
    fn word(self, at: usize) -> u64 {
        match self {
            Records::Paired(records) => records[at][1],
            Records::Apart(_, words) => words[at],
        }
    }

    fn range(self, start: usize, end: usize) -> Records<'a> {
        match self {
            Records::Paired(records) => Records::Paired(&records[start..end]),
            Records::Apart(ids, words) => Records::Apart(&ids[start..end], &words[start..end]),
        }
    }
}

/// A run of records, in id order once the runs are split: the records, where each one's references start
/// (or its hash slot), the hashes the slots are in, and what to add to a reference start.
type Run<'a> = (Records<'a>, &'a [u32], &'a [[u64; 2]], u32);

/// Every run of records as read, in file order: the sequential walk's, each part's, the class objects'.
fn runs_read<'a>(walked: Run<'a>, parts: &'a [Kept], classes: Run<'a>) -> Vec<Run<'a>> {
    let parts = parts.iter().map(|part| {
        (Records::Apart(&part.ids, &part.words), &part.starts[..], &part.hashes[..], part.reference_base)
    });
    std::iter::once(walked).chain(parts).chain([classes]).filter(|run| run.0.len() > 0).collect()
}

/// The merge of sorted runs as stretches in output order, `(run, start, end)`: id order, an earlier run
/// first on equal ids, which is a stable sort. A stretch runs from the smallest head up to the next one.
fn merge_stretches(runs: &[Run]) -> Vec<(usize, usize, usize)> {
    let mut at = vec![0usize; runs.len()];
    let head = |run: usize, at: &[usize]| {
        (at[run] < runs[run].0.len()).then(|| Reverse((runs[run].0.id(at[run]), run)))
    };
    let mut heads: BinaryHeap<Reverse<(u64, usize)>> =
        (0..runs.len()).filter_map(|run| head(run, &at)).collect();
    let mut stretches = Vec::new();
    while let Some(Reverse((_, run))) = heads.pop() {
        let (records, rest) = (runs[run].0, runs[run].0.len() - at[run]);
        let len = match heads.peek() {
            None => rest,
            Some(&Reverse(next)) => {
                // The records of this run before the next head, by halving.
                let (mut lo, mut hi) = (at[run], records.len());
                while lo < hi {
                    let mid = lo + (hi - lo) / 2;
                    if (records.id(mid), run) < next {
                        lo = mid + 1;
                    } else {
                        hi = mid;
                    }
                }
                (lo - at[run]).max(1)
            }
        };
        stretches.push((run, at[run], at[run] + len));
        at[run] += len;
        heads.extend(head(run, &at));
    }
    stretches
}

/// Runs shorter than this on average are not merged: the records are sorted.
const FRAGMENTED_RUN_LEN: usize = 64;
/// Up to this many runs are merged whatever their length.
const MIN_FRAGMENTED_RUNS: usize = 1024;
/// Sorted keys a worker counts and fills at a time.
const KEY_UNIT: usize = 1 << 16;
/// Records a worker buckets at a time.
const BUCKET_UNIT: usize = 1 << 20;
/// Key buckets per worker, so an uneven one does not hold the others up.
const BUCKETS_PER_WORKER: usize = 8;
/// Ids sampled per bucket to place the bucket bounds.
const SAMPLES_PER_BUCKET: usize = 256;

/// A sort key: an id's steps above the lowest id over the record's place among all records, so keys
/// sort by id, the earlier record first. One 8-byte word while both fit, else two, the steps first.
trait Key: Copy + Ord + Send + Sync {
    /// 8-byte words in a key.
    const WORDS: usize;
    fn pack(step: u64, place: u64, place_bits: u32) -> Self;
    fn step(self, place_bits: u32) -> u64;
    fn place(self, place_bits: u32) -> u64;
    /// Write the key as words `at..at + WORDS`.
    fn put(self, words: &[AtomicU64], at: usize);
    /// The words as keys.
    fn keys(words: &mut [u64]) -> &mut [Self];
}

impl Key for u64 {
    const WORDS: usize = 1;

    fn pack(step: u64, place: u64, place_bits: u32) -> u64 {
        step << place_bits | place
    }

    fn step(self, place_bits: u32) -> u64 {
        self >> place_bits
    }

    fn place(self, place_bits: u32) -> u64 {
        self & ((1 << place_bits) - 1)
    }

    fn put(self, words: &[AtomicU64], at: usize) {
        words[at].store(self, Relaxed);
    }

    fn keys(words: &mut [u64]) -> &mut [u64] {
        words
    }
}

impl Key for [u64; 2] {
    const WORDS: usize = 2;

    fn pack(step: u64, place: u64, _: u32) -> [u64; 2] {
        [step, place]
    }

    fn step(self, _: u32) -> u64 {
        self[0]
    }

    fn place(self, _: u32) -> u64 {
        self[1]
    }

    fn put(self, words: &[AtomicU64], at: usize) {
        words[at].store(self[0], Relaxed);
        words[at + 1].store(self[1], Relaxed);
    }

    fn keys(words: &mut [u64]) -> &mut [[u64; 2]] {
        words.as_chunks_mut().0
    }
}

/// Every record's key in id order, one of each id kept (the first), as 8-byte words.
struct Order {
    keys: Column<u64>,
    /// A key is two words.
    wide: bool,
    /// The lowest id, and how far an id's distance above it shifts down to its steps.
    base: u64,
    shift: u32,
    place_bits: u32,
    /// Each run's first place, then the record count.
    firsts: Vec<u64>,
}

impl Order {
    fn new(read: &[Run]) -> Order {
        let mut firsts = vec![0u64];
        for run in read {
            firsts.push(firsts[firsts.len() - 1] + run.0.len() as u64);
        }
        let total = firsts[read.len()];
        // Lowest and highest id, and whether every id is a whole number of 8-byte steps from the first.
        let first = read.first().map_or(0, |run| run.0.id(0));
        let spans = parallel::items(read, |run| {
            (0..run.0.len())
                .map(|at| run.0.id(at))
                .fold((u64::MAX, 0, 0), |(min, max, off), id| (min.min(id), max.max(id), off | (id ^ first)))
        });
        let (base, max, off) = spans
            .into_iter()
            .fold((u64::MAX, 0, 0), |(min, max, off), span| (min.min(span.0), max.max(span.1), off | span.2));
        let shift = if off.trailing_zeros() >= 3 { 3 } else { 0 };
        let place_bits = u64::BITS - total.leading_zeros();
        let step_bits = u64::BITS - ((max - base) >> shift).leading_zeros();
        let wide = step_bits + place_bits > u64::BITS;
        let mut order = Order { keys: Column::with_capacity(0), wide, base, shift, place_bits, firsts };
        order.keys = if wide { order.sorted::<[u64; 2]>(read) } else { order.sorted::<u64>(read) };
        order
    }

    /// The keys of `read` sorted, later records of an id dropped. Keys go into buckets by id, bounds drawn
    /// from a sample, and the workers sort a bucket each.
    fn sorted<K: Key>(&self, read: &[Run]) -> Column<u64> {
        let total = self.firsts[read.len()] as usize;
        let buckets = parallel::threads() * BUCKETS_PER_WORKER;
        let step = (total / (buckets * SAMPLES_PER_BUCKET)).max(1);
        let mut sample: Vec<u64> =
            read.iter().flat_map(|run| (0..run.0.len()).step_by(step).map(|at| run.0.id(at))).collect();
        sample.sort_unstable();
        let bounds: Vec<u64> = (1..buckets).map(|bucket| sample[bucket * sample.len() / buckets]).collect();
        let bucket_of = |id: u64| bounds.partition_point(|&bound| bound <= id);
        let units: Vec<(usize, usize, usize)> = read
            .iter()
            .enumerate()
            .flat_map(|(run, records)| {
                let len = records.0.len();
                (0..len).step_by(BUCKET_UNIT).map(move |lo| (run, lo, (lo + BUCKET_UNIT).min(len)))
            })
            .collect();
        let counts = parallel::items(&units, |&(run, lo, hi)| {
            let mut counts = vec![0usize; buckets];
            for at in lo..hi {
                counts[bucket_of(read[run].0.id(at))] += 1;
            }
            counts
        });
        // Each unit's first place in each bucket: buckets in order, the units in order inside one.
        let mut next = 0;
        let mut ends = Vec::with_capacity(buckets);
        let mut places = vec![vec![0usize; buckets]; units.len()];
        for bucket in 0..buckets {
            for (unit, counts) in counts.iter().enumerate() {
                places[unit][bucket] = next;
                next += counts[bucket];
            }
            ends.push(next);
        }
        let mut column = Column::<u64>::zeroed(total * K::WORDS);
        {
            let words = column.atomics();
            let filling: Vec<_> = units.iter().zip(places).collect();
            parallel::items(&filling, |&(&(run, lo, hi), ref places)| {
                let mut places = places.clone();
                for (place, index) in (self.firsts[run] + lo as u64..).zip(lo..hi) {
                    let id = read[run].0.id(index);
                    let at = &mut places[bucket_of(id)];
                    K::pack((id - self.base) >> self.shift, place, self.place_bits)
                        .put(words, *at * K::WORDS);
                    *at += 1;
                }
            });
        }
        let keys = K::keys(&mut column);
        {
            let mut rest = &mut keys[..];
            let mut sorting = Vec::with_capacity(buckets);
            let mut start = 0;
            for end in ends {
                let (bucket, tail) = std::mem::take(&mut rest).split_at_mut(end - start);
                (rest, start) = (tail, end);
                sorting.push(Mutex::new(bucket));
            }
            parallel::items(&sorting, |bucket| bucket.lock().expect("worker panicked").sort_unstable());
        }
        // Later records of an id go: few, so the keys between them close up in turn.
        let bits = self.place_bits;
        let repeats: Vec<usize> = parallel::ranges(keys.len(), |lo, hi| {
            (lo.max(1)..hi).filter(|&at| keys[at].step(bits) == keys[at - 1].step(bits)).collect::<Vec<_>>()
        })
        .concat();
        let mut kept = repeats.first().copied().unwrap_or(keys.len());
        for (i, &repeat) in repeats.iter().enumerate() {
            let next = repeats.get(i + 1).copied().unwrap_or(keys.len());
            keys.copy_within(repeat + 1..next, kept);
            kept += next - repeat - 1;
        }
        column.truncate(kept * K::WORDS);
        column.shrink_to_fit();
        column
    }

    fn len(&self) -> usize {
        self.keys.len() / if self.wide { 2 } else { 1 }
    }

    /// The steps and place of key `at`.
    fn key(&self, at: usize) -> (u64, u64) {
        if self.wide {
            (self.keys[2 * at], self.keys[2 * at + 1])
        } else {
            let key = self.keys[at];
            (Key::step(key, self.place_bits), Key::place(key, self.place_bits))
        }
    }

    fn id(&self, at: usize) -> u64 {
        self.base + (self.key(at).0 << self.shift)
    }

    /// The table's ids: the keys' steps as they are while they are 8-byte ones within four bytes, which
    /// is what the lookup takes; else whole.
    fn ids(&self) -> TableIds {
        let last_step = self.len().checked_sub(1).map_or(0, |last| self.key(last).0);
        if self.shift == 3 && u32::try_from(last_step).is_ok() {
            return TableIds::Steps(self.base, Blocked::new(self.len(), |at| self.key(at).0));
        }
        let mut wide = Column::<u64>::zeroed(self.len());
        parallel::chunks(&mut wide, |start, part| {
            for (id, at) in part.iter_mut().zip(start..) {
                *id = self.id(at);
            }
        });
        TableIds::Wide(wide)
    }
}

/// The table's columns from records in no order, by their sorted keys; the ids of `read` are not looked at.
fn merge_sorted(order: &Order, read: &[Run], class_count: usize, keep: bool) -> Merged {
    let end = |unit: usize| ((unit + 1) * KEY_UNIT).min(order.len());
    let entries = |unit: usize| {
        (unit * KEY_UNIT..end(unit)).map(|at| {
            let (step, place) = order.key(at);
            let run = order.firsts.partition_point(|&first| first <= place) - 1;
            let ((records, starts, hashes, reference_base), index) =
                (read[run], (place - order.firsts[run]) as usize);
            (order.base + (step << order.shift), records.word(index), starts[index], hashes, reference_base)
        })
    };
    let last = |unit: usize| order.id(end(unit) - 1);
    merge_table(order.len().div_ceil(KEY_UNIT), entries, last, class_count, keep, Some(order.ids()))
}

/// The table's columns from runs in id order, merged.
fn merge_runs(runs: &[Run], class_count: usize, keep: bool) -> Merged {
    let stretches = merge_stretches(runs);
    let entries = |unit: usize| {
        let (run, start, end) = stretches[unit];
        let (records, starts, hashes, reference_base) = runs[run];
        (start..end).map(move |at| (records.id(at), records.word(at), starts[at], hashes, reference_base))
    };
    let last = |unit: usize| {
        let (run, _, end) = stretches[unit];
        runs[run].0.id(end - 1)
    };
    merge_table(stretches.len(), entries, last, class_count, keep, None)
}

/// A record in id order: its id and word, where its references start (or its hash slot), the hashes the
/// slot is in, and what to add to a reference start.
type Entry<'a> = (u64, u64, u32, &'a [[u64; 2]], u32);

/// The object table's columns, merged from the walk's runs.
struct Merged {
    ids: TableIds,
    shapes: Shapes,
    starts: Column<u32>,
    hashes: Column<[u64; 2]>,
    instances: Vec<u64>,
}

/// The table's columns from `units` stretches of records in id order, `entries(unit)` each and `last(unit)`
/// its last id, one of each id kept (the first), over the workers: each stretch is counted first, so every
/// worker knows where its stretches' objects go. `ids`, when given, are the table's ids already.
fn merge_table<'a, I: Iterator<Item = Entry<'a>>>(
    units: usize,
    entries: impl Fn(usize) -> I + Sync,
    last: impl Fn(usize) -> u64 + Sync,
    class_count: usize,
    keep: bool,
    ids: Option<TableIds>,
) -> Merged {
    let last_id = |k: usize| k.checked_sub(1).map(&last);
    let base = if units == 0 { 0 } else { entries(0).next().map_or(0, |entry| entry.0) };
    let fits = |id: u64| (id - base).trailing_zeros() >= 3 && u32::try_from((id - base) >> 3).is_ok();
    // Kept objects and primitive arrays per stretch, and whether its ids fit four bytes.
    let counts: Vec<(usize, usize, bool)> = parallel::ranges(units, |lo, hi| {
        (lo..hi)
            .map(|k| {
                let (mut previous, mut kept, mut arrays, mut fit) = (last_id(k), 0, 0, true);
                for (id, word, ..) in entries(k) {
                    if previous != Some(id) {
                        kept += 1;
                        arrays += usize::from(word_kind(word) == Kind::PrimitiveArray);
                        fit &= fits(id);
                    }
                    previous = Some(id);
                }
                (kept, arrays, fit)
            })
            .collect::<Vec<_>>()
    })
    .concat();
    let total: usize = counts.iter().map(|count| count.0).sum();
    let total_arrays: usize = counts.iter().map(|count| count.1).sum();
    // Ids not given go in as four-byte steps when they all fit, else whole.
    let narrow = ids.is_none() && counts.iter().all(|count| count.2);
    let whole = ids.is_none() && !narrow;
    let mut steps = Column::<u32>::zeroed(if narrow { total } else { 0 });
    let mut wide = Column::<u64>::zeroed(if whole { total } else { 0 });
    let packing = Packing::new(class_count);
    let mut words = Column::<u32>::zeroed(total);
    let mut starts = Column::<u32>::zeroed(if keep { total } else { 0 });
    let mut array_values = Column::<[u64; 2]>::zeroed(total_arrays);
    // Stretches in groups of about equal size, one per worker, each writing its own slice of every column.
    let groups = parallel::threads().max(1) * 4;
    let step = total.div_ceil(groups).max(1);
    let mut bounds = vec![0usize];
    let mut filled = 0;
    for (k, count) in counts.iter().enumerate() {
        filled += count.0;
        if filled >= step * bounds.len() && k + 1 < units {
            bounds.push(k + 1);
        }
    }
    bounds.push(units);
    let mut tasks = Vec::new();
    let (mut id_rest, mut wide_rest) = (&mut steps[..], &mut wide[..]);
    let (mut shape_rest, mut start_rest) = (&mut words[..], &mut starts[..]);
    let mut first_object = 0;
    let mut value_rest = &mut array_values[..];
    for pair in bounds.windows(2) {
        let (lo, hi) = (pair[0], pair[1]);
        let objects: usize = counts[lo..hi].iter().map(|count| count.0).sum();
        let arrays: usize = counts[lo..hi].iter().map(|count| count.1).sum();
        let (id_part, rest) = std::mem::take(&mut id_rest).split_at_mut(if narrow { objects } else { 0 });
        id_rest = rest;
        let (wide_part, rest) = std::mem::take(&mut wide_rest).split_at_mut(if whole { objects } else { 0 });
        wide_rest = rest;
        let (shape_part, rest) = std::mem::take(&mut shape_rest).split_at_mut(objects);
        shape_rest = rest;
        let (start_part, rest) = std::mem::take(&mut start_rest).split_at_mut(if keep { objects } else { 0 });
        start_rest = rest;
        let (value_part, rest) = std::mem::take(&mut value_rest).split_at_mut(arrays);
        value_rest = rest;
        let (entries, last_id) = (&entries, &last_id);
        tasks.push(move || {
            let (mut instances, mut long) = (vec![0u64; class_count], Vec::new());
            let (mut at, mut array_at, mut previous) = (0, 0, last_id(lo));
            for unit in lo..hi {
                for (id, record, start, hashes, reference_base) in entries(unit) {
                    if previous == Some(id) {
                        continue;
                    }
                    previous = Some(id);
                    let (class, kind) = (word_class(record), word_kind(record));
                    instances[class as usize] += 1;
                    if kind == Kind::PrimitiveArray {
                        value_part[array_at] = hashes[start as usize];
                        array_at += 1;
                    }
                    let start = start.wrapping_add(reference_base);
                    if narrow {
                        id_part[at] = ((id - base) >> 3) as u32;
                    } else if whole {
                        wide_part[at] = id;
                    }
                    // An instance's size comes from its class.
                    let len = if kind == Kind::Instance { 0 } else { record as u32 };
                    let (word, too_long) = packing.pack(class, kind, len);
                    shape_part[at] = word;
                    long.extend(too_long.map(|len| ((first_object + at) as u32, len)));
                    if keep {
                        start_part[at] = start;
                    }
                    at += 1;
                }
            }
            (instances, long)
        });
        first_object += objects;
    }
    let parts = parallel::run_all(tasks);
    let (mut instances, mut long) = (vec![0u64; class_count], Vec::new());
    for (part, part_long) in parts {
        instances.iter_mut().zip(part).for_each(|(total, count)| *total += count);
        long.extend(part_long);
    }
    let ids = match ids {
        Some(ids) => ids,
        None if narrow => TableIds::steps(base, &steps),
        None => TableIds::Wide(wide),
    };
    Merged { ids, shapes: Shapes::new(words, packing, long), starts, hashes: array_values, instances }
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

/// Footprints and shallow sizes under `sizing` for layouts already fixed, in the same order and with the
/// same depth cap as [`layout`].
fn size_classes(classes: &mut [Class], sizing: &Sizing) {
    let mut sized = vec![false; classes.len()];
    for i in 0..classes.len() {
        size_class(classes, i as u32, &mut sized, sizing, 0);
    }
}

fn size_class(classes: &mut [Class], idx: u32, sized: &mut [bool], sizing: &Sizing, depth: usize) {
    let i = idx as usize;
    if sized[i] {
        return;
    }
    sized[i] = true;
    let mut footprint: u64 =
        classes[i].fields.iter().map(|field| u64::from(sizing.field_size(field.ty))).sum();
    let super_idx = classes[i].superclass;
    if super_idx != NONE && depth < MAX_CLASS_DEPTH {
        size_class(classes, super_idx, sized, sizing, depth + 1);
        footprint += u64::from(classes[super_idx as usize].footprint);
    }
    let class = &mut classes[i];
    class.footprint = footprint.min(u64::from(u32::MAX)) as u32;
    class.shallow = sizing.instance_size(footprint);
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
