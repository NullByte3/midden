//! Pass one: everything but the references. Symbols, classes and their
//! layouts, the object table with shallow sizes, GC roots and thread stacks.

use std::collections::{HashMap, HashSet};
use std::io;
use std::sync::Arc;

use super::dump::{
    self, Buckets, Class, Dump, FastMap, Field, Kind, MAX_CLASS_DEPTH, NONE, Object, RefKind, Slot, Static,
};
use super::graph::LOADER;
use super::hprof::{self, Body, ClassDump, Frame, Header, Reader, Root, RootKind, Sink, Ty, View, Walked};
use super::parallel;
use super::sizes::{SizeMode, Sizing};
use super::source::Progress;
use crate::error::{Error, Result};

/// Primitive array classes by `Ty as usize`; room for every HPROF basic-type tag (long, the largest, is 11).
const BASIC_TYPE_SLOTS: usize = 12;

#[derive(Default)]
pub struct Indexer {
    id_size: u32,
    symbols: FastMap<u64, String>,
    classes: Vec<Class>,
    class_by_id: FastMap<u64, u32>,
    class_by_serial: HashMap<u32, u32>,
    class_dumps: Vec<ClassDump>,
    objects: Vec<Object>,
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
            prim_array_classes: [NONE; BASIC_TYPE_SLOTS],
            last_class: (0, NONE),
            ..Indexer::default()
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
}

/// The object callbacks: the same code for the sequential walk and a worker's part.
macro_rules! object_callbacks {
    () => {
        fn instance(&mut self, id: u64, class_id: u64, body: Body) -> io::Result<()> {
            let class = self.class_index(class_id);
            self.objects.push(Object { id, class, len: body.len() as u32, shallow: 0, kind: Kind::Instance });
            Ok(())
        }

        fn object_array(&mut self, id: u64, class_id: u64, len: u32, _body: Body) -> io::Result<()> {
            let class = self.class_index(class_id);
            self.objects.push(Object { id, class, len, shallow: 0, kind: Kind::ObjectArray });
            Ok(())
        }

        fn primitive_array(&mut self, id: u64, ty: Ty, len: u32, _body: Body) -> io::Result<()> {
            let class = self.primitive_array_class(ty);
            self.objects.push(Object { id, class, len, shallow: 0, kind: Kind::PrimitiveArray });
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
        self.class_index(class.id);
        self.class_dumps.push(class);
    }

    object_callbacks!();
}

/// One run of heap segments, read on a worker. A class whose load record is not seen yet is left
/// to the sequential walk, which mints placeholders in file order.
struct Part<'a> {
    class_by_id: &'a FastMap<u64, u32>,
    prim_array_classes: [u32; BASIC_TYPE_SLOTS],
    missed: bool,
    class_dumps: Vec<ClassDump>,
    objects: Vec<Object>,
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
}

impl Sink for Part<'_> {
    fn root(&mut self, root: Root) {
        self.roots.push(root);
    }

    fn class(&mut self, class: ClassDump) {
        self.class_dumps.push(class);
    }

    object_callbacks!();
}

impl Indexer {
    /// Read the stepped-over segments, a run of adjacent ones per worker, merged in file order. False
    /// sends the file back to the sequential walk: segments were also walked in place, one runs past
    /// the end, a part fails to parse, or a class needs a placeholder only file order can mint.
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
        let mut prim_array_classes = [NONE; BASIC_TYPE_SLOTS];
        for ty in [Ty::Bool, Ty::Char, Ty::Float, Ty::Double, Ty::Byte, Ty::Short, Ty::Int, Ty::Long] {
            let name = format!("{}[]", ty.name());
            prim_array_classes[ty as usize] = class_named(&self.classes, &name).unwrap_or(NONE);
        }
        progress.begin("indexing objects", runs.iter().map(|&(start, end)| end - start).sum());
        let (id_size, class_by_id) = (self.id_size, &self.class_by_id);
        let parts = parallel::items(&runs, |&(start, end)| {
            let mut reader = Reader::open_at(view, start, id_size).ok()?;
            reader.progress = progress.counter(start);
            let mut part = Part {
                class_by_id,
                prim_array_classes,
                missed: false,
                class_dumps: Vec::new(),
                objects: Vec::new(),
                roots: Vec::new(),
            };
            let mut part_walked = Walked::default();
            hprof::heap(&mut reader, Some(end), &mut part, &mut part_walked).ok()?;
            (!part.missed).then_some((part.class_dumps, part.objects, part.roots, part_walked))
        });
        let Some(parts) = parts.into_iter().collect::<Option<Vec<_>>>() else { return false };
        self.objects.reserve(parts.iter().map(|(_, objects, _, _)| objects.len()).sum());
        for (class_dumps, objects, roots, part_walked) in parts {
            for class_dump in class_dumps {
                self.class(class_dump);
            }
            self.objects.extend(objects);
            self.roots.extend(roots);
            walked.chunks.extend(part_walked.chunks);
            walked.pieces.extend(part_walked.pieces);
        }
        true
    }

    /// Resolve layouts, size every object, sort the table, resolve the roots.
    pub fn finish(
        mut self,
        path: &str,
        reader: &Reader,
        header: Header,
        walked: Walked,
        mode: SizeMode,
    ) -> Result<Dump> {
        let mut names = self.resolve_class_dumps();
        let value_label = intern_str(&mut names, "value");
        let name_label = intern_str(&mut names, "name");

        // Sizes depend on the address range.
        let max_id = self.objects.iter().map(|object| object.id).max().unwrap_or(0);
        let sizing = Sizing::resolve(mode, self.id_size, max_id);
        self.lay_out_classes(&sizing, &names);
        let class_class = self.size_objects(&sizing);
        // u32 indices keep NONE free and the graph root one past the objects; labels stay below LOADER.
        let counts = [
            ("objects", self.objects.len(), NONE - 1),
            ("classes", self.classes.len(), NONE),
            ("field names", names.len(), LOADER),
        ];
        for (what, count, limit) in counts {
            if count > limit as usize {
                return Err(Error::Dump(format!("too many {what} for midden ({count}, limit {limit})")));
            }
        }
        let lookup = Buckets::build(&self.objects);
        let string_class = class_named(&self.classes, "java.lang.String").unwrap_or(NONE);

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
            names,
            symbols: self.symbols,
            classes: self.classes,
            objects: self.objects,
            roots: Vec::new(),
            dangling_roots: 0,
            marked_unreachable: 0,
            threads: Vec::new(),
            traces: self.traces,
            frames: self.frames,
            class_by_serial: self.class_by_serial,
            lookup,
            class_class,
            string_class,
            value_label,
            name_label,
        };
        resolve_roots(&mut dump, self.roots);
        Ok(dump)
    }

    /// Apply the class dumps to their classes, returning the interned field names.
    fn resolve_class_dumps(&mut self) -> Vec<String> {
        // Names are interned by text: one `value` label whatever symbol ids the file used.
        let mut names: Vec<String> = Vec::new();
        let mut name_by_text: HashMap<String, u32> = HashMap::new();
        let mut name_by_id: FastMap<u64, u32> = FastMap::default();
        let mut intern = |id: u64, symbols: &FastMap<u64, String>| -> u32 {
            *name_by_id.entry(id).or_insert_with(|| {
                let text = symbols.get(&id).cloned().unwrap_or_else(|| format!("<0x{id:x}>"));
                *name_by_text.entry(text.clone()).or_insert_with(|| push(&mut names, text))
            })
        };
        for class_dump in std::mem::take(&mut self.class_dumps) {
            let idx = self.class_index(class_dump.id) as usize;
            let superclass =
                if class_dump.super_id == 0 { NONE } else { self.class_index(class_dump.super_id) };
            let class = &mut self.classes[idx];
            class.superclass = superclass;
            class.loader = class_dump.loader_id;
            class.dumped = true;
            class.fields = class_dump
                .fields
                .iter()
                .map(|&(name_id, ty)| Field { name: intern(name_id, &self.symbols), ty })
                .collect();
            class.statics = class_dump
                .statics
                .iter()
                .map(|&(name_id, ty, value)| Static { name: intern(name_id, &self.symbols), ty, value })
                .collect();
        }
        names
    }

    fn lay_out_classes(&mut self, sizing: &Sizing, names: &[String]) {
        let reference = class_named(&self.classes, "java.lang.ref.Reference");
        let referent = names.iter().position(|name| name == "referent").map(|i| i as u32);
        let class_count = self.classes.len();
        let mut laid_out = vec![false; class_count];
        for i in 0..class_count {
            layout(&mut self.classes, i as u32, &mut laid_out, self.id_size, sizing, reference, referent, 0);
        }
        mark_reference_kinds(&mut self.classes);
    }

    /// Add the class objects, sort the table, size every object and count instances.
    /// Returns the `java.lang.Class` class.
    fn size_objects(&mut self, sizing: &Sizing) -> u32 {
        // Class objects live in the object table too: statics are edges and
        // sticky-class roots point at them.
        let class_class = class_named(&self.classes, "java.lang.Class")
            .unwrap_or_else(|| push(&mut self.classes, Class::placeholder("java.lang.Class".to_string(), 0)));
        for class in self.classes.iter().filter(|class| class.dumped) {
            let statics_size: u64 =
                class.statics.iter().map(|field| u64::from(sizing.field_size(field.ty))).sum();
            let (id, shallow) = (class.id, sizing.instance_size(statics_size));
            self.objects.push(Object { id, class: class_class, len: 0, shallow, kind: Kind::Class });
        }
        // One sort by id, dropping duplicates. HotSpot writes by address in runs, so the stable sort is
        // nearly free.
        self.objects.sort_by_key(|object| object.id);
        self.objects.dedup_by_key(|object| object.id);
        for object in &mut self.objects {
            let class = &self.classes[object.class as usize];
            object.shallow = match object.kind {
                Kind::Instance => class.shallow,
                Kind::ObjectArray => sizing.array_size(u64::from(object.len), sizing.ref_size),
                Kind::PrimitiveArray => sizing.array_size(
                    u64::from(object.len),
                    class.element_type.map_or(1, |ty| sizing.field_size(ty)),
                ),
                Kind::Class => object.shallow,
            };
        }
        for object in &self.objects {
            self.classes[object.class as usize].instances += 1;
        }
        class_class
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
