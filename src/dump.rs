//! The indexed dump: classes with their layouts, the object table, roots,
//! threads and stacks. Built by `index.rs`, read by everything after.

use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};

use super::hash::GOLDEN_RATIO;
use super::hprof::{Frame, Header, Piece, Root, Ty, Value};
use super::sizes::Sizing;

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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Kind {
    Instance,
    ObjectArray,
    PrimitiveArray,
    Class,
}

impl Kind {
    pub const ALL: [Kind; 4] = [Kind::Instance, Kind::ObjectArray, Kind::PrimitiveArray, Kind::Class];
}

/// One heap object. `len` is field bytes for instances, elements for arrays.
#[derive(Clone, Copy, Debug)]
pub struct Object {
    pub id: u64,
    pub class: u32,
    pub len: u32,
    pub shallow: u32,
    pub kind: Kind,
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
    pub symbols: FastMap<u64, String>,
    pub classes: Vec<Class>,
    /// Sorted by id.
    pub objects: Vec<Object>,
    pub roots: Vec<(u32, Root)>,
    pub dangling_roots: u64,
    /// Objects ART marked unreachable: counted, never roots.
    pub marked_unreachable: u64,
    pub threads: Vec<Thread>,
    pub traces: HashMap<u32, Trace>,
    pub frames: FastMap<u64, Frame>,
    pub class_by_serial: HashMap<u32, u32>,
    pub lookup: Buckets,
    /// `java.lang.Class`, `java.lang.String`, and the `value` / `name` labels.
    pub class_class: u32,
    pub string_class: u32,
    pub value_label: u32,
    pub name_label: u32,
}

/// Buckets widen until the id span needs at most this many.
const MAX_BUCKETS: u64 = 1 << 22;

/// The object table bucketed by address range: a short binary search per id, not a hash lookup.
pub struct Buckets {
    min: u64,
    max: u64,
    shift: u32,
    starts: Vec<u32>,
}

impl Buckets {
    pub fn build(objects: &[Object]) -> Buckets {
        let (min, max) = match (objects.first(), objects.last()) {
            (Some(first), Some(last)) => (first.id, last.id),
            _ => return Buckets { min: 1, max: 0, shift: 0, starts: vec![0, 0] },
        };
        let span = max - min + 1;
        let mut shift = 0;
        while (span >> shift) > MAX_BUCKETS {
            shift += 1;
        }
        let bucket_count = ((span - 1) >> shift) as usize + 1;
        let mut starts = vec![0u32; bucket_count + 1];
        for object in objects {
            starts[((object.id - min) >> shift) as usize + 1] += 1;
        }
        for i in 0..bucket_count {
            starts[i + 1] += starts[i];
        }
        Buckets { min, max, shift, starts }
    }

    pub fn find(&self, objects: &[Object], id: u64) -> Option<u32> {
        if id < self.min || id > self.max {
            return None;
        }
        let bucket = ((id - self.min) >> self.shift) as usize;
        let (lo, hi) = (self.starts[bucket] as usize, self.starts[bucket + 1] as usize);
        objects[lo..hi].binary_search_by_key(&id, |o| o.id).ok().map(|i| (lo + i) as u32)
    }
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
        self.lookup.find(&self.objects, id)
    }

    pub fn class_of(&self, object: u32) -> &Class {
        &self.classes[self.objects[object as usize].class as usize]
    }

    pub fn class_name(&self, object: u32) -> &str {
        &self.class_of(object).name
    }

    pub fn class_by_serial(&self, serial: u32) -> Option<u32> {
        self.class_by_serial.get(&serial).copied()
    }

    /// The class with exactly this name that has a layout, else any with the name.
    pub fn class_named(&self, name: &str) -> Option<u32> {
        let named = |class: &Class| class.name == name;
        let dumped = self.classes.iter().position(|class| named(class) && class.dumped);
        dumped.or_else(|| self.classes.iter().position(named)).map(|i| i as u32)
    }

    /// Whether `class` is `base` or extends it.
    pub fn extends(&self, class: u32, base: u32) -> bool {
        self.ancestry(class).any(|ancestor| ancestor == base)
    }

    /// A class and its superclasses, nearest first.
    pub fn ancestry(&self, class: u32) -> impl Iterator<Item = u32> + '_ {
        let known = |class: u32| (class != NONE).then_some(class);
        std::iter::successors(known(class), move |&current| known(self.classes[current as usize].superclass))
            .take(MAX_CLASS_DEPTH)
    }

    /// Index of an interned field name.
    pub fn name_id(&self, name: &str) -> Option<u32> {
        self.names.iter().position(|interned| interned == name).map(|i| i as u32)
    }

    /// Instance field layout for `class`: `(name, type, offset)` up the chain.
    pub fn field_layout(&self, class: u32) -> Vec<(u32, Ty, u32)> {
        let mut out = Vec::new();
        let mut offset = 0u32;
        for ancestor in self.ancestry(class) {
            for field in &self.classes[ancestor as usize].fields {
                out.push((field.name, field.ty, offset));
                offset += field.ty.size(self.header.id_size);
            }
        }
        out
    }

    /// Offset and type of the instance field called `name`, if `class` has one.
    pub fn field_offset(&self, class: u32, name: &str) -> Option<(u32, Ty)> {
        let id = self.name_id(name)?;
        self.field_layout(class)
            .into_iter()
            .find(|&(field_id, _, _)| field_id == id)
            .map(|(_, ty, offset)| (offset, ty))
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
        let method = self.symbols.get(&frame.method_id).map_or("?", String::as_str);
        let source = self.symbols.get(&frame.source_id).map_or("", String::as_str);
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
        self.objects.iter().map(|object| u64::from(object.shallow)).sum()
    }
}
