//! HPROF (JAVA PROFILE 1.0.x plus Android tags) read as a stream, after `HotSpot`'s heapDumper.cpp and
//! ART's hprof.cc. Fields are big-endian; ids are `id_size` bytes (4 or 8, from the header).

mod archive;
pub mod gunzip;
mod reader;

pub use reader::{Reader, View};

use std::io;

use crate::error::{Error, Result};

/// A field or array element type; the discriminant is its HPROF basic-type tag.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
#[repr(u8)]
pub enum Ty {
    Object = 2,
    Bool = 4,
    Char,
    Float,
    Double,
    Byte,
    Short,
    Int,
    Long,
}

impl Ty {
    pub fn from_tag(tag: u8) -> Option<Ty> {
        Some(match tag {
            2 => Ty::Object,
            4 => Ty::Bool,
            5 => Ty::Char,
            6 => Ty::Float,
            7 => Ty::Double,
            8 => Ty::Byte,
            9 => Ty::Short,
            10 => Ty::Int,
            11 => Ty::Long,
            _ => return None,
        })
    }

    pub fn tag(self) -> u8 {
        self as u8
    }

    /// Bytes a value of this type takes in the file.
    pub fn size(self, id_size: u32) -> u32 {
        match self {
            Ty::Object => id_size,
            Ty::Bool | Ty::Byte => 1,
            Ty::Char | Ty::Short => 2,
            Ty::Float | Ty::Int => 4,
            Ty::Double | Ty::Long => 8,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Ty::Object => "object",
            Ty::Bool => "boolean",
            Ty::Char => "char",
            Ty::Float => "float",
            Ty::Double => "double",
            Ty::Byte => "byte",
            Ty::Short => "short",
            Ty::Int => "int",
            Ty::Long => "long",
        }
    }

    /// From the JVM descriptor letter, as in `[I`.
    pub fn from_descriptor(letter: u8) -> Option<Ty> {
        Some(match letter {
            b'Z' => Ty::Bool,
            b'C' => Ty::Char,
            b'F' => Ty::Float,
            b'D' => Ty::Double,
            b'B' => Ty::Byte,
            b'S' => Ty::Short,
            b'I' => Ty::Int,
            b'J' => Ty::Long,
            _ => return None,
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Value {
    Ref(u64),
    Bool(bool),
    Char(u16),
    Float(f32),
    Double(f64),
    Byte(i8),
    Short(i16),
    Int(i32),
    Long(i64),
}

impl Value {
    pub fn decode(ty: Ty, bytes: &[u8], id_size: u32) -> Option<Value> {
        let bytes = bytes.get(..ty.size(id_size) as usize)?;
        Some(match ty {
            Ty::Object => Value::Ref(be_uint(bytes)),
            Ty::Bool => Value::Bool(bytes[0] != 0),
            Ty::Char => Value::Char(be_uint(bytes) as u16),
            Ty::Float => Value::Float(f32::from_bits(be_uint(bytes) as u32)),
            Ty::Double => Value::Double(f64::from_bits(be_uint(bytes))),
            Ty::Byte => Value::Byte(bytes[0] as i8),
            Ty::Short => Value::Short(be_uint(bytes) as i16),
            Ty::Int => Value::Int(be_uint(bytes) as i32),
            Ty::Long => Value::Long(be_uint(bytes) as i64),
        })
    }

    /// Raw bits, for the cache and for grouping equal values.
    pub fn bits(self) -> u64 {
        match self {
            Value::Ref(id) => id,
            Value::Bool(value) => u64::from(value),
            Value::Char(value) => u64::from(value),
            Value::Float(value) => u64::from(value.to_bits()),
            Value::Double(value) => value.to_bits(),
            Value::Byte(value) => value as u8 as u64,
            Value::Short(value) => value as u16 as u64,
            Value::Int(value) => value as u32 as u64,
            Value::Long(value) => value as u64,
        }
    }

    pub fn from_bits(ty: Ty, bits: u64) -> Value {
        match ty {
            Ty::Object => Value::Ref(bits),
            Ty::Bool => Value::Bool(bits != 0),
            Ty::Char => Value::Char(bits as u16),
            Ty::Float => Value::Float(f32::from_bits(bits as u32)),
            Ty::Double => Value::Double(f64::from_bits(bits)),
            Ty::Byte => Value::Byte(bits as u8 as i8),
            Ty::Short => Value::Short(bits as u16 as i16),
            Ty::Int => Value::Int(bits as u32 as i32),
            Ty::Long => Value::Long(bits as i64),
        }
    }

    /// The value as the inspector prints it.
    pub fn text(self) -> String {
        match self {
            Value::Ref(id) => format!("0x{id:x}"),
            Value::Bool(value) => value.to_string(),
            Value::Char(code) => match char::from_u32(u32::from(code)) {
                Some(ch) if !ch.is_control() => format!("'{ch}'"),
                _ => format!("\\u{code:04x}"),
            },
            Value::Float(value) => format!("{value}"),
            Value::Double(value) => format!("{value}"),
            Value::Byte(value) => value.to_string(),
            Value::Short(value) => value.to_string(),
            Value::Int(value) => value.to_string(),
            Value::Long(value) => value.to_string(),
        }
    }
}

/// Big-endian unsigned integer of 1..=8 bytes; ids and lengths are 8 or 4.
#[inline]
pub fn be_uint(bytes: &[u8]) -> u64 {
    if let Ok(array) = <[u8; 8]>::try_from(bytes) {
        return u64::from_be_bytes(array);
    }
    if let Ok(array) = <[u8; 4]>::try_from(bytes) {
        return u64::from(u32::from_be_bytes(array));
    }
    bytes.iter().fold(0u64, |acc, &byte| (acc << 8) | u64::from(byte))
}

pub struct Header {
    pub format: String,
    pub id_size: u32,
    pub timestamp_ms: u64,
}

pub struct ClassDump {
    pub id: u64,
    pub super_id: u64,
    pub loader_id: u64,
    /// `(name id, type, value)` per static field.
    pub statics: Vec<(u64, Ty, Value)>,
    /// `(name id, type)` per declared instance field, in layout order.
    pub fields: Vec<(u64, Ty)>,
}

#[derive(Clone, Copy, Debug)]
pub struct Frame {
    pub id: u64,
    pub method_id: u64,
    pub source_id: u64,
    pub class_serial: u32,
    pub line: i32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum RootKind {
    JavaFrame,
    JniLocal,
    ThreadObject,
    NativeStack,
    ThreadBlock,
    MonitorUsed,
    JniGlobal,
    StickyClass,
    InternedString,
    Debugger,
    VmInternal,
    JniMonitor,
    Finalizing,
    ReferenceCleanup,
    /// ART's "unreachable" marker: not a root, kept for the count.
    Unreachable,
    Unknown,
}

impl RootKind {
    pub const ALL: [RootKind; 16] = [
        RootKind::JavaFrame,
        RootKind::JniLocal,
        RootKind::ThreadObject,
        RootKind::NativeStack,
        RootKind::ThreadBlock,
        RootKind::MonitorUsed,
        RootKind::JniGlobal,
        RootKind::StickyClass,
        RootKind::InternedString,
        RootKind::Debugger,
        RootKind::VmInternal,
        RootKind::JniMonitor,
        RootKind::Finalizing,
        RootKind::ReferenceCleanup,
        RootKind::Unreachable,
        RootKind::Unknown,
    ];

    pub fn label(self) -> &'static str {
        match self {
            RootKind::JavaFrame => "java frame",
            RootKind::JniLocal => "jni local",
            RootKind::ThreadObject => "thread",
            RootKind::NativeStack => "native stack",
            RootKind::ThreadBlock => "thread block",
            RootKind::MonitorUsed => "busy monitor",
            RootKind::JniGlobal => "jni global",
            RootKind::StickyClass => "system class",
            RootKind::InternedString => "interned string",
            RootKind::Debugger => "debugger",
            RootKind::VmInternal => "vm internal",
            RootKind::JniMonitor => "jni monitor",
            RootKind::Finalizing => "finalizing",
            RootKind::ReferenceCleanup => "reference cleanup",
            RootKind::Unreachable => "unreachable",
            RootKind::Unknown => "unknown",
        }
    }

    pub fn cache_code(self) -> u8 {
        self as u8
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Root {
    pub id: u64,
    pub kind: RootKind,
    /// Thread serial for the thread-bound kinds; 0 otherwise.
    pub thread_serial: u32,
    /// Frame number in the thread's trace, or `u32::MAX`.
    pub frame: u32,
    /// Stack trace serial, for `ThreadObject` roots.
    pub trace_serial: u32,
}

/// An instance or array record body; the walker skips whatever the sink leaves unread.
pub struct Body<'r> {
    reader: &'r mut Reader,
    len: u64,
}

impl<'r> Body<'r> {
    pub fn len(&self) -> u64 {
        self.len
    }

    /// The whole body; arrays should use [`Body::chunks`].
    pub fn bytes(self) -> io::Result<&'r [u8]> {
        let n = usize::try_from(self.len).map_err(|_| too_big())?;
        self.reader.read_bytes(n)
    }

    pub fn chunks(self, chunk_len: usize, mut f: impl FnMut(&[u8]) -> io::Result<()>) -> io::Result<()> {
        let mut remaining = self.len;
        while remaining > 0 {
            let n = remaining.min(chunk_len as u64) as usize;
            f(self.reader.read_bytes(n)?)?;
            remaining -= n as u64;
        }
        Ok(())
    }
}

fn too_big() -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, "record body larger than addressable memory")
}

fn invalid_data(msg: String) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, msg)
}

/// Receives records as the walker meets them; a pass implements what it needs.
#[allow(unused_variables)]
pub trait Sink {
    fn utf8(&mut self, id: u64, text: &[u8]) {}
    fn load_class(&mut self, serial: u32, id: u64, name_id: u64) {}
    fn frame(&mut self, frame: Frame) {}
    fn trace(&mut self, serial: u32, thread_serial: u32, frames: &[u64]) {}
    fn root(&mut self, root: Root) {}
    fn class(&mut self, class: ClassDump) {}
    fn instance(&mut self, id: u64, class_id: u64, body: Body) -> io::Result<()> {
        Ok(())
    }
    fn object_array(&mut self, id: u64, class_id: u64, len: u32, body: Body) -> io::Result<()> {
        Ok(())
    }
    fn primitive_array(&mut self, id: u64, ty: Ty, len: u32, body: Body) -> io::Result<()> {
        Ok(())
    }
}

// Top-level record tags.
const UTF8: u8 = 0x01;
const LOAD_CLASS: u8 = 0x02;
const STACK_FRAME: u8 = 0x04;
const STACK_TRACE: u8 = 0x05;
const HEAP_DUMP: u8 = 0x0C;
const HEAP_DUMP_SEGMENT: u8 = 0x1C;
const HEAP_DUMP_END: u8 = 0x2C;

/// A top-level record header: u8 tag, u32 time offset, u32 body length.
pub const RECORD_HEADER_LEN: u64 = 9;

/// Buffer size for file reads and writes, and the step a record body is read in.
pub const IO_BUFFER_SIZE: usize = 1 << 20;

/// Heap sub-records are cut into ranges of about this size for parallel passes.
pub const CHUNK_SIZE: u64 = 32 << 20;

/// Smaller pieces with their id range, so a read for a few objects skips pieces that cannot hold them.
const PIECE_SIZE: u64 = 64 << 10;

/// A stretch of heap sub-records, and the lowest and highest object id in it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Piece {
    pub start: u64,
    pub end: u64,
    pub min: u64,
    pub max: u64,
}

impl Piece {
    fn open(start: u64) -> Piece {
        Piece { start, end: u64::MAX, min: u64::MAX, max: 0 }
    }
}

/// What a walk learned about the file's shape.
#[derive(Default, Debug, Clone, PartialEq, Eq)]
pub struct Walked {
    /// The file ended inside a record.
    pub truncated: bool,
    /// Byte ranges of heap sub-records, each starting on a record boundary.
    pub chunks: Vec<(u64, u64)>,
    pub pieces: Vec<Piece>,
    /// Heap segment bodies a split walk stepped over.
    pub segments: Vec<(u64, u64)>,
}

/// Feed every record to the sink; a truncated file is reported, not an error. A `split` walk
/// lists the heap segments that state their length instead of walking them, for the workers.
pub fn walk(reader: &mut Reader, sink: &mut impl Sink, split: bool) -> Result<Walked> {
    let mut walked = Walked::default();
    while !reader.at_eof() {
        let start = reader.position();
        match record(reader, sink, &mut walked, split) {
            Ok(()) => {}
            Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => {
                walked.truncated = true;
                close_all(&mut walked, reader.position());
                return Ok(walked);
            }
            Err(e) => return Err(Error::Dump(format!("corrupt record at byte {start}: {e}"))),
        }
    }
    Ok(walked)
}

/// Walk one chunk of a plain file, `[reader position, end)`; a truncated tail ends it quietly.
pub fn walk_chunk(reader: &mut Reader, end: u64, sink: &mut impl Sink) -> Result<()> {
    while reader.position() < end {
        let start = reader.position();
        match sub_record(reader, sink) {
            Ok(_) => {}
            Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => return Ok(()),
            Err(e) => return Err(Error::Dump(format!("corrupt record at byte {start}: {e}"))),
        }
    }
    Ok(())
}

/// End the open chunk at `at`, dropping it when empty.
fn close_chunk(walked: &mut Walked, at: u64) {
    if let Some((start, _)) = walked.chunks.pop_if(|&mut (_, end)| end == u64::MAX)
        && at > start
    {
        walked.chunks.push((start, at));
    }
}

/// End the open chunk and piece where the heap records stop.
fn close_all(walked: &mut Walked, at: u64) {
    close_chunk(walked, at);
    if let Some(piece) = walked.pieces.pop_if(|piece| piece.end == u64::MAX)
        && at > piece.start
    {
        walked.pieces.push(Piece { end: at, ..piece });
    }
}

/// Walk heap sub-records to `end`, or the end marker when `None`, in chunks of about `chunk_size`.
/// A chunk runs on over an adjacent segment's header until full.
pub fn heap(
    reader: &mut Reader,
    end: Option<u64>,
    sink: &mut impl Sink,
    walked: &mut Walked,
) -> io::Result<()> {
    let mut chunk_start = match walked.chunks.last() {
        Some(&(start, stop))
            if stop + RECORD_HEADER_LEN == reader.position() && stop - start < CHUNK_SIZE =>
        {
            walked.chunks.pop();
            start
        }
        _ => reader.position(),
    };
    walked.chunks.push((chunk_start, u64::MAX));
    walked.pieces.push(Piece::open(reader.position()));
    while end.is_none_or(|end| reader.position() < end) && !reader.at_eof() {
        if end.is_none() && reader.peek() == HEAP_DUMP_END {
            break;
        }
        let id = sub_record(reader, sink)?;
        let at = reader.position();
        let piece = walked.pieces.last_mut().expect("a piece is open");
        if id != 0 {
            (piece.min, piece.max) = (piece.min.min(id), piece.max.max(id));
        }
        if at - piece.start >= PIECE_SIZE {
            piece.end = at;
            walked.pieces.push(Piece::open(at));
        }
        if at - chunk_start >= CHUNK_SIZE {
            close_chunk(walked, at);
            chunk_start = at;
            walked.chunks.push((chunk_start, u64::MAX));
        }
    }
    close_all(walked, reader.position());
    Ok(())
}

fn record(reader: &mut Reader, sink: &mut impl Sink, walked: &mut Walked, split: bool) -> io::Result<()> {
    let tag = reader.u8()?;
    let _time = reader.u32()?;
    let len = u64::from(reader.u32()?);
    let end = reader.position() + len;
    let id_size = u64::from(reader.id_size);
    match tag {
        UTF8 => {
            let id = reader.id()?;
            let n = usize::try_from(len.saturating_sub(id_size)).map_err(|_| too_big())?;
            let text = reader.read_bytes(n)?;
            sink.utf8(id, text);
        }
        LOAD_CLASS => {
            let (serial, id, _trace, name_id) = (reader.u32()?, reader.id()?, reader.u32()?, reader.id()?);
            sink.load_class(serial, id, name_id);
        }
        STACK_FRAME => {
            let (id, method_id, _signature_id, source_id) =
                (reader.id()?, reader.id()?, reader.id()?, reader.id()?);
            let (class_serial, line) = (reader.u32()?, reader.u32()? as i32);
            sink.frame(Frame { id, method_id, source_id, class_serial, line });
        }
        STACK_TRACE => {
            let (serial, thread_serial, frame_count) = (reader.u32()?, reader.u32()?, reader.u32()?);
            let frames: Vec<u64> = (0..frame_count).map(|_| reader.id()).collect::<io::Result<_>>()?;
            sink.trace(serial, thread_serial, &frames);
        }
        HEAP_DUMP | HEAP_DUMP_SEGMENT if split && len > 0 => walked.segments.push((reader.position(), end)),
        // Some writers put a zero length here: the segment runs to the end marker or EOF.
        HEAP_DUMP | HEAP_DUMP_SEGMENT => heap(reader, (len > 0).then_some(end), sink, walked)?,
        _ => {}
    }
    let pos = reader.position();
    if pos < end {
        reader.skip(end - pos)?;
    } else if pos > end && len > 0 && tag != HEAP_DUMP && tag != HEAP_DUMP_SEGMENT {
        return Err(invalid_data(format!("record 0x{tag:02x} overran its declared length")));
    }
    Ok(())
}

// Heap sub-record tags.
const ROOT_UNKNOWN: u8 = 0xFF;
const ROOT_JNI_GLOBAL: u8 = 0x01;
const ROOT_JNI_LOCAL: u8 = 0x02;
const ROOT_JAVA_FRAME: u8 = 0x03;
const ROOT_NATIVE_STACK: u8 = 0x04;
const ROOT_STICKY_CLASS: u8 = 0x05;
const ROOT_THREAD_BLOCK: u8 = 0x06;
const ROOT_MONITOR_USED: u8 = 0x07;
const ROOT_THREAD_OBJ: u8 = 0x08;
const CLASS_DUMP: u8 = 0x20;
const INSTANCE_DUMP: u8 = 0x21;
const OBJ_ARRAY_DUMP: u8 = 0x22;
const PRIM_ARRAY_DUMP: u8 = 0x23;
// Android (ART / Dalvik) extensions.
const ROOT_INTERNED_STRING: u8 = 0x89;
const ROOT_FINALIZING: u8 = 0x8A;
const ROOT_DEBUGGER: u8 = 0x8B;
const ROOT_REFERENCE_CLEANUP: u8 = 0x8C;
const ROOT_VM_INTERNAL: u8 = 0x8D;
const ROOT_JNI_MONITOR: u8 = 0x8E;
const UNREACHABLE: u8 = 0x90;
const PRIM_ARRAY_NODATA: u8 = 0xC3;
const HEAP_DUMP_INFO: u8 = 0xFE;

/// One heap sub-record; the id it describes when it is an object, else 0.
fn sub_record(reader: &mut Reader, sink: &mut impl Sink) -> io::Result<u64> {
    let tag = reader.u8()?;
    let plain_root = |kind| Root { id: 0, kind, thread_serial: 0, frame: u32::MAX, trace_serial: 0 };
    let id_only_kind = |tag: u8| match tag {
        ROOT_UNKNOWN => Some(RootKind::Unknown),
        ROOT_STICKY_CLASS => Some(RootKind::StickyClass),
        ROOT_MONITOR_USED => Some(RootKind::MonitorUsed),
        ROOT_INTERNED_STRING => Some(RootKind::InternedString),
        ROOT_FINALIZING => Some(RootKind::Finalizing),
        ROOT_DEBUGGER => Some(RootKind::Debugger),
        ROOT_REFERENCE_CLEANUP => Some(RootKind::ReferenceCleanup),
        ROOT_VM_INTERNAL => Some(RootKind::VmInternal),
        UNREACHABLE => Some(RootKind::Unreachable),
        _ => None,
    };
    if let Some(kind) = id_only_kind(tag) {
        sink.root(Root { id: reader.id()?, ..plain_root(kind) });
        return Ok(0);
    }
    let mut object = 0;
    match tag {
        ROOT_JNI_GLOBAL => {
            let (id, _global_ref) = (reader.id()?, reader.id()?);
            sink.root(Root { id, ..plain_root(RootKind::JniGlobal) });
        }
        ROOT_JNI_LOCAL | ROOT_JAVA_FRAME | ROOT_JNI_MONITOR => {
            let kind = match tag {
                ROOT_JNI_LOCAL => RootKind::JniLocal,
                ROOT_JAVA_FRAME => RootKind::JavaFrame,
                _ => RootKind::JniMonitor,
            };
            let (id, thread_serial, frame) = (reader.id()?, reader.u32()?, reader.u32()?);
            sink.root(Root { id, kind, thread_serial, frame, trace_serial: 0 });
        }
        ROOT_NATIVE_STACK | ROOT_THREAD_BLOCK => {
            let kind = if tag == ROOT_NATIVE_STACK { RootKind::NativeStack } else { RootKind::ThreadBlock };
            let (id, thread_serial) = (reader.id()?, reader.u32()?);
            sink.root(Root { id, thread_serial, ..plain_root(kind) });
        }
        ROOT_THREAD_OBJ => {
            let (id, thread_serial, trace_serial) = (reader.id()?, reader.u32()?, reader.u32()?);
            let kind = RootKind::ThreadObject;
            sink.root(Root { id, kind, thread_serial, frame: u32::MAX, trace_serial });
        }
        CLASS_DUMP => sink.class(class_dump(reader)?),
        // One read for the fixed header: one bounds check, not four.
        INSTANCE_DUMP => {
            // id, u32 stack serial, class id, u32 body length.
            let id_len = reader.id_size as usize;
            let header = reader.read_bytes(2 * id_len + 8)?;
            let (id, class_id, body_len) = (
                be_uint(&header[..id_len]),
                be_uint(&header[id_len + 4..2 * id_len + 4]),
                be_uint(&header[2 * id_len + 4..]) as u32,
            );
            let end = reader.position() + u64::from(body_len);
            sink.instance(id, class_id, Body { reader, len: u64::from(body_len) })?;
            skip_rest(reader, end)?;
            object = id;
        }
        OBJ_ARRAY_DUMP => {
            // id, u32 stack serial, u32 length, class id.
            let id_len = reader.id_size as usize;
            let header = reader.read_bytes(2 * id_len + 8)?;
            let (id, len, class_id) = (
                be_uint(&header[..id_len]),
                be_uint(&header[id_len + 4..id_len + 8]) as u32,
                be_uint(&header[id_len + 8..]),
            );
            let body_len = u64::from(len) * u64::from(reader.id_size);
            let end = reader.position() + body_len;
            sink.object_array(id, class_id, len, Body { reader, len: body_len })?;
            skip_rest(reader, end)?;
            object = id;
        }
        PRIM_ARRAY_DUMP | PRIM_ARRAY_NODATA => {
            // id, u32 stack serial, u32 length, u8 element type.
            let id_len = reader.id_size as usize;
            let header = reader.read_bytes(id_len + 9)?;
            let (id, len, elem_tag) = (
                be_uint(&header[..id_len]),
                be_uint(&header[id_len + 4..id_len + 8]) as u32,
                header[id_len + 8],
            );
            let ty = Ty::from_tag(elem_tag)
                .ok_or_else(|| invalid_data(format!("bad primitive array type {elem_tag}")))?;
            let body_len =
                if tag == PRIM_ARRAY_DUMP { u64::from(len) * u64::from(ty.size(reader.id_size)) } else { 0 };
            let end = reader.position() + body_len;
            sink.primitive_array(id, ty, len, Body { reader, len: body_len })?;
            skip_rest(reader, end)?;
            object = id;
        }
        HEAP_DUMP_INFO => {
            let (_heap_type, _name_id) = (reader.u32()?, reader.id()?);
        }
        // A chunk can run into the next segment: skip its header.
        HEAP_DUMP | HEAP_DUMP_SEGMENT => {
            let (_time, _len) = (reader.u32()?, reader.u32()?);
        }
        _ => return Err(invalid_data(format!("unknown heap sub-record tag 0x{tag:02x}"))),
    }
    Ok(object)
}

/// Step over whatever part of a body the sink left unread.
fn skip_rest(reader: &mut Reader, end: u64) -> io::Result<()> {
    let pos = reader.position();
    if pos < end { reader.skip(end - pos) } else { Ok(()) }
}

fn class_dump(reader: &mut Reader) -> io::Result<ClassDump> {
    let (id, _trace, super_id, loader_id) = (reader.id()?, reader.u32()?, reader.id()?, reader.id()?);
    let (_signers, _domain, _reserved1, _reserved2) =
        (reader.id()?, reader.id()?, reader.id()?, reader.id()?);
    // The declared instance size is recomputed from the layout.
    let _instance_size = reader.u32()?;
    let id_size = reader.id_size;
    let read_value = |reader: &mut Reader, ty: Ty| -> io::Result<Value> {
        let bytes = reader.read_bytes(ty.size(id_size) as usize)?;
        Value::decode(ty, bytes, id_size).ok_or_else(|| invalid_data("short field value".into()))
    };
    let read_ty = |reader: &mut Reader| -> io::Result<Ty> {
        let tag = reader.u8()?;
        Ty::from_tag(tag).ok_or_else(|| invalid_data(format!("bad field type {tag}")))
    };
    for _ in 0..reader.u16()? {
        let (_pool_index, ty) = (reader.u16()?, read_ty(reader)?);
        read_value(reader, ty)?;
    }
    let mut statics = Vec::new();
    for _ in 0..reader.u16()? {
        let (name_id, ty) = (reader.id()?, read_ty(reader)?);
        statics.push((name_id, ty, read_value(reader, ty)?));
    }
    let mut fields = Vec::new();
    for _ in 0..reader.u16()? {
        fields.push((reader.id()?, read_ty(reader)?));
    }
    Ok(ClassDump { id, super_id, loader_id, statics, fields })
}
