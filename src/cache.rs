//! The index cache: dump model and graph, written next to the dump so later runs skip the two big
//! passes. The file name keys on the dump's size, mtime and graph options, so stale caches never match.

use std::collections::HashMap;
use std::fs::{self, File};
use std::io::{self, BufReader, BufWriter, Read, Write};
use std::path::{Path, PathBuf};

use super::dump::{Buckets, Class, Dump, FastMap, Field, Kind, Object, RefKind, Slot, Static, Thread, Trace};
use super::graph::{Graph, ReferencePolicy};
use super::hash::{FNV_OFFSET_BASIS, FNV_PRIME};
use super::hprof::{Frame, Header, IO_BUFFER_SIZE, Piece, Root, RootKind, Ty, Value};
use super::sizes::{SizeMode, Sizing};

const MAGIC: &[u8; 8] = b"CTDLHEAP";
const VERSION: u32 = 5;
/// Spreads each key field before the next is folded in. Part of the file name: never change.
const KEY_ROTATION: u32 = 17;
/// Written for a class that is no Reference; reads back as None.
const NO_REF_KIND: u8 = 0xff;

/// What a cached index depends on.
#[derive(Clone, Copy)]
pub struct Key {
    pub file_size: u64,
    pub mtime: u64,
    pub reference_policy: ReferencePolicy,
    pub sizes: SizeMode,
}

impl Key {
    /// The key for a dump file under these options.
    pub fn of(path: &Path, reference_policy: ReferencePolicy, sizes: SizeMode) -> io::Result<Key> {
        let metadata = fs::metadata(path)?;
        let mtime = metadata
            .modified()
            .ok()
            .and_then(|time| time.duration_since(std::time::UNIX_EPOCH).ok())
            .map_or(0, |duration| duration.as_secs());
        Ok(Key { file_size: metadata.len(), mtime, reference_policy, sizes })
    }

    pub fn hash(&self) -> u64 {
        let mut hash = FNV_OFFSET_BASIS;
        for value in [
            self.file_size,
            self.mtime,
            u64::from(self.reference_policy.soft),
            u64::from(self.reference_policy.weak),
            self.sizes as u64,
            u64::from(VERSION),
        ] {
            hash = (hash ^ value).wrapping_mul(FNV_PRIME).rotate_left(KEY_ROTATION);
        }
        hash
    }
}

/// `<dump>.midden/`, next to the dump.
pub fn cache_dir(dump: &Path) -> PathBuf {
    let name = dump
        .file_name()
        .map_or_else(|| "dump".to_string(), |file_name| file_name.to_string_lossy().into_owned());
    dump.with_file_name(format!("{name}.midden"))
}

/// The cached index for a key.
pub fn index_path(dir: &Path, key: &Key) -> PathBuf {
    dir.join(format!("index-{:016x}.bin", key.hash()))
}

/// The inflated copy of a gzipped dump for a key.
pub fn inflated_path(dir: &Path, key: &Key) -> PathBuf {
    dir.join(format!("inflated-{:016x}.hprof", key.hash()))
}

/// Drop cache files that belong to other versions of the dump.
pub fn sweep(dir: &Path, key: &Key) {
    let keep = format!("{:016x}", key.hash());
    let Ok(entries) = fs::read_dir(dir) else { return };
    for entry in entries.flatten() {
        let name = entry.file_name().to_string_lossy().into_owned();
        if (name.starts_with("index-") || name.starts_with("inflated-")) && !name.contains(&keep) {
            let _ = fs::remove_file(entry.path());
        }
    }
}

struct Writer(BufWriter<File>);

impl Writer {
    fn u8(&mut self, value: u8) -> io::Result<()> {
        self.0.write_all(&[value])
    }
    fn u32(&mut self, value: u32) -> io::Result<()> {
        self.0.write_all(&value.to_le_bytes())
    }
    fn u64(&mut self, value: u64) -> io::Result<()> {
        self.0.write_all(&value.to_le_bytes())
    }
    /// A u32 count, refused rather than wrapped.
    fn count(&mut self, count: usize) -> io::Result<()> {
        self.u32(
            u32::try_from(count)
                .map_err(|_| io::Error::other(format!("too many entries ({count}) for the cache")))?,
        )
    }
    fn str(&mut self, text: &str) -> io::Result<()> {
        self.count(text.len())?;
        self.0.write_all(text.as_bytes())
    }
    // Columns stream from the live index, so writing it holds no copy.
    fn u32s(&mut self, len: usize, values: impl Iterator<Item = u32>) -> io::Result<()> {
        self.bytes(len, values.map(u32::to_le_bytes))
    }
    fn u64s(&mut self, len: usize, values: impl Iterator<Item = u64>) -> io::Result<()> {
        self.bytes(len, values.map(u64::to_le_bytes))
    }
    fn bytes<const N: usize>(&mut self, len: usize, values: impl Iterator<Item = [u8; N]>) -> io::Result<()> {
        self.u64(len as u64)?;
        let mut block = Vec::with_capacity(IO_BUFFER_SIZE);
        for value in values {
            block.extend_from_slice(&value);
            if block.len() >= IO_BUFFER_SIZE {
                self.0.write_all(&block)?;
                block.clear();
            }
        }
        self.0.write_all(&block)
    }
}

/// The cache file and its length, which bounds every length read from it.
struct Reader(BufReader<File>, u64);

impl Reader {
    /// A length from the file, refused when the file is too short to hold it.
    fn fits(&self, len: u64, width: u64) -> io::Result<usize> {
        let fits = len.saturating_mul(width) <= self.1;
        usize::try_from(len).ok().filter(|_| fits).ok_or_else(|| io::ErrorKind::InvalidData.into())
    }
    fn array<const N: usize>(&mut self) -> io::Result<[u8; N]> {
        let mut buf = [0u8; N];
        self.0.read_exact(&mut buf)?;
        Ok(buf)
    }
    fn u8(&mut self) -> io::Result<u8> {
        Ok(self.array::<1>()?[0])
    }
    fn u32(&mut self) -> io::Result<u32> {
        self.array().map(u32::from_le_bytes)
    }
    fn u64(&mut self) -> io::Result<u64> {
        self.array().map(u64::from_le_bytes)
    }
    fn str(&mut self) -> io::Result<String> {
        let len = self.u32().and_then(|len| self.fits(len.into(), 1))?;
        let mut buf = vec![0u8; len];
        self.0.read_exact(&mut buf)?;
        String::from_utf8(buf).map_err(|_| io::ErrorKind::InvalidData.into())
    }
    fn u32s(&mut self) -> io::Result<Vec<u32>> {
        self.column(u32::from_le_bytes)
    }
    fn u64s(&mut self) -> io::Result<Vec<u64>> {
        self.column(u64::from_le_bytes)
    }
    fn column<const N: usize, T>(&mut self, decode: impl Fn([u8; N]) -> T) -> io::Result<Vec<T>> {
        let len = self.u64().and_then(|len| self.fits(len, N as u64))?;
        let mut out = Vec::with_capacity(len);
        let mut buf = vec![0u8; IO_BUFFER_SIZE];
        let mut remaining = len;
        while remaining > 0 {
            let batch = remaining.min(IO_BUFFER_SIZE / N);
            let bytes = &mut buf[..batch * N];
            self.0.read_exact(bytes)?;
            out.extend(bytes.as_chunks::<N>().0.iter().map(|chunk| decode(*chunk)));
            remaining -= batch;
        }
        Ok(out)
    }
}

/// Write the index, atomically.
pub fn save(path: &Path, key: &Key, dump: &Dump, graph: &Graph) -> io::Result<()> {
    let part_path = path.with_extension("part");
    let mut writer = Writer(BufWriter::with_capacity(IO_BUFFER_SIZE, File::create(&part_path)?));
    writer.0.write_all(MAGIC)?;
    writer.u32(VERSION)?;
    writer.u64(key.hash())?;
    writer.str(&dump.header.format)?;
    writer.u32(dump.header.id_size)?;
    writer.u64(dump.header.timestamp_ms)?;
    writer.u64(dump.file_size)?;
    writer.u8(u8::from(dump.gzip))?;
    writer.str(dump.member.as_deref().unwrap_or_default())?;
    writer.u8(u8::from(dump.truncated))?;
    let sizing = &dump.sizing;
    for value in [sizing.header, sizing.array_header, sizing.ref_size, sizing.mode as u32] {
        writer.u32(value)?;
    }
    writer.u64s(2 * dump.chunks.len(), dump.chunks.iter().flat_map(|&(start, end)| [start, end]))?;
    writer.u64s(
        4 * dump.pieces.len(),
        dump.pieces.iter().flat_map(|piece| [piece.start, piece.end, piece.min, piece.max]),
    )?;
    writer.count(dump.names.len())?;
    for name in &dump.names {
        writer.str(name)?;
    }
    writer.count(dump.symbols.len())?;
    for (id, symbol) in &dump.symbols {
        writer.u64(*id)?;
        writer.str(symbol)?;
    }
    writer.count(dump.classes.len())?;
    for class in &dump.classes {
        writer.u64(class.id)?;
        writer.str(&class.name)?;
        writer.u32(class.superclass)?;
        writer.u64(class.loader)?;
        writer.count(class.fields.len())?;
        for field in &class.fields {
            writer.u32(field.name)?;
            writer.u8(field.ty.tag())?;
        }
        writer.count(class.statics.len())?;
        for field in &class.statics {
            writer.u32(field.name)?;
            writer.u8(field.ty.tag())?;
            writer.u64(field.value.bits())?;
        }
        for value in [class.data_len, class.shallow, class.footprint] {
            writer.u32(value)?;
        }
        writer.count(class.slots.len())?;
        for slot in &class.slots {
            writer.u32(slot.offset)?;
            writer.u32(slot.label)?;
            writer.u8(u8::from(slot.weak))?;
        }
        writer.u8(class.element_type.map_or(0, Ty::tag))?;
        writer.u8(u8::from(class.dumped))?;
        writer.u64(class.instances)?;
        writer.u8(class.ref_kind.map_or(NO_REF_KIND, |kind| kind as u8))?;
    }
    let (objects, count) = (&dump.objects, dump.objects.len());
    writer.u64s(count, objects.iter().map(|object| object.id))?;
    writer.u32s(count, objects.iter().map(|object| object.class))?;
    writer.u32s(count, objects.iter().map(|object| object.len))?;
    writer.u32s(count, objects.iter().map(|object| object.shallow))?;
    writer.bytes(count, objects.iter().map(|object| [object.kind as u8]))?;
    writer.count(dump.roots.len())?;
    for (idx, root) in &dump.roots {
        writer.u32(*idx)?;
        writer.u64(root.id)?;
        writer.u8(root.kind.cache_code())?;
        writer.u32(root.thread_serial)?;
        writer.u32(root.frame)?;
        writer.u32(root.trace_serial)?;
    }
    writer.u64(dump.dangling_roots)?;
    writer.u64(dump.marked_unreachable)?;
    writer.count(dump.threads.len())?;
    for thread in &dump.threads {
        writer.u32(thread.object)?;
        writer.u32(thread.serial)?;
        writer.u32(thread.trace_serial)?;
    }
    writer.count(dump.traces.len())?;
    for (serial, trace) in &dump.traces {
        writer.u32(*serial)?;
        writer.u64s(trace.frames.len(), trace.frames.iter().copied())?;
    }
    writer.count(dump.frames.len())?;
    for frame in dump.frames.values() {
        writer.u64(frame.id)?;
        writer.u64(frame.method_id)?;
        writer.u64(frame.source_id)?;
        writer.u32(frame.class_serial)?;
        writer.u32(frame.line as u32)?;
    }
    writer.count(dump.class_by_serial.len())?;
    for (serial, class) in &dump.class_by_serial {
        writer.u32(*serial)?;
        writer.u32(*class)?;
    }
    for value in [dump.class_class, dump.string_class, dump.value_label, dump.name_label] {
        writer.u32(value)?;
    }
    let (offsets, targets, labels, weak) = graph.parts();
    writer.u64s(offsets.len(), offsets.iter().copied())?;
    writer.u32s(targets.len(), targets.iter().copied())?;
    writer.u32s(labels.len(), labels.iter().copied())?;
    writer.u32s(2 * weak.len(), weak.iter().flat_map(|&(referrer, referent)| [referrer, referent]))?;
    writer.u64(graph.dangling)?;
    writer.u32s(graph.roots.len(), graph.roots.iter().copied())?;
    writer.0.flush()?;
    drop(writer);
    fs::rename(&part_path, path)
}

/// The cached dump and graph, or None when there is none for this key.
pub fn load(path: &Path, key: &Key, dump_path: &str) -> Option<(Dump, Graph)> {
    let file = File::open(path).ok()?;
    let len = file.metadata().ok()?.len();
    read(Reader(BufReader::with_capacity(IO_BUFFER_SIZE, file), len), key, dump_path).ok()
}

fn read(mut reader: Reader, key: &Key, dump_path: &str) -> io::Result<(Dump, Graph)> {
    let invalid = || io::Error::from(io::ErrorKind::InvalidData);
    let mut magic = [0u8; 8];
    reader.0.read_exact(&mut magic)?;
    if &magic != MAGIC || reader.u32()? != VERSION || reader.u64()? != key.hash() {
        return Err(invalid());
    }
    let header = Header { format: reader.str()?, id_size: reader.u32()?, timestamp_ms: reader.u64()? };
    let file_size = reader.u64()?;
    let gzip = reader.u8()? != 0;
    let member = Some(reader.str()?).filter(|member| !member.is_empty());
    let truncated = reader.u8()? != 0;
    let (object_header, array_header, ref_size, mode) =
        (reader.u32()?, reader.u32()?, reader.u32()?, reader.u32()?);
    let mode = [SizeMode::Mat, SizeMode::Compressed, SizeMode::Full, SizeMode::Auto]
        .get(mode as usize)
        .copied()
        .ok_or_else(invalid)?;
    let sizing = Sizing { header: object_header, array_header, ref_size, mode };
    let chunks: Vec<(u64, u64)> =
        reader.u64s()?.as_chunks::<2>().0.iter().map(|chunk| (chunk[0], chunk[1])).collect();
    let pieces: Vec<Piece> = reader
        .u64s()?
        .as_chunks::<4>()
        .0
        .iter()
        .map(|piece| Piece { start: piece[0], end: piece[1], min: piece[2], max: piece[3] })
        .collect();
    let names: Vec<String> = (0..reader.u32()?).map(|_| reader.str()).collect::<io::Result<_>>()?;
    let symbols: FastMap<u64, String> =
        (0..reader.u32()?).map(|_| Ok((reader.u64()?, reader.str()?))).collect::<io::Result<_>>()?;
    let ty_from_tag = |tag: u8| Ty::from_tag(tag).ok_or_else(invalid);
    let mut classes = Vec::new();
    for _ in 0..reader.u32()? {
        let mut class = Class::placeholder(String::new(), reader.u64()?);
        class.name = reader.str()?;
        class.superclass = reader.u32()?;
        class.loader = reader.u64()?;
        for _ in 0..reader.u32()? {
            class.fields.push(Field { name: reader.u32()?, ty: ty_from_tag(reader.u8()?)? });
        }
        for _ in 0..reader.u32()? {
            let (name, ty) = (reader.u32()?, ty_from_tag(reader.u8()?)?);
            class.statics.push(Static { name, ty, value: Value::from_bits(ty, reader.u64()?) });
        }
        class.data_len = reader.u32()?;
        class.shallow = reader.u32()?;
        class.footprint = reader.u32()?;
        for _ in 0..reader.u32()? {
            class.slots.push(Slot { offset: reader.u32()?, label: reader.u32()?, weak: reader.u8()? != 0 });
        }
        class.element_type = Ty::from_tag(reader.u8()?);
        class.dumped = reader.u8()? != 0;
        class.instances = reader.u64()?;
        class.ref_kind = RefKind::ALL.get(reader.u8()? as usize).copied();
        classes.push(class);
    }
    let ids = reader.u64s()?;
    let class_idxs = reader.u32s()?;
    let lens = reader.u32s()?;
    let shallow_sizes = reader.u32s()?;
    let count = reader.u64().and_then(|count| reader.fits(count, 1))?;
    if [class_idxs.len(), lens.len(), shallow_sizes.len(), count].iter().any(|&len| len != ids.len()) {
        return Err(invalid());
    }
    let mut objects = Vec::with_capacity(count);
    for i in 0..count {
        let kind = *Kind::ALL.get(reader.u8()? as usize).ok_or_else(invalid)?;
        let (id, class, len, shallow) = (ids[i], class_idxs[i], lens[i], shallow_sizes[i]);
        objects.push(Object { id, class, len, shallow, kind });
    }
    let mut roots = Vec::new();
    for _ in 0..reader.u32()? {
        let (idx, id) = (reader.u32()?, reader.u64()?);
        let kind = *RootKind::ALL.get(reader.u8()? as usize).ok_or_else(invalid)?;
        let (thread_serial, frame, trace_serial) = (reader.u32()?, reader.u32()?, reader.u32()?);
        roots.push((idx, Root { id, kind, thread_serial, frame, trace_serial }));
    }
    let dangling_roots = reader.u64()?;
    let marked_unreachable = reader.u64()?;
    let threads = (0..reader.u32()?)
        .map(|_| Ok(Thread { object: reader.u32()?, serial: reader.u32()?, trace_serial: reader.u32()? }))
        .collect::<io::Result<_>>()?;
    let traces: HashMap<u32, Trace> = (0..reader.u32()?)
        .map(|_| Ok((reader.u32()?, Trace { frames: reader.u64s()? })))
        .collect::<io::Result<_>>()?;
    let frames: FastMap<u64, Frame> = (0..reader.u32()?)
        .map(|_| {
            let (id, method_id, source_id) = (reader.u64()?, reader.u64()?, reader.u64()?);
            let (class_serial, line) = (reader.u32()?, reader.u32()? as i32);
            Ok((id, Frame { id, method_id, source_id, class_serial, line }))
        })
        .collect::<io::Result<_>>()?;
    let class_by_serial: HashMap<u32, u32> =
        (0..reader.u32()?).map(|_| Ok((reader.u32()?, reader.u32()?))).collect::<io::Result<_>>()?;
    let (class_class, string_class, value_label, name_label) =
        (reader.u32()?, reader.u32()?, reader.u32()?, reader.u32()?);
    let offsets = reader.u64s()?;
    let targets = reader.u32s()?;
    let labels = reader.u32s()?;
    let weak: Vec<(u32, u32)> =
        reader.u32s()?.as_chunks::<2>().0.iter().map(|edge| (edge[0], edge[1])).collect();
    let dangling = reader.u64()?;
    let graph_roots = reader.u32s()?;
    if offsets.len() != count + 1 || targets.len() != labels.len() {
        return Err(invalid());
    }
    let lookup = Buckets::build(&objects);
    let dump = Dump {
        path: dump_path.to_string(),
        file_size,
        gzip,
        member,
        header,
        truncated,
        sizing,
        chunks,
        pieces,
        names,
        symbols,
        classes,
        objects,
        roots,
        dangling_roots,
        marked_unreachable,
        threads,
        traces,
        frames,
        class_by_serial,
        lookup,
        class_class,
        string_class,
        value_label,
        name_label,
    };
    Ok((dump, Graph::from_parts(offsets, targets, labels, weak, dangling, graph_roots)))
}
