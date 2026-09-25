//! Pass three: the bytes behind the numbers. One read fetches the records the report prints, hashes
//! arrays for duplicates, tallies boxed values and runs `--find` / `--where`.

use std::io;

use super::dump::{Dump, FastMap};
use super::hash::{FNV_OFFSET_BASIS, FNV_PRIME, GOLDEN_RATIO};
use super::hprof::{Body, IO_BUFFER_SIZE, Sink, Ty, Value};
use super::source::Source;
use super::strings::Needle;
use crate::error::Result;

/// Fetched bodies are cut here; an inspected 100MB array shows its start.
pub const MAX_BODY_BYTES: usize = 1 << 16;

/// A fetched record body, cut at `MAX_BODY_BYTES` bytes.
pub struct RawRecord {
    pub ty: Ty,
    pub len: u32,
    pub data: Vec<u8>,
}

/// A `--where CLASS.FIELD=VALUE` filter: per class id, the field to read.
pub struct Filter {
    pub classes: FastMap<u64, (u32, Ty)>,
    pub expect: String,
}

/// What one read should collect.
#[derive(Default)]
pub struct Request {
    /// Record bodies to keep.
    pub want: Vec<u64>,
    /// String arrays to hash; the report shows these hashes.
    pub hash: Vec<u64>,
    /// Other primitive arrays to hash, only to group equal ones.
    pub content: Vec<u64>,
    /// Boxed classes by id: `(class index, value offset, value type)`.
    pub boxed: FastMap<u64, (u32, u32, Ty)>,
    /// String arrays to search, and the text.
    pub search: Option<(Vec<u64>, Needle)>,
    pub filter: Option<Filter>,
}

#[derive(Default)]
pub struct Fetched {
    pub raw: FastMap<u64, RawRecord>,
    /// Sorted ids that were hashed, and their hashes (zero: not in the file).
    pub hashed: Vec<u64>,
    pub hashes: Vec<u64>,
    /// `(boxed class, value bits)` → instances.
    pub boxed: FastMap<(u32, u64), u64>,
    /// String arrays that matched `--find`.
    pub found: Vec<u64>,
    /// Instances that matched `--where`.
    pub matched: Vec<u64>,
}

impl Fetched {
    pub fn hash_of(&self, id: u64) -> Option<u64> {
        self.hashed.binary_search(&id).ok().map(|i| self.hashes[i]).filter(|&hash| hash != 0)
    }

    /// Fold a later read's bodies and hashes into this one, for the shell.
    pub fn merge(&mut self, other: Fetched) {
        self.raw.extend(other.raw);
        if self.hashed.is_empty() {
            self.hashed = other.hashed;
            self.hashes = other.hashes;
        }
        for (key, count) in other.boxed {
            *self.boxed.entry(key).or_default() += count;
        }
    }
}

impl Request {
    pub fn is_empty(&self) -> bool {
        self.want.is_empty() && self.records_only()
    }

    /// Whether the read only keeps record bodies.
    fn records_only(&self) -> bool {
        self.hash.is_empty()
            && self.content.is_empty()
            && self.boxed.is_empty()
            && self.search.is_none()
            && self.filter.is_none()
    }
}

/// One read of the file that collects everything in `request`.
pub fn fetch(source: &Source, dump: &Dump, mut request: Request) -> Result<Fetched> {
    if request.is_empty() {
        return Ok(Fetched::default());
    }
    let searched = request.search.as_mut().map(|(ids, _)| ids);
    for list in [&mut request.want, &mut request.hash, &mut request.content].into_iter().chain(searched) {
        list.sort_unstable();
        list.dedup();
    }
    let picked = pieces_for(source, dump, &request);
    if picked.as_ref().is_some_and(Vec::is_empty) {
        return Ok(Fetched::default());
    }
    let parts = source.scan(picked.as_deref().unwrap_or(&dump.chunks), "reading details", || Fetcher {
        request: &request,
        id_size: dump.header.id_size,
        want: Seeker::new(&request.want),
        hash: Seeker::new(&request.hash),
        content: Seeker::new(&request.content),
        search: Seeker::new(request.search.as_ref().map_or(&[], |(ids, _)| ids)),
        raw: FastMap::default(),
        hashes: Vec::new(),
        boxed: FastMap::default(),
        found: Vec::new(),
        matched: Vec::new(),
    })?;
    let mut out =
        Fetched { hashes: vec![0; request.hash.len() + request.content.len()], ..Fetched::default() };
    for part in parts {
        out.raw.extend(part.raw);
        for (i, hash) in part.hashes {
            out.hashes[i] = hash;
        }
        for (key, count) in part.boxed {
            *out.boxed.entry(key).or_default() += count;
        }
        out.found.extend(part.found);
        out.matched.extend(part.matched);
    }
    // One table for both lists: a stable sort merges the two sorted runs.
    let mut table: Vec<(u64, u64)> =
        request.hash.into_iter().chain(request.content).zip(out.hashes).collect();
    table.sort_by_key(|&(id, _)| id);
    (out.hashed, out.hashes) = table.into_iter().unzip();
    Ok(out)
}

/// For a read of whole records alone on a seekable file, the pieces whose id
/// range holds a wanted id, adjacent ones joined; `None` reads every chunk.
fn pieces_for(source: &Source, dump: &Dump, request: &Request) -> Option<Vec<(u64, u64)>> {
    if !request.records_only() || !source.is_seekable() || dump.pieces.is_empty() {
        return None;
    }
    let mut ranges: Vec<(u64, u64)> = Vec::new();
    for piece in &dump.pieces {
        let i = request.want.partition_point(|&id| id < piece.min);
        if request.want.get(i).is_some_and(|&id| id <= piece.max) {
            match ranges.last_mut() {
                Some((_, end)) if *end == piece.start => *end = piece.end,
                _ => ranges.push((piece.start, piece.end)),
            }
        }
    }
    Some(ranges)
}

struct Fetcher<'a> {
    request: &'a Request,
    id_size: u32,
    want: Seeker<'a>,
    hash: Seeker<'a>,
    content: Seeker<'a>,
    search: Seeker<'a>,
    raw: FastMap<u64, RawRecord>,
    hashes: Vec<(usize, u64)>,
    boxed: FastMap<(u32, u64), u64>,
    found: Vec<u64>,
    matched: Vec<u64>,
}

/// Sorted id list membership for mostly ascending ids (`HotSpot` writes by address): a cursor gallops
/// forward from the last hit; only an out-of-order id searches from the start.
struct Seeker<'a> {
    ids: &'a [u64],
    cursor: usize,
}

impl<'a> Seeker<'a> {
    fn new(ids: &'a [u64]) -> Seeker<'a> {
        Seeker { ids, cursor: 0 }
    }

    fn find(&mut self, id: u64) -> Option<usize> {
        let ids = self.ids;
        if ids.is_empty() {
            return None;
        }
        let start = if self.cursor == 0 || ids[self.cursor - 1] < id { self.cursor } else { 0 };
        let mut end = start + 1;
        while end < ids.len() && ids[end - 1] < id {
            end = start + (end - start) * 2;
        }
        let end = end.min(ids.len());
        let pos = start + ids[start..end].partition_point(|&x| x < id);
        self.cursor = pos;
        (pos < ids.len() && ids[pos] == id).then_some(pos)
    }
}

impl Sink for Fetcher<'_> {
    fn instance(&mut self, id: u64, class_id: u64, body: Body) -> io::Result<()> {
        let boxed = self.request.boxed.get(&class_id).copied();
        let filter = self
            .request
            .filter
            .as_ref()
            .and_then(|filter| filter.classes.get(&class_id).map(|&field| (field, filter)));
        let wanted = self.want.find(id).is_some();
        if !wanted && boxed.is_none() && filter.is_none() {
            return Ok(());
        }
        let data = body.bytes()?;
        let id_size = self.id_size;
        if let Some((class, value)) = boxed.and_then(|(class, offset, ty)| {
            Some((class, Value::decode(ty, data.get(offset as usize..)?, id_size)?))
        }) {
            *self.boxed.entry((class, value.bits())).or_default() += 1;
        }
        if let Some(((offset, ty), filter)) = filter {
            let value = data.get(offset as usize..).and_then(|bytes| Value::decode(ty, bytes, id_size));
            let hit = match value {
                Some(Value::Ref(0)) => filter.expect == "null",
                Some(value) => value.text() == filter.expect,
                None => false,
            };
            if hit {
                self.matched.push(id);
            }
        }
        if wanted {
            self.raw.insert(id, RawRecord { ty: Ty::Object, len: data.len() as u32, data: data.to_vec() });
        }
        Ok(())
    }

    fn object_array(&mut self, id: u64, _class_id: u64, len: u32, body: Body) -> io::Result<()> {
        if self.want.find(id).is_some() {
            let mut data = Vec::new();
            body.chunks(IO_BUFFER_SIZE, |chunk| {
                keep(&mut data, chunk);
                Ok(())
            })?;
            self.raw.insert(id, RawRecord { ty: Ty::Object, len, data });
        }
        Ok(())
    }

    fn primitive_array(&mut self, id: u64, ty: Ty, len: u32, body: Body) -> io::Result<()> {
        let wanted = self.want.find(id).is_some();
        let (hashed, content) = (self.hash.find(id), self.content.find(id));
        let searched = self.search.find(id).is_some();
        if !wanted && hashed.is_none() && content.is_none() && !searched {
            return Ok(());
        }
        let (mut string_hash, mut content_hash, mut data) = (FNV_OFFSET_BASIS, GOLDEN_RATIO, Vec::new());
        let mut whole = Vec::new();
        body.chunks(IO_BUFFER_SIZE, |chunk| {
            if hashed.is_some() {
                for &byte in chunk {
                    string_hash = (string_hash ^ u64::from(byte)).wrapping_mul(FNV_PRIME);
                }
            }
            if content.is_some() {
                content_hash = mix_words(content_hash, chunk);
            }
            if wanted {
                keep(&mut data, chunk);
            }
            if searched {
                whole.extend_from_slice(chunk);
            }
            Ok(())
        })?;
        let len_bits = u64::from(len).rotate_left(u32::BITS);
        if let Some(i) = hashed {
            self.hashes.push((i, (string_hash ^ len_bits) | 1));
        }
        if let Some(i) = content {
            self.hashes.push((self.request.hash.len() + i, (content_hash ^ len_bits) | 1));
        }
        if searched && self.request.search.as_ref().is_some_and(|(_, needle)| needle.matches(ty, &whole)) {
            self.found.push(id);
        }
        if wanted {
            self.raw.insert(id, RawRecord { ty, len, data });
        }
        Ok(())
    }
}

/// Groups arrays by content, eight bytes a step through a folded 128-bit multiply. Only compared, so
/// unlike the shown String hash it need not be FNV-1a.
fn mix_words(mut hash: u64, bytes: &[u8]) -> u64 {
    let mix = |x: u64| {
        let product = u128::from(x) * u128::from(GOLDEN_RATIO);
        product as u64 ^ (product >> u64::BITS) as u64
    };
    let (words, rest) = bytes.as_chunks::<8>();
    for &word in words {
        hash = mix(hash ^ u64::from_le_bytes(word));
    }
    let mut tail = [0u8; 8];
    tail[..rest.len()].copy_from_slice(rest);
    mix(hash ^ u64::from_le_bytes(tail))
}

/// Keep the first `MAX_BODY_BYTES` bytes of a body.
fn keep(data: &mut Vec<u8>, chunk: &[u8]) {
    if data.len() < MAX_BODY_BYTES {
        data.extend_from_slice(&chunk[..chunk.len().min(MAX_BODY_BYTES - data.len())]);
    }
}
