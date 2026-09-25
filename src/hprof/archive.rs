//! Heap dumps inside a tar, gzipped tar or zip, found by content: the first member that starts like
//! a heap dump. Stored members are read in place (seekable, splittable); compressed ones inflate in
//! order.

use std::fs::File;
use std::io::{self, BufReader, Cursor, Read, Seek, SeekFrom};
use std::ops::Range;
use std::path::Path;

use flate2::read::{DeflateDecoder, MultiGzDecoder};

use super::IO_BUFFER_SIZE;
use super::gunzip::GZIP_MAGIC;

/// Where the heap dump is in a file.
pub enum Input {
    /// Stored as is, `len` bytes from `offset`: a plain dump or a tar or zip member.
    Stored { offset: u64, len: u64, member: Option<String> },
    /// Inflated in order: gzip, a gzipped tar, a deflated zip member.
    Packed { stream: Box<dyn Read>, gzip: bool, member: Option<String> },
}

const HPROF_MAGIC: &[u8] = b"JAVA PROFILE 1.0.";
/// Tar metadata (a long name, a pax header) is read up to this size.
const MAX_META: u64 = 1 << 20;

/// Tar headers and member data are padded to blocks of this size.
const TAR_BLOCK_SIZE: usize = 512;
// Tar header fields.
const TAR_NAME: Range<usize> = 0..100;
const TAR_SIZE: Range<usize> = 124..136;
const TAR_TYPEFLAG: usize = 156;
const TAR_MAGIC: Range<usize> = 257..262;
const TAR_PREFIX: Range<usize> = 345..500;
/// Set in a number field's first byte when the rest is big-endian binary, not octal.
const TAR_BINARY_FLAG: u8 = 0x80;

/// End of central directory record, without its comment.
const ZIP_END_LEN: usize = 22;
/// Zip64 end locator, right before the end record.
const ZIP64_LOCATOR_LEN: usize = 20;
const ZIP64_END_LEN: usize = 56;
/// Central directory file header, before its name, extra field and comment.
const ZIP_DIR_HEADER_LEN: usize = 46;
/// Local file header, before its name and extra field.
const ZIP_LOCAL_HEADER_LEN: u64 = 30;
/// An extra field's u16 id and u16 size.
const ZIP_EXTRA_HEADER_LEN: usize = 4;
const ZIP64_EXTRA_ID: u64 = 1;
/// A 32-bit size or offset holding this has moved to the zip64 extra field.
const ZIP64_SENTINEL: u64 = 0xffff_ffff;
const ZIP_STORED: u64 = 0;
const ZIP_DEFLATED: u64 = 8;
/// The central directory is read whole, so bounded: 64MB is about a million members.
const MAX_ZIP_DIR: u64 = 1 << 26;

pub fn open(path: &Path) -> io::Result<Input> {
    let mut file = File::open(path)?;
    let len = file.metadata()?.len();
    let mut head = Vec::new();
    (&mut file).take(TAR_BLOCK_SIZE as u64).read_to_end(&mut head)?;
    file.seek(SeekFrom::Start(0))?;
    if head.starts_with(&GZIP_MAGIC) {
        let mut decoder = MultiGzDecoder::new(BufReader::with_capacity(IO_BUFFER_SIZE, file));
        let mut first_block = Vec::new();
        (&mut decoder).take(TAR_BLOCK_SIZE as u64).read_to_end(&mut first_block)?;
        let tarred = is_tar(&first_block);
        let mut stream = Cursor::new(first_block).chain(decoder);
        if !tarred {
            return Ok(Input::Packed { stream: Box::new(stream), gzip: true, member: None });
        }
        let member = tar_member(&mut stream)?.ok_or_else(|| missing("gzipped tar"))?;
        let rest = stream.take(member.size - member.prefix.len() as u64);
        let label = Some(format!("tar member {}", member.name));
        let stream = Box::new(Cursor::new(member.prefix).chain(rest));
        return Ok(Input::Packed { stream, gzip: true, member: label });
    }
    if head.starts_with(b"PK\x03\x04") {
        return zip(path, file, len);
    }
    if is_tar(&head) {
        let mut reader = BufReader::with_capacity(IO_BUFFER_SIZE, file);
        let member = tar_member(&mut reader)?.ok_or_else(|| missing("tar"))?;
        let label = Some(format!("tar member {}", member.name));
        return Ok(Input::Stored { offset: member.offset, len: member.size, member: label });
    }
    Ok(Input::Stored { offset: 0, len, member: None })
}

fn is_tar(head: &[u8]) -> bool {
    head.get(TAR_MAGIC) == Some(&b"ustar"[..])
}

fn missing(what: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, format!("no heap dump among the {what}'s members"))
}

/// A tar member holding a heap dump.
struct Member {
    /// Where its data starts in the tar.
    offset: u64,
    size: u64,
    name: String,
    /// The first bytes of its data, already consumed to identify it.
    prefix: Vec<u8>,
}

/// The first member of a tar stream whose data starts like a heap dump.
fn tar_member(reader: &mut impl Read) -> io::Result<Option<Member>> {
    let (mut offset, mut long_name, mut pax_size) = (0u64, None, None);
    let mut block = [0u8; TAR_BLOCK_SIZE];
    loop {
        match reader.read_exact(&mut block) {
            Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => return Ok(None),
            result => result?,
        }
        if block.iter().all(|&byte| byte == 0) {
            return Ok(None);
        }
        offset += TAR_BLOCK_SIZE as u64;
        let kind = block[TAR_TYPEFLAG];
        let size = pax_size.take().unwrap_or_else(|| number(&block[TAR_SIZE]));
        let mut consumed = 0;
        if matches!(kind, b'x' | b'L') && size <= MAX_META {
            let mut data = vec![0; size as usize];
            reader.read_exact(&mut data)?;
            consumed = size;
            if kind == b'L' {
                long_name = Some(text(&data));
            } else {
                pax_size = pax(&data, "size").and_then(|value| text(value).parse().ok());
                long_name = pax(&data, "path").map(text).or(long_name);
            }
        } else if matches!(kind, 0 | b'0' | b'7') {
            // A regular file: pre-POSIX NUL, '0', or contiguous '7'.
            let mut prefix = vec![0; size.min(HPROF_MAGIC.len() as u64) as usize];
            reader.read_exact(&mut prefix)?;
            if prefix == HPROF_MAGIC {
                let name = long_name.unwrap_or_else(|| header_name(&block));
                return Ok(Some(Member { offset, size, name, prefix }));
            }
            consumed = prefix.len() as u64;
        }
        if !matches!(kind, b'x' | b'L') {
            long_name = None;
        }
        let padded = size.next_multiple_of(TAR_BLOCK_SIZE as u64);
        io::copy(&mut (&mut *reader).take(padded - consumed), &mut io::sink())?;
        offset += padded;
    }
}

/// A tar number field: octal text, or big-endian binary when the top bit is set.
fn number(field: &[u8]) -> u64 {
    if field[0] & TAR_BINARY_FLAG != 0 {
        return field[1..]
            .iter()
            .fold(u64::from(field[0] & !TAR_BINARY_FLAG), |acc, &byte| acc << 8 | u64::from(byte));
    }
    let digits =
        field.iter().skip_while(|&&byte| byte == b' ' || byte == 0).take_while(|byte| byte.is_ascii_digit());
    digits.fold(0, |acc, &digit| acc * 8 + u64::from(digit - b'0'))
}

/// A header's name, with the ustar prefix in front when there is one.
fn header_name(block: &[u8]) -> String {
    let (name, prefix) = (text(&block[TAR_NAME]), text(&block[TAR_PREFIX]));
    if prefix.is_empty() { name } else { format!("{prefix}/{name}") }
}

/// The value of `key` among a pax header's `length key=value` records.
fn pax<'a>(data: &'a [u8], key: &str) -> Option<&'a [u8]> {
    data.split(|&byte| byte == b'\n').find_map(|record| {
        let pair = &record[record.iter().position(|&byte| byte == b' ')? + 1..];
        let eq = pair.iter().position(|&byte| byte == b'=')?;
        (&pair[..eq] == key.as_bytes()).then(|| &pair[eq + 1..])
    })
}

fn text(bytes: &[u8]) -> String {
    let end = bytes.iter().position(|&byte| byte == 0).unwrap_or(bytes.len());
    String::from_utf8_lossy(&bytes[..end]).trim().to_string()
}

fn le_uint(bytes: &[u8]) -> u64 {
    bytes.iter().rev().fold(0, |acc, &byte| acc << 8 | u64::from(byte))
}

fn not_zip(what: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, format!("not a readable zip ({what})"))
}

/// The first zip member that starts like a heap dump, by the central directory (zip64 included).
/// Stored members are read in place, deflated ones inflated, other methods skipped.
fn zip(path: &Path, mut file: File, len: u64) -> io::Result<Input> {
    // End record: last 22 bytes plus at most a 64KB comment.
    let tail_len = len.min((ZIP_END_LEN + usize::from(u16::MAX)) as u64);
    let mut tail = vec![0; tail_len as usize];
    file.seek(SeekFrom::Start(len - tail_len))?;
    file.read_exact(&mut tail)?;
    let end_pos = tail
        .windows(4)
        .rposition(|window| window == b"PK\x05\x06")
        .ok_or_else(|| not_zip("no end record"))?;
    let end_record = tail.get(end_pos..end_pos + ZIP_END_LEN).ok_or_else(|| not_zip("short end record"))?;
    let (mut entry_count, mut dir_size, mut dir_offset) =
        (le_uint(&end_record[10..12]), le_uint(&end_record[12..16]), le_uint(&end_record[16..20]));
    let locator = end_pos.checked_sub(ZIP64_LOCATOR_LEN).map(|start| &tail[start..end_pos]);
    if let Some(locator) = locator.filter(|locator| locator.starts_with(b"PK\x06\x07")) {
        let mut zip64_end = [0u8; ZIP64_END_LEN];
        file.seek(SeekFrom::Start(le_uint(&locator[8..16])))?;
        file.read_exact(&mut zip64_end)?;
        if &zip64_end[..4] == b"PK\x06\x06" {
            (entry_count, dir_size, dir_offset) =
                (le_uint(&zip64_end[32..40]), le_uint(&zip64_end[40..48]), le_uint(&zip64_end[48..56]));
        }
    }
    if dir_size > len || dir_offset > len - dir_size {
        return Err(not_zip("directory past the end"));
    }
    if dir_size > MAX_ZIP_DIR {
        return Err(not_zip("directory over 64MB"));
    }
    let mut dir = vec![0; dir_size as usize];
    file.seek(SeekFrom::Start(dir_offset))?;
    file.read_exact(&mut dir)?;
    let mut pos = 0usize;
    for _ in 0..entry_count {
        let header = dir
            .get(pos..pos + ZIP_DIR_HEADER_LEN)
            .filter(|header| header.starts_with(b"PK\x01\x02"))
            .ok_or_else(|| not_zip("directory"))?;
        let (method, mut packed_size, mut unpacked_size, mut local_offset) = (
            le_uint(&header[10..12]),
            le_uint(&header[20..24]),
            le_uint(&header[24..28]),
            le_uint(&header[42..46]),
        );
        let (name_len, extra_len, comment_len) = (
            le_uint(&header[28..30]) as usize,
            le_uint(&header[30..32]) as usize,
            le_uint(&header[32..34]) as usize,
        );
        let name = dir
            .get(pos + ZIP_DIR_HEADER_LEN..pos + ZIP_DIR_HEADER_LEN + name_len)
            .map(text)
            .ok_or_else(|| not_zip("directory"))?;
        let mut extra = dir
            .get(pos + ZIP_DIR_HEADER_LEN + name_len..pos + ZIP_DIR_HEADER_LEN + name_len + extra_len)
            .unwrap_or_default();
        pos += ZIP_DIR_HEADER_LEN + name_len + extra_len + comment_len;
        // Zip64 moves the fields that overflowed, in this order, into extra field 1.
        while let (Some(id), Some(size)) =
            (extra.get(..2).map(le_uint), extra.get(2..ZIP_EXTRA_HEADER_LEN).map(le_uint))
        {
            let body =
                extra.get(ZIP_EXTRA_HEADER_LEN..ZIP_EXTRA_HEADER_LEN + size as usize).unwrap_or_default();
            if id == ZIP64_EXTRA_ID {
                let mut values = body.as_chunks::<8>().0.iter().map(|&value| u64::from_le_bytes(value));
                for field in [&mut unpacked_size, &mut packed_size, &mut local_offset] {
                    if *field == ZIP64_SENTINEL {
                        *field = values.next().unwrap_or(*field);
                    }
                }
            }
            extra = extra.get(ZIP_EXTRA_HEADER_LEN + size as usize..).unwrap_or_default();
        }
        if name.ends_with('/') || !matches!(method, ZIP_STORED | ZIP_DEFLATED) {
            continue;
        }
        let mut local_header = [0u8; ZIP_LOCAL_HEADER_LEN as usize];
        file.seek(SeekFrom::Start(local_offset))?;
        file.read_exact(&mut local_header)?;
        let data_offset = local_offset
            + ZIP_LOCAL_HEADER_LEN
            + le_uint(&local_header[26..28])
            + le_uint(&local_header[28..30]);
        let mut member_file = File::open(path)?;
        member_file.seek(SeekFrom::Start(data_offset))?;
        let window = BufReader::with_capacity(IO_BUFFER_SIZE, member_file).take(packed_size);
        let mut stream: Box<dyn Read> =
            if method == ZIP_STORED { Box::new(window) } else { Box::new(DeflateDecoder::new(window)) };
        let mut prefix = Vec::new();
        (&mut stream).take(HPROF_MAGIC.len() as u64).read_to_end(&mut prefix)?;
        if prefix != HPROF_MAGIC {
            continue;
        }
        return Ok(match method {
            ZIP_STORED => Input::Stored {
                offset: data_offset,
                len: unpacked_size,
                member: Some(format!("zip member {name}")),
            },
            _ => Input::Packed {
                stream: Box::new(Cursor::new(prefix).chain(stream)),
                gzip: false,
                member: Some(format!("zip member {name}, deflated")),
            },
        });
    }
    Err(missing("zip"))
}
