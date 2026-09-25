//! JDK `-gz` dumps inflated over the workers. `HotSpot` writes gzip members of at most `BLOCKSIZE`
//! inflated bytes (named in the first member's comment) with no time field, each right after the
//! previous size field, so the file splits into runs that inflate in parallel. Each member's CRC and
//! size catch a false split.

use std::fs::File;
use std::io::{self, BufWriter, Read, Seek, SeekFrom, Write};
use std::path::Path;
use std::sync::Arc;

use flate2::read::MultiGzDecoder;

use crate::parallel;
use crate::source::Progress;

use super::IO_BUFFER_SIZE;

/// Gzip member magic.
pub const GZIP_MAGIC: [u8; 2] = [0x1f, 0x8b];
const DEFLATE: u8 = 8;
const FLAG_COMMENT: u8 = 0x10;
/// Gzip member header before its optional fields.
const GZIP_HEADER_LEN: usize = 10;
/// Enough of the first member for its header and `BLOCKSIZE` comment.
const HEAD_LEN: u64 = 64;
/// `HotSpot` writes 1 MiB; a bigger claim inflates in order, as each worker holds whole runs in memory.
const MAX_BLOCK_SIZE: u64 = 4 << 20;
/// A run holds one member, or a few where a start went unseen.
const MAX_MEMBERS_PER_RUN: u64 = 16;
/// Runs per worker in one wave.
const RUNS_PER_WORKER: usize = 4;
/// Read size while scanning for member starts.
const SCAN_BUFFER_SIZE: usize = 8 << 20;
/// The previous member's u32 size field, right before a start.
const SIZE_FIELD_LEN: usize = 4;
/// Header bytes probed at a start: magic, method, flags and a u32 time.
const PROBE_LEN: usize = 8;

/// Inflate `path` into `out` over the workers. False when not a JDK block dump or a run fails its
/// check; the caller then inflates in order.
pub fn inflate(path: &Path, out: &Path, progress: &Arc<Progress>) -> io::Result<bool> {
    let mut file = File::open(path)?;
    let len = file.metadata()?.len();
    let mut head = Vec::new();
    (&mut file).take(HEAD_LEN).read_to_end(&mut head)?;
    let Some(block_size) = parse_block_size(&head) else { return Ok(false) };
    let starts = member_starts(&mut file, len, block_size)?;
    let runs: Vec<(u64, u64)> = starts.windows(2).map(|pair| (pair[0], pair[1])).collect();

    progress.begin("inflating", len);
    let mut tick = progress.counter(0);
    let mut writer = BufWriter::with_capacity(IO_BUFFER_SIZE, File::create(out)?);
    let max_run_len = MAX_MEMBERS_PER_RUN * block_size;
    // One wave is written out while the workers inflate the next.
    std::thread::scope(|scope| {
        let (tx, rx) = std::sync::mpsc::sync_channel::<Vec<Vec<u8>>>(1);
        let writer_thread = scope.spawn(move || -> io::Result<()> {
            for data in rx.iter().flatten() {
                writer.write_all(&data)?;
            }
            writer.flush()
        });
        for wave in runs.chunks(parallel::threads() * RUNS_PER_WORKER) {
            let parts = parallel::items(wave, |&(start, end)| -> io::Result<Vec<u8>> {
                let mut file = File::open(path)?;
                file.seek(SeekFrom::Start(start))?;
                let mut data = Vec::with_capacity(block_size as usize);
                MultiGzDecoder::new(file.take(end - start)).take(max_run_len + 1).read_to_end(&mut data)?;
                Ok(data)
            });
            let Some(parts) = parts
                .into_iter()
                .map(|part| part.ok().filter(|data| data.len() as u64 <= max_run_len))
                .collect()
            else {
                return Ok(false);
            };
            if tx.send(parts).is_err() {
                break;
            }
            if let (Some(tick), Some(&(_, end))) = (tick.as_mut(), wave.last()) {
                tick(end);
            }
        }
        drop(tx);
        writer_thread.join().expect("writer panicked")?;
        Ok(true)
    })
}

/// `N` from the `HPROF BLOCKSIZE=N` comment of the first member's header.
fn parse_block_size(head: &[u8]) -> Option<u64> {
    // Magic, deflate, and the comment flag alone.
    if head.get(..4)? != [GZIP_MAGIC[0], GZIP_MAGIC[1], DEFLATE, FLAG_COMMENT] {
        return None;
    }
    let comment = head.get(GZIP_HEADER_LEN..)?;
    let text = &comment[..comment.iter().position(|&byte| byte == 0)?];
    let size: u64 = std::str::from_utf8(text).ok()?.strip_prefix("HPROF BLOCKSIZE=")?.parse().ok()?;
    (1..=MAX_BLOCK_SIZE).contains(&size).then_some(size)
}

/// Offsets where a member begins, then the file's end: a gzip header with no
/// time, right after a size field of at most a block.
fn member_starts(file: &mut File, len: u64, block_size: u64) -> io::Result<Vec<u64>> {
    let mut starts = vec![0u64];
    let mut buf = vec![0u8; SCAN_BUFFER_SIZE];
    file.seek(SeekFrom::Start(0))?;
    // `buf[..kept]` came from the previous read, so a start across the seam counts.
    let (mut base, mut kept) = (0u64, 0usize);
    loop {
        let got = file.read(&mut buf[kept..])?;
        if got == 0 {
            break;
        }
        let end = kept + got;
        for pos in SIZE_FIELD_LEN..end.saturating_sub(PROBE_LEN - 1) {
            if buf[pos] != GZIP_MAGIC[0] {
                continue;
            }
            let (size_field, header) = (&buf[pos - SIZE_FIELD_LEN..pos], &buf[pos..pos + PROBE_LEN]);
            let size =
                u64::from(u32::from_le_bytes([size_field[0], size_field[1], size_field[2], size_field[3]]));
            if header[1..3] == [GZIP_MAGIC[1], DEFLATE]
                && header[3] & !FLAG_COMMENT == 0
                && header[4..] == [0; 4]
                && (1..=block_size).contains(&size)
            {
                let at = base + pos as u64;
                if starts.last().is_some_and(|&last| at > last) {
                    starts.push(at);
                }
            }
        }
        kept = end.min(SIZE_FIELD_LEN + PROBE_LEN - 1);
        buf.copy_within(end - kept..end, 0);
        base += (end - kept) as u64;
    }
    starts.push(len);
    Ok(starts)
}
