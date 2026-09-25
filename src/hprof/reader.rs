//! Buffered big-endian reader over a stored or compressed dump. Stored dumps seek past unwanted
//! bodies; a compressed stream can be copied to a plain file as it inflates, so later passes can
//! seek and split too.

use std::fs::File;
use std::io::{self, BufWriter, Read, Seek, SeekFrom, Take, Write};
use std::path::{Path, PathBuf};

use super::archive::{self, Input};
use super::{Header, IO_BUFFER_SIZE};
use crate::error::{Error, Result};

enum Source {
    /// The dump's window of its file; reads end where the dump does.
    Plain(Take<File>),
    Packed(Box<dyn Read>),
}

impl Source {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        match self {
            Source::Plain(file) => file.read(buf),
            Source::Packed(stream) => stream.read(buf),
        }
    }
}

/// Where a dump stored as is sits: `len` bytes from `offset` of `path`.
#[derive(Clone, Debug)]
pub struct View {
    pub path: PathBuf,
    pub offset: u64,
    pub len: u64,
}

impl View {
    /// A whole file.
    pub fn file(path: &Path) -> io::Result<View> {
        Ok(View { path: path.to_path_buf(), offset: 0, len: std::fs::metadata(path)?.len() })
    }

    fn open(&self, pos: u64) -> io::Result<Take<File>> {
        let mut file = File::open(&self.path)?;
        file.seek(SeekFrom::Start(self.offset + pos))?;
        Ok(file.take(self.len.saturating_sub(pos)))
    }
}

/// Minimum read into an empty buffer (after a seek), so hopping segments reads their headers, not a
/// buffer's worth each. Other reads fill the buffer.
const MIN_READ: usize = 64 << 10;
/// `JAVA PROFILE 1.0.1` or `1.0.2`, then a NUL.
const FORMAT_LEN: usize = 18;

pub struct Reader {
    src: Source,
    buf: Vec<u8>,
    pos: usize,
    end: usize,
    /// File offset of `buf[0]`.
    base: u64,
    pub id_size: u32,
    pub file_size: u64,
    pub gzip: bool,
    /// Where the dump sits when it is stored as is, for seekable reads.
    pub view: Option<View>,
    /// The archive member the dump is, when it is one.
    pub member: Option<String>,
    /// Called with the position whenever the buffer refills.
    pub progress: Option<Box<dyn FnMut(u64)>>,
    tee: Option<BufWriter<File>>,
}

impl Reader {
    /// Open a dump and read its header.
    pub fn open(path: &Path) -> Result<(Reader, Header)> {
        let err = |source| Error::File { path: path.to_path_buf(), source };
        let file_size = std::fs::metadata(path).map_err(err)?.len();
        let mut reader = match archive::open(path).map_err(err)? {
            Input::Stored { offset, len, member } => {
                let view = View { path: path.to_path_buf(), offset, len };
                let source = Source::Plain(view.open(0).map_err(err)?);
                Reader { view: Some(view), ..Reader::new(source, file_size, false, member) }
            }
            Input::Packed { stream, gzip, member } => {
                Reader::new(Source::Packed(stream), file_size, gzip, member)
            }
        };
        let not_hprof = |why: &str| Error::Dump(format!("{}: not an hprof file ({why})", path.display()));
        let head = reader.read_bytes(FORMAT_LEN + 1).map_err(|_| not_hprof("too short"))?;
        if !head.starts_with(b"JAVA PROFILE 1.0.") || head[FORMAT_LEN] != 0 {
            return Err(not_hprof("no JAVA PROFILE header"));
        }
        let format = String::from_utf8_lossy(&head[..FORMAT_LEN]).into_owned();
        let id_size = reader.u32().map_err(err)?;
        if id_size != 4 && id_size != 8 {
            return Err(Error::Dump(format!("{}: unsupported identifier size {id_size}", path.display())));
        }
        reader.id_size = id_size;
        let timestamp_ms = reader.u64().map_err(err)?;
        Ok((reader, Header { format, id_size, timestamp_ms }))
    }

    /// Open a stored dump positioned at `pos`, for walking one chunk.
    pub fn open_at(view: &View, pos: u64, id_size: u32) -> io::Result<Reader> {
        let source = Source::Plain(view.open(pos)?);
        Ok(Reader { base: pos, id_size, ..Reader::new(source, view.len, false, None) })
    }

    fn new(src: Source, file_size: u64, gzip: bool, member: Option<String>) -> Reader {
        Reader {
            src,
            buf: vec![0; IO_BUFFER_SIZE],
            pos: 0,
            end: 0,
            base: 0,
            id_size: 0,
            file_size,
            gzip,
            view: None,
            member,
            progress: None,
            tee: None,
        }
    }

    /// Copy every inflated byte, the ones already buffered included, to `path`.
    pub fn tee_to(&mut self, path: &Path) -> io::Result<()> {
        let mut writer = BufWriter::with_capacity(IO_BUFFER_SIZE, File::create(path)?);
        writer.write_all(&self.buf[..self.end])?;
        self.tee = Some(writer);
        Ok(())
    }

    /// Flush the copy; true when one was being written.
    pub fn finish_tee(&mut self) -> io::Result<bool> {
        match self.tee.take() {
            Some(mut writer) => writer.flush().map(|()| true),
            None => Ok(false),
        }
    }

    #[inline]
    pub fn position(&self) -> u64 {
        self.base + self.pos as u64
    }

    /// Make `need` bytes available at `pos`, growing the buffer for big records.
    #[inline]
    fn fill(&mut self, need: usize) -> io::Result<()> {
        if self.end - self.pos >= need { Ok(()) } else { self.refill(need) }
    }

    #[cold]
    fn refill(&mut self, need: usize) -> io::Result<()> {
        if self.pos > 0 {
            self.buf.copy_within(self.pos..self.end, 0);
            self.base += self.pos as u64;
            self.end -= self.pos;
            self.pos = 0;
        }
        if need > self.buf.len() {
            // A length from the file past a stored dump's end is a truncated record, not an allocation.
            if let Source::Plain(file) = &self.src
                && (need - self.end) as u64 > file.limit()
            {
                return Err(io::ErrorKind::UnexpectedEof.into());
            }
            self.buf.resize(need.next_multiple_of(IO_BUFFER_SIZE), 0);
        }
        while self.end < need {
            let upto = if self.end == 0 { self.buf.len().min(need.max(MIN_READ)) } else { self.buf.len() };
            match self.src.read(&mut self.buf[self.end..upto])? {
                0 => return Err(io::ErrorKind::UnexpectedEof.into()),
                n => {
                    if let Some(writer) = self.tee.as_mut() {
                        writer.write_all(&self.buf[self.end..self.end + n])?;
                    }
                    self.end += n;
                }
            }
        }
        if let Some(progress) = self.progress.as_mut() {
            progress(self.base + self.end as u64);
        }
        Ok(())
    }

    #[inline]
    pub fn read_bytes(&mut self, n: usize) -> io::Result<&[u8]> {
        self.fill(n)?;
        let bytes = &self.buf[self.pos..self.pos + n];
        self.pos += n;
        Ok(bytes)
    }

    /// Step over `n` bytes: a seek on a plain file, a drain on gzip.
    #[inline]
    pub fn skip(&mut self, n: u64) -> io::Result<()> {
        let buffered = (self.end - self.pos) as u64;
        if n <= buffered {
            self.pos += n as usize;
            return Ok(());
        }
        self.skip_far(n - buffered)
    }

    #[cold]
    fn skip_far(&mut self, rest: u64) -> io::Result<()> {
        match &mut self.src {
            Source::Plain(file) if self.tee.is_none() => {
                self.base += self.end as u64 + rest;
                self.pos = 0;
                self.end = 0;
                file.set_limit(file.limit().saturating_sub(rest));
                file.get_mut().seek(SeekFrom::Current(rest as i64)).map(drop)
            }
            _ => {
                self.pos = self.end;
                let mut remaining = rest;
                while remaining > 0 {
                    let n = remaining.min(IO_BUFFER_SIZE as u64) as usize;
                    self.read_bytes(n)?;
                    remaining -= n as u64;
                }
                Ok(())
            }
        }
    }

    #[inline]
    pub fn u8(&mut self) -> io::Result<u8> {
        Ok(self.read_bytes(1)?[0])
    }

    #[inline]
    pub fn u16(&mut self) -> io::Result<u16> {
        Ok(super::be_uint(self.read_bytes(2)?) as u16)
    }

    #[inline]
    pub fn u32(&mut self) -> io::Result<u32> {
        Ok(super::be_uint(self.read_bytes(4)?) as u32)
    }

    #[inline]
    pub fn u64(&mut self) -> io::Result<u64> {
        Ok(super::be_uint(self.read_bytes(8)?))
    }

    #[inline]
    pub fn id(&mut self) -> io::Result<u64> {
        let n = self.id_size as usize;
        Ok(super::be_uint(self.read_bytes(n)?))
    }

    /// The next byte without consuming it; call after `at_eof` said no.
    pub fn peek(&self) -> u8 {
        self.buf[self.pos]
    }

    pub fn at_eof(&mut self) -> bool {
        self.fill(1).is_err()
    }
}
