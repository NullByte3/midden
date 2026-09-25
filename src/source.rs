//! Where the passes read from: the dump as stored, or the inflated copy of a compressed one when a
//! cache directory exists. Stored input splits over the workers; compressed is walked once, in order.

use std::io::{self, Write};
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use super::hprof::{self, Reader, Sink, View};
use super::parallel;
use crate::error::Result;
use crate::fmt::{fmt_duration, human_bytes};

/// The progress line is redrawn at most this often.
const REDRAW_INTERVAL: Duration = Duration::from_millis(100);

pub struct Source {
    /// The dump the user named.
    pub dump: PathBuf,
    /// Seekable reads: the dump or its stored archive member, else the inflated copy once one exists.
    pub seekable: Option<View>,
    pub id_size: u32,
    pub progress: Arc<Progress>,
}

impl Source {
    pub fn is_seekable(&self) -> bool {
        self.seekable.is_some()
    }

    /// Run a sink over every heap sub-record; plain input returns one sink per chunk, run on the workers.
    pub fn scan<S: Sink + Send>(
        &self,
        chunks: &[(u64, u64)],
        stage: &'static str,
        make_sink: impl Fn() -> S + Sync,
    ) -> Result<Vec<S>> {
        self.progress.begin(
            stage,
            if self.is_seekable() { chunks.iter().map(|&(start, end)| end - start).sum() } else { 0 },
        );
        let sinks = if let Some(view) = self.seekable.as_ref().filter(|_| !chunks.is_empty()) {
            let results = parallel::items(chunks, |&(start, end)| -> Result<S> {
                let mut reader = Reader::open_at(view, start, self.id_size)?;
                reader.progress = self.progress.counter(start);
                let mut sink = make_sink();
                hprof::walk_chunk(&mut reader, end, &mut sink)?;
                Ok(sink)
            });
            results.into_iter().collect::<Result<Vec<S>>>()?
        } else {
            let (mut reader, _) = Reader::open(&self.dump)?;
            reader.progress = self.progress.counter(0);
            let mut sink = make_sink();
            hprof::walk(&mut reader, &mut sink, false)?;
            vec![sink]
        };
        self.progress.end();
        Ok(sinks)
    }
}

/// One stderr line, redrawn as bytes are read; shared by every worker.
pub struct Progress {
    interactive: bool,
    start: Instant,
    done: AtomicU64,
    total: AtomicU64,
    stage: Mutex<Stage>,
}

/// The stage on the line, and when the line was last drawn.
struct Stage {
    name: &'static str,
    drawn: Instant,
}

impl Progress {
    pub fn new(interactive: bool) -> Progress {
        let now = Instant::now();
        Progress {
            interactive,
            start: now,
            done: AtomicU64::new(0),
            total: AtomicU64::new(0),
            stage: Mutex::new(Stage { name: "", drawn: now.checked_sub(Duration::from_secs(1)).unwrap() }),
        }
    }

    pub fn begin(&self, stage: &'static str, total: u64) {
        self.done.store(0, Relaxed);
        self.total.store(total, Relaxed);
        if let Ok(mut current) = self.stage.lock() {
            *current =
                Stage { name: stage, drawn: Instant::now().checked_sub(Duration::from_secs(1)).unwrap() };
        }
        self.draw(true);
    }

    /// A reader callback that adds what it read since the last call.
    pub fn counter(self: &Arc<Self>, from: u64) -> Option<Box<dyn FnMut(u64)>> {
        if !self.interactive {
            return None;
        }
        let (progress, mut last) = (Arc::clone(self), from);
        Some(Box::new(move |pos| {
            progress.done.fetch_add(pos.saturating_sub(last), Relaxed);
            last = pos;
            progress.draw(false);
        }))
    }

    /// Show a stage that has no byte count, or clear the line with "".
    pub fn stage(&self, stage: &'static str) {
        self.begin(stage, 0);
        if stage.is_empty() && self.interactive {
            let _ = write!(io::stderr(), "\r\x1b[K");
        }
    }

    pub fn end(&self) {
        self.stage("");
    }

    fn draw(&self, force: bool) {
        if !self.interactive {
            return;
        }
        let Ok(mut stage) = self.stage.lock() else { return };
        if !force && stage.drawn.elapsed() < REDRAW_INTERVAL {
            return;
        }
        stage.drawn = Instant::now();
        if stage.name.is_empty() {
            return;
        }
        let (done, total) = (self.done.load(Relaxed), self.total.load(Relaxed));
        let bytes = match (done, total) {
            (0, 0) => String::new(),
            (done, 0) => format!("  {}", human_bytes(done as f64)),
            (done, total) => format!("  {} of {}", human_bytes(done as f64), human_bytes(total as f64)),
        };
        let _ =
            write!(io::stderr(), "\r\x1b[K  {}{bytes}  {}", stage.name, fmt_duration(self.start.elapsed()));
    }

    pub fn elapsed(&self) -> Duration {
        self.start.elapsed()
    }
}
