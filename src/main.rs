//! midden: analyse a JVM heap dump in the terminal. An index pass and a reference pass build the
//! object graph; detail passes read only what the report prints.

mod analysis;
mod cache;
mod cli;
mod detail;
mod dom;
mod dump;
mod error;
mod fmt;
mod graph;
mod hash;
mod hprof;
mod index;
mod options;
mod parallel;
mod pattern;
mod report;
mod shell;
mod sizes;
mod source;
mod strings;

pub use options::Sort;
pub use sizes::SizeMode;

use std::io::{self, IsTerminal, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::Arc;
use std::thread;

use clap::Parser;

use analysis::Heap;
use detail::{Fetched, Filter, Request};
use error::{Error, Result};
use graph::{Graph, ReferencePolicy};
use options::Section;
use pattern::Pattern;
use report::{Inputs, Plan, View};
use source::{Progress, Source};

use cli::{Args, ColorWhen};

fn main() -> ExitCode {
    match run(&Args::parse()) {
        Ok(()) => ExitCode::SUCCESS,
        Err(message) => {
            eprintln!("midden: {message}");
            ExitCode::from(2)
        }
    }
}

fn use_color(when: ColorWhen) -> bool {
    match when {
        ColorWhen::Always => true,
        ColorWhen::Never => false,
        ColorWhen::Auto => io::stdout().is_terminal() && std::env::var_os("NO_COLOR").is_none(),
    }
}

fn run(args: &Args) -> Result<()> {
    parallel::set_threads(args.threads);
    let view = View::from_args(args)?;
    let interactive = io::stderr().is_terminal() && !args.json;
    let reference_policy = ReferencePolicy { soft: args.include_soft, weak: args.include_weak };
    let progress = Arc::new(Progress::new(interactive));
    let opts =
        Load { reference_policy, sizes: args.sizes, cache: !args.no_cache, progress: Arc::clone(&progress) };

    // Baseline first, so only its snapshot outlives the load.
    let baseline = match &args.baseline {
        Some(path) => analyse(load(path, &opts)?, view.clone(), |mut session| {
            session.prepare()?;
            let histogram = session.heap.histogram();
            Ok(Some(session.heap.snapshot(&histogram, session.inputs.duplicates.as_ref())))
        })?,
        None => None,
    };

    analyse(load(&args.file, &opts)?, view, |mut session| {
        (session.json, session.color) = (args.json, use_color(args.color));
        session.inputs.baseline = baseline;
        session.prepare()?;
        progress.end();
        let out = session.show(&session.view.clone())?;
        print!("{out}");
        io::stdout().flush()?;
        if args.shell {
            shell::run(&mut session)?;
        }
        Ok(())
    })
}

/// Build the heap of a load and hand its session to `then`. The cache write only reads the index, so it
/// runs beside the analysis.
fn analyse<T>(loaded: Loaded, view: View, then: impl FnOnce(Session) -> Result<T>) -> Result<T> {
    thread::scope(|scope| {
        scope.spawn(|| save(&loaded.dump, &loaded.graph, loaded.index.as_ref()));
        loaded.source.progress.stage("computing dominators");
        then(Session::new(Heap::new(&loaded.dump, &loaded.graph), loaded.source, view))
    })
}

struct Load {
    reference_policy: ReferencePolicy,
    sizes: SizeMode,
    cache: bool,
    progress: Arc<Progress>,
}

struct Loaded {
    dump: dump::Dump,
    graph: Graph,
    source: Source,
    /// Set when this load built the index, so the cache should be written.
    index: Option<(PathBuf, cache::Key)>,
}

/// Write the index cache and sweep out older ones.
fn save(dump: &dump::Dump, graph: &Graph, index: Option<&(PathBuf, cache::Key)>) {
    let Some((dir, key)) = index else { return };
    let saved = std::fs::create_dir_all(dir)
        .and_then(|()| cache::save(&cache::index_path(dir, key), key, dump, graph));
    match saved {
        Ok(()) => cache::sweep(dir, key),
        Err(e) => eprintln!("midden: not caching the index: {e}"),
    }
}

/// The index and reference passes, or the cache when it has them.
fn load(path: &Path, opts: &Load) -> Result<Loaded> {
    let name = path.display().to_string();
    let err = |source| Error::File { path: path.to_path_buf(), source };
    let key = cache::Key::of(path, opts.reference_policy, opts.sizes).map_err(err)?;
    let dir = opts.cache.then(|| cache::cache_dir(path));
    let (mut reader, header) = hprof::Reader::open(path)?;
    // Seekable reads use the dump as stored, else an inflated copy if one exists.
    let copy = dir.as_ref().map(|dir| cache::inflated_path(dir, &key)).filter(|file| file.is_file());
    let seekable = reader.view.clone().or_else(|| copy.and_then(|file| hprof::View::file(&file).ok()));
    let mut source =
        Source { dump: path.to_path_buf(), seekable, id_size: 0, progress: Arc::clone(&opts.progress) };
    if let Some((dump, graph)) =
        dir.as_ref().and_then(|dir| cache::load(&cache::index_path(dir, &key), &key, &name))
    {
        source.id_size = dump.header.id_size;
        return Ok(Loaded { dump, graph, source, index: None });
    }

    let mut inflating = None;
    let inflate =
        dir.as_ref().filter(|_| source.seekable.is_none()).filter(|dir| std::fs::create_dir_all(dir).is_ok());
    if let Some(dir) = inflate {
        let part = cache::inflated_path(dir, &key).with_extension("part");
        let done = cache::inflated_path(dir, &key);
        // Inflate a JDK `-gz` dump over the workers, then read it as a plain one.
        let blocks = reader.gzip && reader.member.is_none() && parallel::threads() > 1;
        if blocks
            && hprof::gunzip::inflate(path, &part, &opts.progress).unwrap_or(false)
            && std::fs::rename(&part, &done).is_ok()
        {
            let (gzip, file_size) = (reader.gzip, reader.file_size);
            (reader, _) = hprof::Reader::open(&done)?;
            (reader.gzip, reader.file_size) = (gzip, file_size);
            source.seekable = hprof::View::file(&done).ok();
        } else {
            match reader.tee_to(&part) {
                Ok(()) => inflating = Some(part),
                Err(e) => eprintln!("midden: not keeping an inflated copy: {e}"),
            }
        }
    }
    opts.progress.begin("indexing objects", reader.view.as_ref().map_or(0, |view| view.len));
    reader.progress = opts.progress.counter(0);
    let mut indexer = index::Indexer::new(header.id_size);
    // Splitting only pays for the merge with more than one worker.
    let view = reader.view.clone().filter(|_| parallel::threads() > 1);
    let mut walked = hprof::walk(&mut reader, &mut indexer, view.is_some())?;
    if let Some(view) = &view
        && !walked.segments.is_empty()
        && !indexer.read_segments(view, &mut walked, &opts.progress)
    {
        opts.progress.begin("indexing objects", view.len);
        (reader, _) = hprof::Reader::open(path)?;
        reader.progress = opts.progress.counter(0);
        indexer = index::Indexer::new(header.id_size);
        walked = hprof::walk(&mut reader, &mut indexer, false)?;
    }
    if let (true, Some(part), Some(dir)) = (reader.finish_tee().map_err(err)?, inflating, &dir) {
        let done = cache::inflated_path(dir, &key);
        if std::fs::rename(&part, &done).is_ok() {
            source.seekable = hprof::View::file(&done).ok();
        }
    }
    let dump = indexer.finish(&name, &reader, header, walked, opts.sizes)?;
    drop(reader);
    if dump.objects.is_empty() {
        return Err(Error::Dump(format!(
            "{name}: no heap dump segment in the file (is it a full dump, not a summary?)"
        )));
    }
    source.id_size = dump.header.id_size;
    let graph = graph::build(&dump, &source, opts.reference_policy)?;
    Ok(Loaded { dump, graph, source, index: dir.map(|dir| (dir, key)) })
}

/// One analysed dump and what has been read from it; the report and the shell render views of it.
pub struct Session<'a> {
    pub heap: Heap<'a>,
    source: Source,
    pub view: View,
    pub inputs: Inputs,
    fetched: Fetched,
    /// Every String with its backing array.
    strings: Vec<(u32, u32)>,
    json: bool,
    color: bool,
}

impl<'a> Session<'a> {
    fn new(mut heap: Heap<'a>, source: Source, view: View) -> Session<'a> {
        heap.set_excludes(&view.excludes);
        Session {
            heap,
            source,
            view,
            inputs: Inputs::default(),
            fetched: Fetched::default(),
            strings: Vec::new(),
            json: false,
            color: false,
        }
    }

    /// First detail read: thread names, array hashes, boxed values, direct buffer bodies and any search.
    fn prepare(&mut self) -> Result<()> {
        let (heap, view) = (&self.heap, &self.view);
        let (dump, graph) = (heap.dump, heap.graph);
        self.strings = strings::strings(dump, graph);
        let mut request = Request::default();
        for thread in &dump.threads {
            if let Some(name) = heap.field(thread.object, "name") {
                strings::string_ids(dump, graph, name, &mut request.want);
            }
        }
        let shows = |section: Section| view.sections.has(section) && !view.focused();
        let mut arrays = Vec::new();
        if view.sections.needs_hashes() && !view.focused() {
            request.hash = self.strings.iter().map(|&(_, array)| dump.objects[array as usize].id).collect();
        }
        if shows(Section::Arrays) {
            arrays = heap.hashable_arrays(&self.strings);
            request.content = arrays.iter().map(|&array| dump.objects[array as usize].id).collect();
        }
        if shows(Section::Boxed) {
            request.boxed = heap
                .boxed_classes()
                .into_iter()
                .map(|(class, id, offset, ty)| (id, (class, offset, ty)))
                .collect();
        }
        let buffers = if shows(Section::Direct) { heap.direct_buffers() } else { Vec::new() };
        request.want.extend(heap.direct_wants(&buffers));
        self.add_search(&mut request, view.find.as_deref(), view.filter.as_deref())?;
        let fetched = detail::fetch(&self.source, dump, request)?;

        let names: Vec<String> = dump
            .threads
            .iter()
            .map(|thread| {
                heap.field(thread.object, "name")
                    .and_then(|name| strings::string_text(dump, graph, &fetched, name))
                    .unwrap_or_default()
            })
            .collect();
        let hash_of = |array: u32| fetched.hash_of(dump.objects[array as usize].id);
        if shows(Section::Strings) {
            self.inputs.duplicates = Some(heap.duplicates(&self.strings, hash_of));
        }
        if shows(Section::Arrays) {
            self.inputs.array_duplicates = Some(heap.array_duplicates(&arrays, hash_of));
        }
        if shows(Section::Boxed) {
            self.inputs.boxed = heap.boxed(&fetched.boxed);
        }
        if shows(Section::Direct) {
            self.inputs.direct = Some(heap.direct(&buffers, &fetched));
        }
        self.take_search(&fetched);
        self.heap.thread_names = names;
        self.fetched = fetched;
        Ok(())
    }

    /// Add `--find` / `--where` to a request.
    fn add_search(&self, request: &mut Request, find: Option<&str>, filter: Option<&str>) -> Result<()> {
        let (heap, dump) = (&self.heap, self.heap.dump);
        if let Some(text) = find {
            let ids = self.strings.iter().map(|&(_, array)| dump.objects[array as usize].id).collect();
            request.search = Some((ids, strings::Needle::new(text)));
        }
        if let Some(text) = filter {
            let usage = || Error::Usage(format!("`{text}`: expected CLASS.FIELD=VALUE"));
            let (class_field, expect) = text.rsplit_once('=').ok_or_else(usage)?;
            let (class, field) = class_field.rsplit_once('.').ok_or_else(usage)?;
            let classes: dump::FastMap<u64, (u32, hprof::Ty)> = heap
                .classes_matching(&Pattern::parse(class))
                .into_iter()
                .filter_map(|class_index| {
                    dump.field_offset(class_index, field)
                        .map(|slot| (dump.classes[class_index as usize].id, slot))
                })
                .collect();
            if classes.is_empty() {
                return Err(Error::Usage(format!("no class matching `{class}` has a field `{field}`")));
            }
            request.filter = Some(Filter { classes, expect: expect.trim().to_string() });
        }
        Ok(())
    }

    /// Turn a read's search hits into objects, biggest retained first.
    fn take_search(&mut self, fetched: &Fetched) {
        let (heap, dump) = (&self.heap, self.heap.dump);
        if fetched.found.is_empty() && fetched.matched.is_empty() {
            self.inputs.found = Vec::new();
            self.inputs.matched = Vec::new();
            return;
        }
        let mut by_array: dump::FastMap<u64, u32> = dump::FastMap::default();
        for &(string, array) in &self.strings {
            by_array.entry(dump.objects[array as usize].id).or_insert(string);
        }
        let mut found: Vec<u32> = fetched.found.iter().filter_map(|id| by_array.get(id).copied()).collect();
        found.sort_by(|&a, &b| heap.retained(b).cmp(&heap.retained(a)).then(a.cmp(&b)));
        let mut matched: Vec<u32> = fetched.matched.iter().filter_map(|&id| dump.lookup(id)).collect();
        matched.sort_by(|&a, &b| heap.retained(b).cmp(&heap.retained(a)).then(a.cmp(&b)));
        self.inputs.found = found;
        self.inputs.matched = matched;
    }

    /// Run a search read for the shell.
    pub fn search(&mut self, find: Option<&str>, filter: Option<&str>) -> Result<()> {
        let mut request = Request::default();
        self.add_search(&mut request, find, filter)?;
        let fetched = detail::fetch(&self.source, self.heap.dump, request)?;
        self.take_search(&fetched);
        Ok(())
    }

    /// Render a view, reading whatever strings it needs first.
    pub fn show(&mut self, view: &View) -> Result<String> {
        self.source.progress.stage("building the report");
        let plan = Plan::new(&self.heap, view, &self.inputs)?;
        let want: Vec<u64> =
            plan.wants().into_iter().filter(|id| !self.fetched.raw.contains_key(id)).collect();
        if !want.is_empty() {
            let more = detail::fetch(&self.source, self.heap.dump, Request { want, ..Request::default() })?;
            self.fetched.merge(more);
        }
        self.source.progress.end();
        let elapsed = self.source.progress.elapsed();
        Ok(if self.json {
            plan.json(&self.fetched, elapsed)
        } else {
            plan.render(&self.fetched, self.color, elapsed)
        })
    }
}
