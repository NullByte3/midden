use std::path::PathBuf;

use clap::{Parser, ValueEnum};

use crate::{SizeMode, Sort};

const AFTER_HELP: &str = "\
EXAMPLES:
  midden server.hprof                          the whole story
  midden server.hprof --class ObjectMapper     one class: referrers, owners, root paths
  midden server.hprof --object 0x7f3a1234      one object: fields, owners, what it retains
  midden after.hprof --baseline before.hprof   what grew between two dumps
  midden server.hprof --json                   for scripts
  midden server.hprof --shell                  then drill in without re-reading the file";

/// Find what is holding a JVM heap dump's memory: retained sizes, owners, leak suspects.
#[derive(Parser, Debug)]
#[command(name = "midden", version, about, after_help = AFTER_HELP)]
pub struct Args {
    /// The .hprof file from `jcmd <pid> GC.heap_dump`, `jmap` or -XX:+HeapDumpOnOutOfMemoryError.
    /// Also reads gzipped dumps (`-gz=1`) and dumps inside a tar, gzipped tar or zip.
    #[arg(value_name = "FILE")]
    pub file: PathBuf,

    /// Rows to show in each table.
    #[arg(long, default_value_t = 20, value_name = "N")]
    pub top: usize,

    /// How deep to expand the dominator tree under each of the biggest objects.
    #[arg(long, default_value_t = 4, value_name = "N")]
    pub depth: usize,

    /// Hide dominator-tree branches below this share of the live heap, in percent.
    #[arg(long, default_value_t = 1.0, value_name = "PCT")]
    pub min: f64,

    /// Leak suspect threshold for an object or a class's instances, in percent of the live heap.
    #[arg(long, default_value_t = 10.0, value_name = "PCT")]
    pub suspect: f64,

    /// Focus on classes matching a pattern: a substring, a glob (`java.util.*Map`)
    /// or `=exact.Name`. Shows instances, referrers, owners and root paths.
    #[arg(long, value_name = "PATTERN")]
    pub class: Option<String>,

    /// Inspect one object: an id the report prints (0x…), `suspect:N`, `top:N`,
    /// or a static field path like `demo.Holder.CACHE[2].tag`.
    #[arg(long, value_name = "ID")]
    pub object: Option<String>,

    /// Strings whose text contains this (ASCII case-insensitive), and who holds them.
    #[arg(long, value_name = "TEXT")]
    pub find: Option<String>,

    /// Objects whose field equals a value, as CLASS.FIELD=VALUE; reference fields take `null` or 0x… ids.
    #[arg(long = "where", value_name = "CLASS.FIELD=VALUE")]
    pub filter: Option<String>,

    /// An earlier dump of the same process: what grew since, by class,
    /// structure, thread, loader and duplicate string.
    #[arg(long, value_name = "FILE")]
    pub baseline: Option<PathBuf>,

    /// Let weak and phantom references keep their referents alive.
    #[arg(long)]
    pub include_weak: bool,

    /// Let soft references keep their referents alive.
    #[arg(long)]
    pub include_soft: bool,

    /// Root paths to show per object, each through a different referrer.
    #[arg(long, default_value_t = 1, value_name = "N")]
    pub paths: usize,

    /// Print long root paths in full instead of eliding the middle.
    #[arg(long)]
    pub full_paths: bool,

    /// Order of the class table.
    #[arg(long, value_enum, default_value_t = Sort::Retained, value_name = "KEY")]
    pub sort: Sort,

    /// Roll the class table up by package.
    #[arg(long)]
    pub by_package: bool,

    /// Hide classes matching a pattern from suspects and tables; repeatable.
    #[arg(long, value_name = "PATTERN")]
    pub exclude: Vec<String>,

    /// Print only these sections (comma-separated): heap, suspects, biggest,
    /// classes, collections, threads, locals, loaders, strings, arrays, boxed,
    /// references, garbage, system, direct, baseline.
    #[arg(long, value_name = "LIST")]
    pub only: Option<String>,

    /// Leave these sections out (comma-separated); skipping strings and arrays skips array hashing too.
    #[arg(long, value_name = "LIST")]
    pub skip: Option<String>,

    /// Object size convention: MAT's, `HotSpot`'s with compressed oops, full width, or auto from addresses.
    #[arg(long, value_enum, default_value_t = SizeMode::Mat, value_name = "MODE")]
    pub sizes: SizeMode,

    /// Worker threads for the file passes and scans; one per core by default.
    #[arg(long, default_value_t = std::thread::available_parallelism().map_or(crate::parallel::DEFAULT_THREADS, |n| n.get()), value_name = "N")]
    pub threads: usize,

    /// Emit the report as JSON.
    #[arg(long)]
    pub json: bool,

    /// Do not read or write the index cache next to the dump.
    #[arg(long)]
    pub no_cache: bool,

    /// After the report, take commands on stdin to drill in without re-reading.
    #[arg(long)]
    pub shell: bool,

    /// When to colourise the output.
    #[arg(long, value_enum, default_value_t = ColorWhen::Auto, value_name = "WHEN")]
    pub color: ColorWhen,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, ValueEnum)]
pub enum ColorWhen {
    Auto,
    Always,
    Never,
}
