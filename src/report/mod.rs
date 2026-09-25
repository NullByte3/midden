//! The heap as a terminal report or JSON: the requested sections, or a focused view of one class,
//! object or search. `Plan` decides what to show and which strings to fetch; `Render` prints it.

/// `writeln!` into the report's `String`, which cannot fail.
macro_rules! outln {
    ($($arg:tt)*) => {{
        use std::fmt::Write as _;
        let _ = writeln!($($arg)*);
    }};
}

mod diff;
mod focus;
mod json;
mod overview;
mod sections;

use std::time::Duration;

use clap::ValueEnum;

use super::analysis::baseline::{Diff, Snapshot};
use super::analysis::collections::Collections;
use super::analysis::duplicates::{ArrayDuplicates, BoxedRow, Duplicates};
use super::analysis::loaders::{LoaderRow, Stale};
use super::analysis::native::Direct;
use super::analysis::references::{Finalizers, ReferenceRow};
use super::analysis::suspects::Suspect;
use super::analysis::threads::{ThreadLocals, ThreadRow};
use super::analysis::{ClassRow, Heap, Referrer, STATIC};
use super::detail::Fetched;
use super::dump::{Kind, NONE};
use super::graph::{ARRAY_ELEMENT, LOADER};
use super::options::{Section, Sections, Sort};
use super::pattern::{Pattern, short};
use super::strings;
use crate::cli::Args;
use crate::error::{Error, Result};
pub(crate) use crate::fmt::{commas, date_utc, human_bytes};

/// Classes `--class` reports on in full.
const MAX_FOCUS_CLASSES: usize = 8;
/// Dominators listed as the `--object` owners in JSON.
const OWNERS_LISTED: usize = 12;
/// Outgoing edges of the `--object` whose targets are fetched to describe them.
const EDGES_FETCHED: usize = 200;
/// Owners shown under each `--find` match.
const FOUND_OWNERS: usize = 4;
/// Stack locals shown under each thread.
const THREAD_LOCALS_SHOWN: usize = 3;
/// Paths longer than this show their first and last hops only, unless `--full-paths`.
const MAX_UNCUT_PATH: usize = 12;
const PATH_HEAD_HOPS: usize = 6;
const PATH_TAIL_HOPS: usize = 4;
/// Characters of a String shown in an object description.
const TEXT_PREVIEW_CHARS: usize = 48;

/// What one report shows; the shell edits it between commands.
#[derive(Clone)]
pub struct View {
    pub top: usize,
    pub depth: usize,
    pub min: f64,
    pub suspect: f64,
    pub sections: Sections,
    pub sort: Sort,
    pub by_package: bool,
    pub paths: usize,
    pub full_paths: bool,
    pub class: Option<Pattern>,
    pub object: Option<String>,
    pub find: Option<String>,
    pub filter: Option<String>,
    /// Classes hidden from suspects and tables.
    pub excludes: Vec<Pattern>,
}

impl View {
    pub fn from_args(args: &Args) -> Result<View> {
        Ok(View {
            top: args.top,
            depth: args.depth,
            min: args.min,
            suspect: args.suspect,
            sections: Sections::from_args(args.only.as_deref(), args.skip.as_deref())?,
            sort: args.sort,
            by_package: args.by_package,
            paths: args.paths.max(1),
            full_paths: args.full_paths,
            class: args.class.as_deref().map(Pattern::parse),
            object: args.object.clone(),
            find: args.find.clone(),
            filter: args.filter.clone(),
            excludes: args.exclude.iter().map(|pattern| Pattern::parse(pattern)).collect(),
        })
    }

    pub fn focused(&self) -> bool {
        self.class.is_some() || self.object.is_some() || self.find.is_some() || self.filter.is_some()
    }
}

/// Results of the first detail read, handed to the plan.
#[derive(Default)]
pub struct Inputs {
    pub duplicates: Option<Duplicates>,
    pub array_duplicates: Option<ArrayDuplicates>,
    pub boxed: Vec<BoxedRow>,
    pub direct: Option<Direct>,
    /// Strings that matched `--find`.
    pub found: Vec<u32>,
    /// Instances that matched `--where`.
    pub matched: Vec<u32>,
    pub baseline: Option<Snapshot>,
}

/// One printed line of a dominator tree: an object, or the summary of the
/// children left unprinted under one.
pub struct TreeRow {
    pub depth: usize,
    pub object: u32,
    pub label: Option<u32>,
    pub hidden: Option<(u64, u64)>,
}

/// Everything the report prints, computed first so its strings are fetched in one read.
pub struct Plan<'a> {
    pub heap: &'a Heap<'a>,
    pub view: &'a View,
    pub histogram: Vec<ClassRow>,
    pub packages: Vec<(String, ClassRow)>,
    pub suspects: Vec<Suspect>,
    pub trees: Vec<Vec<TreeRow>>,
    pub collections: Option<Collections>,
    pub threads: Vec<ThreadRow>,
    pub locals: Option<ThreadLocals>,
    pub loaders: Vec<LoaderRow>,
    pub stale: Vec<Stale>,
    /// Who references each stale loader, in `stale` order.
    pub stale_referrers: Vec<Vec<Referrer>>,
    pub references: Vec<ReferenceRow>,
    pub finalizers: Option<Finalizers>,
    pub cleaners: u64,
    pub garbage: Vec<ClassRow>,
    pub system_properties: Vec<(u32, u32)>,
    pub inputs: &'a Inputs,
    pub diff: Option<Diff>,
    pub focus_classes: Vec<u32>,
    pub focus_object: Option<u32>,
    /// Objects the report prints; the Strings among them get their text.
    pub shown: Vec<u32>,
}

impl<'a> Plan<'a> {
    pub fn new(heap: &'a Heap<'a>, view: &'a View, inputs: &'a Inputs) -> Result<Plan<'a>> {
        let histogram = heap.histogram();
        let focus_classes =
            view.class.as_ref().map(|pattern| heap.classes_matching(pattern)).unwrap_or_default();
        let mut plan = Plan {
            heap,
            view,
            histogram,
            packages: Vec::new(),
            suspects: Vec::new(),
            trees: Vec::new(),
            collections: None,
            threads: Vec::new(),
            locals: None,
            loaders: Vec::new(),
            stale: Vec::new(),
            stale_referrers: Vec::new(),
            references: Vec::new(),
            finalizers: None,
            cleaners: 0,
            garbage: Vec::new(),
            system_properties: Vec::new(),
            inputs,
            diff: None,
            focus_classes,
            focus_object: None,
            shown: Vec::new(),
        };
        plan.focus_object = view.object.as_deref().map(|text| plan.resolve(text)).transpose()?;
        if view.focused() {
            plan.plan_focus();
        } else {
            plan.plan_sections();
        }
        Ok(plan)
    }

    fn plan_sections(&mut self) {
        let (heap, view) = (self.heap, self.view);
        let shows = |section: Section| view.sections.has(section);
        if shows(Section::Suspects) {
            self.plan_suspects();
        }
        if shows(Section::Biggest) {
            let floor = (heap.live as f64 * view.min / 100.0) as u64;
            for &top in heap.top_level().iter().take(view.top) {
                let mut rows = Vec::new();
                self.tree(top, None, 0, floor, &mut rows);
                self.trees.push(rows);
            }
        }
        if shows(Section::Classes) && view.by_package {
            self.packages = heap.packages(&self.histogram);
        }
        if shows(Section::Collections) {
            let collections = heap.collections();
            self.shown.extend(collections.sparse.iter().take(view.top).map(|sparse| sparse.object));
            self.shown.extend(collections.colliding.iter().take(view.top).map(|&(object, _)| object));
            self.collections = Some(collections);
        }
        if shows(Section::Threads) {
            self.threads = heap.threads();
            for thread in &self.threads {
                self.shown.extend(thread.locals.iter().take(THREAD_LOCALS_SHOWN).map(|local| local.object));
            }
        }
        if shows(Section::Locals) {
            let locals = heap.thread_locals();
            self.shown.extend(locals.values.iter().take(view.top).map(|local| local.value));
            self.locals = Some(locals);
        }
        if shows(Section::Loaders) {
            self.plan_loaders();
        }
        if let Some(duplicates) = self.inputs.duplicates.as_ref().filter(|_| shows(Section::Strings)) {
            self.shown.extend(duplicates.groups.iter().take(view.top).map(|group| group.string));
        }
        if shows(Section::References) {
            self.references = heap.references();
            self.finalizers = heap.finalizers();
            self.cleaners = heap.cleaners();
        }
        if shows(Section::Garbage) {
            self.garbage = heap.garbage();
        }
        if shows(Section::System) {
            self.system_properties = heap.system_properties();
            self.shown.extend(self.system_properties.iter().flat_map(|&(key, value)| [key, value]));
        }
        if let Some(direct) = self.inputs.direct.as_ref().filter(|_| shows(Section::Direct)) {
            self.shown.extend(direct.buffers.iter().take(view.top).map(|buffer| buffer.object));
        }
        if let Some(baseline) = self.inputs.baseline.as_ref().filter(|_| shows(Section::Baseline)) {
            let diff = heap.diff(&self.histogram, self.inputs.duplicates.as_ref(), baseline);
            self.shown.extend(
                diff.strings.iter().take(view.top).map(|row| row.string).filter(|&string| string != NONE),
            );
            self.diff = Some(diff);
        }
    }

    fn plan_suspects(&mut self) {
        let heap = self.heap;
        self.suspects = heap.suspects(self.view.suspect, &self.histogram);
        for suspect in &self.suspects {
            match suspect {
                Suspect::Object(object) => {
                    self.shown.extend(object.hops.iter().flat_map(|hop| [hop.object, hop.end]));
                }
                Suspect::Class(class) => self.shown.push(class.biggest),
            }
        }
        for object in self.suspects.iter().map(Suspect::object).collect::<Vec<_>>() {
            self.show_paths(object);
        }
    }

    fn plan_loaders(&mut self) {
        let heap = self.heap;
        self.loaders = heap.loaders(&self.histogram);
        self.stale = heap.stale_loaders(&self.loaders);
        for loader in self
            .loaders
            .iter()
            .take(self.view.top)
            .map(|loader| loader.object)
            .chain(self.stale.iter().map(|stale| stale.object))
        {
            self.shown.extend(heap.loader_name(loader));
        }
        let stale: Vec<u32> = self.stale.iter().map(|stale| stale.object).collect();
        self.stale_referrers = heap.referrers(|object| stale.iter().position(|&loader| loader == object));
        for object in stale {
            self.show_paths(object);
        }
    }

    fn plan_focus(&mut self) {
        let (heap, view) = (self.heap, self.view);
        if let Some(object) = self.focus_object {
            self.shown.push(object);
            self.shown.extend(heap.graph.edges(object).targets().take(EDGES_FETCHED));
            self.shown.extend(
                heap.dominators.dominators_of(heap.graph.root, object).iter().take(OWNERS_LISTED).copied(),
            );
            self.shown.extend(heap.dominators.children(object).iter().take(view.top).copied());
            self.shown.extend(heap.referrer_objects(object, view.top).iter().map(|&(source, _)| source));
            for (key, value) in heap.entries(object, view.top) {
                self.shown.extend(key);
                self.shown.push(value);
            }
            self.show_paths(object);
        }
        for &class in &self.focus_classes.clone() {
            let instances = heap.instances_of(class);
            self.shown.extend(instances.iter().take(view.top));
            if let Some(&first) = instances.first() {
                self.show_paths(first);
            }
        }
        for &string in self.inputs.found.iter().take(view.top) {
            self.shown.push(string);
            self.shown.extend(
                heap.dominators.dominators_of(heap.graph.root, string).iter().take(FOUND_OWNERS).copied(),
            );
            self.shown.extend(heap.referrer_objects(string, 3).iter().map(|&(source, _)| source));
        }
        let matched: Vec<u32> = self.inputs.matched.iter().take(view.top).copied().collect();
        self.shown.extend(&matched);
        if let Some(&first) = matched.first() {
            self.show_paths(first);
        }
    }

    fn show_paths(&mut self, object: u32) {
        for path in self.heap.root_paths(object, self.view.paths) {
            self.shown.extend(path.iter().map(|&(object, _)| object));
        }
    }

    fn tree(&mut self, object: u32, label: Option<u32>, depth: usize, floor: u64, rows: &mut Vec<TreeRow>) {
        let heap = self.heap;
        self.shown.push(object);
        rows.push(TreeRow { depth, object, label, hidden: None });
        let mut hidden = (0u64, 0u64);
        for child in heap.dominators.children(object) {
            if depth + 1 >= self.view.depth || heap.retained(child) < floor.max(1) {
                hidden.0 += 1;
                hidden.1 += heap.retained(child);
                continue;
            }
            let label = heap.graph.label_of(object, child);
            self.tree(child, label, depth + 1, floor, rows);
        }
        if hidden.0 > 0 {
            rows.push(TreeRow { depth: depth + 1, object, label: None, hidden: Some(hidden) });
        }
    }

    /// Ids to fetch before rendering: every String on show, the inspected
    /// object's own record, and the arrays whose contents get previewed.
    pub fn wants(&self) -> Vec<u64> {
        let (dump, graph) = (self.heap.dump, self.heap.graph);
        let mut want = Vec::new();
        let mut shown = self.shown.clone();
        shown.sort_unstable();
        shown.dedup();
        for object in shown {
            if self.heap.is_string(object) {
                strings::string_ids(dump, graph, object, &mut want);
            }
        }
        if let Some(object) = self.focus_object {
            want.push(dump.objects[object as usize].id);
        }
        if let Some(arrays) = &self.inputs.array_duplicates {
            want.extend(
                arrays.groups.iter().take(self.view.top).map(|group| dump.objects[group.array as usize].id),
            );
        }
        want
    }

    /// An object named the way reports and users spell one: a `0x…` id,
    /// `suspect:N`, `top:N`, or a static field path like `demo.Holder.CACHE[2].tag`.
    pub fn resolve(&self, text: &str) -> Result<u32> {
        let heap = self.heap;
        let text = text.trim();
        if let Some(rest) = text.strip_prefix("suspect:") {
            let index: usize =
                rest.parse().map_err(|_| Error::Usage(format!("`{text}`: expected suspect:N")))?;
            let suspects = heap.suspects(self.view.suspect, &self.histogram);
            return suspects
                .get(index.wrapping_sub(1))
                .map(Suspect::object)
                .ok_or_else(|| Error::Usage(format!("there is no suspect {index}")));
        }
        if let Some(rest) = text.strip_prefix("top:") {
            let index: usize = rest.parse().map_err(|_| Error::Usage(format!("`{text}`: expected top:N")))?;
            return heap
                .top_level()
                .get(index.wrapping_sub(1))
                .copied()
                .ok_or_else(|| Error::Usage(format!("there is no top-level object {index}")));
        }
        if let Some(id) = parse_id(text) {
            return heap
                .dump
                .lookup(id)
                .ok_or_else(|| Error::Usage(format!("no object with id 0x{id:x} in the dump")));
        }
        focus::resolve_path(heap, text)
    }

    pub fn render(&self, fetched: &Fetched, color: bool, elapsed: Duration) -> String {
        let style = if color { COLOR } else { PLAIN };
        let render = Render { plan: self, heap: self.heap, style, fetched };
        let mut out = String::new();
        render.header(&mut out, elapsed);
        if self.view.focused() {
            if let Some(object) = self.focus_object {
                render.object(&mut out, object);
            }
            if self.view.class.is_some() {
                render.focus(&mut out);
            }
            if self.view.find.is_some() {
                render.found(&mut out);
            }
            if self.view.filter.is_some() {
                render.matched(&mut out);
            }
            return out;
        }
        for &section in Section::value_variants().iter().filter(|&&section| self.view.sections.has(section)) {
            match section {
                Section::Heap => render.heap_section(&mut out),
                Section::Suspects => render.suspects(&mut out),
                Section::Biggest => render.biggest(&mut out),
                Section::Classes => render.classes(&mut out),
                Section::Collections => render.collections(&mut out),
                Section::Threads => render.threads(&mut out),
                Section::Locals => render.locals(&mut out),
                Section::Loaders => render.loaders(&mut out),
                Section::Strings => render.duplicates(&mut out),
                Section::Arrays => render.arrays(&mut out),
                Section::Boxed => render.boxed(&mut out),
                Section::References => render.references(&mut out),
                Section::Garbage => render.garbage(&mut out),
                Section::System => render.system(&mut out),
                Section::Direct => render.direct(&mut out),
                Section::Baseline => render.baseline(&mut out),
            }
        }
        out
    }

    pub fn json(&self, fetched: &Fetched, elapsed: Duration) -> String {
        let render = Render { plan: self, heap: self.heap, style: PLAIN, fetched };
        serde_json::to_string_pretty(&render.json(elapsed)).unwrap_or_default() + "\n"
    }
}

/// An object id as printed in reports (`0x7f3a1234`, `@0x…`) or decimal.
pub fn parse_id(text: &str) -> Option<u64> {
    let trimmed = text.trim().trim_start_matches('@');
    let parsed = match trimmed.strip_prefix("0x").or_else(|| trimmed.strip_prefix("0X")) {
        Some(hex) => u64::from_str_radix(hex, 16).ok(),
        None => trimmed.parse::<u64>().ok(),
    };
    parsed.filter(|&id| id != 0)
}

/// Terminal escapes for the report, empty when colour is off.
pub struct Style {
    bold: &'static str,
    dim: &'static str,
    yellow: &'static str,
    reset: &'static str,
}
const COLOR: Style = Style { bold: "\x1b[1m", dim: "\x1b[2m", yellow: "\x1b[33m", reset: "\x1b[0m" };
const PLAIN: Style = Style { bold: "", dim: "", yellow: "", reset: "" };

pub struct Render<'p, 'a> {
    plan: &'p Plan<'a>,
    heap: &'a Heap<'a>,
    style: Style,
    fetched: &'p Fetched,
}

impl Render<'_, '_> {
    fn title(&self, out: &mut String, text: &str) {
        outln!(out, "\n  {}{text}{}", self.style.bold, self.style.reset);
    }

    fn line(&self, out: &mut String, text: &str) {
        outln!(out, "  {}{text}{}", self.style.dim, self.style.reset);
    }

    fn warn(&self, out: &mut String, text: &str) {
        outln!(out, "  {}{text}{}", self.style.yellow, self.style.reset);
    }

    /// A dimmed line inside a section: a table header or a "more" tail.
    fn dim_line(&self, out: &mut String, text: &str) {
        outln!(out, "    {}", self.dim(text));
    }

    fn section(&self, out: &mut String, name: &str, note: &str) {
        let sep = if note.is_empty() { "" } else { "  " };
        outln!(
            out,
            "\n  {}{name}{}{sep}{}{note}{}",
            self.style.bold,
            self.style.reset,
            self.style.dim,
            self.style.reset
        );
    }

    fn bold(&self, text: &str) -> String {
        format!("{}{text}{}", self.style.bold, self.style.reset)
    }

    fn dim(&self, text: &str) -> String {
        format!("{}{text}{}", self.style.dim, self.style.reset)
    }

    fn percent(&self, bytes: u64) -> String {
        format!("{:.1}%", self.heap.percent_of_live(bytes))
    }

    fn top(&self) -> usize {
        self.plan.view.top
    }

    /// An object for a line: `java.util.HashMap @0x7f3a1234`, arrays with
    /// their length, strings with their text, class objects by class.
    fn describe(&self, object: u32) -> String {
        let (dump, record) = (self.heap.dump, &self.heap.dump.objects[object as usize]);
        let name = &dump.classes[record.class as usize].name;
        match record.kind {
            Kind::Class => format!("{} @0x{:x}", self.heap.kind_text(object), record.id),
            Kind::ObjectArray | Kind::PrimitiveArray => {
                let base = name.strip_suffix("[]").unwrap_or(name);
                format!("{base}[{}] @0x{:x}", commas(u64::from(record.len)), record.id)
            }
            Kind::Instance => match self.text(object) {
                Some(text) => format!("{name} \"{text}\" @0x{:x}", record.id),
                None => format!("{name} @0x{:x}", record.id),
            },
        }
    }

    /// A String's text, when it is one and its bytes were fetched.
    fn text(&self, object: u32) -> Option<String> {
        if !self.heap.is_string(object) {
            return None;
        }
        strings::string_text(self.heap.dump, self.heap.graph, self.fetched, object)
            .map(|text| strings::preview(&text, TEXT_PREVIEW_CHARS))
    }

    fn quoted(&self, object: u32) -> String {
        self.text(object).map_or_else(|| self.describe(object), |text| format!("\"{text}\""))
    }

    /// An edge as text: `.field`, `[17]`, or `static Owner.FIELD`.
    fn label(&self, from: Option<u32>, label: Option<u32>) -> String {
        match label {
            None => String::new(),
            Some(edge) if edge & ARRAY_ELEMENT != 0 && edge != LOADER => {
                format!("[{}]", edge & !ARRAY_ELEMENT)
            }
            Some(edge) => self.heap.edge_text(from, edge),
        }
    }

    /// A dominator tree row's edge from its parent.
    fn tree_label(&self, row: &TreeRow) -> String {
        let from = (row.depth > 0).then(|| self.heap.dominators.idom[row.object as usize]);
        self.label(from, row.label)
    }

    fn class_name(&self, class: u32) -> &str {
        &self.heap.dump.classes[class as usize].name
    }

    /// `Name ×count | …` for the first `take` classes.
    fn class_counts(&self, counts: &[(u32, u64)], take: usize) -> String {
        let items: Vec<String> = counts
            .iter()
            .take(take)
            .map(|&(class, count)| format!("{} ×{}", self.class_name(class), commas(count)))
            .collect();
        items.join(" | ")
    }

    /// A class's histogram row, zero when it has no instances.
    fn histogram_row(&self, class: u32) -> ClassRow {
        let row = self.plan.histogram.iter().find(|row| row.class == class).copied();
        row.unwrap_or(ClassRow { class, instances: 0, shallow: 0, retained: 0 })
    }

    /// `  ← root note` after a top-level object, empty when it has none.
    fn root_mark(&self, object: u32) -> String {
        match self.heap.root_note(object) {
            note if note.is_empty() => note,
            note => self.dim(&format!("  ← {note}")),
        }
    }

    /// The system properties whose key and value texts were fetched.
    fn properties(&self) -> Vec<(String, String)> {
        let (dump, graph) = (self.heap.dump, self.heap.graph);
        self.plan
            .system_properties
            .iter()
            .filter_map(|&(key, value)| {
                Some((self.text(key)?, strings::string_text(dump, graph, self.fetched, value)?))
            })
            .collect()
    }

    fn keeps(&self, keeps: &[ClassRow]) -> String {
        keeps
            .iter()
            .take(4)
            .map(|row| {
                format!(
                    "{} × {} {}",
                    commas(row.instances),
                    short(self.class_name(row.class)),
                    human_bytes(row.shallow as f64)
                )
            })
            .collect::<Vec<_>>()
            .join(" | ")
    }

    fn referrer_text(&self, referrer: &Referrer) -> String {
        let dump = self.heap.dump;
        let class = self.class_name(referrer.class);
        let what = match referrer.label {
            ARRAY_ELEMENT => format!("{class} elements"),
            LOADER => format!("{class} <classloader>"),
            label if label & STATIC != 0 => {
                format!("static {class}.{}", dump.names[(label & !STATIC) as usize])
            }
            label => format!("{class}.{}", dump.names[label as usize]),
        };
        format!("{what} ×{}", commas(referrer.count))
    }

    fn referrers(&self, referrers: &[Referrer], take: usize) -> String {
        let items: Vec<String> =
            referrers.iter().take(take).map(|referrer| self.referrer_text(referrer)).collect();
        let more = referrers.len().saturating_sub(take);
        if more > 0 { format!("{} | +{more} more", items.join(" | ")) } else { items.join(" | ") }
    }

    fn owners(&self, owners: &[(u32, u64, u64)]) -> String {
        owners
            .iter()
            .map(|&(class, bytes, total)| {
                let share = if total == 0 { 100.0 } else { bytes as f64 * 100.0 / total as f64 };
                let name = match class {
                    NONE if owners.len() == 1 => {
                        "gc roots directly (more than one path keeps them alive)".to_string()
                    }
                    NONE => "gc roots".to_string(),
                    _ => self.class_name(class).to_string(),
                };
                if share >= 99.5 { name } else { format!("{name} {share:.0}%") }
            })
            .collect::<Vec<_>>()
            .join(" ← ")
    }

    /// The root paths to `object`, a hop per line, long paths elided unless asked.
    fn path_lines(&self, out: &mut String, object: u32, indent: &str) {
        let heap = self.heap;
        let paths = heap.root_paths(object, self.plan.view.paths);
        if paths.is_empty() {
            outln!(out, "{indent}{}", self.dim("unreachable from any gc root"));
            return;
        }
        let pad = " ".repeat(indent.chars().count());
        for (path_index, path) in paths.iter().enumerate() {
            let hop = |i: usize| -> String {
                let (object, label) = path[i];
                if i == 0 {
                    format!(
                        "{}  {}",
                        self.describe(object),
                        self.dim(&format!("← {}", heap.root_note(object)))
                    )
                } else {
                    format!("{} {}", self.label(Some(path[i - 1].0), label), self.describe(object))
                }
            };
            let lines: Vec<String> = if path.len() > MAX_UNCUT_PATH && !self.plan.view.full_paths {
                (0..PATH_HEAD_HOPS)
                    .map(hop)
                    .chain([
                        self.dim(&format!("… {} more hops …", path.len() - PATH_HEAD_HOPS - PATH_TAIL_HOPS))
                    ])
                    .chain((path.len() - PATH_TAIL_HOPS..path.len()).map(hop))
                    .collect()
            } else {
                (0..path.len()).map(hop).collect()
            };
            if path_index > 0 {
                outln!(out, "{pad}{}", self.dim("also via"));
            }
            for (i, line) in lines.iter().enumerate() {
                outln!(out, "{}{line}", if i == 0 && path_index == 0 { indent } else { &pad });
            }
        }
    }

    /// A loader with its name when it has one.
    fn loader_text(&self, loader: u32) -> String {
        if loader == NONE {
            return "bootstrap".to_string();
        }
        let name = self
            .heap
            .loader_name(loader)
            .and_then(|name| self.text(name))
            .map(|text| format!(" \"{text}\""))
            .unwrap_or_default();
        format!("{}{name}", self.describe(loader))
    }

    /// A `ThreadLocal` key: the static field that holds it, else its class.
    fn key_text(&self, key: u32) -> String {
        if key == NONE {
            return "(key collected)".to_string();
        }
        let path = self.heap.root_path(key);
        match path.last().and_then(|&(_, label)| label) {
            Some(label) if label & ARRAY_ELEMENT == 0 && path.len() >= 2 => {
                format!(
                    "{} {}",
                    self.heap.edge_text(Some(path[path.len() - 2].0), label),
                    short(self.heap.dump.class_name(key))
                )
            }
            _ => self.describe(key),
        }
    }
}
