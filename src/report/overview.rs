//! The headline sections: the file, the heap, the leak suspects, the biggest
//! objects and the class table.

use std::time::Duration;

use super::{Render, commas, date_utc, human_bytes};
use crate::analysis::suspects::Suspect;
use crate::dump::FastMap;
use crate::fmt::fmt_duration;
use crate::hprof::RootKind;
use crate::options::Sort;
use crate::pattern::short;

impl Render<'_, '_> {
    pub(super) fn header(&self, out: &mut String, elapsed: Duration) {
        let (dump, heap) = (self.heap.dump, self.heap);
        let bits = dump.header.id_size * 8;
        let gzip = if dump.gzip { " gzip" } else { "" };
        let member = dump.member.as_ref().map(|name| format!(", {name}")).unwrap_or_default();
        self.title(
            out,
            &format!(
                "heap dump {} | {} | {bits}-bit ids | {}{gzip} file{member}",
                dump.path,
                dump.header.format,
                human_bytes(dump.file_size as f64)
            ),
        );
        let taken = match dump.header.timestamp_ms {
            0 => String::new(),
            ms => format!("taken {} | ", date_utc(ms as i64)),
        };
        let classes = dump.classes.iter().filter(|class| class.dumped).count();
        self.line(
            out,
            &format!(
                "{taken}{} classes | {} objects | {} references | {} threads | sizes: {} | analysed in {}",
                commas(classes as u64),
                commas(dump.objects.len() as u64),
                commas(heap.graph.edge_count()),
                dump.threads.len(),
                dump.sizing.label(),
                fmt_duration(elapsed)
            ),
        );
        if dump.truncated {
            self.warn(
                out,
                "the file ends inside a record: the dump is truncated, so objects and references are missing",
            );
        }
        if heap.graph.dangling + dump.dangling_roots > 0 {
            self.line(
                out,
                &format!(
                    "{} references and {} roots point at objects the dump does not contain",
                    commas(heap.graph.dangling),
                    commas(dump.dangling_roots)
                ),
            );
        }
    }

    pub(super) fn heap_section(&self, out: &mut String) {
        let (dump, heap) = (self.heap.dump, self.heap);
        self.section(out, "heap", "");
        let garbage = heap.unreachable;
        outln!(
            out,
            "    {} in {} objects | {} live ({}) | {} in {} objects unreachable, garbage the dump still holds",
            human_bytes(heap.total as f64),
            commas(dump.objects.len() as u64),
            human_bytes(heap.live as f64),
            self.percent_of_total(heap.live),
            human_bytes(garbage.bytes as f64),
            commas(garbage.count)
        );
        if heap.weak_only.count > 0 {
            outln!(
                out,
                "    {} in {} objects reachable only through soft/weak/phantom references; not counted as retained by anything",
                human_bytes(heap.weak_only.bytes as f64),
                commas(heap.weak_only.count)
            );
        }
        if dump.marked_unreachable > 0 {
            outln!(out, "    {} objects the runtime marked unreachable", commas(dump.marked_unreachable));
        }
        let mut kinds: FastMap<RootKind, u64> = FastMap::default();
        for (_, root) in &dump.roots {
            *kinds.entry(root.kind).or_default() += 1;
        }
        let mut kinds: Vec<(RootKind, u64)> = kinds.into_iter().collect();
        kinds.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
        let list: Vec<String> = kinds
            .iter()
            .take(6)
            .map(|(kind, count)| format!("{} {}", commas(*count), kind.label()))
            .collect();
        outln!(out, "    gc roots  {} objects | {}", commas(heap.graph.roots.len() as u64), list.join(" | "));
    }

    fn percent_of_total(&self, bytes: u64) -> String {
        if self.heap.total == 0 {
            "0%".into()
        } else {
            format!("{:.1}%", bytes as f64 * 100.0 / self.heap.total as f64)
        }
    }

    /// The change since the baseline for a structure, when one matches.
    fn since(&self, object: u32) -> String {
        let Some(diff) = &self.plan.diff else { return String::new() };
        let key = self.heap.path_key(object);
        diff.structures.iter().find(|row| row.key == key).map_or_else(String::new, |row| {
            self.dim(&format!("  {} since baseline", delta(row.before, row.after)))
        })
    }

    pub(super) fn suspects(&self, out: &mut String) {
        let (heap, plan) = (self.heap, self.plan);
        let note = format!("objects or classes retaining ≥{:.0}% of the live heap", plan.view.suspect);
        self.section(out, "leak suspects", &note);
        if plan.suspects.is_empty() {
            outln!(
                out,
                "    nothing holds that much on its own; the biggest objects below are where to look (--suspect lowers the bar)"
            );
            return;
        }
        for (i, suspect) in plan.suspects.iter().enumerate() {
            let number = format!("{}{}.{}", self.style.yellow, i + 1, self.style.reset);
            match suspect {
                Suspect::Object(object) => {
                    let top = object.hops[0].object;
                    outln!(
                        out,
                        "    {number} {:>8}  {:>5}  {}{}{}",
                        human_bytes(heap.retained(top) as f64),
                        self.percent(heap.retained(top)),
                        self.describe(top),
                        self.root_mark(top),
                        self.since(top)
                    );
                    for (i, hop) in object.hops.iter().enumerate().skip(1) {
                        let last = i + 1 == object.hops.len();
                        let prev = object.hops[i - 1].end;
                        let mark = if last { self.dim("  ← accumulation point") } else { String::new() };
                        outln!(
                            out,
                            "         {:>8}  {:>5}  {} {}{mark}",
                            human_bytes(heap.retained(hop.object) as f64),
                            self.percent(heap.retained(hop.object)),
                            self.label(Some(prev), hop.label),
                            self.describe(hop.object)
                        );
                        if hop.chain > 1 {
                            let chain = format!(
                                "… a chain of {} {} linked by {}, ending at {}",
                                commas(hop.chain),
                                short(heap.dump.class_name(hop.object)),
                                self.label(None, hop.label),
                                self.describe(hop.end)
                            );
                            outln!(out, "                          {}", self.dim(&chain));
                        }
                    }
                    outln!(
                        out,
                        "       keeps  {} objects: {}",
                        commas(object.kept_objects),
                        self.keeps(&object.keeps)
                    );
                    self.path_lines(out, top, "       path   ");
                }
                Suspect::Class(class) => {
                    let name = self.class_name(class.row.class);
                    let each = class.row.retained.checked_div(class.row.instances).unwrap_or(0);
                    outln!(
                        out,
                        "    {number} {:>8}  {:>5}  {} × {name}{}",
                        human_bytes(class.row.retained as f64),
                        self.percent(class.row.retained),
                        commas(class.row.instances),
                        self.dim(&format!("  ~{} retained each", human_bytes(each as f64)))
                    );
                    if !class.referrers.is_empty() {
                        outln!(out, "       held by   {}", self.referrers(&class.referrers, 4));
                    }
                    if !class.owners.is_empty() {
                        outln!(out, "       owned by  {}", self.owners(&class.owners));
                    }
                    outln!(
                        out,
                        "       biggest   {} retains {}",
                        self.describe(class.biggest),
                        human_bytes(heap.retained(class.biggest) as f64)
                    );
                    self.path_lines(out, class.biggest, "       path      ");
                }
            }
        }
    }

    pub(super) fn biggest(&self, out: &mut String) {
        let (heap, plan) = (self.heap, self.plan);
        let note = format!(
            "by retained size | dominator tree to depth {}, branches ≥{:.1}% of the live heap",
            plan.view.depth, plan.view.min
        );
        self.section(out, "biggest objects", &note);
        for rows in &plan.trees {
            for row in rows {
                let indent = " ".repeat(4 + row.depth * 2);
                if let Some((count, bytes)) = row.hidden {
                    let more = format!(
                        "+ {} smaller or deeper branches, {}",
                        commas(count),
                        human_bytes(bytes as f64)
                    );
                    outln!(out, "{indent}{}", self.dim(&more));
                    continue;
                }
                let label = self.tree_label(row);
                let label = if row.depth > 0 && label.is_empty() { self.dim("(indirectly)") } else { label };
                let (note, since) = if row.depth == 0 {
                    (self.root_mark(row.object), self.since(row.object))
                } else {
                    Default::default()
                };
                let sep = if label.is_empty() { "" } else { " " };
                outln!(
                    out,
                    "{indent}{:>8}  {:>5}  {label}{sep}{}{note}{since}",
                    human_bytes(heap.retained(row.object) as f64),
                    self.percent(heap.retained(row.object)),
                    self.describe(row.object)
                );
            }
        }
        let rest = heap.top_level().len().saturating_sub(plan.trees.len());
        if rest > 0 {
            self.dim_line(out, &format!("+ {} more top-level objects", commas(rest as u64)));
        }
    }

    pub(super) fn classes(&self, out: &mut String) {
        let plan = self.plan;
        if plan.view.by_package {
            let note = format!(
                "by package | top {} of {}",
                plan.view.top.min(plan.packages.len()),
                commas(plan.packages.len() as u64)
            );
            self.section(out, "packages", &note);
            self.dim_line(out, " retained   shallow   instances  package");
            for (name, row) in plan.packages.iter().take(plan.view.top) {
                let name = if name.is_empty() { "(default package and arrays)" } else { name };
                outln!(
                    out,
                    "    {:>9} {:>9} {:>11}  {name}",
                    human_bytes(row.retained as f64),
                    human_bytes(row.shallow as f64),
                    commas(row.instances)
                );
            }
            return;
        }
        let mut rows: Vec<_> = plan.histogram.iter().filter(|row| !self.heap.excluded(row.class)).collect();
        let name = |class: u32| self.class_name(class);
        match plan.view.sort {
            Sort::Retained => {}
            Sort::Shallow => rows.sort_by(|a, b| b.shallow.cmp(&a.shallow).then(a.class.cmp(&b.class))),
            Sort::Instances => rows.sort_by(|a, b| b.instances.cmp(&a.instances).then(a.class.cmp(&b.class))),
            Sort::Name => rows.sort_by(|a, b| name(a.class).cmp(name(b.class))),
        }
        let sort = match plan.view.sort {
            Sort::Retained => "retained size",
            Sort::Shallow => "shallow size",
            Sort::Instances => "instance count",
            Sort::Name => "name",
        };
        let note =
            format!("top {} of {} by {sort}", plan.view.top.min(rows.len()), commas(rows.len() as u64));
        self.section(out, "classes", &note);
        self.dim_line(out, " retained   shallow   instances  class");
        for row in rows.iter().take(plan.view.top) {
            outln!(
                out,
                "    {:>9} {:>9} {:>11}  {}",
                human_bytes(row.retained as f64),
                human_bytes(row.shallow as f64),
                commas(row.instances),
                name(row.class)
            );
        }
    }
}

/// `+1.2MB` / `-300KB`.
pub(super) fn signed(bytes: i64) -> String {
    format!("{}{}", sign(bytes), human_bytes(bytes.unsigned_abs() as f64))
}

/// The signed change from `before` to `after` bytes.
pub(super) fn delta(before: u64, after: u64) -> String {
    signed(after as i64 - before as i64)
}

pub(super) fn signed_count(count: i64) -> String {
    format!("{}{}", sign(count), commas(count.unsigned_abs()))
}

fn sign(value: i64) -> char {
    if value < 0 { '-' } else { '+' }
}
