//! The baseline section: what changed since an earlier dump of the process.

use super::overview::{delta, signed, signed_count};
use super::{Render, commas, human_bytes};
use crate::analysis::baseline::{NamedChange, StringChange, StructureChange};
use crate::dump::NONE;

impl Render<'_, '_> {
    pub(super) fn baseline(&self, out: &mut String) {
        let Some(diff) = &self.plan.diff else { return };
        let top = self.top();
        self.section(out, "since baseline", &diff.path);
        outln!(
            out,
            "    live heap {} | objects {} | file contents {}",
            signed(diff.live),
            signed_count(diff.objects),
            signed(diff.total)
        );
        if diff.classes.is_empty()
            && diff.structures.is_empty()
            && diff.threads.is_empty()
            && diff.loaders.is_empty()
            && diff.strings.is_empty()
        {
            outln!(out, "    nothing changed by class, structure, thread, loader or duplicate string");
            return;
        }
        self.dim_line(out, "Δ retained   Δ shallow  Δ instances  class");
        for class in diff.classes.iter().take(top) {
            outln!(
                out,
                "    {:>10} {:>11} {:>12}  {}",
                signed(class.retained.after - class.retained.before),
                signed(class.shallow.after - class.shallow.before),
                signed_count(class.instances.after - class.instances.before),
                class.name
            );
        }
        if diff.classes.len() > top {
            self.dim_line(
                out,
                &format!("+ {} more classes changed", commas((diff.classes.len() - top) as u64)),
            );
        }
        if !diff.structures.is_empty() {
            self.dim_line(out, "Δ retained  structure, matched by its root path");
            for StructureChange { key, object, before, after } in diff.structures.iter().take(top) {
                let what = if *object == NONE {
                    format!("{key}  {}", self.dim("(gone)"))
                } else {
                    self.describe(*object)
                };
                outln!(out, "    {:>10}  {what}  {}", delta(*before, *after), self.grew(*before, *after));
            }
        }
        if !diff.threads.is_empty() {
            self.dim_line(out, "Δ retained  thread");
            for NamedChange { name, before, after } in diff.threads.iter().take(top) {
                outln!(out, "    {:>10}  {name}  {}", delta(*before, *after), self.grew(*before, *after));
            }
        }
        if !diff.loaders.is_empty() {
            self.dim_line(out, "Δ owned     class loader");
            for NamedChange { name, before, after } in diff.loaders.iter().take(top) {
                outln!(out, "    {:>10}  {name}", delta(*before, *after));
            }
        }
        if !diff.strings.is_empty() {
            self.dim_line(out, "Δ wasted    copies  duplicate string");
            for &StringChange { string, hash, copies_before, copies_after, wasted_before, wasted_after } in
                diff.strings.iter().take(top)
            {
                let text = if string == NONE {
                    self.dim(&format!("(gone, hash {hash:x})"))
                } else {
                    self.quoted(string)
                };
                outln!(
                    out,
                    "    {:>10}  {:>6}  {text}",
                    delta(wasted_before, wasted_after),
                    format!("{copies_before}→{copies_after}")
                );
            }
        }
    }

    /// `1.2MB → 3.4MB`, dimmed.
    fn grew(&self, before: u64, after: u64) -> String {
        self.dim(&format!("{} → {}", human_bytes(before as f64), human_bytes(after as f64)))
    }
}
