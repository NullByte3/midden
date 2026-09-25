//! The topic sections: collections, threads and thread locals, class loaders,
//! duplicates, references, garbage, system properties and direct buffers.

use super::{Render, THREAD_LOCALS_SHOWN, commas, human_bytes};
use crate::analysis::duplicates::MIN_ARRAY_DATA_BYTES;
use crate::analysis::threads::StackLocal;
use crate::dump::{FastMap, NONE};
use crate::hprof::{RootKind, Ty, Value};
use crate::strings;

/// Frames shown of each thread's stack.
const STACK_FRAMES_SHOWN: usize = 3;
/// Characters of an array shown as text.
const ARRAY_TEXT_CHARS: usize = 40;
/// Elements of an array shown when it does not read as text.
const ARRAY_ELEMENTS_SHOWN: usize = 12;
/// Characters of a system property value shown.
const PROPERTY_VALUE_CHARS: usize = 90;

impl Render<'_, '_> {
    pub(super) fn collections(&self, out: &mut String) {
        let Some(collections) = &self.plan.collections else { return };
        if collections.rows.is_empty() && collections.sparse.is_empty() {
            return;
        }
        let wasted: u64 = collections.rows.iter().map(|row| row.wasted).sum();
        let note = format!(
            "{} of empty slots | {} empty collections holding {}",
            human_bytes(wasted as f64),
            commas(collections.empty.count),
            human_bytes(collections.empty.bytes as f64)
        );
        self.section(out, "collections", &note);
        self.dim_line(out, " instances     entries    capacity  fill    wasted     empty  class");
        for row in collections.rows.iter().take(self.top()) {
            let fill =
                if row.capacity == 0 { 100.0 } else { row.entries as f64 * 100.0 / row.capacity as f64 };
            outln!(
                out,
                "    {:>9} {:>11} {:>11} {:>4.0}% {:>9} {:>9}  {}",
                commas(row.instances),
                commas(row.entries),
                commas(row.capacity),
                fill.min(100.0),
                human_bytes(row.wasted as f64),
                commas(row.empty),
                self.class_name(row.class)
            );
        }
        if !collections.sparse.is_empty() {
            self.dim_line(out, "under-filled  most empty slots first");
            for sparse in collections.sparse.iter().take(self.top()) {
                let (entries, capacity) = (sparse.stats.entries, sparse.stats.capacity);
                let fill = entries as f64 * 100.0 / capacity.max(1) as f64;
                let slots = self.dim(&format!("{} of {} slots", commas(entries), commas(capacity)));
                let wasted = human_bytes(sparse.wasted as f64);
                outln!(out, "    {wasted:>9}  {fill:>4.0}%  {}  {slots}", self.describe(sparse.object));
            }
        }
        if !collections.colliding.is_empty() {
            self.dim_line(out, "colliding  hash tables with the most chained entries");
            for (object, stats) in collections.colliding.iter().take(self.top()) {
                let chained = commas(stats.entries - stats.used_buckets);
                let buckets =
                    format!("{} entries in {} buckets", commas(stats.entries), commas(stats.used_buckets));
                outln!(out, "    {chained:>9}  {}  {}", self.describe(*object), self.dim(&buckets));
            }
        }
    }

    pub(super) fn threads(&self, out: &mut String) {
        let (heap, plan) = (self.heap, self.plan);
        if plan.threads.is_empty() {
            return;
        }
        self.section(out, "threads", &format!("{} | by memory held, top {}", plan.threads.len(), self.top()));
        for row in plan.threads.iter().take(self.top()) {
            let thread = &heap.dump.threads[row.thread];
            let stack = heap.dump.stack(thread.trace_serial);
            outln!(
                out,
                "    {}  thread object retains {} | stack pins {} | {} frames",
                self.bold(&heap.thread_name(thread.serial)),
                human_bytes(row.retained as f64),
                human_bytes(row.locals_retained as f64),
                stack.len()
            );
            for frame in stack.iter().take(STACK_FRAMES_SHOWN) {
                outln!(out, "      {}", self.dim(&format!("at {frame}")));
            }
            if stack.len() > STACK_FRAMES_SHOWN {
                let more = stack.len() - STACK_FRAMES_SHOWN;
                outln!(out, "      {}", self.dim(&format!("… {more} more frames")));
            }
            for &StackLocal { object, frame, kind } in row.locals.iter().take(THREAD_LOCALS_SHOWN) {
                let at = match heap.dump.frame_of(thread.serial, frame) {
                    Some(location) if kind == RootKind::JavaFrame => format!("local in {location}"),
                    Some(location) => format!("{} in {location}", kind.label()),
                    None => kind.label().to_string(),
                };
                outln!(
                    out,
                    "      {:>8}  {}  {}",
                    human_bytes(heap.retained(object) as f64),
                    self.describe(object),
                    self.dim(&at)
                );
            }
        }
    }

    pub(super) fn locals(&self, out: &mut String) {
        let Some(locals) = &self.plan.locals else { return };
        if locals.values.is_empty() {
            return;
        }
        let heap = self.heap;
        let note = format!(
            "{} values in {} threads retain {}",
            commas(locals.values.len() as u64),
            heap.dump.threads.len(),
            human_bytes(locals.total as f64)
        );
        self.section(out, "thread locals", &note);
        for local in locals.values.iter().take(self.top()) {
            let thread = heap.thread_name(heap.dump.threads[local.thread].serial);
            outln!(
                out,
                "    {:>8}  {}  {}",
                human_bytes(local.retained as f64),
                self.describe(local.value),
                self.dim(&format!("← {} in {thread}", self.key_text(local.key)))
            );
        }
        let shared: Vec<_> =
            locals.by_key.iter().filter(|&&(_, count, _)| count > 1).take(self.top()).collect();
        if !shared.is_empty() {
            self.dim_line(out, "per key, across threads");
            for &(key, count, retained) in shared {
                outln!(
                    out,
                    "    {:>8}  {:>6} ×  {}",
                    human_bytes(retained as f64),
                    commas(count),
                    self.key_text(key)
                );
            }
        }
    }

    pub(super) fn loaders(&self, out: &mut String) {
        let plan = self.plan;
        if plan.loaders.len() < 2 {
            return;
        }
        let duplicates: u64 = plan.loaders.iter().map(|loader| loader.duplicates).sum();
        let note = match duplicates {
            0 => format!("{}", plan.loaders.len()),
            count => format!("{} | {} class names loaded more than once", plan.loaders.len(), commas(count)),
        };
        self.section(out, "class loaders", &note);
        self.dim_line(out, " classes   instances       live     shallow       owns   retained  loader");
        for loader in plan.loaders.iter().take(self.top()) {
            let retained =
                if loader.object == NONE { "-".to_string() } else { human_bytes(loader.retained as f64) };
            let elsewhere = if loader.duplicates > 0 {
                self.dim(&format!("  {} also elsewhere", loader.duplicates))
            } else {
                String::new()
            };
            outln!(
                out,
                "    {:>8} {:>11} {:>10} {:>11} {:>10} {:>10}  {}{elsewhere}",
                commas(loader.classes),
                commas(loader.instances),
                commas(loader.live),
                human_bytes(loader.shallow as f64),
                human_bytes(loader.owns as f64),
                retained,
                self.loader_text(loader.object)
            );
        }
        if plan.stale.is_empty() {
            return;
        }
        outln!(
            out,
            "    {}",
            self.bold("stale loaders  their classes lost the live instances to a newer loader, or have none")
        );
        for (i, stale) in plan.stale.iter().enumerate().take(self.top()) {
            outln!(
                out,
                "    {}  {} classes | {} live instances | {} shared names lost | classes own {}",
                self.loader_text(stale.object),
                commas(stale.classes),
                commas(stale.live),
                commas(stale.lost),
                human_bytes(stale.owns as f64)
            );
            if let Some(referrers) = plan.stale_referrers.get(i).filter(|referrers| !referrers.is_empty()) {
                outln!(out, "      held by  {}", self.referrers(referrers, 4));
            }
            self.path_lines(out, stale.object, "      path     ");
        }
    }

    pub(super) fn duplicates(&self, out: &mut String) {
        let Some(duplicates) = &self.plan.inputs.duplicates else { return };
        if duplicates.groups.is_empty() {
            return;
        }
        let note = format!(
            "{} wasted in {} groups | {} strings, {} distinct",
            human_bytes(duplicates.wasted as f64),
            commas(duplicates.groups.len() as u64),
            commas(duplicates.strings),
            commas(duplicates.distinct)
        );
        self.section(out, "duplicate strings", &note);
        self.dim_line(out, "  wasted    copies  text");
        for group in duplicates.groups.iter().take(self.top()) {
            outln!(
                out,
                "    {:>8} {:>9}  {}",
                human_bytes(group.wasted as f64),
                commas(group.count),
                self.quoted(group.string)
            );
        }
    }

    pub(super) fn arrays(&self, out: &mut String) {
        let Some(arrays) = &self.plan.inputs.array_duplicates else { return };
        if arrays.groups.is_empty() {
            return;
        }
        let note = format!(
            "{} wasted in {} groups | {} arrays of {MIN_ARRAY_DATA_BYTES}+ bytes, {} distinct",
            human_bytes(arrays.wasted as f64),
            commas(arrays.groups.len() as u64),
            commas(arrays.arrays),
            commas(arrays.distinct)
        );
        self.section(out, "duplicate arrays", &note);
        self.dim_line(out, "  wasted    copies  array");
        for group in arrays.groups.iter().take(self.top()) {
            outln!(
                out,
                "    {:>8} {:>9}  {}  {}",
                human_bytes(group.wasted as f64),
                commas(group.count),
                self.describe(group.array),
                self.dim(&self.array_preview(group.array))
            );
        }
    }

    /// The first elements of a primitive array, as text when it reads as text.
    pub(super) fn array_preview(&self, object: u32) -> String {
        let dump = self.heap.dump;
        let Some(raw) = self.fetched.raw.get(&dump.objects[object as usize].id) else { return String::new() };
        let readable = |text: &String| {
            !text.is_empty()
                && text.chars().all(|c| !c.is_control() && c != '�')
                && text.bytes().all(|byte| byte.is_ascii_graphic() || byte == b' ' || byte >= 0x80)
        };
        if let Some(text) = strings::text_of_array(raw, ARRAY_TEXT_CHARS).filter(readable) {
            return format!("\"{text}\"");
        }
        let size = raw.ty.size(8) as usize;
        let items: Vec<String> = raw
            .data
            .chunks_exact(size)
            .take(ARRAY_ELEMENTS_SHOWN)
            .filter_map(|element| Value::decode(raw.ty, element, 8))
            .map(Value::text)
            .collect();
        let more = if raw.len as usize > items.len() { " …" } else { "" };
        format!("[{}{more}]", items.join(", "))
    }

    pub(super) fn boxed(&self, out: &mut String) {
        let rows = &self.plan.inputs.boxed;
        if rows.is_empty() {
            return;
        }
        let types: FastMap<u32, Ty> =
            self.heap.boxed_classes().into_iter().map(|(class, _, _, ty)| (class, ty)).collect();
        let wasted: u64 = rows.iter().map(|row| row.wasted).sum();
        self.section(out, "boxed primitives", &format!("{} in repeated values", human_bytes(wasted as f64)));
        self.dim_line(out, "  wasted   instances   distinct  class  most repeated");
        for row in rows.iter().take(self.top()) {
            let ty = types.get(&row.class).copied().unwrap_or(Ty::Long);
            let top: Vec<String> = row
                .top
                .iter()
                .take(3)
                .map(|&(bits, count)| format!("{} ×{}", Value::from_bits(ty, bits).text(), commas(count)))
                .collect();
            outln!(
                out,
                "    {:>8} {:>11} {:>10}  {}  {}",
                human_bytes(row.wasted as f64),
                commas(row.instances),
                commas(row.distinct),
                self.class_name(row.class),
                self.dim(&top.join(" | "))
            );
        }
    }

    pub(super) fn references(&self, out: &mut String) {
        let plan = self.plan;
        if plan.references.is_empty() && plan.finalizers.is_none() {
            return;
        }
        self.section(out, "references", "soft, weak, phantom and final references, and what only they keep");
        self.dim_line(out, "    kind  references   referents   only-through  referent classes");
        for row in &plan.references {
            outln!(
                out,
                "    {:>8} {:>11} {:>11} {:>14}  {}",
                row.kind.label(),
                commas(row.references),
                commas(row.referents),
                format!("{} in {}", human_bytes(row.only.bytes as f64), commas(row.only.count)),
                self.dim(&self.class_counts(&row.top, 3))
            );
        }
        if let Some(finalizers) = &plan.finalizers {
            outln!(
                out,
                "    finalizable  {} objects, {} queued for the finalizer thread  {}",
                commas(finalizers.registered),
                commas(finalizers.enqueued),
                self.dim(&self.class_counts(&finalizers.classes, 4))
            );
        }
        if plan.cleaners > 0 {
            outln!(out, "    cleaners     {} registered", commas(plan.cleaners));
        }
    }

    pub(super) fn garbage(&self, out: &mut String) {
        let rows = &self.plan.garbage;
        if rows.is_empty() {
            return;
        }
        let garbage = self.heap.unreachable;
        let note = format!(
            "{} in {} unreachable objects, by class",
            human_bytes(garbage.bytes as f64),
            commas(garbage.count)
        );
        self.section(out, "garbage", &note);
        self.dim_line(out, "   shallow   instances  class");
        for row in rows.iter().take(self.top()) {
            outln!(
                out,
                "    {:>9} {:>11}  {}",
                human_bytes(row.shallow as f64),
                commas(row.instances),
                self.class_name(row.class)
            );
        }
    }

    pub(super) fn system(&self, out: &mut String) {
        if self.plan.system_properties.is_empty() {
            return;
        }
        let texts = self.properties();
        self.section(out, "system", &format!("{} properties", commas(texts.len() as u64)));
        let wanted = [
            "java.version",
            "java.vm.name",
            "java.vm.version",
            "java.vendor",
            "java.home",
            "os.name",
            "os.arch",
            "os.version",
            "user.dir",
            "user.name",
            "sun.java.command",
            "java.class.path",
        ];
        let mut shown = 0;
        for key in wanted {
            if let Some((_, value)) = texts.iter().find(|(name, _)| name == key) {
                outln!(out, "    {key:<18}  {}", strings::preview(value, PROPERTY_VALUE_CHARS));
                shown += 1;
            }
        }
        if texts.len() > shown {
            self.dim_line(out, &format!("+ {} more; --json lists them all", texts.len() - shown));
        }
    }

    pub(super) fn direct(&self, out: &mut String) {
        let Some(direct) = &self.plan.inputs.direct else { return };
        if direct.buffers.is_empty() && direct.views == 0 {
            return;
        }
        let note = format!(
            "{} off-heap in {} DirectByteBuffers | {} views | {} memory-mapped in {}",
            human_bytes(direct.capacity as f64),
            commas(direct.buffers.len() as u64),
            commas(direct.views),
            human_bytes(direct.mapped.bytes as f64),
            commas(direct.mapped.count)
        );
        self.section(out, "direct buffers", &note);
        if !direct.bits.is_empty() {
            let bits: Vec<String> = direct
                .bits
                .iter()
                .map(|(name, value)| {
                    let count = name.to_lowercase().contains("count");
                    format!("{name} {}", if count { commas(*value) } else { human_bytes(*value as f64) })
                })
                .collect();
            outln!(out, "    java.nio.Bits  {}", bits.join(" | "));
        }
        if !direct.held_by.is_empty() {
            outln!(out, "    held by  {}", self.referrers(&direct.held_by, 5));
        }
        for buffer in direct.buffers.iter().take(self.top()) {
            let kind = if buffer.mapped { self.dim("  mapped") } else { String::new() };
            outln!(
                out,
                "    {:>9}  {}{kind}",
                human_bytes(buffer.capacity as f64),
                self.describe(buffer.object)
            );
        }
    }
}
