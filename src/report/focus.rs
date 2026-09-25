//! The focused views: one class, one object, the strings `--find` matched,
//! the objects `--where` matched, and object addresses like `Holder.CACHE[2]`.

use super::{FOUND_OWNERS, MAX_FOCUS_CLASSES, Render, commas, human_bytes};
use crate::analysis::Heap;
use crate::dump::{Kind, NONE};
use crate::error::{Error, Result};
use crate::graph::ARRAY_ELEMENT;
use crate::hprof::Value;
use crate::pattern::Pattern;
use crate::strings;

/// Map keys are cut and padded to this many characters.
const MAP_KEY_WIDTH: usize = 40;
/// Owners shown in the chain above the `--object`.
const OWNERS_SHOWN: usize = 6;

impl Render<'_, '_> {
    pub(super) fn focus(&self, out: &mut String) {
        let (heap, plan) = (self.heap, self.plan);
        let needle = plan.view.class.as_ref().map_or("", |pattern| pattern.text());
        if plan.focus_classes.is_empty() {
            self.section(out, &format!("class focus: {needle}"), "");
            outln!(out, "    no class with instances matches this");
            return;
        }
        let classes: Vec<u32> =
            plan.focus_classes.iter().copied().take(self.top().min(MAX_FOCUS_CLASSES)).collect();
        let referrers =
            heap.referrers(|object| classes.iter().position(|&class| class == heap.class(object)));
        for (i, &class_index) in classes.iter().enumerate() {
            let class = &heap.dump.classes[class_index as usize];
            let row = self.histogram_row(class_index);
            self.section(
                out,
                &format!("class {}", class.name),
                &format!(
                    "{} instances | {} shallow | {} retained ({})",
                    commas(row.instances),
                    human_bytes(row.shallow as f64),
                    human_bytes(row.retained as f64),
                    self.percent(row.retained)
                ),
            );
            let fields: Vec<String> = heap
                .dump
                .field_layout(class_index)
                .iter()
                .map(|(name, ty, _)| format!("{} {}", ty.name(), heap.dump.names[*name as usize]))
                .collect();
            if !fields.is_empty() {
                outln!(out, "    fields    {}", fields.join(" | "));
            }
            if class.superclass != NONE {
                outln!(out, "    extends   {}", self.class_name(class.superclass));
            }
            if !class.statics.is_empty() {
                let statics: Vec<String> = class
                    .statics
                    .iter()
                    .enumerate()
                    .map(|(index, field)| {
                        format!("{} = {}", heap.dump.static_name(class_index, index), self.value(field.value))
                    })
                    .collect();
                outln!(out, "    statics   {}", statics.join(" | "));
            }
            if let Some(held_by) = referrers.get(i).filter(|held_by| !held_by.is_empty()) {
                outln!(out, "    held by   {}", self.referrers(held_by, 6));
            }
            let instances = heap.instances_of(class_index);
            let owners = heap.owners_of(&instances);
            if !owners.is_empty() {
                outln!(out, "    owned by  {}", self.owners(&owners));
            }
            let (keeps, kept) = heap.keeps_of_class(class_index);
            if kept > row.instances {
                outln!(out, "    keeps     {} objects: {}", commas(kept), self.keeps(&keeps));
            }
            self.dim_line(out, "biggest instances");
            for &instance in instances.iter().take(self.top()) {
                let reach = match (heap.reachable(instance), heap.weakly_reachable(instance)) {
                    (true, _) => String::new(),
                    (false, true) => self.dim("  weakly reachable"),
                    (false, false) => self.dim("  unreachable"),
                };
                outln!(
                    out,
                    "    {:>8}  {:>8} shallow  {}{reach}",
                    human_bytes(heap.retained(instance) as f64),
                    human_bytes(heap.shallow(instance) as f64),
                    self.describe(instance)
                );
            }
            if let Some(&first) = instances.first() {
                self.path_lines(out, first, "    path      ");
            }
        }
        if plan.focus_classes.len() > classes.len() {
            let more = plan.focus_classes.len() - classes.len();
            outln!(out, "\n  {}", self.dim(&format!("+ {more} more classes match; narrow the pattern")));
        }
    }

    pub(super) fn object(&self, out: &mut String, object: u32) {
        let (heap, dump) = (self.heap, self.heap.dump);
        let record = &dump.objects[object as usize];
        let reach = match (heap.reachable(object), heap.weakly_reachable(object)) {
            (true, _) => "reachable".to_string(),
            (false, true) => self.dim("weakly reachable"),
            (false, false) => self.dim("unreachable"),
        };
        self.section(
            out,
            &format!("object {}", self.describe(object)),
            &format!(
                "{} shallow | {} retained ({}) | {reach}",
                human_bytes(heap.shallow(object) as f64),
                human_bytes(heap.retained(object) as f64),
                self.percent(heap.retained(object))
            ),
        );
        let raw = self.fetched.raw.get(&record.id);
        match record.kind {
            Kind::Instance | Kind::Class => {
                self.dim_line(out, "fields");
                let mut shown = 0;
                if let Some(&class) = heap.class_objects.get(&object).filter(|_| record.kind == Kind::Class) {
                    for (index, field) in dump.classes[class as usize].statics.iter().enumerate() {
                        outln!(
                            out,
                            "    {:<22}  {}",
                            format!("static {}", dump.static_name(class, index)),
                            self.value(field.value)
                        );
                        shown += 1;
                    }
                } else if record.kind == Kind::Instance {
                    for (name, ty, offset) in dump.field_layout(record.class) {
                        let value = raw
                            .and_then(|raw| raw.data.get(offset as usize..))
                            .and_then(|bytes| Value::decode(ty, bytes, dump.header.id_size))
                            .map_or(self.dim("?"), |decoded| self.value(decoded));
                        outln!(out, "    {:<22}  {value}", dump.names[name as usize]);
                        shown += 1;
                    }
                }
                if shown == 0 {
                    self.dim_line(out, "(none)");
                }
            }
            Kind::ObjectArray => {
                let edges = heap.graph.edges(object);
                let set = format!("{} of {} set", commas(edges.len() as u64), commas(u64::from(record.len)));
                self.dim_line(out, &format!("elements  {set}"));
                for (target, label) in edges.iter().take(self.top()) {
                    outln!(
                        out,
                        "    {:<8}  {}  {}",
                        self.label(None, Some(label)),
                        self.describe(target),
                        self.dim(&format!("retains {}", human_bytes(heap.retained(target) as f64)))
                    );
                }
            }
            Kind::PrimitiveArray => {
                if raw.is_some() {
                    outln!(out, "    elements  {}", self.array_preview(object));
                }
            }
        }
        if let Some(stats) = heap.measure(object) {
            let kind = if stats.used_buckets > 0 {
                format!(", {} buckets used", commas(stats.used_buckets))
            } else {
                String::new()
            };
            let size =
                format!("{} entries, capacity {}{kind}", commas(stats.entries), commas(stats.capacity));
            self.dim_line(out, &format!("collection  {size}"));
            let entries = heap.entries(object, self.top());
            for &(key, value) in &entries {
                if let Some(key) = key {
                    let key = strings::preview(&self.quoted(key), MAP_KEY_WIDTH);
                    outln!(out, "    {key:<MAP_KEY_WIDTH$}  →  {}", self.quoted(value));
                } else {
                    outln!(out, "    - {}", self.quoted(value));
                }
            }
            if stats.entries as usize > entries.len() {
                let more = commas(stats.entries - entries.len() as u64);
                self.dim_line(out, &format!("… {more} more entries"));
            }
        }
        let owners = heap.dominators.dominators_of(heap.graph.root, object);
        let chain: Vec<String> =
            owners.iter().take(OWNERS_SHOWN).map(|&owner| self.describe(owner)).collect();
        let more = if owners.len() > OWNERS_SHOWN {
            self.dim(&format!(" ← … {} more", owners.len() - OWNERS_SHOWN))
        } else {
            String::new()
        };
        let owned = if chain.is_empty() {
            "gc roots directly".to_string()
        } else {
            chain.join(" ← ") + " ← gc roots"
        };
        outln!(out, "    owned by  {owned}{more}");
        self.path_lines(out, object, "    path      ");
        let referrers = heap.referrers_of(object);
        if !referrers.is_empty() {
            outln!(out, "    held by   {}", self.referrers(&referrers, 6));
        }
        let sources = heap.referrer_objects(object, self.top());
        if !sources.is_empty() {
            self.dim_line(out, "referrers  biggest first; --object any of them to go up");
            for &(referrer, label) in &sources {
                outln!(
                    out,
                    "    {:>8}  {} {}",
                    human_bytes(heap.retained(referrer) as f64),
                    self.describe(referrer),
                    self.dim(&self.label(Some(referrer), Some(label)))
                );
            }
        }
        let children = heap.dominators.children(object);
        if !children.is_empty() {
            let count = commas(children.len() as u64);
            self.dim_line(out, &format!("retains {count} objects directly dominated, biggest first"));
            for &child in children.iter().take(self.top()) {
                outln!(
                    out,
                    "    {:>8}  {}  {}",
                    human_bytes(heap.retained(child) as f64),
                    self.label(Some(object), heap.graph.label_of(object, child)),
                    self.describe(child)
                );
            }
        }
    }

    /// A field value: primitives as literals, references as the target.
    pub(super) fn value(&self, value: Value) -> String {
        match value {
            Value::Ref(0) => "null".to_string(),
            Value::Ref(id) => match self.heap.dump.lookup(id) {
                Some(target) => format!(
                    "{}  {}",
                    self.describe(target),
                    self.dim(&format!("retains {}", human_bytes(self.heap.retained(target) as f64)))
                ),
                None => format!("0x{id:x} {}", self.dim("(not in dump)")),
            },
            other => other.text(),
        }
    }

    pub(super) fn found(&self, out: &mut String) {
        let (heap, plan) = (self.heap, self.plan);
        let text = plan.view.find.as_deref().unwrap_or("");
        let found = &plan.inputs.found;
        self.section(
            out,
            &format!("strings containing \"{text}\""),
            &format!("{} matches, biggest retained first", commas(found.len() as u64)),
        );
        if found.is_empty() {
            outln!(out, "    none");
            return;
        }
        let shown: Vec<u32> = found.iter().take(self.top()).copied().collect();
        let referrers = heap.referrers(|object| shown.iter().position(|&string| string == object));
        for (i, &string) in shown.iter().enumerate() {
            outln!(out, "    {:>8}  {}", human_bytes(heap.retained(string) as f64), self.describe(string));
            if let Some(held_by) = referrers.get(i).filter(|held_by| !held_by.is_empty()) {
                outln!(out, "              held by   {}", self.referrers(held_by, 4));
            }
            let owners: Vec<String> = heap
                .dominators
                .dominators_of(heap.graph.root, string)
                .iter()
                .take(FOUND_OWNERS)
                .map(|&owner| self.describe(owner))
                .collect();
            if !owners.is_empty() {
                outln!(out, "              owned by  {}", owners.join(" ← "));
            }
        }
        if found.len() > shown.len() {
            self.dim_line(out, &format!("+ {} more; --top shows more", found.len() - shown.len()));
        }
    }

    pub(super) fn matched(&self, out: &mut String) {
        let (heap, plan) = (self.heap, self.plan);
        let filter = plan.view.filter.as_deref().unwrap_or("");
        let matched = &plan.inputs.matched;
        self.section(
            out,
            &format!("objects where {filter}"),
            &format!("{} matches", commas(matched.len() as u64)),
        );
        if matched.is_empty() {
            outln!(out, "    none");
            return;
        }
        for &object in matched.iter().take(self.top()) {
            let reach = if heap.reachable(object) { String::new() } else { self.dim("  unreachable") };
            outln!(
                out,
                "    {:>8}  {:>8} shallow  {}{reach}",
                human_bytes(heap.retained(object) as f64),
                human_bytes(heap.shallow(object) as f64),
                self.describe(object)
            );
        }
        if let Some(&first) = matched.first() {
            self.path_lines(out, first, "    path      ");
        }
        if matched.len() > self.top() {
            self.dim_line(out, &format!("+ {} more; --top shows more", matched.len() - self.top()));
        }
    }
}

/// `pkg.Class.FIELD[.field|[N]]*`: the class's static, then fields and
/// indices from there. A bare class name gives the class object.
pub fn resolve_path(heap: &Heap, text: &str) -> Result<u32> {
    let dump = heap.dump;
    let segments: Vec<&str> = text.split('.').collect();
    for i in (1..=segments.len()).rev() {
        let name = segments[..i].join(".");
        let (name, _) = split_indices(&name);
        let Some(class) = find_class(dump, name) else { continue };
        let Some(mut current) = dump.lookup(dump.classes[class as usize].id) else { continue };
        for (hop, segment) in segments[i..].iter().enumerate() {
            let (field, indices) = split_indices(segment);
            current = if hop == 0 {
                let label = dump
                    .name_id(field)
                    .ok_or_else(|| Error::Usage(format!("{name} has no static field {field}")))?;
                heap.graph
                    .field(current, label)
                    .ok_or_else(|| Error::Usage(format!("static {name}.{field} is null or not an object")))?
            } else {
                heap.field(current, field)
                    .or_else(|| dump.name_id(field).and_then(|label| heap.graph.field(current, label)))
                    .ok_or_else(|| {
                        Error::Usage(format!("no reference field `{field}` on {}", dump.class_name(current)))
                    })?
            };
            for index in indices {
                current = heap
                    .graph
                    .field(current, ARRAY_ELEMENT | index)
                    .ok_or_else(|| Error::Usage(format!("element [{index}] is null or out of range")))?;
            }
        }
        return Ok(current);
    }
    Err(Error::Usage(format!("`{text}` is not an object id, suspect:N, top:N, or a Class.FIELD path")))
}

/// `CACHE[2][0]` → `("CACHE", [2, 0])`.
fn split_indices(segment: &str) -> (&str, Vec<u32>) {
    let Some(open) = segment.find('[') else { return (segment, Vec::new()) };
    let indices = segment[open..]
        .split(['[', ']'])
        .filter(|part| !part.is_empty())
        .filter_map(|part| part.parse().ok())
        .collect();
    (&segment[..open], indices)
}

fn find_class(dump: &crate::dump::Dump, name: &str) -> Option<u32> {
    if let Some(class) = dump.class_named(name) {
        return Some(class);
    }
    let pattern = Pattern::parse(&format!("={name}"));
    let mut hits = (0..dump.classes.len() as u32).filter(|&class| {
        dump.classes[class as usize].dumped && pattern.matches(&dump.classes[class as usize].name)
    });
    match (hits.next(), hits.next()) {
        (Some(class), None) => Some(class),
        _ => None,
    }
}
