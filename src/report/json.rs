//! The report as JSON: the same sections, as data.

use std::time::Duration;

use serde_json::{Value, json};

use super::{MAX_FOCUS_CLASSES, OWNERS_LISTED, Render, THREAD_LOCALS_SHOWN};
use crate::analysis::suspects::Suspect;
use crate::analysis::{ClassRow, Referrer};
use crate::dump::{FastMap, Kind, NONE};
use crate::hprof::Ty;
use crate::options::Section;

impl Render<'_, '_> {
    /// An object as data; strings carry their text.
    fn object_value(&self, object: u32) -> Value {
        let (heap, dump) = (self.heap, self.heap.dump);
        let record = &dump.objects[object as usize];
        let mut item = json!({
            "id": format!("0x{:x}", record.id),
            "class": heap.kind_text(object),
            "shallow": heap.shallow(object),
            "retained": heap.retained(object),
            "reachable": heap.reachable(object),
        });
        if matches!(record.kind, Kind::ObjectArray | Kind::PrimitiveArray) {
            item["length"] = json!(record.len);
        }
        if let Some(text) = self.text(object) {
            item["text"] = json!(text);
        }
        item
    }

    /// `object_value` with more fields.
    fn object_with(&self, object: u32, extra: Value) -> Value {
        let mut item = self.object_value(object);
        if let (Value::Object(item), Value::Object(extra)) = (&mut item, extra) {
            item.extend(extra);
        }
        item
    }

    fn class_row(&self, row: &ClassRow) -> Value {
        json!({ "class": self.class_name(row.class), "instances": row.instances, "shallow": row.shallow, "retained": row.retained })
    }

    fn referrers_json(&self, referrers: &[Referrer]) -> Value {
        referrers
            .iter()
            .take(8)
            .map(|referrer| json!({ "by": self.referrer_text(referrer), "count": referrer.count }))
            .collect()
    }

    fn path(&self, object: u32) -> Value {
        let heap = self.heap;
        heap.root_paths(object, self.plan.view.paths)
            .iter()
            .map(|path| {
                path.iter()
                    .enumerate()
                    .map(|(i, &(hop, label))| {
                        let from = if i == 0 { None } else { Some(path[i - 1].0) };
                        let mut item = self.object_with(hop, json!({ "via": self.label(from, label) }));
                        if i == 0 {
                            item["root"] = json!(heap.root_note(hop));
                        }
                        item
                    })
                    .collect::<Value>()
            })
            .collect()
    }

    pub(super) fn json(&self, elapsed: Duration) -> Value {
        let (heap, plan, dump) = (self.heap, self.plan, self.heap.dump);
        let shows = |section: Section| plan.view.sections.has(section) && !plan.view.focused();
        let mut out = json!({
            "dump": {
                "path": dump.path, "format": dump.header.format, "id_size": dump.header.id_size,
                "file_size": dump.file_size, "gzip": dump.gzip, "truncated": dump.truncated,
                "taken_ms": dump.header.timestamp_ms, "sizes": dump.sizing.label(),
                "classes": dump.classes.iter().filter(|class| class.dumped).count(), "objects": dump.objects.len(),
                "references": heap.graph.edge_count(), "threads": dump.threads.len(),
                "dangling_references": heap.graph.dangling, "dangling_roots": dump.dangling_roots,
                "analysed_ms": elapsed.as_millis() as u64,
            },
            "heap": {
                "total": heap.total, "live": heap.live,
                "unreachable": { "objects": heap.unreachable.count, "bytes": heap.unreachable.bytes },
                "weak_only": { "objects": heap.weak_only.count, "bytes": heap.weak_only.bytes },
                "gc_roots": heap.graph.roots.len(),
            },
        });
        if let Some(member) = &dump.member {
            out["dump"]["member"] = json!(member);
        }
        if let Some(object) = plan.focus_object {
            out["object"] = self.object_json(object);
        }
        if plan.view.class.is_some() {
            out["classes_focus"] = plan
                .focus_classes
                .iter()
                .take(MAX_FOCUS_CLASSES)
                .map(|&class| self.class_json(class))
                .collect();
        }
        if plan.view.find.is_some() {
            out["find"] = json!({ "text": plan.view.find, "matches": plan.inputs.found.len(),
                "strings": plan.inputs.found.iter().take(self.top()).map(|&string| self.object_value(string)).collect::<Value>() });
        }
        if plan.view.filter.is_some() {
            out["where"] = json!({ "filter": plan.view.filter, "matches": plan.inputs.matched.len(),
                "objects": plan.inputs.matched.iter().take(self.top()).map(|&object| self.object_value(object)).collect::<Value>() });
        }
        if shows(Section::Suspects) {
            out["suspects"] = plan.suspects.iter().map(|suspect| self.suspect_json(suspect)).collect();
        }
        if shows(Section::Biggest) {
            out["biggest"] = plan
                .trees
                .iter()
                .map(|rows| {
                    rows.iter()
                        .filter(|row| row.hidden.is_none())
                        .map(|row| {
                            self.object_with(
                                row.object,
                                json!({ "depth": row.depth, "via": self.tree_label(row) }),
                            )
                        })
                        .collect::<Value>()
                })
                .collect();
        }
        if shows(Section::Classes) {
            out["classes"] = plan
                .histogram
                .iter()
                .filter(|row| !heap.excluded(row.class))
                .take(self.top())
                .map(|row| self.class_row(row))
                .collect();
            if plan.view.by_package {
                out["packages"] = plan.packages.iter().take(self.top()).map(|(name, row)| json!({ "package": name, "instances": row.instances, "shallow": row.shallow, "retained": row.retained })).collect();
            }
        }
        if let Some(collections) = plan.collections.as_ref().filter(|_| shows(Section::Collections)) {
            out["collections"] = json!({
                "empty": { "count": collections.empty.count, "bytes": collections.empty.bytes },
                "classes": collections.rows.iter().take(self.top()).map(|row| json!({ "class": self.class_name(row.class), "instances": row.instances, "entries": row.entries, "capacity": row.capacity, "wasted": row.wasted, "empty": row.empty, "collisions": row.collisions })).collect::<Value>(),
                "sparse": collections.sparse.iter().take(self.top()).map(|sparse| self.object_with(sparse.object, json!({ "entries": sparse.stats.entries, "capacity": sparse.stats.capacity, "wasted": sparse.wasted }))).collect::<Value>(),
                "colliding": collections.colliding.iter().take(self.top()).map(|(object, stats)| self.object_with(*object, json!({ "entries": stats.entries, "buckets": stats.used_buckets }))).collect::<Value>(),
            });
        }
        if shows(Section::Threads) {
            out["threads"] = plan.threads.iter().take(self.top()).map(|row| {
                let thread = &dump.threads[row.thread];
                json!({ "name": heap.thread_name(thread.serial), "retained": row.retained, "stack_pins": row.locals_retained,
                    "stack": dump.stack(thread.trace_serial),
                    "locals": row.locals.iter().take(THREAD_LOCALS_SHOWN).map(|local| self.object_with(local.object, json!({ "kind": local.kind.label() }))).collect::<Value>() })
            }).collect();
        }
        if let Some(locals) = plan.locals.as_ref().filter(|_| shows(Section::Locals)) {
            out["thread_locals"] = json!({ "total": locals.total, "values": locals.values.iter().take(self.top()).map(|local| {
                self.object_with(local.value, json!({ "key": self.key_text(local.key), "thread": heap.thread_name(dump.threads[local.thread].serial) })) }).collect::<Value>() });
        }
        if shows(Section::Loaders) {
            out["loaders"] = plan.loaders.iter().take(self.top()).map(|loader| json!({ "loader": self.loader_text(loader.object), "classes": loader.classes, "instances": loader.instances, "live": loader.live, "shallow": loader.shallow, "owns": loader.owns, "retained": loader.retained, "duplicate_names": loader.duplicates })).collect();
            out["stale_loaders"] = plan.stale.iter().map(|stale| json!({ "loader": self.loader_text(stale.object), "classes": stale.classes, "live": stale.live, "lost_names": stale.lost, "owns": stale.owns, "paths": self.path(stale.object) })).collect();
        }
        if let Some(duplicates) = plan.inputs.duplicates.as_ref().filter(|_| shows(Section::Strings)) {
            out["duplicate_strings"] = json!({ "wasted": duplicates.wasted, "strings": duplicates.strings, "distinct": duplicates.distinct,
                "groups": duplicates.groups.iter().take(self.top()).map(|group| json!({ "text": self.text(group.string), "copies": group.count, "wasted": group.wasted })).collect::<Value>() });
        }
        if let Some(arrays) = plan.inputs.array_duplicates.as_ref().filter(|_| shows(Section::Arrays)) {
            out["duplicate_arrays"] = json!({ "wasted": arrays.wasted, "arrays": arrays.arrays, "distinct": arrays.distinct,
                "groups": arrays.groups.iter().take(self.top()).map(|group| self.object_with(group.array, json!({ "copies": group.count, "wasted": group.wasted, "preview": self.array_preview(group.array) }))).collect::<Value>() });
        }
        if shows(Section::Boxed) {
            let types: FastMap<u32, Ty> =
                heap.boxed_classes().into_iter().map(|(class, _, _, ty)| (class, ty)).collect();
            out["boxed"] = plan.inputs.boxed.iter().map(|row| {
                let ty = types.get(&row.class).copied().unwrap_or(Ty::Long);
                json!({ "class": self.class_name(row.class), "instances": row.instances, "distinct": row.distinct, "wasted": row.wasted,
                    "top": row.top.iter().map(|&(bits, count)| json!({ "value": crate::hprof::Value::from_bits(ty, bits).text(), "count": count })).collect::<Value>() })
            }).collect();
        }
        if shows(Section::References) {
            out["references"] = plan.references.iter().map(|row| json!({ "kind": row.kind.label(), "references": row.references, "referents": row.referents,
                "only_through": { "objects": row.only.count, "bytes": row.only.bytes },
                "referent_classes": row.top.iter().map(|&(class, count)| json!({ "class": self.class_name(class), "count": count })).collect::<Value>() })).collect();
            if let Some(finalizers) = &plan.finalizers {
                out["finalizers"] = json!({ "registered": finalizers.registered, "enqueued": finalizers.enqueued,
                    "classes": finalizers.classes.iter().map(|&(class, count)| json!({ "class": self.class_name(class), "count": count })).collect::<Value>() });
            }
            out["cleaners"] = json!(plan.cleaners);
        }
        if shows(Section::Garbage) {
            out["garbage"] = plan.garbage.iter().take(self.top()).map(|row| self.class_row(row)).collect();
        }
        if shows(Section::System) {
            out["system"] = Value::Object(
                self.properties().into_iter().map(|(key, value)| (key, json!(value))).collect(),
            );
        }
        if let Some(direct) = plan.inputs.direct.as_ref().filter(|_| shows(Section::Direct)) {
            out["direct_buffers"] = json!({ "capacity": direct.capacity, "owners": direct.buffers.len(), "views": direct.views,
                "mapped": { "count": direct.mapped.count, "bytes": direct.mapped.bytes },
                "bits": direct.bits.iter().map(|(name, value)| json!({ "name": name, "value": value })).collect::<Value>(),
                "held_by": self.referrers_json(&direct.held_by),
                "buffers": direct.buffers.iter().take(self.top()).map(|buffer| self.object_with(buffer.object, json!({ "capacity": buffer.capacity, "mapped": buffer.mapped }))).collect::<Value>() });
        }
        if let Some(diff) = plan.diff.as_ref().filter(|_| shows(Section::Baseline)) {
            out["baseline"] = json!({ "path": diff.path, "live": diff.live, "objects": diff.objects, "total": diff.total,
                "classes": diff.classes.iter().take(self.top()).map(|class| json!({ "class": class.name, "instances": [class.instances.before, class.instances.after], "shallow": [class.shallow.before, class.shallow.after], "retained": [class.retained.before, class.retained.after] })).collect::<Value>(),
                "structures": diff.structures.iter().take(self.top()).map(|row| json!({ "key": row.key, "object": if row.object == NONE { Value::Null } else { self.object_value(row.object) }, "retained": [row.before, row.after] })).collect::<Value>(),
                "threads": diff.threads.iter().take(self.top()).map(|row| json!({ "thread": row.name, "retained": [row.before, row.after] })).collect::<Value>(),
                "loaders": diff.loaders.iter().take(self.top()).map(|row| json!({ "loader": row.name, "owns": [row.before, row.after] })).collect::<Value>(),
                "strings": diff.strings.iter().take(self.top()).map(|row| json!({ "text": if row.string == NONE { Value::Null } else { json!(self.text(row.string)) }, "hash": format!("{:x}", row.hash), "copies": [row.copies_before, row.copies_after], "wasted": [row.wasted_before, row.wasted_after] })).collect::<Value>() });
        }
        out
    }

    fn suspect_json(&self, suspect: &Suspect) -> Value {
        let heap = self.heap;
        match suspect {
            Suspect::Object(object) => json!({
                "kind": "object", "retained": heap.retained(object.hops[0].object),
                "hops": object.hops.iter().enumerate().map(|(i, hop)| {
                    let prev = if i == 0 { None } else { Some(object.hops[i - 1].end) };
                    self.object_with(hop.object, json!({ "via": self.label(prev, hop.label), "chain": hop.chain })) }).collect::<Value>(),
                "keeps": object.keeps.iter().take(8).map(|row| self.class_row(row)).collect::<Value>(),
                "kept_objects": object.kept_objects,
                "paths": self.path(object.hops[0].object),
            }),
            Suspect::Class(class) => json!({
                "kind": "class", "retained": class.row.retained, "class": self.class_row(&class.row),
                "held_by": self.referrers_json(&class.referrers),
                "owned_by": class.owners.iter().map(|&(owner, bytes, total)| json!({ "class": if owner == NONE { "gc roots".to_string() } else { self.class_name(owner).to_string() }, "bytes": bytes, "of": total })).collect::<Value>(),
                "biggest": self.object_value(class.biggest),
                "paths": self.path(class.biggest),
            }),
        }
    }

    fn class_json(&self, class: u32) -> Value {
        let heap = self.heap;
        let instances = heap.instances_of(class);
        json!({
            "class": self.class_row(&self.histogram_row(class)),
            "fields": heap.dump.field_layout(class).iter().map(|(name, ty, _)| format!("{} {}", ty.name(), heap.dump.names[*name as usize])).collect::<Vec<_>>(),
            "held_by": self.referrers_json(&heap.referrers(|object| (heap.class(object) == class).then_some(0)).into_iter().next().unwrap_or_default()),
            "biggest": instances.iter().take(self.top()).map(|&instance| self.object_value(instance)).collect::<Value>(),
            "paths": instances.first().map_or(Value::Null, |&first| self.path(first)),
        })
    }

    fn object_json(&self, object: u32) -> Value {
        let heap = self.heap;
        let mut out = self.object_value(object);
        out["owned_by"] = heap
            .dominators
            .dominators_of(heap.graph.root, object)
            .iter()
            .take(OWNERS_LISTED)
            .map(|&owner| self.object_value(owner))
            .collect();
        out["paths"] = self.path(object);
        out["held_by"] = self.referrers_json(&heap.referrers_of(object));
        let via = |target: u32, from: u32, label: Option<u32>| {
            self.object_with(target, json!({ "via": self.label(Some(from), label) }))
        };
        out["referrers"] = heap
            .referrer_objects(object, self.top())
            .iter()
            .map(|&(referrer, label)| via(referrer, referrer, Some(label)))
            .collect();
        out["retains"] = heap
            .dominators
            .children(object)
            .iter()
            .take(self.top())
            .map(|&child| via(child, object, heap.graph.label_of(object, child)))
            .collect();
        out["out"] = heap
            .graph
            .edges(object)
            .iter()
            .take(self.top())
            .map(|(target, label)| via(target, object, Some(label)))
            .collect();
        if let Some(stats) = heap.measure(object) {
            out["collection"] = json!({ "entries": stats.entries, "capacity": stats.capacity, "buckets": stats.used_buckets,
                "items": heap.entries(object, self.top()).iter().map(|(key, value)| json!({ "key": key.map(|key| self.object_value(key)), "value": self.object_value(*value) })).collect::<Value>() });
        }
        out
    }
}
