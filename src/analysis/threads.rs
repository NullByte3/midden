//! Threads: what their stacks pin, and what their thread locals hold.

use super::Heap;
use crate::dump::{FastMap, Kind, NONE};
use crate::hprof::RootKind;

/// One thread: its object, and what its stack pins.
pub struct ThreadRow {
    pub thread: usize,
    pub retained: u64,
    /// Objects pinned by the stack.
    pub locals: Vec<StackLocal>,
    pub locals_retained: u64,
}

/// An object a thread's stack pins, and the frame that holds it.
#[derive(Clone, Copy)]
pub struct StackLocal {
    pub object: u32,
    pub frame: u32,
    pub kind: RootKind,
}

pub struct Local {
    pub thread: usize,
    /// The `ThreadLocal` key object, or `NONE` when it was collected.
    pub key: u32,
    pub value: u32,
    pub retained: u64,
}

pub struct ThreadLocals {
    /// Biggest values first.
    pub values: Vec<Local>,
    pub total: u64,
    /// Per key across threads: `(key, values, retained)`, biggest first.
    pub by_key: Vec<(u32, u64, u64)>,
}

impl Heap<'_> {
    /// Every thread, by memory held.
    pub fn threads(&self) -> Vec<ThreadRow> {
        let dump = self.dump;
        let stack_kinds =
            [RootKind::JavaFrame, RootKind::JniLocal, RootKind::NativeStack, RootKind::ThreadBlock];
        let mut rows: Vec<ThreadRow> = dump
            .threads
            .iter()
            .enumerate()
            .map(|(i, thread)| {
                let mut locals: Vec<StackLocal> = dump
                    .roots
                    .iter()
                    .filter(|(_, root)| {
                        root.thread_serial == thread.serial && stack_kinds.contains(&root.kind)
                    })
                    .filter(|(object, _)| dump.objects[*object as usize].kind != Kind::Class)
                    .map(|(object, root)| StackLocal { object: *object, frame: root.frame, kind: root.kind })
                    .collect();
                locals.sort_by(|a, b| {
                    self.retained(b.object).cmp(&self.retained(a.object)).then(a.object.cmp(&b.object))
                });
                locals.dedup_by_key(|local| local.object);
                let locals_retained = locals
                    .iter()
                    .filter(|local| self.dominators.idom[local.object as usize] == self.graph.root)
                    .map(|local| self.retained(local.object))
                    .sum();
                ThreadRow { thread: i, retained: self.retained(thread.object), locals, locals_retained }
            })
            .collect();
        rows.sort_by(|a, b| {
            (b.retained + b.locals_retained)
                .cmp(&(a.retained + a.locals_retained))
                .then(a.thread.cmp(&b.thread))
        });
        rows
    }

    /// Every value held through `Thread.threadLocals` and the inheritable map.
    pub fn thread_locals(&self) -> ThreadLocals {
        let (graph, dump) = (self.graph, self.dump);
        let mut values = Vec::new();
        let (table_label, value_label) = (self.labels.get("table"), self.labels.get("value"));
        for (i, thread) in dump.threads.iter().enumerate() {
            for field in ["threadLocals", "inheritableThreadLocals"] {
                let Some(map) = self.field(thread.object, field) else { continue };
                let Some(table) = table_label.and_then(|label| graph.field(map, label)) else { continue };
                for entry in graph.edges(table).targets() {
                    let Some(value) = value_label.and_then(|label| graph.field(entry, label)) else {
                        continue;
                    };
                    let key = self.referent_of(entry).unwrap_or(NONE);
                    values.push(Local { thread: i, key, value, retained: self.retained(value) });
                }
            }
        }
        values.sort_by(|a, b| b.retained.cmp(&a.retained).then(a.value.cmp(&b.value)));
        let total = values.iter().map(|local| local.retained).sum();
        let mut keys: FastMap<u32, (u64, u64)> = FastMap::default();
        for local in &values {
            let sums = keys.entry(local.key).or_default();
            sums.0 += 1;
            sums.1 += local.retained;
        }
        let mut by_key: Vec<(u32, u64, u64)> =
            keys.into_iter().map(|(key, (count, retained))| (key, count, retained)).collect();
        by_key.sort_by(|a, b| b.2.cmp(&a.2).then(a.0.cmp(&b.0)));
        ThreadLocals { values, total, by_key }
    }
}
