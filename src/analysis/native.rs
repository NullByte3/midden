//! Off-heap memory the heap points at: `DirectByteBuffer` capacities, and
//! the JVM's own counters in `java.nio.Bits`.

use super::{Heap, Objects, Referrer};
use crate::detail::Fetched;
use crate::hprof::{Ty, Value};

/// A `DirectByteBuffer` that owns its memory.
pub struct Buffer {
    pub object: u32,
    pub capacity: u64,
    pub mapped: bool,
}

#[derive(Default)]
pub struct Direct {
    /// Buffers that own their memory, biggest first.
    pub buffers: Vec<Buffer>,
    /// Slices, duplicates and views over another buffer.
    pub views: u64,
    pub capacity: u64,
    /// Memory-mapped files among the owners.
    pub mapped: Objects,
    /// `java.nio.Bits` counters: `(name, value)`.
    pub bits: Vec<(String, u64)>,
    pub held_by: Vec<Referrer>,
}

impl Heap<'_> {
    /// Reachable `DirectByteBuffer` instances, subclasses included.
    pub fn direct_buffers(&self) -> Vec<u32> {
        let dump = self.dump;
        let Some(base) = dump.class_named("java.nio.DirectByteBuffer") else { return Vec::new() };
        let classes: Vec<u32> =
            (0..dump.classes.len() as u32).filter(|&class| dump.extends(class, base)).collect();
        self.members_of(&classes).concat()
    }

    /// Ids the detail pass must fetch: the buffers, and the Bits counters.
    pub fn direct_wants(&self, buffers: &[u32]) -> Vec<u64> {
        let mut want: Vec<u64> =
            buffers.iter().map(|&buffer| self.dump.objects[buffer as usize].id).collect();
        for (_, value) in self.bits_statics() {
            if let Value::Ref(id) = value {
                want.push(id);
            }
        }
        want
    }

    fn bits_statics(&self) -> Vec<(String, Value)> {
        let dump = self.dump;
        let Some(bits_class) = dump.class_named("java.nio.Bits") else { return Vec::new() };
        let wanted = ["reservedmemory", "totalcapacity", "count", "maxmemory"];
        dump.classes[bits_class as usize]
            .statics
            .iter()
            .filter(|field| {
                wanted.contains(&dump.names[field.name as usize].replace('_', "").to_lowercase().as_str())
            })
            .map(|field| (dump.names[field.name as usize].clone(), field.value))
            .collect()
    }

    /// Sum the buffers once their bodies are fetched.
    pub fn direct(&self, buffers: &[u32], fetched: &Fetched) -> Direct {
        let dump = self.dump;
        let mut out = Direct::default();
        for &buffer in buffers {
            if self.field(buffer, "att").is_some() {
                out.views += 1;
                continue;
            }
            let capacity = self.int_field(buffer, "capacity", fetched).unwrap_or(0);
            let mapped = self.field(buffer, "fd").is_some();
            out.capacity += capacity;
            if mapped {
                out.mapped.count += 1;
                out.mapped.bytes += capacity;
            }
            out.buffers.push(Buffer { object: buffer, capacity, mapped });
        }
        out.buffers.sort_by(|a, b| b.capacity.cmp(&a.capacity).then(a.object.cmp(&b.object)));
        for (name, value) in self.bits_statics() {
            let counter = match value {
                Value::Long(long) => Some(long as u64),
                Value::Int(int) => Some(int as u64),
                Value::Ref(id) => dump.lookup(id).and_then(|object| self.int_field(object, "value", fetched)),
                _ => None,
            };
            if let Some(counter) = counter {
                out.bits.push((name, counter));
            }
        }
        let mut owners: Vec<u32> = out.buffers.iter().map(|buffer| buffer.object).collect();
        owners.sort_unstable();
        out.held_by = self
            .referrers(|target| owners.binary_search(&target).ok().map(|_| 0))
            .into_iter()
            .next()
            .unwrap_or_default();
        out
    }

    /// An int or long field read from a fetched instance body.
    pub fn int_field(&self, object: u32, name: &str, fetched: &Fetched) -> Option<u64> {
        let dump = self.dump;
        let (offset, ty) = dump.field_offset(self.class(object), name)?;
        let raw = fetched.raw.get(&dump.objects[object as usize].id)?;
        match Value::decode(ty, raw.data.get(offset as usize..)?, dump.header.id_size)? {
            Value::Int(int) => Some(int as u64),
            Value::Long(long) => Some(long as u64),
            Value::Short(short) => Some(short as u64),
            value if ty == Ty::Byte => Some(value.bits()),
            _ => None,
        }
    }
}
