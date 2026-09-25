//! The JVM's system properties, read from `java.lang.System.props`.

use super::Heap;
use crate::hprof::Value;

/// System properties read at most.
const MAX_PROPERTIES: usize = 10_000;

impl Heap<'_> {
    /// `(key, value)` String objects, unsorted.
    pub fn system_properties(&self) -> Vec<(u32, u32)> {
        let dump = self.dump;
        let Some(system) = dump.class_named("java.lang.System") else { return Vec::new() };
        let Some(Value::Ref(id)) = dump.static_value(system, "props") else { return Vec::new() };
        let Some(properties) = dump.lookup(id) else { return Vec::new() };
        self.entries(properties, MAX_PROPERTIES)
            .into_iter()
            .filter_map(|(key, value)| key.map(|key| (key, value)))
            .filter(|&(key, value)| self.is_string(key) && self.is_string(value))
            .collect()
    }
}
