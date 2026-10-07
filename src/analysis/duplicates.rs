//! Wasted copies: Strings with equal contents, primitive arrays with equal
//! contents, and boxed primitives holding the same value.

use super::Heap;
use crate::dump::{self, Class, FastMap, Kind};
use crate::hprof::Ty;
use crate::parallel;
use crate::store::Bits;

/// Strings sharing one content.
pub struct DuplicateGroup {
    pub string: u32,
    pub array: u32,
    pub hash: u64,
    pub count: u64,
    pub wasted: u64,
}

pub struct Duplicates {
    pub groups: Vec<DuplicateGroup>,
    pub wasted: u64,
    pub strings: u64,
    pub distinct: u64,
}

/// Primitive arrays sharing one content.
pub struct ArrayGroup {
    pub array: u32,
    pub count: u64,
    pub wasted: u64,
}

pub struct ArrayDuplicates {
    pub groups: Vec<ArrayGroup>,
    pub wasted: u64,
    pub arrays: u64,
    pub distinct: u64,
}

/// One boxed class and how often its values repeat.
pub struct BoxedRow {
    pub class: u32,
    pub instances: u64,
    pub distinct: u64,
    pub wasted: u64,
    /// `(value bits, instances)`, most repeated first.
    pub top: Vec<(u64, u64)>,
}

/// Primitive arrays with less data than this are not hashed for duplicates.
pub const MIN_ARRAY_DATA_BYTES: u32 = 16;

const BOXED: [(&str, Ty); 8] = [
    ("java.lang.Integer", Ty::Int),
    ("java.lang.Long", Ty::Long),
    ("java.lang.Short", Ty::Short),
    ("java.lang.Byte", Ty::Byte),
    ("java.lang.Character", Ty::Char),
    ("java.lang.Boolean", Ty::Bool),
    ("java.lang.Float", Ty::Float),
    ("java.lang.Double", Ty::Double),
];

/// The boxed classes among `classes`: `(class, class id, value offset, type)`. The index pass tallies
/// their values with this too.
pub fn boxed_classes(classes: &[Class], names: &[String], id_size: u32) -> Vec<(u32, u64, u32, Ty)> {
    BOXED
        .iter()
        .filter_map(|&(name, ty)| {
            let class = dump::class_named(classes, name)?;
            let (offset, field_ty) =
                dump::field_offset(classes, names, id_size, class, "value").filter(|field| field.1 == ty)?;
            Some((class, classes[class as usize].id, offset, field_ty))
        })
        .collect()
}

/// Items sharing one hash: the lowest-ranked of them, how many, and the bytes of all but that one.
struct HashGroup<T> {
    hash: u64,
    first: T,
    count: u64,
    wasted: u64,
}

/// Group `items` by hash over the workers, each taking one share of the hashes.
fn group_by_hash<T: Copy + Send + Sync>(
    items: &[T],
    hash: impl Fn(T) -> Option<u64> + Sync,
    rank: impl Fn(T) -> u32 + Sync,
    bytes: impl Fn(T) -> u64 + Sync,
) -> Vec<HashGroup<T>> {
    let shares = parallel::threads();
    let parts = parallel::ranges(items.len(), |lo, hi| {
        let mut out = vec![Vec::new(); shares];
        for &item in &items[lo..hi] {
            if let Some(hash) = hash(item) {
                out[(hash >> 32) as usize % shares].push((hash, item));
            }
        }
        out
    });
    let share_ids: Vec<usize> = (0..shares).collect();
    parallel::items(&share_ids, |&share| {
        let mut groups: FastMap<u64, (T, u64, u64)> = FastMap::default();
        for &(hash, item) in parts.iter().flat_map(|part| &part[share]) {
            let group = groups.entry(hash).or_insert((item, 0, 0));
            if rank(item) < rank(group.0) {
                group.0 = item;
            }
            group.1 += 1;
            group.2 += bytes(item);
        }
        groups
            .into_iter()
            .map(|(hash, (first, count, total))| HashGroup {
                hash,
                first,
                count,
                wasted: total - bytes(first),
            })
            .collect::<Vec<_>>()
    })
    .into_iter()
    .flatten()
    .collect()
}

impl Heap<'_> {
    /// Group Strings by the content of their backing arrays.
    pub fn duplicates(
        &self,
        pairs: &[(u32, u32)],
        hash_of: impl Fn(u32) -> Option<u64> + Sync,
    ) -> Duplicates {
        // Each array once, with its first String: the pairs come in String order.
        let mut shared = Bits::new(self.dump.objects.len());
        let mut seen: Vec<(u32, u32)> = Vec::with_capacity(pairs.len());
        for &(string, array) in pairs {
            if !shared.get(array as usize) {
                shared.set(array as usize);
                seen.push((string, array));
            }
        }
        drop(shared);
        let groups = group_by_hash(
            &seen,
            |(_, array)| hash_of(array),
            |(_, array)| array,
            |(string, array)| self.shallow(array) + self.shallow(string),
        );
        let distinct = groups.len() as u64;
        let mut out: Vec<DuplicateGroup> = groups
            .into_iter()
            .filter(|group| group.count > 1)
            .map(|group| {
                let (string, array) = group.first;
                DuplicateGroup { string, array, hash: group.hash, count: group.count, wasted: group.wasted }
            })
            .collect();
        out.sort_by(|a, b| b.wasted.cmp(&a.wasted).then(a.array.cmp(&b.array)));
        Duplicates {
            wasted: out.iter().map(|group| group.wasted).sum(),
            groups: out,
            strings: seen.len() as u64,
            distinct,
        }
    }

    /// Reachable primitive arrays of at least `MIN_ARRAY_DATA_BYTES` that no String owns.
    pub fn hashable_arrays(&self, strings: &[(u32, u32)]) -> Vec<u32> {
        let dump = self.dump;
        let mut string_arrays = Bits::new(dump.objects.len());
        for &(_, array) in strings {
            string_arrays.set(array as usize);
        }
        parallel::ranges(dump.objects.len(), |lo, hi| {
            (lo as u32..hi as u32)
                .filter(|&object| {
                    let record = dump.objects.get(object as usize);
                    record.kind == Kind::PrimitiveArray
                        && record.shallow >= dump.sizing.array_header + MIN_ARRAY_DATA_BYTES
                })
                .filter(|&object| self.reachable(object) && !string_arrays.get(object as usize))
                .collect::<Vec<_>>()
        })
        .concat()
    }

    /// Group primitive arrays by content.
    pub fn array_duplicates(
        &self,
        arrays: &[u32],
        hash_of: impl Fn(u32) -> Option<u64> + Sync,
    ) -> ArrayDuplicates {
        let groups = group_by_hash(arrays, hash_of, |array| array, |array| self.shallow(array));
        let distinct = groups.len() as u64;
        let mut out: Vec<ArrayGroup> = groups
            .into_iter()
            .filter(|group| group.count > 1)
            .map(|group| ArrayGroup { array: group.first, count: group.count, wasted: group.wasted })
            .collect();
        out.sort_by(|a, b| b.wasted.cmp(&a.wasted).then(a.array.cmp(&b.array)));
        ArrayDuplicates {
            wasted: out.iter().map(|group| group.wasted).sum(),
            groups: out,
            arrays: arrays.len() as u64,
            distinct,
        }
    }

    /// The boxed classes present: `(class, class id, value offset, type)`.
    pub fn boxed_classes(&self) -> Vec<(u32, u64, u32, Ty)> {
        boxed_classes(&self.dump.classes, &self.dump.names, self.dump.header.id_size)
    }

    /// Boxed duplicates from the tallies the detail pass made.
    pub fn boxed(&self, tallies: &FastMap<(u32, u64), u64>) -> Vec<BoxedRow> {
        let mut by_class: FastMap<u32, Vec<(u64, u64)>> = FastMap::default();
        for (&(class, bits), &count) in tallies {
            by_class.entry(class).or_default().push((bits, count));
        }
        let mut rows: Vec<BoxedRow> = by_class
            .into_iter()
            .map(|(class, mut values)| {
                values.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
                let shallow = u64::from(self.dump.classes[class as usize].shallow);
                let instances = values.iter().map(|&(_, count)| count).sum();
                let wasted = values.iter().map(|&(_, count)| (count - 1) * shallow).sum();
                let distinct = values.len() as u64;
                values.truncate(5);
                BoxedRow { class, instances, distinct, wasted, top: values }
            })
            .filter(|row| row.wasted > 0)
            .collect();
        rows.sort_by(|a, b| b.wasted.cmp(&a.wasted).then(a.class.cmp(&b.class)));
        rows
    }
}
