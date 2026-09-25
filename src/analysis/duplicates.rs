//! Wasted copies: Strings with equal contents, primitive arrays with equal
//! contents, and boxed primitives holding the same value.

use super::Heap;
use crate::dump::{FastMap, Kind};
use crate::hprof::Ty;
use crate::parallel;

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

impl Heap<'_> {
    /// Group Strings by the content of their backing arrays.
    pub fn duplicates(&self, pairs: &[(u32, u32)], hash_of: impl Fn(u32) -> Option<u64>) -> Duplicates {
        let mut seen: Vec<(u32, u32)> = pairs.to_vec();
        seen.sort_unstable_by_key(|pair| (pair.1, pair.0));
        seen.dedup_by_key(|pair| pair.1);
        let mut groups: FastMap<u64, (u64, u32, u32, u64)> = FastMap::default();
        for &(string, array) in &seen {
            let Some(hash) = hash_of(array) else { continue };
            let group = groups.entry(hash).or_insert((0, string, array, 0));
            group.0 += 1;
            if group.0 > 1 {
                group.3 += self.shallow(array) + self.shallow(string);
            }
        }
        let distinct = groups.len() as u64;
        let mut out: Vec<DuplicateGroup> = groups
            .into_iter()
            .filter(|(_, group)| group.0 > 1)
            .map(|(hash, (count, string, array, wasted))| DuplicateGroup {
                string,
                array,
                hash,
                count,
                wasted,
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
        let mut string_arrays: Vec<u32> = strings.iter().map(|&(_, array)| array).collect();
        string_arrays.sort_unstable();
        let dump = self.dump;
        parallel::ranges(dump.objects.len(), |lo, hi| {
            (lo as u32..hi as u32)
                .filter(|&object| {
                    let record = &dump.objects[object as usize];
                    record.kind == Kind::PrimitiveArray
                        && record.shallow >= dump.sizing.array_header + MIN_ARRAY_DATA_BYTES
                })
                .filter(|&object| self.reachable(object) && string_arrays.binary_search(&object).is_err())
                .collect::<Vec<_>>()
        })
        .concat()
    }

    /// Group primitive arrays by content.
    pub fn array_duplicates(&self, arrays: &[u32], hash_of: impl Fn(u32) -> Option<u64>) -> ArrayDuplicates {
        let mut groups: FastMap<u64, ArrayGroup> = FastMap::default();
        for &array in arrays {
            let Some(hash) = hash_of(array) else { continue };
            let group = groups.entry(hash).or_insert(ArrayGroup { array, count: 0, wasted: 0 });
            group.count += 1;
            if group.count > 1 {
                group.wasted += self.shallow(array);
            }
        }
        let distinct = groups.len() as u64;
        let mut out: Vec<ArrayGroup> = groups.into_values().filter(|group| group.count > 1).collect();
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
        let dump = self.dump;
        BOXED
            .iter()
            .filter_map(|&(name, ty)| {
                let class = dump.class_named(name)?;
                let (offset, field_ty) = dump.field_offset(class, "value").filter(|field| field.1 == ty)?;
                Some((class, dump.classes[class as usize].id, offset, field_ty))
            })
            .collect()
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
