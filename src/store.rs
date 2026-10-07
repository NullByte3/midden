//! Big arrays as plain vectors. A large one is its own mapping from the allocator: zeroed room costs no
//! memory until written, and growing or shrinking it remaps instead of copying.

use std::ops::{Deref, DerefMut};
use std::sync::atomic::{AtomicU32, AtomicU64};

use zerocopy::{FromBytes, FromZeros, IntoBytes};

/// An array of plain values, zeroed when made.
pub struct Column<T>(Vec<T>);

impl<T: FromZeros> Column<T> {
    /// `len` zeroes.
    pub fn zeroed(len: usize) -> Column<T> {
        Column(T::new_vec_zeroed(len).expect("column too large"))
    }
}

impl<T> Column<T> {
    /// Room for `capacity` values, none yet. Untouched room costs no memory; pushing past it grows.
    pub fn with_capacity(capacity: usize) -> Column<T> {
        Column(Vec::with_capacity(capacity))
    }

    pub fn push(&mut self, value: T) {
        self.0.push(value);
    }

    pub fn extend_from_slice(&mut self, values: &[T])
    where
        T: Copy,
    {
        self.0.extend_from_slice(values);
    }

    pub fn reserve(&mut self, additional: usize) {
        self.0.reserve(additional);
    }

    pub fn truncate(&mut self, len: usize) {
        self.0.truncate(len);
    }

    /// Hand the unused tail back. Nothing past `len` is read again.
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit();
    }
}

impl Column<u32> {
    /// The values as atomics, for workers filling disjoint slots.
    pub fn atomics(&mut self) -> &[AtomicU32] {
        <[AtomicU32]>::mut_from_bytes(self.0.as_mut_bytes()).expect("AtomicU32 has the layout of u32")
    }
}

impl Column<u64> {
    /// The values as atomics, for workers adding into shared slots.
    pub fn atomics(&mut self) -> &[AtomicU64] {
        <[AtomicU64]>::mut_from_bytes(self.0.as_mut_bytes()).expect("AtomicU64 has the layout of u64")
    }
}

impl<T> Deref for Column<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        &self.0
    }
}

impl<T> DerefMut for Column<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        &mut self.0
    }
}

impl<T> FromIterator<T> for Column<T> {
    fn from_iter<I: IntoIterator<Item = T>>(values: I) -> Column<T> {
        Column(values.into_iter().collect())
    }
}

/// One bit per index, in a column.
pub struct Bits {
    words: Column<u64>,
}

impl Bits {
    pub fn new(len: usize) -> Bits {
        Bits { words: Column::zeroed(len.div_ceil(64)) }
    }

    pub fn get(&self, index: usize) -> bool {
        self.words[index / 64] >> (index % 64) & 1 != 0
    }

    pub fn set(&mut self, index: usize) {
        self.words[index / 64] |= 1 << (index % 64);
    }

    /// Clear a bit, saying whether it was set.
    pub fn take(&mut self, index: usize) -> bool {
        let (word, bit) = (&mut self.words[index / 64], 1u64 << (index % 64));
        let was = *word & bit != 0;
        *word &= !bit;
        was
    }

    pub fn word(&self, index: usize) -> u64 {
        self.words[index]
    }

    /// The words, 64 indices each, lowest bit first.
    pub fn words(&mut self) -> &mut [u64] {
        &mut self.words
    }

    /// The words as atomics, for workers setting bits.
    pub fn atomics(&mut self) -> &[AtomicU64] {
        self.words.atomics()
    }
}

impl<T> Extend<T> for Column<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, values: I) {
        self.0.extend(values);
    }
}

/// Values per base in a [`Blocked`] column.
pub const BLOCK: usize = 256;

/// Ascending values in two bytes each above a base every [`BLOCK`] of them. One too far above its base
/// is all ones there and kept whole in `long`, by index.
pub struct Blocked {
    bases: Column<u64>,
    above: Column<u16>,
    long: Vec<(u32, u64)>,
}

impl Blocked {
    /// `value(i)` for every `i` in `0..len`, ascending, laid out by the workers.
    pub fn new(len: usize, value: impl Fn(usize) -> u64 + Sync) -> Blocked {
        let mut bases = Column::<u64>::zeroed(len.div_ceil(BLOCK));
        let mut above = Column::<u16>::zeroed(len);
        let per = bases.len().div_ceil(super::parallel::threads()).max(1);
        let value = &value;
        let tasks: Vec<_> = bases
            .chunks_mut(per)
            .zip(above.chunks_mut(per * BLOCK))
            .enumerate()
            .map(|(task, (bases, above))| {
                move || {
                    let mut long = Vec::new();
                    for (block, (base, above)) in bases.iter_mut().zip(above.chunks_mut(BLOCK)).enumerate() {
                        let start = (task * per + block) * BLOCK;
                        *base = value(start);
                        for (i, above) in (start..).zip(above.iter_mut()) {
                            let value = value(i);
                            *above = u16::try_from(value - *base).unwrap_or(u16::MAX);
                            if *above == u16::MAX {
                                long.push((i as u32, value));
                            }
                        }
                    }
                    long
                }
            })
            .collect();
        let long = super::parallel::run_all(tasks).concat();
        Blocked { bases, above, long }
    }

    pub fn get(&self, i: usize) -> u64 {
        match self.above[i] {
            u16::MAX => self.long[self.long.partition_point(|&(at, _)| (at as usize) < i)].1,
            above => self.bases[i / BLOCK] + u64::from(above),
        }
    }

    pub fn len(&self) -> usize {
        self.above.len()
    }

    /// The base of the block holding `i`.
    pub fn base(&self, i: usize) -> u64 {
        self.bases[i / BLOCK]
    }

    /// The two-byte parts of `lo..hi`: within one block they ascend, the long ones last.
    pub fn above(&self, lo: usize, hi: usize) -> &[u16] {
        &self.above[lo..hi]
    }
}
