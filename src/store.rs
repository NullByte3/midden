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
