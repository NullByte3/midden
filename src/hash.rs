//! Hash constants shared by the cache key, the array hashes and the id maps.

/// FNV-1a 64-bit offset basis.
pub const FNV_OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
/// FNV-1a 64-bit prime.
pub const FNV_PRIME: u64 = 0x0100_0000_01b3;
/// 2^64 divided by the golden ratio, the Fibonacci hashing multiplier.
pub const GOLDEN_RATIO: u64 = 0x9e37_79b9_7f4a_7c15;
