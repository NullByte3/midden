//! Object size conventions: MAT's (two id-sized header words), or `HotSpot`'s
//! footprint with compressed or full-width oops.

use clap::ValueEnum;

use super::hprof::Ty;

#[derive(Clone, Copy, Debug, PartialEq, Eq, ValueEnum)]
pub enum SizeMode {
    /// Two id-sized header words, id-sized references: matches Eclipse MAT.
    Mat,
    /// 12-byte headers and 4-byte references: heaps under 32GB.
    Compressed,
    /// 16-byte headers and 8-byte references.
    Full,
    /// Compressed when the object addresses fit under 32GB, else full.
    Auto,
}

/// Resolved byte costs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Sizing {
    pub header: u32,
    pub array_header: u32,
    pub ref_size: u32,
    pub mode: SizeMode,
}

const ALIGN: u64 = 8;

/// Compressed oops address heaps up to this size.
const COMPRESSED_OOPS_LIMIT: u64 = 32 << 30;

/// Mark word and narrow class pointer, then the u32 array length.
const COMPRESSED: Sizing = Sizing { header: 12, array_header: 16, ref_size: 4, mode: SizeMode::Compressed };
/// Mark word and full class pointer, then the u32 array length padded to 8.
const FULL: Sizing = Sizing { header: 16, array_header: 24, ref_size: 8, mode: SizeMode::Full };

impl Sizing {
    pub fn resolve(mode: SizeMode, id_size: u32, max_id: u64) -> Sizing {
        match mode {
            SizeMode::Auto if id_size != 4 && max_id < COMPRESSED_OOPS_LIMIT => COMPRESSED,
            SizeMode::Auto if id_size != 4 => FULL,
            SizeMode::Mat | SizeMode::Auto => Sizing {
                header: 2 * id_size,
                // MAT's array header for 64-bit and 32-bit dumps.
                array_header: if id_size == 8 { 16 } else { 12 },
                ref_size: id_size,
                mode: SizeMode::Mat,
            },
            SizeMode::Compressed => COMPRESSED,
            SizeMode::Full => FULL,
        }
    }

    /// Footprint of one field or array element of `ty`.
    pub fn field_size(&self, ty: Ty) -> u32 {
        ty.size(self.ref_size)
    }

    pub fn instance_size(&self, field_bytes: u64) -> u32 {
        (u64::from(self.header) + field_bytes).next_multiple_of(ALIGN) as u32
    }

    pub fn array_size(&self, len: u64, element_size: u32) -> u32 {
        (u64::from(self.array_header) + len * u64::from(element_size))
            .next_multiple_of(ALIGN)
            .min(u64::from(u32::MAX)) as u32
    }

    pub fn label(&self) -> &'static str {
        match self.mode {
            SizeMode::Compressed => "compressed oops",
            SizeMode::Full => "full-width oops",
            _ => "MAT convention",
        }
    }
}
