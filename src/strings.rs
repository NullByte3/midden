//! Strings as text: which array backs a `java.lang.String`, decoding it from
//! fetched bytes, previews safe for a terminal line, and `--find` needles.

use super::detail::{Fetched, RawRecord};
use super::dump::{Dump, Kind, NONE};
use super::graph::Graph;
use super::hprof::Ty;
use super::parallel;

pub fn string_array(dump: &Dump, graph: &Graph, string: u32) -> Option<u32> {
    let array = graph.field(string, dump.value_label)?;
    (dump.objects[array as usize].kind == Kind::PrimitiveArray).then_some(array)
}

/// Every String with its backing array.
pub fn strings(dump: &Dump, graph: &Graph) -> Vec<(u32, u32)> {
    if dump.string_class == NONE {
        return Vec::new();
    }
    parallel::ranges(dump.objects.len(), |lo, hi| {
        (lo as u32..hi as u32)
            .filter(|&object| dump.objects[object as usize].class == dump.string_class)
            .filter_map(|string| string_array(dump, graph, string).map(|array| (string, array)))
            .collect::<Vec<_>>()
    })
    .concat()
}

/// The ids to fetch so String `string` can be shown.
pub fn string_ids(dump: &Dump, graph: &Graph, string: u32, want: &mut Vec<u64>) {
    want.push(dump.objects[string as usize].id);
    if let Some(array) = string_array(dump, graph, string) {
        want.push(dump.objects[array as usize].id);
    }
}

/// Decode a String: JDK 9+ has a `byte[]` and a `coder` (0 latin-1, 1 utf-16), older JDKs a `char[]`.
pub fn string_text(dump: &Dump, graph: &Graph, fetched: &Fetched, string: u32) -> Option<String> {
    let backing = string_array(dump, graph, string)?;
    let array = fetched.raw.get(&dump.objects[backing as usize].id)?;
    let coder = fetched.raw.get(&dump.objects[string as usize].id).and_then(|raw| {
        let (offset, _) = dump
            .field_offset(dump.objects[string as usize].class, "coder")
            .filter(|&(_, ty)| ty == Ty::Byte)?;
        raw.data.get(offset as usize).copied()
    });
    let text = decode(array, array.ty == Ty::Char || coder == Some(1));
    Some(if (array.data.len() as u32) < array.len * array.ty.size(8).max(1) { text + "…" } else { text })
}

fn decode(array: &RawRecord, utf16: bool) -> String {
    if utf16 {
        let units: Vec<u16> =
            array.data.as_chunks::<2>().0.iter().map(|unit| u16::from_be_bytes(*unit)).collect();
        String::from_utf16_lossy(&units)
    } else {
        array.data.iter().map(|&byte| char::from(byte)).collect()
    }
}

/// A char[] or byte[] shown as text, for the inspector.
pub fn text_of_array(raw: &RawRecord, max: usize) -> Option<String> {
    match raw.ty {
        Ty::Char | Ty::Byte => Some(preview(&decode(raw, raw.ty == Ty::Char), max)),
        _ => None,
    }
}

/// A string made safe and short for one line.
pub fn preview(text: &str, max: usize) -> String {
    let mut out = String::with_capacity(max + 4);
    for (i, c) in text.chars().enumerate() {
        if i >= max {
            out.push('…');
            break;
        }
        match c {
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c.is_control() => out.push('�'),
            c => out.push(c),
        }
    }
    out
}

/// Text to look for inside string arrays, in both encodings a String uses.
pub struct Needle {
    latin: Vec<u8>,
    utf16: Vec<u8>,
}

impl Needle {
    pub fn new(text: &str) -> Needle {
        let latin = text.chars().map(|c| if (c as u32) < 256 { c as u32 as u8 } else { b'?' }).collect();
        let utf16 = text.encode_utf16().flat_map(u16::to_be_bytes).collect();
        Needle { latin, utf16 }
    }

    /// ASCII case-insensitive containment in an array's bytes.
    pub fn matches(&self, ty: Ty, data: &[u8]) -> bool {
        match ty {
            Ty::Byte => contains(data, &self.latin, 1) || contains(data, &self.utf16, 2),
            Ty::Char => contains(data, &self.utf16, 2),
            _ => false,
        }
    }
}

/// Substring search, ASCII letters in either case; `unit` is the code unit width so utf-16 stays aligned.
fn contains(haystack: &[u8], needle: &[u8], unit: usize) -> bool {
    let Some(last) = haystack.len().checked_sub(needle.len()) else { return false };
    (0..=last)
        .step_by(unit)
        .any(|i| haystack[i..i + needle.len()].iter().zip(needle).all(|(a, b)| a.eq_ignore_ascii_case(b)))
}
