//! What the dump still holds but nothing reaches: the garbage by class.

use super::{ClassRow, Heap, rows_of};
use crate::dump::FastMap;
use crate::parallel;

impl Heap<'_> {
    /// Unreachable objects by class, biggest first, weakly held left out; retained equals shallow.
    pub fn garbage(&self) -> Vec<ClassRow> {
        let dump = self.dump;
        let parts = parallel::ranges(dump.objects.len(), |lo, hi| {
            let mut by_class: FastMap<u32, (u64, u64)> = FastMap::default();
            for object in lo as u32..hi as u32 {
                if !self.reachable(object) && !self.weakly_reachable(object) {
                    let sums = by_class.entry(self.class(object)).or_default();
                    sums.0 += 1;
                    sums.1 += self.shallow(object);
                }
            }
            by_class
        });
        let mut all: FastMap<u32, (u64, u64)> = FastMap::default();
        for (class, (count, bytes)) in parts.into_iter().flatten() {
            let sums = all.entry(class).or_default();
            sums.0 += count;
            sums.1 += bytes;
        }
        rows_of(all).into_iter().filter(|row| !self.excluded(row.class)).collect()
    }
}
