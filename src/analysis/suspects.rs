//! Leak suspects: an object retaining a large share of the heap, followed down the dominator tree
//! to where the memory accumulates, or a class whose instances add up to one.

use super::{ClassRow, Heap, Referrer, Tally};
use crate::dump::{FastMap, NONE};
use crate::graph::ARRAY_ELEMENT;
use crate::parallel;

/// Dominator tree steps `descend` takes at most, so a corrupt tree cannot loop.
const MAX_DESCENT: usize = 10_000_000;

/// One step from a top-level object towards its accumulation point. A run
/// of same-class objects linked by one field folds into a hop with `chain > 1`.
#[derive(Clone, Copy, Debug)]
pub struct Hop {
    pub object: u32,
    /// Label of the edge from the previous hop.
    pub label: Option<u32>,
    pub chain: u64,
    pub end: u32,
}

/// A top-level object retaining a large share, and where it accumulates.
pub struct ObjectSuspect {
    pub hops: Vec<Hop>,
    /// The accumulation point's dominated set, by class.
    pub keeps: Vec<ClassRow>,
    pub kept_objects: u64,
}

/// A class whose instances together retain a large share.
pub struct ClassSuspect {
    pub row: ClassRow,
    pub biggest: u32,
    pub referrers: Vec<Referrer>,
    /// Dominator classes up from the instances: `(class or NONE, bytes, bytes considered)`.
    pub owners: Vec<(u32, u64, u64)>,
}

pub enum Suspect {
    Object(ObjectSuspect),
    Class(ClassSuspect),
}

impl Suspect {
    /// The top object a suspect stands for.
    pub fn object(&self) -> u32 {
        match self {
            Suspect::Object(object) => object.hops[0].object,
            Suspect::Class(class) => class.biggest,
        }
    }
}

impl Heap<'_> {
    /// Follow the dominator tree down from `top` while one child holds at
    /// least three quarters: where that stops is the accumulation point.
    pub fn descend(&self, top: u32) -> Vec<Hop> {
        let mut hops = vec![Hop { object: top, label: None, chain: 1, end: top }];
        let mut current = top;
        for _ in 0..MAX_DESCENT {
            let Some(child) = self.dominators.biggest_child(current) else { break };
            if self.dominators.retained[child as usize] * 4 < self.dominators.retained[current as usize] * 3 {
                break;
            }
            let label = self.graph.label_of(current, child);
            let folds = hops.len() >= 2;
            let last = hops.last_mut().expect("never empty");
            let is_field = label.is_some_and(|label| label & ARRAY_ELEMENT == 0);
            if folds && self.class(child) == self.class(current) && is_field && label == last.label {
                last.chain += 1;
                last.end = child;
            } else {
                hops.push(Hop { object: child, label, chain: 1, end: child });
            }
            current = child;
        }
        hops
    }

    /// Objects and classes holding at least `min_percent` percent of the live heap, biggest first. A class
    /// mostly inside another suspect is the same leak one level down and is left out.
    pub fn suspects(&self, min_percent: f64, histogram: &[ClassRow]) -> Vec<Suspect> {
        let floor = ((self.live as f64 * min_percent / 100.0) as u64).max(1);
        let mut out = Vec::new();
        let mut inside: FastMap<u32, u64> = FastMap::default();
        for &object in self.top_level() {
            if self.dominators.retained[object as usize] < floor {
                break;
            }
            if self.excluded(self.class(object)) {
                continue;
            }
            let hops = self.descend(object);
            let (keeps, kept_objects) = self.retained_set(hops.last().expect("never empty").object);
            for kept in &keeps {
                *inside.entry(kept.class).or_default() += kept.instances;
            }
            out.push(Suspect::Object(ObjectSuspect { hops, keeps, kept_objects }));
        }
        let biggest = self.biggest_per_class();
        let rows: Vec<ClassRow> = histogram
            .iter()
            .filter(|row| {
                row.retained >= floor && row.class != self.dump.class_class && !self.excluded(row.class)
            })
            .filter(|row| biggest[row.class as usize].0 < floor)
            .copied()
            .collect();
        let classes: Vec<u32> = rows.iter().map(|row| row.class).collect();
        let members = self.members_of(&classes);
        // Only members are counted: a bit per object keeps most edges off the object table.
        let mut slot = vec![NONE; self.dump.classes.len()];
        let mut bits = vec![0u64; self.dump.objects.len().div_ceil(u64::BITS as usize)];
        for (i, (&class, class_members)) in classes.iter().zip(&members).enumerate() {
            slot[class as usize] = i as u32;
            for &member in class_members {
                bits[member as usize / u64::BITS as usize] |= 1 << (member % u64::BITS);
            }
        }
        let is_member =
            |object: u32| bits[object as usize / u64::BITS as usize] >> (object % u64::BITS) & 1 != 0;
        let mut referrers =
            self.referrers(|target| is_member(target).then(|| slot[self.class(target) as usize] as usize));
        let mut covered: Vec<u32> = Vec::new();
        for (i, (&row, class_members)) in rows.iter().zip(&members).enumerate() {
            let owned = class_members
                .iter()
                .filter(|&&member| {
                    let dominator = self.dominators.idom[member as usize];
                    dominator != self.graph.root && covered.contains(&self.class(dominator))
                })
                .count() as u64;
            let seen = owned + inside.get(&row.class).copied().unwrap_or(0);
            covered.push(row.class);
            if seen * 2 >= row.instances {
                continue;
            }
            out.push(Suspect::Class(ClassSuspect {
                row,
                biggest: biggest[row.class as usize].1,
                referrers: std::mem::take(&mut referrers[i]),
                owners: self.owners_of(class_members),
            }));
        }
        out.sort_by_key(|suspect| std::cmp::Reverse(self.suspect_retained(suspect)));
        out
    }

    /// Bytes a suspect stands for.
    pub fn suspect_retained(&self, suspect: &Suspect) -> u64 {
        match suspect {
            Suspect::Object(object) => self.retained(object.hops[0].object),
            Suspect::Class(class) => class.row.retained,
        }
    }

    /// What a class's instances keep alive, from the instances no other instance of it dominates.
    pub fn keeps_of_class(&self, class: u32) -> (Vec<ClassRow>, u64) {
        let (dump, tree) = (self.dump, &self.dominators);
        // Each worker scans a range of the preorder, inside an instance's
        // subtree until `until`, starting from the topmost instance above.
        let parts = parallel::ranges(tree.preorder.len(), |lo, hi| {
            let mut tally = Tally::new(dump.classes.len());
            let mut until = 0;
            let mut ancestor = tree.preorder.get(lo).map_or(NONE, |&object| tree.idom[object as usize]);
            while ancestor != NONE && ancestor != self.graph.root {
                if self.class(ancestor) == class {
                    until = tree.subtree_end[tree.preorder_index[ancestor as usize] as usize];
                }
                ancestor = tree.idom[ancestor as usize];
            }
            for (pos, &object) in (lo as u32..).zip(&tree.preorder[lo..hi]) {
                if pos >= until && self.class(object) == class {
                    until = tree.subtree_end[pos as usize];
                }
                if pos < until {
                    tally.add(&dump.objects[object as usize]);
                }
            }
            tally
        });
        parts.into_iter().reduce(Tally::merge).expect("one part at least").rows()
    }
}
