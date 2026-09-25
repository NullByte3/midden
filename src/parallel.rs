//! Thread fan-out over `--threads` scoped workers. Nothing is shared mutably: each worker returns its
//! part and the caller merges.

use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering::Relaxed};
use std::thread;

/// Workers when the core count is unknown, and before `--threads` is applied.
pub const DEFAULT_THREADS: usize = 4;

static THREADS: AtomicUsize = AtomicUsize::new(DEFAULT_THREADS);

pub fn set_threads(count: usize) {
    THREADS.store(count.max(1), Relaxed);
}

pub fn threads() -> usize {
    THREADS.load(Relaxed)
}

/// `len` atomics at zero, on pages nothing has touched yet: the workers that
/// fill them take the page faults, not the thread that allocates.
pub fn zeroed(len: usize) -> Vec<AtomicU32> {
    vec![0u32; len].into_iter().map(AtomicU32::new).collect()
}

/// Split `0..len` into one range per worker and run `f` on each, in order.
pub fn ranges<T: Send>(len: usize, f: impl Fn(usize, usize) -> T + Sync) -> Vec<T> {
    let workers = threads().min(len.max(1));
    if workers <= 1 {
        return vec![f(0, len)];
    }
    let (step, f) = (len.div_ceil(workers), &f);
    run((0..workers).map(|worker| move || f((worker * step).min(len), ((worker + 1) * step).min(len))))
}

/// Run `f(start, piece)` on one piece of `data` per worker, `start` being its offset; results in order.
pub fn chunks<T: Send, R: Send>(data: &mut [T], f: impl Fn(usize, &mut [T]) -> R + Sync) -> Vec<R> {
    let (step, f) = (data.len().div_ceil(threads()).max(1), &f);
    run(data.chunks_mut(step).enumerate().map(|(i, piece)| move || f(i * step, piece)))
}

/// Run `f` over every item, workers taking the next as they free up; results come back in item order.
pub fn items<I: Sync, T: Send>(items: &[I], f: impl Fn(&I) -> T + Sync) -> Vec<T> {
    let workers = threads().min(items.len().max(1));
    if workers <= 1 {
        return items.iter().map(&f).collect();
    }
    let (next, f) = (&AtomicUsize::new(0), &f);
    let mut out: Vec<(usize, T)> = run((0..workers).map(|_| {
        move || {
            let mut mine = Vec::new();
            loop {
                let i = next.fetch_add(1, Relaxed);
                let Some(item) = items.get(i) else { break mine };
                mine.push((i, f(item)));
            }
        }
    }))
    .into_iter()
    .flatten()
    .collect();
    out.sort_by_key(|(i, _)| *i);
    out.into_iter().map(|(_, result)| result).collect()
}

/// Run each task on its own scoped thread; results in task order.
fn run<'env, T: Send + 'env>(tasks: impl Iterator<Item = impl FnOnce() -> T + Send + 'env>) -> Vec<T> {
    thread::scope(|scope| {
        let handles: Vec<_> = tasks.map(|task| scope.spawn(task)).collect();
        handles.into_iter().map(|handle| handle.join().expect("worker panicked")).collect()
    })
}
