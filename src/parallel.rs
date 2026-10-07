//! Thread fan-out over `--threads` scoped workers. Nothing is shared mutably: each worker returns its
//! part and the caller merges.

use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use std::sync::{Condvar, Mutex};
use std::thread;

use zerocopy::FromZeros;

use super::store::{Bits, Column};

/// Workers when the core count is unknown, and before `--threads` is applied.
pub const DEFAULT_THREADS: usize = 4;

static THREADS: AtomicUsize = AtomicUsize::new(DEFAULT_THREADS);

pub fn set_threads(count: usize) {
    THREADS.store(count.max(1), Relaxed);
}

pub fn threads() -> usize {
    THREADS.load(Relaxed)
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

/// Run `work` over every item on the workers and hand the results to `consume` in item order, on the
/// calling thread, as each one and all before it are done. Workers stay a few items ahead, so only that
/// many results are held at once. `consume` returning false stops the rest.
pub fn ordered<I: Sync, T: Send>(
    items: &[I],
    work: impl Fn(&I) -> T + Sync,
    mut consume: impl FnMut(T) -> bool,
) {
    let workers = threads().min(items.len().max(1));
    if workers <= 1 {
        for item in items {
            if !consume(work(item)) {
                return;
            }
        }
        return;
    }
    let window = 2 * workers;
    let state = Mutex::new(Ordered {
        next: 0,
        consumed: 0,
        stop: false,
        ready: (0..items.len()).map(|_| None).collect(),
    });
    let (done, room) = (Condvar::new(), Condvar::new());
    thread::scope(|scope| {
        for _ in 0..workers {
            scope.spawn(|| {
                loop {
                    let i = {
                        let mut state = state.lock().expect("worker panicked");
                        while !state.stop && state.next < items.len() && state.next >= state.consumed + window
                        {
                            state = room.wait(state).expect("worker panicked");
                        }
                        if state.stop || state.next >= items.len() {
                            return;
                        }
                        state.next += 1;
                        state.next - 1
                    };
                    let result = work(&items[i]);
                    state.lock().expect("worker panicked").ready[i] = Some(result);
                    done.notify_all();
                }
            });
        }
        for i in 0..items.len() {
            let result = {
                let mut state = state.lock().expect("worker panicked");
                loop {
                    if let Some(result) = state.ready[i].take() {
                        state.consumed = i + 1;
                        break result;
                    }
                    state = done.wait(state).expect("worker panicked");
                }
            };
            room.notify_all();
            if !consume(result) {
                state.lock().expect("worker panicked").stop = true;
                room.notify_all();
                return;
            }
        }
    });
}

/// Shared by the workers of [`ordered`]: the next item to claim, how many were consumed, the results.
struct Ordered<T> {
    next: usize,
    consumed: usize,
    stop: bool,
    ready: Vec<Option<T>>,
}

/// `len` copies of `value` in a column, filled by the workers.
pub fn filled<T: FromZeros + Copy + Send + Sync>(len: usize, value: T) -> Column<T> {
    let mut column = Column::zeroed(len);
    chunks(&mut column, |_, part| part.fill(value));
    column
}

/// `0..len` in a column.
pub fn iota(len: usize) -> Column<u32> {
    let mut column = Column::zeroed(len);
    chunks(&mut column, |start, part| {
        for (value, i) in part.iter_mut().zip(start as u32..) {
            *value = i;
        }
    });
    column
}

/// A bit per index in `0..len`, set where `f` holds, filled by the workers.
pub fn bits(len: usize, f: impl Fn(usize) -> bool + Sync) -> Bits {
    let mut bits = Bits::new(len);
    chunks(bits.words(), |start, words| {
        for (word, at) in words.iter_mut().zip((start * 64..).step_by(64)) {
            *word = (at..(at + 64).min(len)).rev().fold(0, |word, index| word << 1 | u64::from(f(index)));
        }
    });
    bits
}

/// Run each task on its own worker; results in task order.
pub fn run_all<T: Send>(tasks: Vec<impl FnOnce() -> T + Send>) -> Vec<T> {
    run(tasks.into_iter())
}
