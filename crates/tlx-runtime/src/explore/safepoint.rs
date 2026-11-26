//! The control word and safepoints (docs/scale.md §3).
//!
//! Workers read the control word between tasks: zero means "go on", which
//! is the only cost on the hot path (one relaxed load, as the stop flag it
//! replaces). Bit 0 (`STOP`) stops the search; the other bits are pending
//! safepoint requests, set by any thread with `Control::request`.
//!
//! A worker that sees a request parks (`Safepoint::park`). When every
//! active worker has parked, the last one to arrive (the executor) takes
//! the pending requests and serves them while the others wait; it may split
//! work among them with `Crew::broadcast`. Then they all go on.
//!
//! Only active workers take part. A worker that is not expanding tasks
//! (waiting at a level barrier, or finished) holds no reference into the
//! structures a safepoint operates on, so it leaves (`leave`) and the
//! safepoint does not wait for it; it joins again (`join`, which waits for a
//! safepoint in progress) before it expands tasks. If a worker leaves while
//! all the others are parked, it serves the requests itself. Requests made
//! while no worker is active are served once workers are active again (in
//! the level-synchronous search: at the start of the next level, with every
//! worker in the crew).

use std::any::Any;
use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicU32, Ordering};

use parking_lot::{Condvar, Mutex, MutexGuard};

/// The stop bit of the control word.
pub const STOP: u32 = 1;

/// The control word: `STOP`, and one bit per kind of pending safepoint
/// request. (On its own cache line: every worker reads it between tasks.)
#[repr(align(128))]
#[derive(Default)]
pub struct Control(AtomicU32);

impl Control {
    pub fn new() -> Control {
        Control(AtomicU32::new(0))
    }

    /// The control word (relaxed): zero when there is nothing to do.
    #[inline]
    pub fn get(&self) -> u32 {
        self.0.load(Ordering::Relaxed)
    }

    /// Whether the search is stopping.
    #[inline]
    pub fn stopped(&self) -> bool {
        self.get() & STOP != 0
    }

    /// Stop the search.
    pub fn stop(&self) {
        self.0.fetch_or(STOP, Ordering::SeqCst);
    }

    /// Request a safepoint: `bits` (not `STOP`) are served by the next one.
    pub fn request(&self, bits: u32) {
        assert!(bits != 0 && bits & STOP == 0, "safepoint request bits {bits:#x}");
        self.0.fetch_or(bits, Ordering::SeqCst);
    }

    /// The pending safepoint requests.
    pub fn requests(&self) -> u32 {
        self.0.load(Ordering::SeqCst) & !STOP
    }

    /// Take (clear and return) the pending safepoint requests.
    fn take_requests(&self) -> u32 {
        self.0.fetch_and(STOP, Ordering::SeqCst) & !STOP
    }
}

/// Safepoints of `n` workers (see the module documentation).
pub struct Safepoint {
    control: Control,
    state: Mutex<State>,
    cv: Condvar,
}

struct State {
    /// Workers expanding tasks (not left).
    active: usize,
    /// Active workers parked at the current safepoint.
    parked: usize,
    /// An executor is serving requests.
    executing: bool,
    /// A worker panicked (or a request handler did): nobody waits any
    /// more (`park` and `join` return at once).
    broken: bool,
    /// The number of safepoints served.
    epoch: u64,
    /// Work the executor shares with the parked workers.
    job: Option<Job>,
}

/// A `Crew::broadcast` in progress: parts `0..parts` of `f`.
struct Job {
    f: JobFn,
    parts: usize,
    /// The next part nobody has taken yet.
    next: usize,
    /// Parts taken and not yet finished.
    running: usize,
    panic: Option<Box<dyn Any + Send>>,
}

/// `Crew::broadcast`'s function, its lifetime erased: it is called only
/// while the broadcast waits for all its parts.
#[derive(Clone, Copy)]
struct JobFn(*const (dyn Fn(usize) + Sync + 'static));

// SAFETY: the pointee is `Sync`, and the pointer is dereferenced only while
// the broadcast that owns it is waiting for its parts (see `run_part`).
unsafe impl Send for JobFn {}

/// The workers stopped at a safepoint, as seen by its executor.
pub struct Crew<'a> {
    sp: &'a Safepoint,
    size: usize,
}

impl Crew<'_> {
    /// The number of workers available (the executor and the parked ones).
    pub fn size(&self) -> usize {
        self.size
    }

    /// Run `f(part)` for every part in `0..self.size()`, spread over the
    /// workers of the crew (the executor included); returns when all are
    /// done. A panic in `f` is propagated after all parts have finished.
    pub fn broadcast(&self, f: impl Fn(usize) + Sync) {
        let parts = self.size;
        if parts <= 1 {
            f(0);
            return;
        }
        let f: &(dyn Fn(usize) + Sync) = &f;
        // SAFETY: only the lifetime changes; the pointer is not used after
        // this function returns (it waits until no part is running and
        // removes the job).
        let f = JobFn(unsafe { std::mem::transmute::<*const (dyn Fn(usize) + Sync + '_), *const (dyn Fn(usize) + Sync + 'static)>(f) });
        let sp = self.sp;
        let mut g = sp.state.lock();
        debug_assert!(g.job.is_none());
        g.job = Some(Job { f, parts, next: 0, running: 0, panic: None });
        sp.cv.notify_all();
        // The executor takes parts too, so the job ends even if no helper
        // shows up (e.g. once the safepoint is broken).
        loop {
            let job = g.job.as_ref().expect("broadcast job");
            if job.next < job.parts {
                g = sp.run_part(g);
            } else if job.running > 0 {
                sp.cv.wait(&mut g);
            } else {
                break;
            }
        }
        let job = g.job.take().expect("broadcast job");
        drop(g);
        if let Some(p) = job.panic {
            resume_unwind(p);
        }
    }
}

impl Safepoint {
    /// Safepoints of `n` workers, all active.
    pub fn new(n: usize) -> Safepoint {
        Safepoint {
            control: Control::new(),
            state: Mutex::new(State { active: n, parked: 0, executing: false, broken: false, epoch: 0, job: None }),
            cv: Condvar::new(),
        }
    }

    /// The control word.
    #[inline]
    pub fn control(&self) -> &Control {
        &self.control
    }

    /// The number of safepoints served so far.
    pub fn served(&self) -> u64 {
        self.state.lock().epoch
    }

    /// Called by an active worker that saw a request (between tasks, or at
    /// any point where it holds no reference into what a safepoint may
    /// change): wait until the requests are served. The last active worker
    /// to arrive serves them with `serve(requests, crew)`. Returns at once
    /// if no request is pending or the safepoint is broken.
    pub fn park(&self, serve: impl FnOnce(u32, &Crew<'_>)) {
        let mut g = self.state.lock();
        if g.broken || self.control.requests() == 0 {
            return;
        }
        debug_assert!(!g.executing && g.parked < g.active, "park by an inactive worker");
        g.parked += 1;
        if g.parked == g.active {
            let helpers = g.parked - 1;
            self.execute(g, helpers, serve);
            return;
        }
        let epoch = g.epoch;
        while g.epoch == epoch && !g.broken {
            if g.job.as_ref().is_some_and(|j| j.next < j.parts) {
                g = self.run_part(g);
                continue;
            }
            self.cv.wait(&mut g);
        }
    }

    /// The calling worker stops expanding tasks (it is about to wait at a
    /// level barrier, or it is done). If all the other active workers are
    /// parked, it serves their requests (with `serve`) before it returns.
    pub fn leave(&self, serve: impl FnOnce(u32, &Crew<'_>)) {
        let mut g = self.state.lock();
        debug_assert!(!g.executing && g.active > g.parked, "leave by an inactive worker");
        g.active -= 1;
        if g.parked > 0 && g.parked == g.active && !g.broken {
            let helpers = g.parked;
            self.execute(g, helpers, serve);
        }
    }

    /// The calling worker (not active) starts expanding tasks again: waits
    /// for a safepoint in progress.
    pub fn join(&self) {
        let mut g = self.state.lock();
        while g.executing && !g.broken {
            self.cv.wait(&mut g);
        }
        g.active += 1;
    }

    /// `join` for `k` workers that are not active, on their behalf (they
    /// are waiting for the caller and start expanding tasks afterwards;
    /// each then counts itself active without calling `join`).
    pub fn join_all(&self, k: usize) {
        let mut g = self.state.lock();
        while g.executing && !g.broken {
            self.cv.wait(&mut g);
        }
        g.active += k;
    }

    /// Release every waiting worker, now and later (a worker panicked).
    pub fn break_all(&self) {
        self.state.lock().broken = true;
        self.cv.notify_all();
    }

    /// Serve the pending requests: all active workers are parked (`helpers`
    /// of them besides the caller).
    fn execute(&self, mut g: MutexGuard<'_, State>, helpers: usize, serve: impl FnOnce(u32, &Crew<'_>)) {
        g.executing = true;
        drop(g);
        let requests = self.control.take_requests();
        /// Ends the safepoint, also when `serve` panics (then nobody waits
        /// for anything any more, and the search stops).
        struct End<'a>(&'a Safepoint);
        impl Drop for End<'_> {
            fn drop(&mut self) {
                let sp = self.0;
                let mut g = sp.state.lock();
                g.executing = false;
                g.parked = 0;
                g.epoch += 1;
                if std::thread::panicking() {
                    g.broken = true;
                    sp.control.stop();
                }
                drop(g);
                sp.cv.notify_all();
            }
        }
        let _end = End(self);
        serve(requests, &Crew { sp: self, size: helpers + 1 });
    }

    /// Take the next part of the current job and run it (without the lock).
    fn run_part<'a>(&'a self, mut g: MutexGuard<'a, State>) -> MutexGuard<'a, State> {
        let job = g.job.as_mut().expect("broadcast job");
        let (part, f) = (job.next, job.f);
        job.next += 1;
        job.running += 1;
        drop(g);
        // SAFETY: the broadcast owning `f` waits until `running` is back to
        // zero before it returns, and this part is counted in `running`.
        let r = catch_unwind(AssertUnwindSafe(|| unsafe { (*f.0)(part) }));
        let mut g = self.state.lock();
        let job = g.job.as_mut().expect("broadcast job");
        job.running -= 1;
        if let Err(p) = r {
            job.panic.get_or_insert(p);
        }
        if job.running == 0 && job.next == job.parts {
            self.cv.notify_all();
        }
        g
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize};
    use std::sync::Barrier;

    const REQ: u32 = 1 << 1;

    /// Workers that do "tasks" (incrementing a shared counter) and park
    /// whenever a request is pending; the executor checks that nobody runs
    /// a task during the safepoint, and the crew covers every part.
    #[test]
    fn workers_are_quiescent_while_serving() {
        // Miri needs far fewer task iterations to exercise the same
        // quiescence assertions.
        let served_target = if cfg!(miri) { 20 } else { 200 };
        for n in [1, 2, 3, 8] {
            let sp = Safepoint::new(n);
            let in_task = AtomicUsize::new(0);
            let tasks = AtomicU64::new(0);
            let served = AtomicU64::new(0);
            let done = AtomicBool::new(false);
            std::thread::scope(|sc| {
                for me in 0..n {
                    let (sp, in_task, tasks, served, done) = (&sp, &in_task, &tasks, &served, &done);
                    sc.spawn(move || {
                        let serve = |req: u32, crew: &Crew<'_>| {
                            assert_eq!(req, REQ);
                            assert_eq!(in_task.load(Ordering::SeqCst), 0, "a worker is in a task");
                            let before = tasks.load(Ordering::SeqCst);
                            let parts: Vec<AtomicUsize> = (0..crew.size()).map(|_| AtomicUsize::new(0)).collect();
                            crew.broadcast(|p| {
                                parts[p].fetch_add(1, Ordering::SeqCst);
                                std::thread::yield_now();
                            });
                            assert!(parts.iter().all(|p| p.load(Ordering::SeqCst) == 1));
                            assert_eq!(tasks.load(Ordering::SeqCst), before, "a task ran during the safepoint");
                            served.fetch_add(1, Ordering::SeqCst);
                        };
                        for k in 0u64.. {
                            if done.load(Ordering::SeqCst) {
                                break;
                            }
                            if sp.control().get() != 0 {
                                sp.park(serve);
                                continue;
                            }
                            in_task.fetch_add(1, Ordering::SeqCst);
                            tasks.fetch_add(1, Ordering::SeqCst);
                            if k % 97 == (me as u64) * 13 {
                                sp.control().request(REQ);
                            }
                            in_task.fetch_sub(1, Ordering::SeqCst);
                            if served.load(Ordering::SeqCst) >= served_target {
                                done.store(true, Ordering::SeqCst);
                            }
                        }
                        sp.leave(serve);
                    });
                }
            });
            assert!(served.load(Ordering::SeqCst) >= served_target, "{n} workers");
            assert_eq!(sp.served(), served.load(Ordering::SeqCst));
        }
    }

    /// A worker that leaves while the others are parked serves the request
    /// (with the parked ones as its crew); a worker that joins waits for a
    /// safepoint in progress.
    #[test]
    fn leave_serves_and_join_waits() {
        let sp = Safepoint::new(3);
        let parked = Barrier::new(2);
        let serving = AtomicBool::new(false);
        let crew_size = AtomicUsize::new(0);
        std::thread::scope(|sc| {
            // Two workers park.
            for _ in 0..2 {
                sc.spawn(|| {
                    while sp.control().requests() == 0 {
                        std::hint::spin_loop();
                    }
                    sp.park(|_, _| panic!("a parked worker is not the executor here"));
                });
            }
            sp.control().request(REQ);
            // Wait until both are parked.
            while sp.state.lock().parked < 2 {
                std::thread::yield_now();
            }
            sc.spawn(|| {
                sp.leave(|req, crew| {
                    assert_eq!(req, REQ);
                    crew_size.store(crew.size(), Ordering::SeqCst);
                    serving.store(true, Ordering::SeqCst);
                    parked.wait();
                    std::thread::sleep(std::time::Duration::from_millis(20));
                    serving.store(false, Ordering::SeqCst);
                });
            });
            // Join while the leaving worker serves: returns after it.
            parked.wait();
            sp.join();
            assert!(!serving.load(Ordering::SeqCst));
        });
        assert_eq!(crew_size.load(Ordering::SeqCst), 3);
        assert_eq!(sp.served(), 1);
        assert_eq!(sp.control().get(), 0);
        let g = sp.state.lock();
        assert_eq!((g.active, g.parked), (3, 0));
    }

    /// No request, or no active worker left to wait for: nothing happens.
    #[test]
    fn park_without_request_and_requests_while_inactive() {
        let sp = Safepoint::new(2);
        sp.park(|_, _| panic!("no request"));
        sp.leave(|_, _| panic!("nobody parked"));
        sp.leave(|_, _| panic!("nobody parked"));
        // Requested while no worker is active: served once one is.
        sp.control().request(REQ);
        sp.join();
        let mut got = 0;
        sp.park(|req, crew| {
            assert_eq!(crew.size(), 1);
            got = req;
        });
        assert_eq!((got, sp.served()), (REQ, 1));
        // The stop bit is not a request and survives a safepoint.
        sp.control().stop();
        sp.park(|_, _| panic!("no request"));
        sp.control().request(REQ);
        sp.park(|_, _| {});
        assert_eq!(sp.control().get(), STOP);
    }

    /// A panic in a part of a broadcast reaches the executor after every
    /// part has finished; a panicking executor breaks the safepoint and
    /// stops the search, so that nobody waits forever.
    #[test]
    fn panics_break_the_safepoint() {
        let sp = Safepoint::new(3);
        sp.control().request(REQ);
        let finished = AtomicUsize::new(0);
        let r = std::thread::scope(|sc| {
            let hs: Vec<_> = (0..3)
                .map(|_| {
                    sc.spawn(|| {
                        catch_unwind(AssertUnwindSafe(|| {
                            sp.park(|_, crew| {
                                crew.broadcast(|p| {
                                    if p == 1 {
                                        panic!("part 1");
                                    }
                                    std::thread::sleep(std::time::Duration::from_millis(5));
                                    finished.fetch_add(1, Ordering::SeqCst);
                                });
                            })
                        }))
                        .is_err()
                    })
                })
                .collect();
            hs.into_iter().map(|h| h.join().unwrap()).filter(|&e| e).count()
        });
        assert_eq!(r, 1, "exactly the executor panics");
        assert_eq!(finished.load(Ordering::SeqCst), 2);
        assert!(sp.control().stopped());
        // Broken: parking and joining return at once.
        sp.control().request(REQ);
        sp.park(|_, _| panic!("broken"));
        sp.join();
    }
}
