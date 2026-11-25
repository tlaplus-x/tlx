//! The level-synchronous search of several workers: all workers expand
//! level k (stealing from each other), then meet at a barrier before any
//! starts level k + 1, so that every state is reached by a shortest path (as
//! in TLC's BFS). Narrow levels are expanded by a single worker.
//!
//! The states a worker claimed are not lost to the barrier when it is
//! descheduled: near the end of a parallel level its block is staged for
//! stealing (`super::frontier`), and a worker that finds nothing left to
//! claim expands those states before it waits here. A narrow level expanded
//! by one worker alone stages nothing: its peers are waiting here anyway.

use std::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicUsize, Ordering};
use std::sync::OnceLock;
use std::thread::Thread;
use std::time::Instant;

use parking_lot::Mutex;

use super::worker::WorkerState;
use super::Shared;
use crate::model::Model;
use crate::stats;

/// The shared state of the level-synchronous search.
pub(super) struct Levels {
    /// Workers meet at this barrier between levels.
    pub(super) barrier: LevelBarrier,
    /// Tasks of the next level, counted per level parity.
    tasks: [AtomicU64; 2],
    /// Set by the barrier leader: no level follows.
    done: AtomicBool,
    /// Set by the barrier leader: the worker that expands the next level
    /// (and the following narrow ones) alone, or `NO_SOLO`.
    solo: AtomicUsize,
    /// Expansion time and number of tasks expanded at the current level, summed
    /// over the workers (parallel levels).
    busy_ns: AtomicU64,
    expanded: AtomicU64,
    /// Estimated cost of expanding a task, maintained by the barrier leader
    /// or the solo worker.
    cost: Mutex<CostEstimate>,
}

impl Levels {
    pub(super) fn new(n: usize) -> Levels {
        Levels {
            barrier: LevelBarrier::new(n),
            tasks: [AtomicU64::new(0), AtomicU64::new(0)],
            done: AtomicBool::new(false),
            solo: AtomicUsize::new(NO_SOLO),
            busy_ns: AtomicU64::new(0),
            expanded: AtomicU64::new(0),
            cost: Mutex::new(CostEstimate::new(n)),
        }
    }
}

/// A reusable barrier for the workers of the level-synchronous search.
///
/// A waiting worker spins for a while (levels are often short), then
/// yields a few times, then parks (`std::thread::park`); the last to arrive
/// (the leader) runs the barrier's action before it releases the others,
/// and wakes the parked ones directly, all at once (not one after another
/// through a mutex, as a condition variable's waiters reacquiring it).
///
/// The spin budget adapts: it doubles after a wait that ended while
/// spinning or yielding and halves after one that had to park, between
/// `MIN_SPINS` and `MAX_SPINS`. When the machine is oversubscribed (more
/// runnable threads than cores), a worker that arrives late was usually
/// scheduled out, and spinning only takes a core away from it: the waits
/// park and the budget stays low.
pub(super) struct LevelBarrier {
    n: usize,
    /// Workers arrived in the current generation.
    count: AtomicUsize,
    /// Incremented when all workers have arrived (after the action).
    generation: AtomicUsize,
    /// Spin iterations before yielding (adaptive).
    spins: AtomicU32,
    /// Per worker: its thread (once it has parked once) and whether it is
    /// parked or about to park in the current generation.
    sleepers: Vec<Sleeper>,
    /// Set when a worker panicked: it will never arrive, so nobody waits
    /// any more (`wait` returns at once).
    broken: AtomicBool,
}

#[derive(Default)]
struct Sleeper {
    thread: OnceLock<Thread>,
    parked: AtomicBool,
}

impl LevelBarrier {
    /// Bounds of the spin budget (iterations of `spin_loop`, each some
    /// nanoseconds to tens of nanoseconds).
    const MIN_SPINS: u32 = 1 << 6;
    const MAX_SPINS: u32 = 1 << 12;
    /// `yield_now` calls after spinning, before parking.
    const YIELDS: u32 = 4;

    fn new(n: usize) -> LevelBarrier {
        LevelBarrier {
            n,
            count: AtomicUsize::new(0),
            generation: AtomicUsize::new(0),
            spins: AtomicU32::new(Self::MAX_SPINS),
            sleepers: (0..n).map(|_| Sleeper::default()).collect(),
            broken: AtomicBool::new(false),
        }
    }

    /// Release every waiting worker, now and later (a worker panicked).
    pub(super) fn break_all(&self) {
        self.broken.store(true, Ordering::SeqCst);
        self.wake();
    }

    pub(super) fn is_broken(&self) -> bool {
        self.broken.load(Ordering::SeqCst)
    }

    /// Wait until all workers have arrived. Returns true for exactly one
    /// of them (the last to arrive: the leader). Once the barrier is
    /// broken, returns false at once (callers check `is_broken`).
    #[cfg(test)]
    fn wait(&self, me: usize) -> bool {
        self.wait_then(me, || ())
    }

    /// Wait until all workers have arrived; the last to arrive (the
    /// leader) runs `action` before any other returns. Returns true for
    /// the leader. `me` is the caller's worker number. Once the barrier is
    /// broken, returns false at once (callers check `is_broken`).
    pub(super) fn wait_then(&self, me: usize, action: impl FnOnce()) -> bool {
        if self.is_broken() {
            return false;
        }
        let gen = self.generation.load(Ordering::SeqCst);
        if self.count.fetch_add(1, Ordering::SeqCst) + 1 == self.n {
            // Nobody arrives again before the generation changes.
            self.count.store(0, Ordering::SeqCst);
            action();
            self.generation.store(gen.wrapping_add(1), Ordering::SeqCst);
            self.wake();
            return true;
        }
        let released = || self.generation.load(Ordering::SeqCst) != gen || self.is_broken();
        let budget = self.spins.load(Ordering::Relaxed);
        for _ in 0..budget {
            if released() {
                self.adapt(true);
                return false;
            }
            std::hint::spin_loop();
        }
        for _ in 0..Self::YIELDS {
            if released() {
                self.adapt(true);
                return false;
            }
            std::thread::yield_now();
        }
        self.adapt(false);
        // Announce the park before checking the generation a last time; the
        // leader bumps the generation before it reads the flags (both
        // sequentially consistent): it sees the flag, or we see the bump.
        let me = &self.sleepers[me];
        me.thread.get_or_init(std::thread::current);
        me.parked.store(true, Ordering::SeqCst);
        while !released() {
            // (May return spuriously, or for an unpark of an earlier
            // generation: the loop checks again.)
            std::thread::park();
        }
        me.parked.store(false, Ordering::SeqCst);
        false
    }

    /// Unpark the workers parked (or about to park).
    fn wake(&self) {
        for s in &self.sleepers {
            if s.parked.load(Ordering::SeqCst) {
                if let Some(t) = s.thread.get() {
                    t.unpark();
                }
            }
        }
    }

    /// Adjust the spin budget after a wait that ended while spinning or
    /// yielding (`spun`), or that had to park.
    fn adapt(&self, spun: bool) {
        let s = self.spins.load(Ordering::Relaxed);
        let t = if spun { (s * 2).min(Self::MAX_SPINS) } else { (s / 2).max(Self::MIN_SPINS) };
        if t != s {
            self.spins.store(t, Ordering::Relaxed);
        }
    }
}

/// No worker expands levels alone: the next level is expanded in parallel.
const NO_SOLO: usize = usize::MAX;

/// Initial estimate of the synchronization overhead of a parallel level, per
/// worker (refined by measuring the parallel levels).
const INITIAL_OVERHEAD_PER_WORKER_NS: f64 = 2_000.0;

/// What the choice between expanding a level in parallel or by one worker
/// depends on: the time to expand a task (expansion times and task counts
/// of the recent levels, older ones decaying geometrically) and the
/// synchronization overhead of a parallel level.
struct CostEstimate {
    ns: f64,
    tasks: f64,
    /// Estimated overhead of a parallel level (ns): its duration minus its
    /// expansion time divided among the workers.
    overhead: f64,
    workers: f64,
    /// When the previous level ended (all workers at the barrier).
    last_sync: Option<Instant>,
}

impl CostEstimate {
    fn new(workers: usize) -> CostEstimate {
        let workers = workers as f64;
        CostEstimate { ns: 0.0, tasks: 0.0, overhead: INITIAL_OVERHEAD_PER_WORKER_NS * workers, workers, last_sync: None }
    }

    fn add(&mut self, ns: u64, tasks: u64) {
        if tasks > 0 {
            self.ns = self.ns / 2.0 + ns as f64;
            self.tasks = self.tasks / 2.0 + tasks as f64;
        }
    }

    /// Estimated nanoseconds per task (infinite before any measurement).
    fn per_task(&self) -> f64 {
        if self.tasks > 0.0 {
            self.ns / self.tasks
        } else {
            f64::INFINITY
        }
    }

    /// Whether a level of `width` tasks is better expanded by one worker:
    /// what the other workers would save is less than the overhead.
    fn solo(&self, width: usize) -> bool {
        width as f64 * self.per_task() * (1.0 - 1.0 / self.workers) < self.overhead
    }

    /// Called by the barrier leader when all workers have finished a level,
    /// at `now`: `parallel` is the number of tasks of the level if it was
    /// expanded in parallel (its duration then refines the overhead).
    fn level_end(&mut self, now: Instant, parallel: Option<u64>) {
        if let (Some(prev), Some(n)) = (self.last_sync, parallel) {
            let period = (now - prev).as_nanos() as f64;
            let work = n as f64 * self.per_task() / self.workers;
            // On wide levels the overhead is lost in the noise.
            if work.is_finite() && work <= 16.0 * self.overhead + 100_000.0 {
                let sample = (period - work).clamp(0.0, 2.0 * self.overhead + 10_000.0);
                self.overhead = (self.overhead + (sample - self.overhead) / 8.0).max(500.0);
            }
        }
        self.last_sync = Some(now);
    }
}

impl<M: Model> WorkerState<'_, '_, M> {
    /// Expand tasks of the current level until none is left or the search
    /// stops. Returns the number of tasks expanded. `stealing`: the level is
    /// expanded in parallel, so the blocks this worker claims are staged for
    /// the others to steal the states of (`Local::share`); a narrow level it
    /// expands alone keeps them private.
    pub(super) fn expand_level(&mut self, stealing: bool) -> u64 {
        let shared = self.shared;
        self.local.share(stealing);
        self.order_level();
        let mut n = 0;
        loop {
            if shared.store_gc.is_some_and(|gc| gc.needs_gc()) {
                shared.control().request(super::SP_STORE_GC);
            }
            if !self.proceed() {
                break;
            }
            if shared.model.stop_requested() {
                shared.control().stop();
                break;
            }
            let Some(task) = self.local.pop() else { break };
            self.run(&task);
            self.retire(task);
            n += 1;
        }
        if let Some(e) = self.local.take_io_error() {
            // (A spilled segment could not be read back.)
            shared.fail(super::Outcome::Io(e.0), super::tracelog::NO_PARENT);
        }
        n
    }
}

/// Level-synchronous search: all workers expand level k (claiming its
/// blocks), then meet at the barrier before any starts level k + 1. Each
/// submits its tasks of level k + 1 before the barrier; the barrier leader
/// makes them the current level (`Frontier::install`) before it releases the
/// others, so that one barrier per level suffices (two when choosing
/// representatives in BFS order). Under oversubscription each barrier costs
/// about a scheduling quantum of the slowest worker to be scheduled again.
///
/// Narrow levels, too small to be worth that synchronization, are expanded by
/// a single worker (the barrier leader that found the level narrow) while
/// the others stay parked at the barrier: it goes on level by level in exact
/// BFS order, through any number of narrow levels, and meets the others again
/// when a level is wide (or the search ends).
///
/// A worker is active for the safepoints (see `safepoint`) from the moment
/// all workers have queued the tasks of a level (the leader joins them all)
/// until it waits at the next barrier.
pub(super) fn run_levels<M: Model>(w: &mut WorkerState<'_, '_, M>) {
    let shared = w.shared;
    let levels = &shared.levels;
    for level in 0usize.. {
        let solo = levels.solo.load(Ordering::SeqCst);
        if solo == NO_SOLO {
            let start = Instant::now();
            let n = w.expand_level(true);
            levels.busy_ns.fetch_add(start.elapsed().as_nanos() as u64, Ordering::SeqCst);
            levels.expanded.fetch_add(n, Ordering::SeqCst);
            if shared.order.is_some() {
                // Choosing the representatives in BFS order: once every
                // worker has offered its candidates (see `order`).
                w.leave_safepoints();
                barrier_wait_then(shared, w.me, || {
                    if shared.store_gc.is_some() {
                        shared.safepoint.join_all(shared.slots.len());
                    }
                });
                if levels.barrier.is_broken() {
                    return;
                }
                if shared.store_gc.is_some() {
                    w.joined_safepoints();
                }
                w.resolve();
            }
        } else if solo == w.me {
            let mut cost = levels.cost.lock();
            // The cost estimate is updated every `SOLO_SAMPLE` tasks (reading
            // the clock at every level would be noticeable on very narrow ones).
            const SOLO_SAMPLE: u64 = 64;
            let mut mark = Instant::now();
            let mut since_mark = 0;
            loop {
                since_mark += w.expand_level(false);
                w.resolve();
                let width = w.local.next_len();
                let end = width == 0 || shared.control().stopped();
                if since_mark >= SOLO_SAMPLE || end {
                    let now = Instant::now();
                    cost.add((now - mark).as_nanos() as u64, since_mark);
                    (mark, since_mark) = (now, 0);
                }
                // (A checkpoint due ends the stretch: it is taken at the
                // barrier, where every worker writes its part.)
                if end || !cost.solo(width) || shared.checkpoint_wanted() {
                    break;
                }
                // (The other workers wait at the barrier.)
                if let Some(o) = &shared.order {
                    o.advance();
                }
                w.local.advance();
            }
        }
        let width = w.local.next_len();
        levels.tasks[level % 2].fetch_add(width as u64, Ordering::SeqCst);
        w.local.submit();
        w.leave_safepoints();
        let me = w.me;
        // The leader (the last to arrive) prepares the next level before
        // any worker returns from the barrier.
        barrier_wait_then(shared, me, || {
            // Every worker has counted its tasks; the other counter was read
            // by all at the previous level.
            let total = levels.tasks[level % 2].load(Ordering::SeqCst);
            levels.tasks[(level + 1) % 2].store(0, Ordering::SeqCst);
            // (Also when the search stops: the tasks left are counted,
            // or retained, from the current level.)
            shared.frontier.install();
            if shared.model.stop_requested() {
                shared.control().stop();
            }
            // (Not when the search stops: a resumed search expands this
            // level again.)
            if let (Some(o), false) = (&shared.order, total == 0 || shared.control().stopped()) {
                o.advance();
            }
            let solo_next = {
                let mut cost = levels.cost.lock();
                let expanded = levels.expanded.swap(0, Ordering::SeqCst);
                cost.add(levels.busy_ns.swap(0, Ordering::SeqCst), expanded);
                cost.level_end(Instant::now(), (solo == NO_SOLO).then_some(expanded));
                cost.solo(total as usize)
            };
            levels.solo.store(if solo_next { me } else { NO_SOLO }, Ordering::SeqCst);
            let done = total == 0 || shared.control().stopped();
            levels.done.store(done, Ordering::SeqCst);
            // (A checkpoint: the workers write their parts below, and join
            // the safepoints after it.)
            if !done {
                if shared.checkpoint_due() {
                    if shared.store_gc.is_some_and(|gc| gc.needs_gc()) {
                        shared.gc_store();
                    }
                } else {
                    // Every worker is active again before any expands a task of
                    // the level, so that a safepoint requested meanwhile is
                    // served by all of them. (The others are waiting here: they
                    // hold no reference into what a safepoint changes.)
                    shared.safepoint.join_all(shared.slots.len());
                }
            }
        });
        if levels.done.load(Ordering::SeqCst) || levels.barrier.is_broken() {
            return;
        }
        if shared.ckpt.as_ref().is_some_and(|c| c.now.load(Ordering::SeqCst)) {
            // A checkpoint between the levels: every worker writes its
            // part, then the last to finish writes the rest and commits
            // before any goes on (all still out of the safepoints).
            w.take_roots();
            w.publish_history();
            barrier_wait(shared, me);
            if levels.barrier.is_broken() {
                return;
            }
            w.checkpoint_part();
            barrier_wait_then(shared, me, || {
                shared.commit_checkpoint();
                shared.safepoint.join_all(shared.slots.len());
            });
            if levels.barrier.is_broken() {
                return;
            }
            w.lease_history();
        }
        w.joined_safepoints();
    }
}

/// `LevelBarrier::wait_then` with no action, timed for the statistics.
fn barrier_wait<M: Model>(shared: &Shared<'_, M>, me: usize) -> bool {
    barrier_wait_then(shared, me, || ())
}

/// `LevelBarrier::wait_then`, timed for the statistics.
fn barrier_wait_then<M: Model>(shared: &Shared<'_, M>, me: usize, action: impl FnOnce()) -> bool {
    let _wait = stats::wait(true);
    shared.levels.barrier.wait_then(me, action)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    /// Every round has exactly one leader, whose action every worker sees
    /// when it returns; some workers arrive late (they sleep), so that the
    /// others park.
    #[test]
    fn barrier_rounds_and_actions() {
        for (n, rounds) in [(1, 100), (2, 2000), (5, 1000), (16, 300)] {
            let b = LevelBarrier::new(n);
            let done = AtomicU64::new(0);
            let leaders = AtomicU64::new(0);
            std::thread::scope(|sc| {
                for me in 0..n {
                    let (b, done, leaders) = (&b, &done, &leaders);
                    sc.spawn(move || {
                        for r in 0..rounds {
                            if (r + me as u64).is_multiple_of(97) {
                                std::thread::sleep(Duration::from_micros(300));
                            }
                            let leader = b.wait_then(me, || {
                                assert_eq!(done.load(Ordering::Relaxed), r);
                                done.store(r + 1, Ordering::Relaxed);
                            });
                            if leader {
                                leaders.fetch_add(1, Ordering::Relaxed);
                            }
                            // (The next round's action only runs once this
                            // worker arrives again.)
                            assert_eq!(done.load(Ordering::Relaxed), r + 1, "worker {me} of {n}, round {r}");
                        }
                    });
                }
            });
            assert_eq!(leaders.load(Ordering::Relaxed), rounds, "{n} workers");
        }
    }

    /// Breaking the barrier releases the workers parked at it, and later
    /// waits return at once.
    #[test]
    fn break_releases_parked_workers() {
        let b = LevelBarrier::new(3);
        std::thread::scope(|sc| {
            let hs: Vec<_> = (0..2)
                .map(|me| {
                    sc.spawn({
                        let b = &b;
                        move || b.wait(me)
                    })
                })
                .collect();
            while b.sleepers.iter().filter(|s| s.parked.load(Ordering::SeqCst)).count() < 2 {
                std::thread::sleep(Duration::from_millis(1));
            }
            b.break_all();
            for h in hs {
                assert!(!h.join().unwrap());
            }
        });
        assert!(!b.wait(2));
        assert!(b.spins.load(Ordering::Relaxed) < LevelBarrier::MAX_SPINS, "parking lowers the spin budget");
    }
}
