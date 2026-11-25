//! Adaptive tiering of mixed-mode functions (docs/mixed-mode.md §7).
//!
//! A mixed native function (native code calling host regions) is not
//! always faster than its fallback (the IR executor or the interpreter
//! running the whole action or predicate): the regions may convert large
//! values on every call, or do all the work anyway. Each worker thread
//! therefore times both paths on alternating calls of a function (a
//! *sampling* phase of `2 * SAMPLES` calls), then runs the faster one (the
//! native one only if clearly faster: `MARGIN`) for a while (`RUN_FIRST`
//! calls, growing to `RUN_MAX` while the choice stays the same) before
//! sampling again.
//!
//! Both paths give the same results (the fallback is what runs whenever
//! native code fails), so the choice only affects speed; it is per thread,
//! per function and per run, without synchronization between workers.
//! The time of a call is that of the path chosen, including an interpreter
//! re-run after a failed native call, without the time the explorer spends
//! on the successors (`out`).
//!
//! When the native library changes during the run (the C library replacing
//! the JIT one), the measurements no longer hold: every function of the
//! model samples again at its next call.

use std::cell::RefCell;

mod report;
pub(super) use report::publish as report;

/// Calls of each path timed per sampling phase.
const SAMPLES: u32 = 32;
/// Calls run on the chosen path after a sampling phase: `RUN_FIRST` after
/// the first one or after a change of path, else 4 times the last period,
/// at most `RUN_MAX`.
const RUN_FIRST: u32 = 1024;
const RUN_MAX: u32 = 1 << 16;
/// The native path is chosen if its (trimmed) mean time is at most this
/// fraction of the fallback's: per-call times vary with the states, and a
/// mixed function that is only about as fast is not worth the risk of
/// being slower than the fallback (which runs without mixed mode).
const MARGIN: f64 = 0.95;
/// With memoized region results, a function first runs
/// natively for this many calls before its first sampling phase: cold
/// memo tables make the first native calls slow, and while the fallback
/// runs they stay cold (MCQuicksort's liveness atom: 77% hits once warm,
/// 1% in the first samples).
pub(super) const WARM: u32 = 4096;

/// Kinds of functions (as in `tlx_runtime::stats`): actions, state
/// predicates (`EncModel::invariants`), transition predicates
/// (`EncModel::aprops`).
pub(super) const ACTION: usize = 0;
pub(super) const STATE_PRED: usize = 1;
pub(super) const TRANS_PRED: usize = 2;

/// How to run one call of a mixed function.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Choice {
    /// Run the native (mixed) code; else the fallback.
    pub native: bool,
    /// Time the call and `record` it.
    pub timed: bool,
}

/// The adaptive state of one function on one thread.
#[derive(Clone, Debug)]
struct Tier {
    sampling: bool,
    /// Calls left in the current phase.
    left: u32,
    /// Sampling: the path of the next call; running: the path chosen.
    native: bool,
    /// Sampled call times (ns) by path: [native, fallback].
    samples: [Vec<u32>; 2],
    /// The path chosen after the last sampling phase.
    chosen: Option<bool>,
    /// Length of the last running phase.
    period: u32,
    means: Option<(f64, f64)>,
}

impl Tier {
    fn new() -> Tier {
        Tier { sampling: true, left: 2 * SAMPLES, native: true, samples: [Vec::new(), Vec::new()], chosen: None, period: 0, means: None }
    }

    /// A tier that first runs natively for `warm` calls (0: samples at
    /// once).
    fn warming(warm: u32) -> Tier {
        if warm == 0 {
            return Tier::new();
        }
        Tier { sampling: false, left: warm, ..Tier::new() }
    }

    fn choose(&mut self) -> Choice {
        if self.sampling {
            return Choice { native: self.native, timed: true };
        }
        let native = self.native;
        self.left -= 1;
        if self.left == 0 {
            self.sampling = true;
            self.left = 2 * SAMPLES;
            self.native = true;
        }
        Choice { native, timed: false }
    }

    /// A sampled call by path `native` took `ns`; Some(choice) when the
    /// sampling phase ends with it.
    fn record(&mut self, native: bool, ns: u64) -> Option<bool> {
        if !self.sampling {
            return None;
        }
        self.samples[(!native) as usize].push(ns.min(u32::MAX as u64) as u32);
        self.native = !native;
        self.left -= 1;
        if self.left > 0 {
            return None;
        }
        let (n, f) = (trimmed_mean(&mut self.samples[0]), trimmed_mean(&mut self.samples[1]));
        self.native = n <= MARGIN * f;
        if tlx_runtime::stats::on() {
            self.means = Some((n, f));
        }
        self.samples.iter_mut().for_each(Vec::clear);
        self.period = if self.chosen == Some(self.native) { (self.period * 4).min(RUN_MAX) } else { RUN_FIRST };
        self.chosen = Some(self.native);
        self.sampling = false;
        self.left = self.period;
        Some(self.native)
    }
}

/// The mean of `xs` without its largest eighth (preempted calls on a
/// loaded machine); infinite if empty.
fn trimmed_mean(xs: &mut [u32]) -> f64 {
    if xs.is_empty() {
        return f64::INFINITY;
    }
    xs.sort_unstable();
    let keep = &xs[..xs.len() - xs.len() / 8];
    keep.iter().map(|&x| x as f64).sum::<f64>() / keep.len() as f64
}

/// The tiers of this thread for the functions of one model and library.
struct Tiers {
    model: u64,
    lib: usize,
    fns: [Vec<Tier>; 3],
}

thread_local! {
    static TIERS: RefCell<Tiers> = const { RefCell::new(Tiers { model: 0, lib: 0, fns: [Vec::new(), Vec::new(), Vec::new()] }) };
}

fn with_tier<R>(model: u64, lib: usize, kind: usize, i: usize, warm: u32, f: impl FnOnce(&mut Tier) -> R) -> R {
    TIERS.with(|t| {
        let mut t = t.borrow_mut();
        if t.model != model {
            t.model = model;
            t.lib = lib;
            t.fns.iter_mut().for_each(Vec::clear);
        } else if t.lib != lib {
            // A new library: sample again now (warm memo tables stay warm).
            t.lib = lib;
            t.fns.iter_mut().flatten().for_each(|x| *x = Tier::new());
        }
        let v = &mut t.fns[kind];
        if v.len() <= i {
            v.resize(i + 1, Tier::warming(warm));
        }
        f(&mut v[i])
    })
}

/// How to run the next call of mixed function `i` of `kind` of model
/// `model` with native library `lib` (an identity) on this thread.
/// `warm`: a new tier first runs natively for this many calls (see
/// `WARM`).
pub(super) fn choose(model: u64, lib: usize, kind: usize, i: usize, warm: u32) -> Choice {
    with_tier(model, lib, kind, i, warm, |t| {
        let choice = t.choose();
        if tlx_runtime::stats::on() {
            report::observe((model, lib, kind, i), t, None);
        }
        choice
    })
}

/// A timed call (see `Choice::timed`) by path `native` took `ns`
/// nanoseconds. Returns the path chosen if this ended a sampling phase.
pub(super) fn record(model: u64, lib: usize, kind: usize, i: usize, native: bool, ns: u64) -> Option<bool> {
    with_tier(model, lib, kind, i, 0, |t| {
        let chosen = t.record(native, ns);
        if tlx_runtime::stats::on() {
            report::observe((model, lib, kind, i), t, Some((native, ns, chosen)));
        }
        chosen
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn telemetry_preserves_samples_and_library_decisions() {
        tlx_runtime::stats::enable(1);
        let model = (1 << 40) + 19;
        for _ in 0..2 * SAMPLES {
            let c = choose(model, 1, ACTION, 0, 0);
            record(model, 1, ACTION, 0, c.native, if c.native { 300 } else { 100 });
        }
        report(model, ACTION, 0, "telemetry-test");
        let json = tlx_runtime::stats::json();
        assert!(json.contains("\"chosen\":\"fallback\""));
        assert!(json.contains("\"sample_calls\":{\"mixed_native\":32,\"fallback\":32}"));
        assert!(json.contains("\"sample_ns\":{\"mixed_native\":9600,\"fallback\":3200}"));
        choose(model, 2, ACTION, 0, 0);
        report(model, ACTION, 0, "telemetry-test");
        let json = tlx_runtime::stats::json();
        assert_eq!(json.matches("\"name\":\"telemetry-test\"").count(), 2);
        assert!(tlx_runtime::stats::text().contains("chosen fallback; samples mixed_native=32"));
    }

    /// Run `n` calls where native calls take `nat` ns and fallback calls
    /// `fb` ns; returns the number of native calls.
    fn run(t: &mut Tier, n: u32, nat: u64, fb: u64) -> u32 {
        let mut natives = 0;
        for _ in 0..n {
            let c = t.choose();
            natives += c.native as u32;
            if c.timed {
                t.record(c.native, if c.native { nat } else { fb });
            }
        }
        natives
    }

    #[test]
    fn samples_both_then_runs_the_faster() {
        let mut t = Tier::new();
        // Sampling: alternating paths.
        assert_eq!(run(&mut t, 2 * SAMPLES, 100, 300), SAMPLES);
        assert!(!t.sampling && t.native && t.left == RUN_FIRST);
        // Running: only the faster path, untimed.
        assert_eq!(run(&mut t, RUN_FIRST, 100, 300), RUN_FIRST);
        // The same choice again: a longer period.
        assert!(t.sampling);
        run(&mut t, 2 * SAMPLES, 100, 300);
        assert!(t.native && t.left == RUN_FIRST * 4);
        run(&mut t, RUN_FIRST * 4, 100, 300);
        // Then the fallback became faster: a short period again.
        run(&mut t, 2 * SAMPLES, 500, 300);
        assert!(!t.sampling && !t.native && t.left == RUN_FIRST);
        assert_eq!(run(&mut t, RUN_FIRST, 500, 300), 0);
        assert!(t.sampling);
    }

    #[test]
    fn about_as_fast_keeps_the_fallback() {
        let mut t = Tier::new();
        run(&mut t, 2 * SAMPLES, 98, 100);
        assert!(!t.native);
        let mut t = Tier::new();
        run(&mut t, 2 * SAMPLES, 90, 100);
        assert!(t.native);
    }

    #[test]
    fn outliers_are_trimmed() {
        let mut xs: Vec<u32> = (0..32).map(|i| if i % 8 == 0 { 1_000_000 } else { 100 }).collect();
        assert_eq!(trimmed_mean(&mut xs), 100.0);
        assert_eq!(trimmed_mean(&mut []), f64::INFINITY);
    }

    #[test]
    fn period_is_bounded() {
        let mut t = Tier::new();
        for _ in 0..12 {
            run(&mut t, 2 * SAMPLES, 100, 300);
            let p = t.left;
            assert!(p <= RUN_MAX);
            run(&mut t, p, 100, 300);
        }
        assert_eq!(t.period, RUN_MAX);
    }

    #[test]
    fn tiers_are_per_model_and_function() {
        let (m, l) = (1 << 40, 1);
        assert_eq!(choose(m, l, ACTION, 3, 0), Choice { native: true, timed: true });
        assert_eq!(record(m, l, ACTION, 3, true, 10), None);
        // The next call samples the fallback; another function starts over.
        assert_eq!(choose(m, l, ACTION, 3, 0), Choice { native: false, timed: true });
        assert_eq!(choose(m, l, STATE_PRED, 3, 0), Choice { native: true, timed: true });
        // Another model resets this thread's tiers; a warming tier runs
        // natively first.
        assert_eq!(choose(m + 1, l, ACTION, 3, 2), Choice { native: true, timed: false });
        assert_eq!(choose(m + 1, l, ACTION, 3, 2), Choice { native: true, timed: false });
        assert_eq!(choose(m + 1, l, ACTION, 3, 2), Choice { native: true, timed: true });
        let _ = TRANS_PRED;
    }

    /// A function that chose its fallback samples again as soon as the
    /// library changes, not after its running period.
    #[test]
    fn a_new_library_samples_again() {
        let (m, l) = ((1 << 40) + 7, 1);
        let mut calls = 0;
        // Sample until the (faster) fallback is chosen.
        loop {
            let c = choose(m, l, TRANS_PRED, 0, 0);
            calls += 1;
            if !c.timed {
                assert!(!c.native);
                break;
            }
            record(m, l, TRANS_PRED, 0, c.native, if c.native { 300 } else { 100 });
            assert!(calls <= 2 * SAMPLES + 1);
        }
        assert_eq!(choose(m, l, TRANS_PRED, 0, 0), Choice { native: false, timed: false });
        // The C library replaces the JIT one: sampling starts at once.
        assert_eq!(choose(m, l + 1, TRANS_PRED, 0, 0), Choice { native: true, timed: true });
        assert_eq!(record(m, l + 1, TRANS_PRED, 0, true, 50), None);
        assert_eq!(choose(m, l + 1, TRANS_PRED, 0, 0), Choice { native: false, timed: true });
    }
}
