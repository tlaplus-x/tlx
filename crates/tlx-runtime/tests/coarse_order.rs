//! A search of several workers with a coarse fingerprint (as under VIEW or
//! SYMMETRY: `Model::coarse_fingerprint`) chooses the representative of
//! every fingerprint class as the single-worker BFS does (the first in BFS
//! order), so that its results are those of one worker.

use tlx_runtime::{explore, explore_resumable, FpConfig, Model, ModelError, Options, Outcome, Report};
use tlx_testkit::report::{project, ComparisonPolicy, Counts, Projection};

type S = (u32, u32, u32, u32);

/// `tests/specs/VR1` (wider): counters `a, b, c` below `n` and a hidden
/// `h` that the fingerprint ignores but the guards read. Expanding a state
/// costs about `spin` iterations of a busy loop, so that levels are
/// expanded in parallel rather than by a single worker.
struct Hidden {
    n: u32,
    spin: u32,
    /// The invariant: the state is not one of these (only representatives
    /// are checked).
    bad: Vec<S>,
    /// Checking the invariant on this state fails (an evaluation error).
    trap: Option<S>,
    inv: Vec<String>,
    acts: Vec<String>,
}

impl Hidden {
    fn new(n: u32, spin: u32) -> Hidden {
        Hidden { n, spin, bad: Vec::new(), trap: None, inv: vec!["Inv".into()], acts: vec!["A".into(), "B".into(), "C".into(), "D".into()] }
    }
}

impl Model for Hidden {
    type State = S;
    tlx_runtime::model_without_checks!(but coarse_fingerprint);
    fn init_states(&self, out: &mut dyn FnMut(S)) -> Result<(), ModelError> {
        out((0, 0, 0, 0));
        out((0, 0, 0, 3));
        out((1, 0, 0, 5));
        out((0, 0, 0, 6));
        Ok(())
    }
    fn successors(&self, s: &S, out: &mut dyn FnMut(S, u32) -> bool) -> Result<(), ModelError> {
        let mut x = 0u64;
        for i in 0..self.spin {
            x = std::hint::black_box(x.wrapping_mul(31).wrapping_add(i as u64));
        }
        let (a, b, c, h) = *s;
        let n = self.n;
        if a < n && h != 4 && !out((a + 1, b, c, (h * 3 + b + 1) % 7), 0) {
            return Ok(());
        }
        if b < n && h != 5 && !out((a, b + 1, c, (h + a + c) % 7), 1) {
            return Ok(());
        }
        if c < n && h < 5 && !out((a, b, c + 1, (h * 2 + a) % 7), 2) {
            return Ok(());
        }
        if h == 6 {
            out(((a + b) % (n + 1), b, c, 0), 3);
        }
        Ok(())
    }
    fn fingerprint(&self, s: &S) -> u64 {
        ((s.0 as u64) << 40 | (s.1 as u64) << 20 | s.2 as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0x1234
    }
    fn coarse_fingerprint(&self) -> bool {
        true
    }
    fn check_invariants(&self, s: &S) -> Result<Option<usize>, ModelError> {
        if Some(*s) == self.trap {
            return Err(ModelError::new("trapped"));
        }
        Ok(self.bad.contains(s).then_some(0))
    }
    fn invariant_names(&self) -> &[String] {
        &self.inv
    }
    fn action_names(&self) -> &[String] {
        &self.acts
    }
    fn render(&self, s: &S) -> String {
        format!("/\\ a = {}\n/\\ b = {}\n/\\ c = {}\n/\\ h = {}", s.0, s.1, s.2, s.3)
    }
}

/// What must not depend on the number of workers.
fn summary(r: &Report<S>) -> Projection<S> {
    project(r, ComparisonPolicy { outdegree: Counts::Always, ..ComparisonPolicy::COUNTS_AND_LENGTH })
}

fn opts(workers: usize) -> Options {
    Options { workers, check_deadlock: false, ..Default::default() }
}

/// The representatives (hence counts and outdegrees) of one worker, with
/// levels expanded in parallel or by one worker, with the fingerprint set
/// growing at safepoints and test safepoints.
#[test]
fn several_workers_choose_bfs_representatives() {
    let m = Hidden::new(14, 3000);
    let one = summary(&explore(&m, &opts(1)));
    assert_eq!(one.outcome, Outcome::Ok);
    let tiny = FpConfig::growing(1 << 20).with_initial(1024);
    for workers in [2, 3, 8] {
        for run in 0..6 {
            let o = Options {
                fp: if run % 2 == 1 { tiny } else { FpConfig::default() },
                safepoint_every: if run % 3 == 2 { 7 } else { 0 },
                ..opts(workers)
            };
            assert_eq!(summary(&explore(&m, &o)), one, "{workers} workers, run {run}");
        }
    }
    // Narrow levels expanded by one worker.
    let fast = Hidden::new(14, 0);
    let one = summary(&explore(&fast, &opts(1)));
    for workers in [2, 8] {
        assert_eq!(summary(&explore(&fast, &opts(workers))), one, "{workers} workers");
    }
}

/// Only the representatives are checked against the invariant: states of
/// their classes found later (in BFS order) that violate it are not
/// reported, whichever worker finds them first.
#[test]
fn invariant_of_representatives_only() {
    let mut m = Hidden::new(14, 3000);
    let r1 = explore(&m, &opts(1));
    // States of the same class (a, b, c) as a representative, with another h.
    let mut probe = Hidden::new(14, 0);
    probe.bad = (0..7).flat_map(|h| [(1, 0, 1, h), (0, 1, 1, h), (1, 1, 1, h), (2, 1, 1, h)]).collect();
    let reps: Vec<S> = probe
        .bad
        .iter()
        .copied()
        .filter(|s| explore(&Hidden { bad: vec![*s], ..Hidden::new(14, 0) }, &opts(1)).outcome != Outcome::Ok)
        .collect();
    assert!(!reps.is_empty());
    m.bad = probe.bad.iter().copied().filter(|s| !reps.contains(s)).collect();
    assert_eq!(summary(&explore(&m, &opts(1))), summary(&r1));
    for workers in [2, 4, 8] {
        for _ in 0..4 {
            assert_eq!(summary(&explore(&m, &opts(workers))), summary(&r1), "{workers} workers");
        }
    }
    // A representative violating it is found.
    m.bad = reps.clone();
    for workers in [1, 4] {
        let r = explore(&m, &opts(workers));
        assert_eq!(r.outcome, Outcome::InvariantViolated("Inv".into()), "{workers} workers");
        assert!(reps.contains(&r.trace.last().unwrap().state));
    }
}

/// The representative of class `(a, b, c)` (with one worker).
fn representative((a, b, c): (u32, u32, u32)) -> S {
    (0..7)
        .map(|h| (a, b, c, h))
        .find(|&s| explore(&Hidden { bad: vec![s], ..Hidden::new(14, 0) }, &opts(1)).outcome != Outcome::Ok)
        .expect("a reachable class")
}

/// A search stopped by an evaluation error while checking the
/// representatives of a level, resumed from its resume point, ends like an
/// uninterrupted one.
#[test]
fn resumed_search_keeps_bfs_representatives() {
    let m = Hidden::new(14, 3000);
    for workers in [3, 8] {
        let want = summary(&explore(&m, &opts(workers)));
        let mut from = None;
        for trap in [(2, 1, 0), (5, 3, 2), (9, 7, 4)].map(representative) {
            let tm = Hidden { trap: Some(trap), ..Hidden::new(14, 3000) };
            let (r, c) = explore_resumable(&tm, &opts(workers), from.take(), Some(usize::MAX));
            let Outcome::Error(e) = &r.outcome else { panic!("trap {trap:?} not reached: {:?}", r.outcome) };
            assert_eq!(e.message, "trapped");
            from = Some(c.expect("resume point").try_map(2, Ok::<_, ()>).unwrap());
        }
        let (r, c) = explore_resumable(&m, &opts(workers), from, None);
        assert!(c.is_none());
        assert_eq!(summary(&r), want, "{workers} workers");
    }
}

/// A fingerprint set too small stops the search (also while offering
/// candidates) with `Outcome::FpSetFull`.
#[test]
fn full_fingerprint_set() {
    let m = Hidden::new(14, 0);
    for workers in [1, 4] {
        let r = explore(&m, &Options { fp: FpConfig::fixed(0), ..opts(workers) });
        assert!(matches!(r.outcome, Outcome::FpSetFull { entries: 922 }), "{:?} with {workers} workers", r.outcome);
    }
}

/// With the fingerprint set rotating to disk (the smallest tables, from the
/// start), the representatives and results do not change: the seen-set
/// insertion under the shard lock asks the disk tier too.
#[test]
fn representatives_with_the_disk_tier() {
    use tlx_runtime::io::{Spill, SpillConfig, SpillMode};
    let disk = |workers: usize, n: u64| Options {
        fp: FpConfig::default().with_disk_slots(1024),
        spill: Spill::new(SpillConfig {
            mode: SpillMode::Always,
            dir: Some(std::env::temp_dir().join(format!("tlx-coarse-disk-{}-{workers}-{n}", std::process::id()))),
            ..Default::default()
        }),
        ..opts(workers)
    };
    let m = Hidden::new(14, 300);
    let one = summary(&explore(&m, &opts(1)));
    assert_eq!(one.outcome, Outcome::Ok);
    assert!(one.counts.as_ref().unwrap().distinct > 4 * 768, "{one:?}");
    for workers in [1, 2, 8] {
        for run in 0..3 {
            assert_eq!(summary(&explore(&m, &disk(workers, run))), one, "{workers} workers, run {run}");
        }
    }
    // A representative violating the invariant, found deep.
    let rep = representative((14, 13, 12));
    let bad = Hidden { bad: vec![rep], ..Hidden::new(14, 300) };
    let r1 = explore(&bad, &opts(1));
    assert_eq!(r1.outcome, Outcome::InvariantViolated("Inv".into()));
    for workers in [1, 8] {
        let r = explore(&bad, &disk(workers, 9));
        // Preserve the failure policy: verdict, shortest length and the chosen representative.
        assert_eq!(r.outcome, r1.outcome, "{workers} workers");
        assert_eq!(r.trace.len(), r1.trace.len(), "{workers} workers");
        assert_eq!(r.trace.last().map(|t| t.state), Some(rep), "{workers} workers");
    }
}

/// The candidates buffered at a level count in the memory budget:
/// under a budget the search exceeds from the start (every pressure stage,
/// the fingerprint set on disk), the representatives and results do not
/// change.
#[test]
fn representatives_under_a_tiny_budget() {
    use tlx_runtime::io::{Spill, SpillConfig};
    let m = Hidden::new(60, 0);
    let one = summary(&explore(&m, &opts(1)));
    assert_eq!(one.outcome, Outcome::Ok);
    for workers in [2, 8] {
        let dir = std::env::temp_dir().join(format!("tlx-coarse-budget-{}-{workers}", std::process::id()));
        let o = Options { maxmem: 1 << 20, spill: Spill::new(SpillConfig { dir: Some(dir), ..Default::default() }), ..opts(workers) };
        assert_eq!(summary(&explore(&m, &o)), one, "{workers} workers");
    }
}

/// Shared coarse-fingerprint test model with controllable spin (to exercise both
/// parallel and solo levels), optional invariant trap (for layout-miss resume),
/// optional panic triggers (inside expansion or inside `resolve_kept`), and
/// optional `StoreGc` (exercising mid-resolve `SP_STORE_GC` and `StoreFull`).
mod resolve_lifecycle {
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

    use tlx_runtime::{
        explore, explore_resumable, Caps, Effects, ErrorKind, GcResult, Model, ModelError, Options, Report, ResumePoint, StoreGc,
    };

    pub(super) type State = (u32, u32, u32);

    pub(super) struct CoarseModel {
        pub(super) max_a: u32,
        pub(super) max_b: u32,
        pub(super) spin: u32,
        pub(super) trap_inv: Option<State>,
        pub(super) panic_on_expand: Option<State>,
        pub(super) panic_on_inv: Option<State>,
        pub(super) gc: Option<MockStoreGc>,
        inv: Vec<String>,
        acts: Vec<String>,
    }

    pub(super) struct MockStoreGc {
        pub(super) collections: AtomicUsize,
        pub(super) marked_states: AtomicUsize,
        pub(super) inv_checks: AtomicUsize,
        pub(super) store_full_fired: AtomicBool,
        pub(super) trigger_store_full_on_inv: bool,
    }

    impl MockStoreGc {
        pub(super) fn new(trigger_store_full_on_inv: bool) -> MockStoreGc {
            MockStoreGc {
                collections: AtomicUsize::new(0),
                marked_states: AtomicUsize::new(0),
                inv_checks: AtomicUsize::new(0),
                store_full_fired: AtomicBool::new(false),
                trigger_store_full_on_inv,
            }
        }
    }

    impl StoreGc<State> for MockStoreGc {
        fn enter_scope(&self) -> Box<dyn std::any::Any + Send + Sync> {
            Box::new(())
        }
        fn needs_gc(&self) -> bool {
            // Trigger proactive SP_STORE_GC periodically during expand & resolve_kept.
            let n = self.inv_checks.load(Ordering::Relaxed);
            n > 0 && n.is_multiple_of(17) && self.collections.load(Ordering::Relaxed) < 8
        }
        fn mark_full(&self) {}
        fn mark_state(&self, s: &State, mark: &mut dyn FnMut(u64)) {
            self.marked_states.fetch_add(1, Ordering::Relaxed);
            mark(((s.0 as u64) << 32) | ((s.1 as u64) << 16) | (s.2 as u64));
        }
        fn mark_words(&self, _words: &[u64], _mark: &mut dyn FnMut(u64)) {}
        fn collect(&self, visit_roots: &mut dyn FnMut(&mut dyn FnMut(u64)) -> Result<(), String>) -> Result<GcResult, String> {
            let mut roots = 0usize;
            visit_roots(&mut |_h| {
                roots += 1;
            })?;
            self.collections.fetch_add(1, Ordering::Relaxed);
            Ok(GcResult { live_bytes: roots * 8, budget: 1 << 20, reclaimed_bytes: 0, full: false })
        }
    }

    impl CoarseModel {
        pub(super) fn new(max_a: u32, max_b: u32, spin: u32) -> CoarseModel {
            CoarseModel {
                max_a,
                max_b,
                spin,
                trap_inv: None,
                panic_on_expand: None,
                panic_on_inv: None,
                gc: None,
                inv: vec!["Inv".into()],
                acts: vec!["A".into(), "B".into(), "H".into()],
            }
        }
    }

    impl Effects for CoarseModel {
        fn interrupts(&self, e: &ModelError) -> bool {
            e.is_layout_miss()
        }
        fn resumes(&self, e: &ModelError) -> bool {
            e.is_layout_miss()
        }
    }

    impl Model for CoarseModel {
        type State = State;
        fn init_states(&self, out: &mut dyn FnMut(State)) -> Result<(), ModelError> {
            out((0, 0, 0));
            out((0, 0, 2));
            out((1, 0, 1));
            Ok(())
        }
        fn successors(&self, s: &State, out: &mut dyn FnMut(State, u32) -> bool) -> Result<(), ModelError> {
            if self.panic_on_expand == Some(*s) {
                panic!("injected expand panic");
            }
            let mut acc = s.0 as u64;
            for i in 0..self.spin {
                acc = std::hint::black_box(acc.wrapping_mul(31).wrapping_add(i as u64));
            }
            let (a, b, h) = *s;
            if a < self.max_a && h != 3 && !out((a + 1, b, (h * 2 + b + 1) % 5), 0) {
                return Ok(());
            }
            if b < self.max_b && h != 4 && !out((a, b + 1, (h + a + 2) % 5), 1) {
                return Ok(());
            }
            if a < self.max_a && b < self.max_b {
                let _ = out((a + 1, b + 1, (h + 1) % 5), 2);
            }
            Ok(())
        }
        fn fingerprint(&self, s: &State) -> u64 {
            // Coarse VIEW fingerprint ignores hidden `h = s.2`.
            ((s.0 as u64) << 32 | s.1 as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0xBEEF
        }
        fn coarse_fingerprint(&self) -> bool {
            true
        }
        fn check_invariants(&self, s: &State) -> Result<Option<usize>, ModelError> {
            if self.panic_on_inv == Some(*s) {
                panic!("injected resolve_kept invariant panic");
            }
            if let Some(gc) = &self.gc {
                gc.inv_checks.fetch_add(1, Ordering::Relaxed);
            }
            if self.trap_inv == Some(*s) {
                return Err(ModelError::of_kind(ErrorKind::LayoutMiss, "layout miss in resolve"));
            }
            Ok(None)
        }
        fn check_invariants_gc(&self, s: &State, collect: &mut dyn FnMut(bool) -> bool) -> Result<Option<usize>, ModelError> {
            if let Some(gc) = &self.gc {
                if gc.trigger_store_full_on_inv
                    && s.0 == self.max_a / 2
                    && s.1 == self.max_b / 2
                    && !gc.store_full_fired.swap(true, Ordering::AcqRel)
                {
                    // Simulate a mid-resolve StoreFull retry that parks for SP_STORE_GC.
                    assert!(collect(false), "mid-resolve store GC collect should continue");
                }
            }
            self.check_invariants(s)
        }
        fn check_init_property(&self, _s: &State) -> Result<Option<String>, ModelError> {
            Ok(None)
        }
        fn constraint(&self, _s: &State) -> Result<bool, ModelError> {
            Ok(true)
        }
        fn action_constraint(&self, _s: &State, _t: &State) -> Result<bool, ModelError> {
            Ok(true)
        }
        fn check_transition(&self, _s: &State, _t: &State) -> Result<Option<usize>, ModelError> {
            Ok(None)
        }
        fn invariant_names(&self) -> &[String] {
            &self.inv
        }
        fn action_names(&self) -> &[String] {
            &self.acts
        }
        fn action_property_names(&self) -> &[String] {
            &[]
        }
        fn extra_generated(&self) -> u64 {
            0
        }
        fn stop_requested(&self) -> bool {
            false
        }
        fn render(&self, s: &State) -> String {
            format!("({},{},{})", s.0, s.1, s.2)
        }
        fn caps(&self) -> Caps<'_, State> {
            Caps {
                format: None,
                live_atoms: None,
                effects: Some(self),
                checkpoint: None,
                gc: self.gc.as_ref().map(|g| g as &dyn StoreGc<State>),
            }
        }
    }

    pub(super) fn model_opts(workers: usize) -> Options {
        Options { workers, check_deadlock: false, ..Default::default() }
    }

    pub(super) fn assert_same_stats(got: &Report<State>, want: &Report<State>, label: &str) {
        assert_eq!(got.outcome, want.outcome, "{label}: outcome");
        assert_eq!(got.stats.distinct, want.stats.distinct, "{label}: distinct");
        assert_eq!(got.stats.generated, want.stats.generated, "{label}: generated");
        assert_eq!(got.stats.depth, want.stats.depth, "{label}: depth");
        assert_eq!(got.stats.outdegree, want.stats.outdegree, "{label}: outdegree");
    }

    pub(super) fn run_explore(m: &CoarseModel, workers: usize) -> Report<State> {
        explore(m, &model_opts(workers))
    }

    pub(super) fn run_resumable(
        m: &CoarseModel,
        workers: usize,
        from: Option<ResumePoint<State>>,
        retain: Option<usize>,
    ) -> (Report<State>, Option<ResumePoint<State>>) {
        explore_resumable(m, &model_opts(workers), from, retain)
    }
}

/// Layout-miss resume inside `resolve_kept()` works across both parallel and
/// solo narrow levels, while non-resumable runs release `Order::current` early
/// and handle errors inside `resolve_kept()` cleanly without panicking.
#[test]
fn multi_worker_view_resolve_resume_and_solo_modes() {
    use resolve_lifecycle::*;
    let plain = CoarseModel::new(10, 10, 0);
    let baseline = run_explore(&plain, 1);
    assert_eq!(baseline.outcome, Outcome::Ok);

    let trap = (0..5u32)
        .map(|h| (4, 4, h))
        .find(|&s| {
            let mut probe = CoarseModel::new(10, 10, 0);
            probe.trap_inv = Some(s);
            matches!(run_explore(&probe, 1).outcome, Outcome::Error(e) if e.is_layout_miss())
        })
        .expect("reachable representative at (4, 4)");

    for spin in [0u32, 2000] {
        let mut trapped = CoarseModel::new(10, 10, spin);
        trapped.trap_inv = Some(trap);

        // 1. Resumable run (`retain = Some`): Order::current stays intact across
        //    resolve_kept so keep_resume builds a valid ResumePoint.
        let (r1, resume) = run_resumable(&trapped, 4, None, Some(usize::MAX));
        assert!(matches!(&r1.outcome, Outcome::Error(e) if e.is_layout_miss()), "spin={spin}: {:?}", r1.outcome);
        let rp = resume.expect("layout miss inside resolve_kept must produce a ResumePoint");

        let resumed_model = CoarseModel::new(10, 10, spin);
        let (r2, none) = run_resumable(&resumed_model, 4, Some(rp), None);
        assert!(none.is_none());
        assert_same_stats(&r2, &baseline, &format!("resumed spin={spin}"));

        // 2. Non-resumable run (`retain = None`): Order::current was released
        //    early after expand_level; error in resolve_kept stops cleanly.
        let (r3, no_resume) = run_resumable(&trapped, 4, None, None);
        assert!(matches!(&r3.outcome, Outcome::Error(e) if e.is_layout_miss()), "spin={spin}: {:?}", r3.outcome);
        assert!(no_resume.is_none());
    }
}

/// Multi-worker ordered search with `StoreGc` handles both proactive
/// `SP_STORE_GC` and `StoreFull` retries (`park_for_store_gc`) inside
/// `resolve_kept()` across the split barriers without deadlocking or losing
/// candidate roots.
#[test]
fn ordered_resolve_mid_resolve_store_gc() {
    use resolve_lifecycle::*;
    use std::sync::atomic::Ordering;
    let plain = CoarseModel::new(10, 10, 0);
    let baseline = run_explore(&plain, 1);
    assert_eq!(baseline.outcome, Outcome::Ok);

    for spin in [0u32, 1500] {
        let mut m = CoarseModel::new(10, 10, spin);
        m.gc = Some(MockStoreGc::new(true));
        let got = run_explore(&m, 4);
        assert_same_stats(&got, &baseline, &format!("store_gc spin={spin}"));
        let gc = m.gc.as_ref().unwrap();
        assert!(gc.store_full_fired.load(Ordering::Acquire), "spin={spin}: StoreFull inside resolve_kept must trigger");
        assert!(gc.collections.load(Ordering::Acquire) > 0, "spin={spin}: SP_STORE_GC must run");
        assert!(gc.marked_states.load(Ordering::Acquire) > 0, "spin={spin}: candidate/frontier roots must be scanned");
    }
}

/// A worker panic during `expand_level` or `resolve_kept()` breaks both
/// resolve barriers (`break_all()`) and unwinds cleanly without deadlocking
/// peer workers (both with and without `StoreGc`).
#[test]
fn ordered_worker_panic_aborts_cleanly_across_resolve_barriers() {
    use resolve_lifecycle::*;
    let target = (0..5u32)
        .map(|h| (3, 3, h))
        .find(|&s| {
            let mut probe = CoarseModel::new(8, 8, 0);
            probe.trap_inv = Some(s);
            matches!(run_explore(&probe, 1).outcome, Outcome::Error(e) if e.is_layout_miss())
        })
        .expect("reachable representative at (3, 3)");

    for with_gc in [false, true] {
        for panic_in_resolve in [false, true] {
            let mut m = CoarseModel::new(8, 8, 1500);
            if with_gc {
                m.gc = Some(MockStoreGc::new(false));
            }
            if panic_in_resolve {
                m.panic_on_inv = Some(target);
            } else {
                m.panic_on_expand = Some(target);
            }
            let res = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run_explore(&m, 4)));
            assert!(res.is_err(), "with_gc={with_gc} panic_in_resolve={panic_in_resolve}: panic must propagate without deadlock");
        }
    }
}

/// A multi-worker ordered `resume_phase` that fails before calling `Order::start`
/// (e.g., `Outcome::FpSetFull` while re-inserting archived states) returns the
/// error cleanly instead of panicking on an unstarted `Order`.
#[test]
fn failed_ordered_resume_returns_error_without_panicking() {
    use resolve_lifecycle::*;

    let trap = (0..5u32)
        .map(|h| (35, 35, h))
        .find(|&s| {
            let mut probe = CoarseModel::new(40, 40, 0);
            probe.trap_inv = Some(s);
            matches!(run_explore(&probe, 1).outcome, Outcome::Error(e) if e.is_layout_miss())
        })
        .expect("reachable representative at (35, 35)");
    let mut trapped = CoarseModel::new(40, 40, 0);
    trapped.trap_inv = Some(trap);
    let (r1, resume) = run_resumable(&trapped, 4, None, Some(usize::MAX));
    assert!(matches!(&r1.outcome, Outcome::Error(e) if e.is_layout_miss()));
    let rp = resume.expect("resume point");
    assert!(rp.len() > 1000, "need > 922 archived states to overflow fixed(0), got {}", rp.len());

    let plain = CoarseModel::new(40, 40, 0);
    let tiny = Options { workers: 4, fp: FpConfig::fixed(0), check_deadlock: false, ..Default::default() };
    let (r2, none) = explore_resumable(&plain, &tiny, Some(rp), None);
    assert!(none.is_none());
    assert!(matches!(r2.outcome, Outcome::FpSetFull { .. }), "expected FpSetFull, got {:?}", r2.outcome);
}
