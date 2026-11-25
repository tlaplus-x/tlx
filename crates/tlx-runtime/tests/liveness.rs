//! Liveness checking after the search (`tlx_runtime::liveness`) on a toy
//! model, on the graph recorded during the search and TLC's way (as under
//! VIEW or SYMMETRY); and `admits`, the successor "in the model".

use std::cell::Cell;
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicUsize, Ordering};
use std::sync::Mutex;

use tlx_live::{Fairness, Ltl};
use tlx_runtime::liveness::{self, LiveInput, LiveResult};
use tlx_runtime::mem::RssGuard;
use tlx_runtime::{admits, explore, AtomBits, Caps, ErrorKind, GcResult, Model, ModelError, Options, Outcome, StoreGc};

struct TrackingAlloc;

thread_local! {
    static THREAD_ALLOC_BYTES: Cell<Option<usize>> = const { Cell::new(None) };
}

static WATCH_LOCK: Mutex<()> = Mutex::new(());
static WATCH_TGT: AtomicUsize = AtomicUsize::new(0);
static WATCH_FPS: AtomicUsize = AtomicUsize::new(0);
static FREED_TGT: AtomicBool = AtomicBool::new(false);
static FREED_FPS: AtomicBool = AtomicBool::new(false);

#[global_allocator]
static ALLOC: TrackingAlloc = TrackingAlloc;

fn count_alloc(bytes: usize) {
    let _ = THREAD_ALLOC_BYTES.try_with(|n| {
        if let Some(cur) = n.get() {
            n.set(Some(cur.saturating_add(bytes)));
        }
    });
}

// SAFETY: all operations delegate directly to `std::alloc::System` with the
// caller's original pointer and layout arguments.
unsafe impl std::alloc::GlobalAlloc for TrackingAlloc {
    unsafe fn alloc(&self, layout: std::alloc::Layout) -> *mut u8 {
        count_alloc(layout.size());
        // SAFETY: the caller supplied a valid allocation layout.
        unsafe { std::alloc::System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: std::alloc::Layout) {
        let addr = ptr as usize;
        if addr != 0 {
            if addr == WATCH_TGT.load(Ordering::Relaxed) {
                FREED_TGT.store(true, Ordering::Release);
            }
            if addr == WATCH_FPS.load(Ordering::Relaxed) {
                FREED_FPS.store(true, Ordering::Release);
            }
        }
        // SAFETY: the caller supplied a live allocation with this layout.
        unsafe { std::alloc::System.dealloc(ptr, layout) }
    }

    unsafe fn alloc_zeroed(&self, layout: std::alloc::Layout) -> *mut u8 {
        count_alloc(layout.size());
        // SAFETY: the caller supplied a valid allocation layout.
        unsafe { std::alloc::System.alloc_zeroed(layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: std::alloc::Layout, new_size: usize) -> *mut u8 {
        count_alloc(new_size);
        // SAFETY: the caller supplied a live allocation and a valid new size.
        unsafe { std::alloc::System.realloc(ptr, layout, new_size) }
    }
}

fn measure_thread_alloc_bytes<T>(f: impl FnOnce() -> T) -> (T, usize) {
    THREAD_ALLOC_BYTES.with(|n| n.set(Some(0)));
    let res = f();
    let bytes = THREAD_ALLOC_BYTES.with(|n| n.replace(None).unwrap_or(0));
    (res, bytes)
}

/// A ring `0..n`: the step `x -> x + 1 (mod n)`, action 0.
struct Ring {
    n: u32,
    inv: Vec<String>,
    acts: Vec<String>,
}

impl Ring {
    fn new(n: u32) -> Ring {
        Ring { n, inv: Vec::new(), acts: vec!["Next".into()] }
    }
}

impl Model for Ring {
    type State = u32;
    tlx_runtime::model_without_checks!();
    fn init_states(&self, out: &mut dyn FnMut(u32)) -> Result<(), ModelError> {
        out(0);
        Ok(())
    }
    fn successors(&self, s: &u32, out: &mut dyn FnMut(u32, u32) -> bool) -> Result<(), ModelError> {
        out((s + 1) % self.n, 0);
        Ok(())
    }
    fn fingerprint(&self, s: &u32) -> u64 {
        (*s as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15)
    }
    fn check_invariants(&self, _s: &u32) -> Result<Option<usize>, ModelError> {
        Ok(None)
    }
    fn invariant_names(&self) -> &[String] {
        &self.inv
    }
    fn action_names(&self) -> &[String] {
        &self.acts
    }
    fn render(&self, s: &u32) -> String {
        format!("/\\ x = {s}")
    }
    fn caps(&self) -> Caps<'_, u32> {
        Caps { format: None, live_atoms: Some(self), effects: None, checkpoint: None, gc: None }
    }
}

/// State atom 0: `x = 0`; 1: some step changes `x` (ENABLED, from the
/// steps); action atom 0: the step changes `x`.
impl AtomBits<u32> for Ring {
    fn state(&self, s: &u32, out: &[&[u64]]) -> Result<Vec<u64>, ModelError> {
        let enabled = out.iter().any(|b| b[0] & 1 == 1);
        Ok(vec![u64::from(*s == 0) | u64::from(enabled) << 1])
    }
    fn action(&self, s: &u32, t: &u32) -> Result<Vec<u64>, ModelError> {
        Ok(vec![u64::from(s != t)])
    }
}

/// `[]<>(x = 0)`, named P.
fn infinitely_often_zero() -> Vec<(String, Ltl)> {
    vec![("P".to_string(), Ltl::Always(Box::new(Ltl::Eventually(Box::new(Ltl::State(0))))))]
}

/// Check `props` on the ring of 3 under `fairness`, on the recorded graph
/// or TLC's way (`concrete`).
fn check(props: &[(String, Ltl)], fairness: Vec<Fairness>, concrete: bool) -> LiveResult<u32> {
    let m = Ring::new(3);
    let alone: Vec<Ltl> = props.iter().map(|(_, f)| f.clone()).collect();
    let input = LiveInput { props, alone: &alone, fairness, concrete };
    let r = explore(&m, &Options { workers: 1, check_deadlock: false, ..Default::default() });
    assert_eq!(r.outcome, Outcome::Ok);
    let recorded = (!concrete).then(|| r.live_graph.expect("a recorded graph"));
    liveness::check(&m, &input, &m, 2, usize::MAX, recorded, RssGuard::new(usize::MAX, 0))
}

#[test]
fn without_fairness_a_stuttering_counterexample() {
    for concrete in [false, true] {
        let LiveResult::Violated(v) = check(&infinitely_often_zero(), Vec::new(), concrete) else {
            panic!("a violation (concrete: {concrete})")
        };
        assert_eq!(v.names, ["P"], "concrete: {concrete}");
        assert_eq!(v.prop, 0);
        // From the initial state 0 to 1, where the behavior stutters.
        let states = &v.lasso.states;
        assert!(v.lasso.stuttering(), "concrete: {concrete}");
        assert_eq!(states[0], (0, None));
        assert!(states[1..].iter().all(|&(s, a)| s != 0 && a == Some(0)), "concrete: {concrete}");
    }
}

#[test]
fn weak_fairness_of_the_step_rules_out_stuttering() {
    for concrete in [false, true] {
        let wf = vec![Fairness { strong: false, enabled: 1, taken: 0 }];
        assert!(matches!(check(&infinitely_often_zero(), wf, concrete), LiveResult::Holds), "concrete: {concrete}");
    }
}

#[test]
fn a_property_that_holds_is_not_named() {
    // `<>(x = 0)` holds at once; P is violated as above: only P is named.
    let props = vec![("Q".to_string(), Ltl::Eventually(Box::new(Ltl::State(0)))), infinitely_often_zero().remove(0)];
    for concrete in [false, true] {
        let LiveResult::Violated(v) = check(&props, Vec::new(), concrete) else { panic!("a violation (concrete: {concrete})") };
        assert_eq!(v.names, ["P"], "concrete: {concrete}");
        assert_eq!(v.prop, 1);
    }
}

#[test]
fn input_lists_the_tableau_atoms_once() {
    let props = vec![infinitely_often_zero().remove(0), ("P2".to_string(), Ltl::Eventually(Box::new(Ltl::State(0))))];
    let alone: Vec<Ltl> = props.iter().map(|(_, f)| f.clone()).collect();
    let input = LiveInput { props: &props, alone: &alone, fairness: Vec::new(), concrete: false };
    let atoms = input.tableau_atoms();
    let mut unique = atoms.clone();
    unique.dedup();
    assert_eq!(atoms, unique);
}

/// A model whose CONSTRAINT and ACTION_CONSTRAINT fail or hold as told,
/// counting how often the ACTION_CONSTRAINT is evaluated.
struct Constrained {
    constraint: Result<bool, ()>,
    action: Result<bool, ()>,
    actions_evaluated: AtomicU32,
    names: Vec<String>,
}

impl Model for Constrained {
    type State = u32;
    fn init_states(&self, _out: &mut dyn FnMut(u32)) -> Result<(), ModelError> {
        Ok(())
    }
    fn successors(&self, _s: &u32, _out: &mut dyn FnMut(u32, u32) -> bool) -> Result<(), ModelError> {
        Ok(())
    }
    fn fingerprint(&self, s: &u32) -> u64 {
        *s as u64
    }
    fn coarse_fingerprint(&self) -> bool {
        false
    }
    fn check_invariants(&self, _s: &u32) -> Result<Option<usize>, ModelError> {
        Ok(None)
    }
    fn check_init_property(&self, _s: &u32) -> Result<Option<String>, ModelError> {
        Ok(None)
    }
    fn constraint(&self, _s: &u32) -> Result<bool, ModelError> {
        self.constraint.map_err(|()| ModelError::new("constraint"))
    }
    fn action_constraint(&self, _s: &u32, _t: &u32) -> Result<bool, ModelError> {
        self.actions_evaluated.fetch_add(1, Ordering::Relaxed);
        self.action.map_err(|()| ModelError::new("action constraint"))
    }
    fn check_transition(&self, _s: &u32, _t: &u32) -> Result<Option<usize>, ModelError> {
        Ok(None)
    }
    fn action_property_names(&self) -> &[String] {
        &self.names
    }
    fn extra_generated(&self) -> u64 {
        0
    }
    fn stop_requested(&self) -> bool {
        false
    }
    fn invariant_names(&self) -> &[String] {
        &self.names
    }
    fn action_names(&self) -> &[String] {
        &self.names
    }
    fn render(&self, s: &u32) -> String {
        s.to_string()
    }
}

#[test]
fn admits_is_constraint_then_action_constraint() {
    let m = |constraint, action| Constrained { constraint, action, actions_evaluated: AtomicU32::new(0), names: Vec::new() };
    let r = |m: &Constrained| admits(m, &0, &1).map_err(|e| e.message);
    let both = m(Ok(true), Ok(true));
    assert_eq!(r(&both), Ok(true));
    let action_false = m(Ok(true), Ok(false));
    assert_eq!(r(&action_false), Ok(false));
    let action_err = m(Ok(true), Err(()));
    assert_eq!(r(&action_err), Err("action constraint".to_string()));
    // The ACTION_CONSTRAINT only if the CONSTRAINT holds.
    let out = m(Ok(false), Err(()));
    assert_eq!(r(&out), Ok(false));
    assert_eq!(out.actions_evaluated.load(Ordering::Relaxed), 0);
    let err = m(Err(()), Ok(true));
    assert_eq!(r(&err), Err("constraint".to_string()));
    assert_eq!(err.actions_evaluated.load(Ordering::Relaxed), 0);
}

struct WideRing {
    n: u32,
    words: usize,
    replaying: AtomicBool,
    saw_tgt_freed: AtomicBool,
    saw_fps_freed: AtomicBool,
    inv: Vec<String>,
    acts: Vec<String>,
}

impl Model for WideRing {
    type State = u32;
    tlx_runtime::model_without_checks!();
    fn init_states(&self, out: &mut dyn FnMut(u32)) -> Result<(), ModelError> {
        if self.replaying.load(Ordering::Relaxed) {
            self.saw_tgt_freed.store(FREED_TGT.load(Ordering::Acquire), Ordering::Relaxed);
            self.saw_fps_freed.store(FREED_FPS.load(Ordering::Acquire), Ordering::Relaxed);
        }
        out(0);
        Ok(())
    }
    fn successors(&self, s: &u32, out: &mut dyn FnMut(u32, u32) -> bool) -> Result<(), ModelError> {
        out((s + 1) % self.n, 0);
        Ok(())
    }
    fn fingerprint(&self, s: &u32) -> u64 {
        (*s as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15)
    }
    fn check_invariants(&self, _s: &u32) -> Result<Option<usize>, ModelError> {
        Ok(None)
    }
    fn invariant_names(&self) -> &[String] {
        &self.inv
    }
    fn action_names(&self) -> &[String] {
        &self.acts
    }
    fn render(&self, s: &u32) -> String {
        format!("/\\ x = {s}")
    }
    fn caps(&self) -> Caps<'_, u32> {
        Caps { format: None, live_atoms: Some(self), effects: None, checkpoint: None, gc: None }
    }
}

impl AtomBits<u32> for WideRing {
    fn state(&self, _s: &u32, out: &[&[u64]]) -> Result<Vec<u64>, ModelError> {
        let enabled = out.iter().any(|b| b[0] & 1 == 1);
        let mut v = vec![0x5555_AAAA_5555_AAAAu64; self.words];
        v[0] = u64::from(enabled) << 1;
        v[self.words - 1] = 0;
        Ok(v)
    }
    fn action(&self, s: &u32, t: &u32) -> Result<Vec<u64>, ModelError> {
        let mut v = vec![0xAAAA_5555_AAAA_5555u64; self.words];
        v[0] = u64::from(s != t);
        Ok(v)
    }
}

#[test]
fn long_lasso_keeps_pattern_ids_without_cloning_multiword_patterns() {
    // 20,000-state fair cycle with shared 8 KiB state and action patterns:
    // cloning both patterns per lasso step and again in `violated_names` would
    // allocate ~640 MiB, whereas indexing the interned dictionaries by pattern
    // id keeps total heap allocations during liveness checking small regardless
    // of OS page-return or allocator caching behavior.
    let m = WideRing {
        n: 20_000,
        words: 1_024,
        replaying: AtomicBool::new(false),
        saw_tgt_freed: AtomicBool::new(false),
        saw_fps_freed: AtomicBool::new(false),
        inv: Vec::new(),
        acts: vec!["Next".into()],
    };
    let last_bit = (m.words * 64 - 1) as u32;
    let props = vec![("NeverLast".to_string(), Ltl::Always(Box::new(Ltl::Eventually(Box::new(Ltl::State(last_bit))))))];
    let alone: Vec<Ltl> = props.iter().map(|(_, f)| f.clone()).collect();
    let wf = vec![Fairness { strong: false, enabled: 1, taken: 0 }];
    let input = LiveInput { props: &props, alone: &alone, fairness: wf, concrete: false };

    let r = explore(&m, &Options { workers: 1, check_deadlock: false, ..Default::default() });
    assert_eq!(r.outcome, Outcome::Ok);
    let recorded = r.live_graph.expect("recorded graph");
    let g_ref = recorded.as_ref().expect("built");
    assert_eq!(g_ref.state_pats.len(), 1);
    assert_eq!(g_ref.action_pats.len(), 2);

    let (res, alloc_bytes) =
        measure_thread_alloc_bytes(|| liveness::check(&m, &input, &m, 1, usize::MAX, Some(recorded), RssGuard::new(usize::MAX, 0)));
    let LiveResult::Violated(v) = res else { panic!("expected fair-cycle violation") };
    assert_eq!(v.names, ["NeverLast"]);
    assert_eq!(v.lasso.states.len(), m.n as usize);
    assert!(alloc_bytes < 32 << 20, "multiword patterns cloned during replay/naming: allocated {alloc_bytes} bytes");
}

#[test]
fn csr_topology_is_released_before_replay() {
    let _guard = WATCH_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    struct ClearWatch;
    impl Drop for ClearWatch {
        fn drop(&mut self) {
            WATCH_TGT.store(0, Ordering::Relaxed);
            WATCH_FPS.store(0, Ordering::Relaxed);
        }
    }
    let _clear = ClearWatch;

    let m = WideRing {
        n: 3,
        words: 1,
        replaying: AtomicBool::new(false),
        saw_tgt_freed: AtomicBool::new(false),
        saw_fps_freed: AtomicBool::new(false),
        inv: Vec::new(),
        acts: vec!["Next".into()],
    };
    let props = infinitely_often_zero();
    let alone: Vec<Ltl> = props.iter().map(|(_, f)| f.clone()).collect();
    let input = LiveInput { props: &props, alone: &alone, fairness: Vec::new(), concrete: false };

    let r = explore(&m, &Options { workers: 1, check_deadlock: false, ..Default::default() });
    assert_eq!(r.outcome, Outcome::Ok);
    let g = r.live_graph.expect("recorded graph").expect("built");
    assert!(!g.tgt.is_empty() && !g.fps.is_empty());

    FREED_TGT.store(false, Ordering::Relaxed);
    FREED_FPS.store(false, Ordering::Relaxed);
    WATCH_TGT.store(g.tgt.as_ptr() as usize, Ordering::Relaxed);
    WATCH_FPS.store(g.fps.as_ptr() as usize, Ordering::Relaxed);

    m.replaying.store(true, Ordering::Relaxed);
    let res = liveness::check(&m, &input, &m, 1, usize::MAX, Some(Ok(g)), RssGuard::new(usize::MAX, 0));
    assert!(matches!(res, LiveResult::Violated(_)));
    assert!(m.saw_tgt_freed.load(Ordering::Relaxed), "CSR `tgt` buffer was still allocated at replay entry");
    assert!(m.saw_fps_freed.load(Ordering::Relaxed), "fingerprint vector `fps` was still allocated at replay entry");
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ReplayFailAt {
    None,
    InitConstraint,
    SuccAdmits,
    SuccEmit,
}

/// Toy model with a `StoreGc` capability where state `0` branches to `1`
/// (ordinal 0) and `2` (ordinal 1), so exhausting the store during recorded
/// counterexample replay exercises both `constraint_gc` and `admits_gc`
/// (including the ordinal-shift hazard when successor 0 fails before edge 1).
struct ReplayFullModel {
    fail_at: std::sync::atomic::AtomicU8,
    marked_full: AtomicBool,
    admits_seen: AtomicU32,
    inv: Vec<String>,
    acts: Vec<String>,
}

impl ReplayFullModel {
    fn new() -> Self {
        Self {
            fail_at: std::sync::atomic::AtomicU8::new(ReplayFailAt::None as u8),
            marked_full: AtomicBool::new(false),
            admits_seen: AtomicU32::new(0),
            inv: Vec::new(),
            acts: vec!["Next".into()],
        }
    }

    fn mode(&self) -> ReplayFailAt {
        match self.fail_at.load(Ordering::Relaxed) {
            1 => ReplayFailAt::InitConstraint,
            2 => ReplayFailAt::SuccAdmits,
            3 => ReplayFailAt::SuccEmit,
            _ => ReplayFailAt::None,
        }
    }

    fn set_mode(&self, m: ReplayFailAt) {
        self.fail_at.store(m as u8, Ordering::Relaxed);
        self.marked_full.store(false, Ordering::Relaxed);
        self.admits_seen.store(0, Ordering::Relaxed);
    }

    fn store_full() -> ModelError {
        ModelError::of_kind(ErrorKind::StoreFull, "value store budget exhausted during replay")
    }
}

impl StoreGc<u32> for ReplayFullModel {
    fn enter_scope(&self) -> Box<dyn std::any::Any + Send + Sync> {
        Box::new(())
    }
    fn needs_gc(&self) -> bool {
        false
    }
    fn mark_full(&self) {
        self.marked_full.store(true, Ordering::Relaxed);
    }
    fn mark_state(&self, _s: &u32, _mark: &mut dyn FnMut(u64)) {}
    fn mark_words(&self, _words: &[u64], _mark: &mut dyn FnMut(u64)) {}
    fn collect(&self, visit_roots: &mut dyn FnMut(&mut dyn FnMut(u64)) -> Result<(), String>) -> Result<GcResult, String> {
        visit_roots(&mut |_| {})?;
        Ok(GcResult::default())
    }
}

impl Model for ReplayFullModel {
    type State = u32;
    fn coarse_fingerprint(&self) -> bool {
        false
    }
    fn check_init_property(&self, _s: &u32) -> Result<Option<String>, ModelError> {
        Ok(None)
    }
    fn constraint(&self, _s: &u32) -> Result<bool, ModelError> {
        Ok(true)
    }
    fn constraint_gc(&self, s: &u32, _collect: &mut dyn FnMut(bool) -> bool) -> Result<bool, ModelError> {
        if self.mode() == ReplayFailAt::InitConstraint && *s == 0 {
            return Err(Self::store_full());
        }
        Ok(true)
    }
    fn action_constraint(&self, _s: &u32, _t: &u32) -> Result<bool, ModelError> {
        Ok(true)
    }
    fn action_constraint_gc(&self, s: &u32, t: &u32, _collect: &mut dyn FnMut(bool) -> bool) -> Result<bool, ModelError> {
        if self.mode() == ReplayFailAt::SuccAdmits && *s == 0 {
            self.admits_seen.fetch_add(1, Ordering::Relaxed);
            if *t == 1 {
                return Err(Self::store_full());
            }
        }
        Ok(true)
    }
    fn check_transition(&self, _s: &u32, _t: &u32) -> Result<Option<usize>, ModelError> {
        Ok(None)
    }
    fn action_property_names(&self) -> &[String] {
        &self.inv
    }
    fn extra_generated(&self) -> u64 {
        0
    }
    fn stop_requested(&self) -> bool {
        false
    }
    fn init_states(&self, out: &mut dyn FnMut(u32)) -> Result<(), ModelError> {
        out(0);
        Ok(())
    }
    fn successors(&self, s: &u32, out: &mut dyn FnMut(u32, u32) -> bool) -> Result<(), ModelError> {
        if self.mode() == ReplayFailAt::SuccEmit && *s == 0 {
            return Err(Self::store_full());
        }
        match *s {
            // Ordinal 0 -> state 1 (returns to 0); ordinal 1 -> state 2 (loops on 2, violating []<>(x = 0)).
            0 => {
                if out(1, 0) {
                    let _ = out(2, 0);
                }
            }
            1 => {
                let _ = out(0, 0);
            }
            _ => {
                let _ = out(2, 0);
            }
        }
        Ok(())
    }
    fn fingerprint(&self, s: &u32) -> u64 {
        (*s as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15)
    }
    fn check_invariants(&self, _s: &u32) -> Result<Option<usize>, ModelError> {
        Ok(None)
    }
    fn invariant_names(&self) -> &[String] {
        &self.inv
    }
    fn action_names(&self) -> &[String] {
        &self.acts
    }
    fn render(&self, s: &u32) -> String {
        format!("/\\ x = {s}")
    }
    fn caps(&self) -> Caps<'_, u32> {
        Caps { format: None, live_atoms: Some(self), effects: None, checkpoint: None, gc: Some(self) }
    }
}

impl AtomBits<u32> for ReplayFullModel {
    fn state(&self, s: &u32, _out: &[&[u64]]) -> Result<Vec<u64>, ModelError> {
        Ok(vec![u64::from(*s == 0)])
    }
    fn action(&self, s: &u32, t: &u32) -> Result<Vec<u64>, ModelError> {
        Ok(vec![u64::from(s != t)])
    }
}

#[test]
fn recorded_replay_propagates_store_full_errors() {
    let m = ReplayFullModel::new();
    let props = infinitely_often_zero();
    let alone: Vec<Ltl> = props.iter().map(|(_, f)| f.clone()).collect();
    let input = LiveInput { props: &props, alone: &alone, fairness: Vec::new(), concrete: false };

    let run = |mode: ReplayFailAt| -> LiveResult<u32> {
        m.set_mode(ReplayFailAt::None);
        let r = explore(&m, &Options { workers: 1, check_deadlock: false, ..Default::default() });
        assert_eq!(r.outcome, Outcome::Ok);
        let recorded = r.live_graph.expect("recorded graph");
        m.set_mode(mode);
        liveness::check(&m, &input, &m, 1, usize::MAX, Some(recorded), RssGuard::new(usize::MAX, 0))
    };

    // Baseline: counterexample replays cleanly when the store has budget.
    assert!(matches!(run(ReplayFailAt::None), LiveResult::Violated(_)));

    // Exhaustion in initial-state constraint_gc propagates StoreFull (not "cannot be replayed").
    match run(ReplayFailAt::InitConstraint) {
        LiveResult::Error(e) => assert!(e.is_store_full(), "expected StoreFull, got: {e}"),
        LiveResult::Holds => panic!("expected StoreFull on init constraint, got Holds"),
        LiveResult::Violated(_) => panic!("expected StoreFull on init constraint, got Violated"),
        LiveResult::OutOfMemory(m) => panic!("expected StoreFull on init constraint, got OutOfMemory({m})"),
    }
    assert!(m.marked_full.load(Ordering::Relaxed), "expected gc.mark_full() on init constraint StoreFull");

    // Exhaustion in successor admits_gc on ordinal 0 stops immediately without shifting ordinals.
    match run(ReplayFailAt::SuccAdmits) {
        LiveResult::Error(e) => assert!(e.is_store_full(), "expected StoreFull, got: {e}"),
        LiveResult::Holds => panic!("expected StoreFull on successor admits, got Holds"),
        LiveResult::Violated(_) => panic!("expected StoreFull on successor admits, got Violated"),
        LiveResult::OutOfMemory(m) => panic!("expected StoreFull on successor admits, got OutOfMemory({m})"),
    }
    assert!(m.marked_full.load(Ordering::Relaxed), "expected gc.mark_full() on successor admits StoreFull");
    assert_eq!(
        m.admits_seen.load(Ordering::Relaxed),
        1,
        "replay must stop at the first StoreFull successor rather than skipping and shifting ordinals"
    );

    // Exhaustion in action_successors_gc also latches mark_full and propagates StoreFull.
    match run(ReplayFailAt::SuccEmit) {
        LiveResult::Error(e) => assert!(e.is_store_full(), "expected StoreFull, got: {e}"),
        LiveResult::Holds => panic!("expected StoreFull on action_successors_gc, got Holds"),
        LiveResult::Violated(_) => panic!("expected StoreFull on action_successors_gc, got Violated"),
        LiveResult::OutOfMemory(m) => panic!("expected StoreFull on action_successors_gc, got OutOfMemory({m})"),
    }
    assert!(m.marked_full.load(Ordering::Relaxed), "expected gc.mark_full() on action_successors_gc StoreFull");
}
