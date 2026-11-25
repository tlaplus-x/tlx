//! The value store with the switch on (`TLX_VALUE_STORE=1`,
//! docs/configuration.md; it is off by default): a run with a `Dyn` slot
//! keeps its values in the store, a full budget is a hard error naming the
//! way out, default and explicit checkpoints persist `model-store` and
//! recover cleanly (including multi-run recovery in one process where each
//! `Store` allocates a fresh uid), and a run whose slots all have fixed
//! shapes stores nothing.
//!
//! The switch itself (its values, the unset default, the interaction with
//! `TLX_ESCAPE`) is parsed in `tlx_compile::settings` and tested there: this
//! binary runs one process with one environment.

use std::sync::{Arc, Once};
use std::time::Duration;

use tlx_compile::enc::{check_from, Checked};
use tlx_runtime::io::{Spill, SpillConfig};
use tlx_runtime::{AfterCommit, CheckpointConfig, Checkpointer, Options, Outcome, Recovery};
use tlx_testkit::spec::{load, run_mode, Mode};
use tlx_testkit::TempDir;

/// A bag keyed by records with a sequence field: the key universe has no
/// fixed bound, so the slot's shape has a `Dyn` part and the store holds
/// it. Every step adds one key, so the states' bags are all new nodes.
const BAG: &str = r#"---- MODULE Bag ----
EXTENDS Naturals, Sequences, TLC
VARIABLES bag, n
K(i) == [id |-> i, log |-> <<i>>]
Init == bag = (K(0) :> 0) /\ n = 0
Next == n < 1000 /\ bag' = bag @@ (K(n + 1) :> n) /\ n' = n + 1
====
"#;

/// A bag spec whose level-251 frontier holds 1,500 distinct 251-key bags
/// simultaneously: even after live-root GC drops the archive, the live
/// frontier alone exceeds a tight budget, verifying that genuine live-root
/// exhaustion still stops cleanly with the budget error.
const WIDE_BAG: &str = r#"---- MODULE WideBag ----
EXTENDS Naturals, Sequences, TLC
VARIABLES bag, n, branch
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ branch = 0
Next == \/ n < 250 /\ bag' = bag @@ (K(n + 1) :> n) /\ n' = n + 1 /\ branch' = 0
        \/ n = 250 /\ branch = 0 /\ \E b \in 1..1500 :
             bag' = bag @@ (K(1000 + b) :> b) /\ n' = 251 /\ branch' = b
====
"#;

/// A multi-worker mid-level transient churn spec: steps 0..120 build a
/// 121-key bag, step 120 fans out to 64 parallel tasks at level 121, step 121
/// performs 6,400 `bag' = bag @@ (K(...) :> j)` merges inside ONE single level
/// (~14.5 MiB of transient `Store` nodes, ~227 KiB per task) filtered by
/// `CONSTRAINT Bound` down to 4 live states, and step 122 reuses `ConstBag`.
const MID_LEVEL_CHURN: &str = r#"---- MODULE MidLevelChurn ----
EXTENDS Naturals, Sequences, TLC
VARIABLES bag, w, step, tag
K(i) == [id |-> i, log |-> <<i, i + 1, i + 2>>]
ConstBag == (K(999999) :> 42)
Init == bag = ConstBag /\ w = 0 /\ step = 0 /\ tag = 0
Next == \/ step < 120 /\ bag' = bag @@ (K(step + 1) :> step) /\ w' = 0 /\ step' = step + 1 /\ tag' = 0
        \/ step = 120 /\ \E id \in 1..64 :
             bag' = bag @@ (K(1000 + id) :> id) /\ w' = id /\ step' = 121 /\ tag' = 0
        \/ step = 121 /\ \E j \in 1..100 :
             bag' = bag @@ (K(w * 100000 + j) :> j) /\ w' = w /\ step' = 122 /\ tag' = j
        \/ step = 122 /\ bag' = ConstBag /\ w' = w /\ step' = 123 /\ tag' = tag
Bound == step < 122 \/ (tag = 1 /\ w <= 4)
====
"#;
const MID_LEVEL_CFG: &str = "INIT Init\nNEXT Next\nCONSTRAINT Bound\nCHECK_DEADLOCK FALSE\n";

/// Every slot of this run has a fixed shape (an integer): nothing of it
/// is a handle.
const FIXED: &str = r#"---- MODULE Fixed ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 6 /\ x' = x + 1
====
"#;

const CFG: &str = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";

/// The environment of every test in this file: the store on, the escape
/// experiment off. (The compiled tier parses the settings once per process,
/// so a test that wants another environment needs another process - the CLI
/// tests' business, not this binary's.)
fn store_on_environment() {
    static ONCE: Once = Once::new();
    ONCE.call_once(|| {
        std::env::set_var("TLX_VALUE_STORE", "1");
        std::env::remove_var("TLX_ESCAPE");
        // Run the generated code, not only the closure IR.
        std::env::set_var("TLX_NATIVE_SYNC", "1");
    });
}

/// The compiled run of `src` under `cfg` and `opts`: its model and its counts.
fn compiled_cfg(src: &str, cfg: &str, opts: &Options) -> Result<(tlx_compile::enc::EncModel, (u64, u64, u32)), String> {
    store_on_environment();
    let model = load(src, cfg);
    model.ip.set_run_config(opts.workers, opts.check_deadlock);
    let (m, r) = tlx_compile::enc::check(Arc::new(model), opts, 16)?;
    assert!(matches!(r.outcome, Outcome::Ok), "{:?}", r.outcome);
    Ok((m, (r.stats.generated, r.stats.distinct, r.stats.depth)))
}

/// The compiled run of `src` under `CFG` and `opts`: its model and its counts.
fn compiled(src: &str, opts: &Options) -> Result<(tlx_compile::enc::EncModel, (u64, u64, u32)), String> {
    compiled_cfg(src, CFG, opts)
}

/// The interpreter's counts, the semantic reference (compat.md §0).
fn interpreted_cfg(src: &str, cfg: &str) -> (u64, u64, u32) {
    let s = run_mode(src, cfg, Mode::Interp);
    assert_eq!(s.outcome, "Ok");
    (s.generated, s.distinct, s.depth)
}

/// The interpreter's counts under `CFG`.
fn interpreted(src: &str) -> (u64, u64, u32) {
    interpreted_cfg(src, CFG)
}

fn options() -> Options {
    Options { workers: 1, check_deadlock: false, ..Default::default() }
}

/// The checkpointer of a run that takes checkpoints (or, with `explicit`
/// false, one that holds TLC's default interval or a state trigger).
fn checkpointer(explicit: bool, every_states: Option<u64>, after: AfterCommit) -> Arc<Checkpointer> {
    let every = (!explicit && every_states.is_none()).then(|| Duration::from_secs(30 * 60));
    Checkpointer::new(CheckpointConfig { every, every_states, after, identity: Vec::new(), report: None, explicit })
}

#[test]
fn a_dyn_slot_is_a_store_slot_with_the_switch_on() {
    let want = interpreted(BAG);
    let (m, got) = compiled(BAG, &options()).unwrap();
    assert_eq!(got, want);
    let store = m.value_store().expect("the switch holds a Dyn slot in the value store");
    assert!(store.stats().nodes > 0, "the run stored no values");
    assert_eq!(m.bailouts.get(), 0, "action runs fell back to the interpreter");
    assert!(m.layout.vars.iter().any(|s| matches!(s, tlx_layout::Shape::Ref(_))), "no slot is a handle");
}

#[test]
fn a_run_of_fixed_shapes_stores_nothing() {
    let want = interpreted(FIXED);
    let (m, got) = compiled(FIXED, &options()).unwrap();
    assert_eq!(got, want);
    // No slot is a handle and no value was stored: a run whose shapes are
    // all fixed neither encodes nor fingerprints through the store.
    assert!(m.value_store().is_none(), "a fixed-shape run took the store path");
    assert!(!m.layout.vars.iter().any(|s| matches!(s, tlx_layout::Shape::Ref(_))), "a slot became a handle");
}

/// The values of the `BAG` run, in bytes: what its store holds once the
/// whole search is done. The budget tests below are relative to it, so a
/// larger spec does not invalidate their numbers.
fn bag_bytes() -> usize {
    let (m, _) = compiled(BAG, &options()).unwrap();
    let bytes = m.value_store().expect("the run's store").stats().node_bytes as usize;
    assert!(bytes > 0, "the run stored no values");
    bytes
}

#[test]
fn the_budget_is_the_runs_own_budget_not_a_fraction_of_it() {
    // The store replaces the `Dyn` interner, which had no limit of its
    // own: a value set that fits the run's memory budget must not end the
    // run (it used to stop at a quarter of it, which this budget is below).
    let bytes = bag_bytes();
    let budget = bytes + bytes / 4;
    let opts = Options { maxmem: budget, ..options() };
    let (m, got) = compiled(BAG, &opts).unwrap();
    assert_eq!(got, interpreted(BAG));
    assert_eq!(m.value_store().expect("the run's store").budget(), budget, "the store's budget is not the run's");
}

#[test]
fn a_full_store_is_a_hard_error_naming_the_way_out() {
    // Measure WIDE_BAG's full uncollected store size, then run with a budget
    // well below its live level-251 frontier (~6 MiB): even after live-root
    // GC reclaims dead nodes and drops the archive, the live frontier itself
    // exceeds the budget and the run ends cleanly with the budget error.
    let (m_full, _) = compiled(WIDE_BAG, &options()).unwrap();
    let full_bytes = m_full.value_store().expect("wide bag store").stats().node_bytes as usize;
    let budget = (full_bytes / 4).max(128 * 1024);
    let opts = Options { maxmem: budget, ..options() };
    let err = match compiled(WIDE_BAG, &opts) {
        Err(e) => e,
        Ok(_) => panic!("a live frontier exceeding budget ({budget}) must end the run"),
    };
    assert!(err.contains("the value store (TLX_VALUE_STORE) exceeded its budget of"), "{err}");
    assert!(err.contains("turn the store off (TLX_VALUE_STORE=0)"), "the error does not name the way out: {err}");
}

#[test]
fn safepoint_reclamation_handles_five_x_churn_single_and_multi_worker() {
    // 1. Multi-level frontier churn (BAG): cumulative bytes (~10+ MiB) exceed
    //    the budget by >= 5x while the live frontier is a single state.
    let full_bytes = bag_bytes();
    let budget = (full_bytes / 7).max(256 * 1024);
    assert!(full_bytes >= 5 * budget, "test setup requires >= 5x churn: full={full_bytes}, budget={budget}");
    let want = interpreted(BAG);
    let opts = Options { maxmem: budget, ..options() };
    let (m, got) = compiled(BAG, &opts).unwrap();
    assert_eq!(got, want);
    assert_eq!(m.bailouts.get(), 0, "GC churn fell back to interpreter");
    let st = m.value_store().expect("bag store").stats();
    assert!(st.gc_cycles >= 3, "expected multiple GC cycles, got {}", st.gc_cycles);
    assert!(
        st.reclaimed_bytes + st.node_bytes >= 5 * budget as u64,
        "expected >= 5x budget cumulative bytes processed: reclaimed={}, live={}, budget={}",
        st.reclaimed_bytes,
        st.node_bytes,
        budget
    );
    assert!(st.node_bytes <= budget as u64, "final live bytes {} exceeded budget {}", st.node_bytes, budget);

    // 2. Mid-level transient churn with both 1 and 4 workers: a single level
    //    generates >= 5x budget of transient bags filtered by CONSTRAINT.
    let want_mid = interpreted_cfg(MID_LEVEL_CHURN, MID_LEVEL_CFG);
    let (m_mid_full, _) = compiled_cfg(MID_LEVEL_CHURN, MID_LEVEL_CFG, &options()).unwrap();
    let mid_full_bytes = m_mid_full.value_store().expect("mid churn store").stats().node_bytes as usize;
    let mid_budget = (mid_full_bytes / 7).max(256 * 1024);
    assert!(mid_full_bytes >= 5 * mid_budget, "mid-level test setup requires >= 5x churn: full={mid_full_bytes}, budget={mid_budget}");
    for workers in [1, 4] {
        let opts = Options { workers, maxmem: mid_budget, ..options() };
        let (m, got) = compiled_cfg(MID_LEVEL_CHURN, MID_LEVEL_CFG, &opts).unwrap();
        assert_eq!(got, want_mid, "workers={workers}");
        assert_eq!(m.bailouts.get(), 0, "workers={workers} fell back to interpreter");
        let st = m.value_store().expect("mid churn store").stats();
        assert!(st.gc_cycles >= 2, "workers={workers}: expected mid-level GC cycles, got {}", st.gc_cycles);
        assert!(
            st.reclaimed_bytes + st.node_bytes >= 5 * mid_budget as u64,
            "workers={workers}: cumulative {} < 5x budget {}",
            st.reclaimed_bytes + st.node_bytes,
            mid_budget
        );
    }
}

#[test]
fn checkpoint_and_recovery_work_across_multiple_gc_cycles() {
    store_on_environment();
    let want = interpreted(BAG);
    let full_bytes = bag_bytes();
    let budget = (full_bytes / 6).max(256 * 1024);
    let md = TempDir::new("value-store-gc-recover");
    let spill = |reused: bool| Spill::new(SpillConfig { dir: Some(md.path().to_path_buf()), reused, ..Default::default() });

    // Run 1: force GC before checkpointing at 550 states.
    let ck1 = checkpointer(true, Some(550), AfterCommit::Stop(1));
    let opts1 = Options { maxmem: budget, checkpoint: Some(ck1.clone()), spill: spill(false), ..options() };
    let model1 = load(BAG, CFG);
    model1.ip.set_run_config(1, false);
    let Checked::Compiled(m1, _) = check_from(Arc::new(model1), &opts1, 16, None).unwrap() else {
        panic!("expected compiled run 1");
    };
    assert_eq!(ck1.count(), 1);
    assert!(m1.value_store().expect("store 1").stats().gc_cycles >= 1, "expected GC before checkpoint 1");

    // Run 2: recover sparse v2 model-store under the same tight budget and finish.
    let rec = Recovery::open(md.path()).unwrap();
    let ck2 = checkpointer(true, None, AfterCommit::Continue);
    let opts2 = Options { maxmem: budget, checkpoint: Some(ck2), spill: spill(true), ..options() };
    let model2 = load(BAG, CFG);
    model2.ip.set_run_config(1, false);
    let Checked::Compiled(m2, r2) = check_from(Arc::new(model2), &opts2, 16, Some(&rec)).unwrap() else {
        panic!("expected compiled recovery");
    };
    assert!(matches!(r2.outcome, Outcome::Ok), "{:?}", r2.outcome);
    assert_eq!((r2.stats.generated, r2.stats.distinct, r2.stats.depth), want);
    assert_eq!(m2.bailouts.get(), 0);
    assert!(m2.value_store().expect("store 2").stats().gc_cycles >= 1, "expected GC after recovery");
}

#[test]
fn default_interval_keeps_the_store_and_takes_checkpoints() {
    store_on_environment();
    let want = interpreted(BAG);
    let md = TempDir::new("value-store-default-ck");
    // `explicit: false` models a non-explicit checkpointer (like TLC's default
    // timer); triggering by states proves the driver does not strip it.
    let ck = checkpointer(false, Some(250), AfterCommit::Continue);
    let opts = Options {
        checkpoint: Some(ck.clone()),
        spill: Spill::new(SpillConfig { dir: Some(md.path().to_path_buf()), reused: false, ..Default::default() }),
        ..options()
    };
    let (m, got) = compiled(BAG, &opts).unwrap();
    assert_eq!(got, want);
    let store = m.value_store().expect("the default checkpoint interval keeps the store");
    assert!(store.stats().nodes > 0, "the run stored no values");
    assert!(ck.count() >= 1, "expected at least one checkpoint, got {}", ck.count());
}

#[test]
fn explicit_checkpoint_and_repeated_in_process_recovery_preserve_results() {
    store_on_environment();
    let want = interpreted(BAG);
    let md = TempDir::new("value-store-inproc-recover");
    let spill = |reused: bool| Spill::new(SpillConfig { dir: Some(md.path().to_path_buf()), reused, ..Default::default() });

    // Run 1: stop right after the first checkpoint (keeps checkpoint on disk).
    let ck1 = checkpointer(true, Some(300), AfterCommit::Stop(1));
    let opts1 = Options { checkpoint: Some(ck1.clone()), spill: spill(false), ..options() };
    let model1 = load(BAG, CFG);
    model1.ip.set_run_config(1, false);
    let Checked::Compiled(m1, _) = check_from(Arc::new(model1), &opts1, 16, None).unwrap() else {
        panic!("expected compiled run");
    };
    assert_eq!(ck1.count(), 1);
    let uid1 = m1.value_store().expect("store 1").uid();
    assert!(md.path().join("checkpoint/model-store").is_file(), "missing model-store");

    // Run 2 (same process!): recover into a fresh Store uid, take a second
    // checkpoint (exercising incremental archive linking), and stop.
    let rec1 = Recovery::open(md.path()).unwrap();
    let ck2 = checkpointer(true, Some(300), AfterCommit::Stop(1));
    let opts2 = Options { checkpoint: Some(ck2.clone()), spill: spill(true), ..options() };
    let model2 = load(BAG, CFG);
    model2.ip.set_run_config(1, false);
    let Checked::Compiled(m2, _) = check_from(Arc::new(model2), &opts2, 16, Some(&rec1)).unwrap() else {
        panic!("expected compiled recovery 1");
    };
    assert_eq!(ck2.count(), 1);
    let uid2 = m2.value_store().expect("store 2").uid();
    assert_ne!(uid2, uid1, "recovered run must allocate a fresh store uid");

    // Run 3 (same process!): recover again and finish to completion.
    let rec2 = Recovery::open(md.path()).unwrap();
    let ck3 = checkpointer(true, None, AfterCommit::Continue);
    let opts3 = Options { checkpoint: Some(ck3), spill: spill(true), ..options() };
    let model3 = load(BAG, CFG);
    model3.ip.set_run_config(1, false);
    let Checked::Compiled(m3, r3) = check_from(Arc::new(model3), &opts3, 16, Some(&rec2)).unwrap() else {
        panic!("expected compiled recovery 2");
    };
    assert!(matches!(r3.outcome, Outcome::Ok), "{:?}", r3.outcome);
    let uid3 = m3.value_store().expect("store 3").uid();
    assert_ne!(uid3, uid1);
    assert_ne!(uid3, uid2);
    assert_eq!((r3.stats.generated, r3.stats.distinct, r3.stats.depth), want);
    assert_eq!(m3.bailouts.get(), 0, "recovered action runs fell back to the interpreter");
}

#[test]
fn recovery_rejects_budget_overflow_and_corrupt_model_store() {
    store_on_environment();
    let md = TempDir::new("value-store-bad-recover");
    let ck = checkpointer(true, Some(300), AfterCommit::Stop(1));
    let opts = Options {
        checkpoint: Some(ck),
        spill: Spill::new(SpillConfig { dir: Some(md.path().to_path_buf()), reused: false, ..Default::default() }),
        ..options()
    };
    let model = load(BAG, CFG);
    model.ip.set_run_config(1, false);
    let Checked::Compiled(m1, _) = check_from(Arc::new(model), &opts, 16, None).unwrap() else {
        panic!("expected compiled run");
    };
    let store_bytes = m1.value_store().expect("store").stats().node_bytes as usize;
    assert!(store_bytes > 1024);

    // Tighter -maxmem than the checkpointed store is rejected cleanly.
    let rec = Recovery::open(md.path()).unwrap();
    let tight_opts = Options {
        maxmem: store_bytes / 2,
        spill: Spill::new(SpillConfig { dir: Some(md.path().to_path_buf()), reused: true, ..Default::default() }),
        ..options()
    };
    let model2 = load(BAG, CFG);
    model2.ip.set_run_config(1, false);
    let err = match check_from(Arc::new(model2), &tight_opts, 16, Some(&rec)) {
        Err(e) => e,
        Ok(_) => panic!("budget overflow during recovery must fail"),
    };
    assert!(err.contains("exceeds its budget"), "{err}");

    // Truncating model-store is rejected cleanly on Recovery::open.
    let store_path = md.path().join("checkpoint/model-store");
    let raw = std::fs::read(&store_path).unwrap();
    std::fs::write(&store_path, &raw[..raw.len() / 2]).unwrap();
    let open_err = Recovery::open(md.path()).unwrap_err();
    assert!(open_err.contains("corrupt checkpoint") || open_err.contains("truncated"), "{open_err}");
}
