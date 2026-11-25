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

/// The compiled run of `src` under `opts`: its model and its counts.
fn compiled(src: &str, opts: &Options) -> Result<(tlx_compile::enc::EncModel, (u64, u64, u32)), String> {
    store_on_environment();
    let model = load(src, CFG);
    model.ip.set_run_config(opts.workers, opts.check_deadlock);
    let (m, r) = tlx_compile::enc::check(Arc::new(model), opts, 16)?;
    assert!(matches!(r.outcome, Outcome::Ok), "{:?}", r.outcome);
    Ok((m, (r.stats.generated, r.stats.distinct, r.stats.depth)))
}

/// The interpreter's counts, the semantic reference (compat.md §0).
fn interpreted(src: &str) -> (u64, u64, u32) {
    let s = run_mode(src, CFG, Mode::Interp);
    assert_eq!(s.outcome, "Ok");
    (s.generated, s.distinct, s.depth)
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
    // Half of what the values need: the store refuses and the run ends.
    let opts = Options { maxmem: bag_bytes() / 2, ..options() };
    let err = match compiled(BAG, &opts) {
        Err(e) => e,
        Ok(_) => panic!("a full value store must end the run"),
    };
    assert!(err.contains("the value store (TLX_VALUE_STORE) exceeded its budget of"), "{err}");
    assert!(err.contains("turn the store off (TLX_VALUE_STORE=0)"), "the error does not name the way out: {err}");
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
