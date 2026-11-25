//! The experimental value store (`TLX_VALUE_STORE`, docs/configuration.md):
//! its byte budget (the run's `-maxmem`, never a fraction of it) is a hard
//! limit, and runs with the store on take both default and explicit
//! checkpoints (`model-store`) and recover cleanly with identical results.

use std::path::Path;

use tlx_testkit::cli::counts;
use tlx_testkit::TempDir;

/// A bag keyed by records with a sequence field (a `Dyn` shape, so a value
/// store slot) growing by one key per step: every state's bag is a new
/// node, so the store grows quadratically.
const SPEC: &str = r#"---- MODULE Store ----
EXTENDS Naturals, Sequences, TLC
VARIABLES bag, n
K(i) == [id |-> i, log |-> <<i>>]
Init == bag = (K(0) :> 0) /\ n = 0
Next == n < 1000 /\ bag' = bag @@ (K(n + 1) :> n) /\ n' = n + 1
====
"#;
const CFG: &str = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";

/// A branching bag spec with a counterexample invariant, VIEW, SYMMETRY, and
/// a late layout miss after recovery.
const VIEW_SYM_SPEC: &str = r#"---- MODULE StoreViewSym ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS P
VARIABLES bag, p, h
K(i, owner) == [id |-> i, owner |-> owner, log |-> <<i, owner>>]
Init == bag = (K(0, CHOOSE x \in P : TRUE) :> 0) /\ p \in P /\ h = 0
Next == /\ Cardinality(DOMAIN bag) < 6
        /\ \E q \in P :
             /\ bag' = bag @@ (K(Cardinality(DOMAIN bag), q) :> h)
             /\ p' = q
             /\ h' = (h + 1) % 3
View == <<bag, p>>
Sym == Permutations(P)
====
"#;
const VIEW_SYM_CFG: &str = "CONSTANTS P = {p1, p2}\nINIT Init\nNEXT Next\nVIEW View\nSYMMETRY Sym\nCHECK_DEADLOCK FALSE\n";

/// A spec whose invariant fails late (after a checkpoint) so recovery must
/// produce the exact same counterexample trace and counts.
const TRACE_SPEC: &str = r#"---- MODULE StoreTrace ----
EXTENDS Naturals, Sequences, TLC
VARIABLES bag, n
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0
Next == n < 60 /\ bag' = bag @@ (K(n + 1) :> n) /\ n' = n + 1
Inv == n < 50
====
"#;
const TRACE_CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";

/// A spec that starts with a fixed integer variable `y` and widens `y` to a
/// tuple late (after recovery), while `bag` lives in the value store.
const MISS_SPEC: &str = r#"---- MODULE StoreMiss ----
EXTENDS Naturals, Sequences, TLC
VARIABLES bag, n, y
K(i) == [id |-> i, log |-> <<i>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ y = 0
Next == n < 80 /\ bag' = bag @@ (K(n + 1) :> n) /\ n' = n + 1 /\ y' = IF n' > 55 THEN <<"late", n'>> ELSE y
====
"#;
const MISS_CFG: &str = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";

fn run_spec(dir: &Path, name: &str, args: &[&str], env: &[(&str, &str)]) -> tlx_testkit::cli::Run {
    tlx_testkit::tlx!()
        .check(format!("{name}.tla"))
        .cfg(format!("{name}.cfg"))
        .args(args.iter().copied())
        .envs(env.iter().copied())
        .dir(dir)
        .run()
}

fn check(dir: &TempDir, store: &str, args: &[&str]) -> tlx_testkit::cli::Run {
    run_spec(dir.path(), "Store", &[&["-workers", "1", "-compile"][..], args].concat(), &[("TLX_VALUE_STORE", store)])
}

const COUNTS: [&str; 2] =
    ["1001 states generated, 1001 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 1001."];

#[test]
fn the_budget_is_a_hard_limit() {
    let dir = TempDir::with_spec("value-store-budget", SPEC, CFG);
    // 4 MiB: the bags of the first few hundred states (the budget used to
    // be a quarter of the memory budget).
    let out = check(&dir, "1", &["-maxmem", "4M"]);
    let text = out.text();
    assert_ne!(out.code, 0, "{text}");
    assert!(text.contains("the value store (TLX_VALUE_STORE) exceeded its budget of 4 MiB"), "{text}");
    assert!(text.contains("turn the store off (TLX_VALUE_STORE=0)"), "{text}");
    // Without the store the run completes in the same memory budget, and
    // with the default budget the store holds it.
    let out = check(&dir, "0", &["-maxmem", "4M"]);
    assert_eq!(counts(&out.text()), COUNTS, "{}", out.text());
    let out = check(&dir, "1", &[]);
    assert_eq!(counts(&out.text()), COUNTS, "{}", out.text());
}

#[test]
fn store_exhaustion_preserves_last_checkpoint_for_larger_budget_recovery() {
    let dir = TempDir::with_spec("value-store-exhaust-keep", SPEC, CFG);

    // Case 1: recover a 150-state checkpoint under a 4 MiB budget (store loads,
    // then fills mid-run). The checkpoint must be preserved so a subsequent
    // recovery with 32 MiB finishes all 1,001 states.
    let md1 = dir.child_path("md-recovered-exhaust");
    let ck = run_spec(
        dir.path(),
        "Store",
        &["-workers", "1", "-compile", "-tlc", "-metadir", md1.to_str().unwrap()],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN_REUSE", "0"), ("TLX_CHECKPOINT_STATES", "150"), ("TLX_CHECKPOINT_ABORT", "1")],
    );
    assert_eq!(ck.code, 134, "{}", ck.text());
    assert!(md1.join("checkpoint/model-store").is_file());

    let exhausted = run_spec(
        dir.path(),
        "Store",
        &["-workers", "1", "-compile", "-tlc", "-maxmem", "4M", "-recover", md1.to_str().unwrap()],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN_REUSE", "0")],
    );
    let text = exhausted.text();
    assert_ne!(exhausted.code, 0, "{text}");
    assert!(text.contains("the value store (TLX_VALUE_STORE) exceeded its budget of 4 MiB"), "{text}");
    assert!(text.contains("recovering the last checkpoint, which is kept"), "{text}");
    assert!(md1.join("checkpoint/MANIFEST").is_file(), "exhaustion deleted MANIFEST");
    assert!(md1.join("checkpoint/model-store").is_file(), "exhaustion deleted model-store");

    let resumed = run_spec(
        dir.path(),
        "Store",
        &["-workers", "1", "-compile", "-tlc", "-maxmem", "32M", "-recover", md1.to_str().unwrap()],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN_REUSE", "0")],
    );
    assert_eq!(resumed.code, 0, "{}", resumed.text());
    assert_eq!(counts(&resumed.text()), COUNTS, "{}", resumed.text());
    assert!(!md1.exists(), "completed recovery should clean up metadir");

    // Case 2: a fresh run takes a checkpoint at 150 states under -maxmem 4M,
    // keeps going until the store fills, preserves that checkpoint, and a
    // recovery with -maxmem 32M finishes all 1,001 states.
    let md2 = dir.child_path("md-fresh-exhaust");
    let fresh_exhaust = run_spec(
        dir.path(),
        "Store",
        &["-workers", "1", "-compile", "-tlc", "-maxmem", "4M", "-metadir", md2.to_str().unwrap()],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN_REUSE", "0"), ("TLX_CHECKPOINT_STATES", "150")],
    );
    let text = fresh_exhaust.text();
    assert_ne!(fresh_exhaust.code, 0, "{text}");
    assert!(text.contains("the value store (TLX_VALUE_STORE) exceeded its budget of 4 MiB"), "{text}");
    assert!(text.contains("recovering the last checkpoint, which is kept"), "{text}");
    assert!(md2.join("checkpoint/model-store").is_file(), "fresh run exhaustion deleted model-store");

    let resumed2 = run_spec(
        dir.path(),
        "Store",
        &["-workers", "1", "-compile", "-tlc", "-maxmem", "32M", "-recover", md2.to_str().unwrap()],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN_REUSE", "0")],
    );
    assert_eq!(resumed2.code, 0, "{}", resumed2.text());
    assert_eq!(counts(&resumed2.text()), COUNTS, "{}", resumed2.text());
    assert!(!md2.exists(), "completed recovery should clean up metadir");

    // Case 3: recovering a 25-state checkpoint with a short pre-run triggers a
    // layout-miss restart before the store fills at -maxmem 4M. The committed
    // checkpoint must survive the intermediate layout restart so retrying with
    // -maxmem 32M completes all 1,001 states and cleans up on terminal success.
    let md3 = dir.child_path("md-restart-exhaust");
    let ck3 = run_spec(
        dir.path(),
        "Store",
        &["-workers", "1", "-compile", "-tlc", "-metadir", md3.to_str().unwrap()],
        &[
            ("TLX_VALUE_STORE", "1"),
            ("TLX_PRERUN", "10"),
            ("TLX_PRERUN_REUSE", "0"),
            ("TLX_CHECKPOINT_STATES", "25"),
            ("TLX_CHECKPOINT_ABORT", "1"),
        ],
    );
    assert_eq!(ck3.code, 134, "{}", ck3.text());
    assert!(md3.join("checkpoint/model-store").is_file());

    let restart_exhaust = run_spec(
        dir.path(),
        "Store",
        &["-workers", "1", "-compile", "-tlc", "-maxmem", "4M", "-recover", md3.to_str().unwrap()],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0")],
    );
    let text = restart_exhaust.text();
    assert_ne!(restart_exhaust.code, 0, "{text}");
    assert!(text.contains("widening and restarting"), "expected layout-miss restart before exhaustion:\n{text}");
    assert!(text.contains("the value store (TLX_VALUE_STORE) exceeded its budget of 4 MiB"), "{text}");
    assert!(text.contains("recovering the last checkpoint, which is kept"), "{text}");
    assert!(md3.join("checkpoint/MANIFEST").is_file(), "layout restart deleted MANIFEST");
    assert!(md3.join("checkpoint/model-store").is_file(), "layout restart deleted model-store");

    let resumed3 = run_spec(
        dir.path(),
        "Store",
        &["-workers", "1", "-compile", "-tlc", "-maxmem", "32M", "-recover", md3.to_str().unwrap()],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0")],
    );
    assert_eq!(resumed3.code, 0, "{}", resumed3.text());
    assert_eq!(counts(&resumed3.text()), COUNTS, "{}", resumed3.text());
    assert!(!md3.exists(), "completed recovery after layout restart should clean up metadir");

    // Case 4: after a layout-miss restart, the widened attempt can still take
    // and replace the checkpoint; a subsequent store exhaustion preserves that
    // replacement checkpoint, and recovery resumes from the widened attempt.
    let md4 = dir.child_path("md-restart-replace");
    let ck4 = run_spec(
        dir.path(),
        "Store",
        &["-workers", "1", "-compile", "-tlc", "-metadir", md4.to_str().unwrap()],
        &[
            ("TLX_VALUE_STORE", "1"),
            ("TLX_PRERUN", "10"),
            ("TLX_PRERUN_REUSE", "0"),
            ("TLX_CHECKPOINT_STATES", "25"),
            ("TLX_CHECKPOINT_ABORT", "1"),
        ],
    );
    assert_eq!(ck4.code, 134, "{}", ck4.text());

    let replace_exhaust = run_spec(
        dir.path(),
        "Store",
        &["-workers", "1", "-compile", "-tlc", "-maxmem", "4M", "-recover", md4.to_str().unwrap()],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0"), ("TLX_CHECKPOINT_STATES", "100")],
    );
    let text = replace_exhaust.text();
    assert_ne!(replace_exhaust.code, 0, "{text}");
    assert!(text.contains("widening and restarting"), "{text}");
    assert!(text.contains("Checkpointing completed"), "widened attempt should replace checkpoint:\n{text}");
    assert!(text.contains("recovering the last checkpoint, which is kept"), "{text}");
    assert!(md4.join("checkpoint/model-store").is_file());

    let resumed4 = run_spec(
        dir.path(),
        "Store",
        &["-workers", "1", "-compile", "-tlc", "-maxmem", "32M", "-recover", md4.to_str().unwrap()],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0")],
    );
    let text = resumed4.text();
    assert_eq!(resumed4.code, 0, "{text}");
    assert!(text.contains("recovering with the shapes of attempt 1"), "expected replacement checkpoint from attempt 1:\n{text}");
    assert_eq!(counts(&text), COUNTS, "{text}");
    assert!(!md4.exists(), "completed recovery should clean up metadir");
}

#[test]
fn checkpoints_and_recovery_work_with_value_store() {
    let dir = TempDir::with_spec("value-store-checkpoint", SPEC, CFG);

    // Default 30-min checkpoint interval and explicit -checkpoint both keep the store enabled.
    for extra in [&[][..], &["-checkpoint", "60"]] {
        let out = check(&dir, "1", extra);
        let text = out.text();
        assert_eq!(out.code, 0, "{text}");
        assert!(!text.contains("disabled: checkpoints"), "{text}");
        assert!(!text.contains("this run takes no checkpoints"), "{text}");
        assert_eq!(counts(&text), COUNTS, "{text}");
    }

    // Single-worker and multi-worker checkpoint -> abort -> recover, plus repeated recovery and `all`.
    for (store_mode, workers) in [("1", "1"), ("1", "4"), ("all", "1")] {
        let md = dir.child_path(&format!("md-{store_mode}-w{workers}"));
        let base_args = ["-workers", workers, "-compile", "-tlc"];
        let mut ck_args = base_args.to_vec();
        ck_args.extend(["-metadir", md.to_str().unwrap()]);
        let abort_env =
            [("TLX_VALUE_STORE", store_mode), ("TLX_PRERUN_REUSE", "0"), ("TLX_CHECKPOINT_STATES", "300"), ("TLX_CHECKPOINT_ABORT", "1")];
        let r1 = run_spec(dir.path(), "Store", &ck_args, &abort_env);
        assert_eq!(r1.code, 134, "mode={store_mode} w={workers}\n{}", r1.text());
        assert!(md.join("checkpoint/model-store").is_file(), "model-store missing for mode={store_mode}");

        // Second generation checkpoint on top of the first recovery.
        let mut rec_args = base_args.to_vec();
        rec_args.extend(["-recover", md.to_str().unwrap()]);
        let r2 = run_spec(dir.path(), "Store", &rec_args, &abort_env);
        assert_eq!(r2.code, 134, "second ckpt mode={store_mode} w={workers}\n{}", r2.text());

        // Final recovery to completion.
        let r3 = run_spec(dir.path(), "Store", &rec_args, &[("TLX_VALUE_STORE", store_mode), ("TLX_PRERUN_REUSE", "0")]);
        assert_eq!(r3.code, 0, "recover mode={store_mode} w={workers}\n{}", r3.text());
        assert_eq!(counts(&r3.text()), COUNTS, "{}", r3.text());
        assert!(!md.exists(), "metadir should be cleaned up after completed recovery");
    }
}

#[test]
fn recovery_preserves_counterexample_view_symmetry_and_late_layout_miss() {
    // 1. Counterexample trace preservation.
    let dir = TempDir::with_spec("value-store-trace", TRACE_SPEC, TRACE_CFG);
    let base_env = [("TLX_VALUE_STORE", "1"), ("TLX_PRERUN_REUSE", "0"), ("TLX_PARANOID", "1")];
    let want = run_spec(dir.path(), "StoreTrace", &["-workers", "1", "-compile", "-tlc"], &base_env);
    assert_eq!(want.code, 12, "{}", want.text());
    let md = dir.child_path("md-trace");
    let abort_env = [("TLX_VALUE_STORE", "1"), ("TLX_PRERUN_REUSE", "0"), ("TLX_CHECKPOINT_STATES", "20"), ("TLX_CHECKPOINT_ABORT", "1")];
    let ck = run_spec(dir.path(), "StoreTrace", &["-workers", "1", "-compile", "-tlc", "-metadir", md.to_str().unwrap()], &abort_env);
    assert_eq!(ck.code, 134, "{}", ck.text());
    let got = run_spec(dir.path(), "StoreTrace", &["-workers", "1", "-compile", "-tlc", "-recover", md.to_str().unwrap()], &base_env);
    assert_eq!(got.code, 12, "{}", got.text());
    assert_eq!(counts(&got.text()), counts(&want.text()), "{}", got.text());
    fn trace_lines(s: &str) -> Vec<&str> {
        s.lines().skip_while(|l| !l.contains("The behavior up to this point is:")).take_while(|l| !l.contains("states generated")).collect()
    }
    assert_eq!(trace_lines(&got.text()), trace_lines(&want.text()));

    // 2. VIEW + SYMMETRY with single and multiple workers.
    let dir = TempDir::with_spec("value-store-viewsym", VIEW_SYM_SPEC, VIEW_SYM_CFG);
    let want = run_spec(dir.path(), "StoreViewSym", &["-workers", "1", "-compile", "-tlc"], &[("TLX_VALUE_STORE", "1")]);
    assert_eq!(want.code, 0, "{}", want.text());
    for workers in ["1", "2"] {
        let md = dir.child_path(&format!("md-vs-w{workers}"));
        let ck = run_spec(
            dir.path(),
            "StoreViewSym",
            &["-workers", workers, "-compile", "-tlc", "-metadir", md.to_str().unwrap()],
            &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN_REUSE", "0"), ("TLX_CHECKPOINT_STATES", "5"), ("TLX_CHECKPOINT_ABORT", "1")],
        );
        assert_eq!(ck.code, 134, "w={workers}\n{}", ck.text());
        let got = run_spec(
            dir.path(),
            "StoreViewSym",
            &["-workers", workers, "-compile", "-tlc", "-recover", md.to_str().unwrap()],
            &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN_REUSE", "0")],
        );
        assert_eq!(got.code, 0, "w={workers}\n{}", got.text());
        assert_eq!(counts(&got.text()), counts(&want.text()), "w={workers}\n{}", got.text());
    }

    // 3. Layout-miss restart AFTER -recover.
    let dir = TempDir::with_spec("value-store-miss", MISS_SPEC, MISS_CFG);
    let want = run_spec(
        dir.path(),
        "StoreMiss",
        &["-workers", "1", "-compile", "-tlc"],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0")],
    );
    assert_eq!(want.code, 0, "{}", want.text());
    let md = dir.child_path("md-miss");
    let ck = run_spec(
        dir.path(),
        "StoreMiss",
        &["-workers", "1", "-compile", "-tlc", "-metadir", md.to_str().unwrap()],
        &[
            ("TLX_VALUE_STORE", "1"),
            ("TLX_PRERUN", "10"),
            ("TLX_PRERUN_REUSE", "0"),
            ("TLX_CHECKPOINT_STATES", "25"),
            ("TLX_CHECKPOINT_ABORT", "1"),
        ],
    );
    assert_eq!(ck.code, 134, "{}", ck.text());
    let got = run_spec(
        dir.path(),
        "StoreMiss",
        &["-workers", "1", "-compile", "-tlc", "-recover", md.to_str().unwrap()],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0"), ("TLX_PARANOID", "1")],
    );
    assert_eq!(got.code, 0, "{}", got.text());
    assert_eq!(counts(&got.text()), counts(&want.text()), "{}", got.text());
}

#[test]
fn recovery_refuses_mode_mismatches_and_corrupt_model_store() {
    let dir = TempDir::with_spec("value-store-mismatch", SPEC, CFG);

    // Take a TLX_VALUE_STORE=1 checkpoint.
    let md_on = dir.child_path("md-on");
    let r = run_spec(
        dir.path(),
        "Store",
        &["-workers", "1", "-compile", "-metadir", md_on.to_str().unwrap()],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN_REUSE", "0"), ("TLX_CHECKPOINT_STATES", "300"), ("TLX_CHECKPOINT_ABORT", "1")],
    );
    assert_eq!(r.code, 134, "{}", r.text());

    // Refuse recovering with TLX_VALUE_STORE=0, TLX_VALUE_STORE=all, and TLX_ESCAPE=1.
    for (label, env, expect) in [
        ("store=0", &[("TLX_VALUE_STORE", "0")][..], "TLX_VALUE_STORE=1"),
        ("store=all", &[("TLX_VALUE_STORE", "all")][..], "TLX_VALUE_STORE=all"),
        ("escape=1", &[("TLX_ESCAPE", "1")][..], "TLX_ESCAPE=1"),
        ("escape=1+store=1", &[("TLX_ESCAPE", "1"), ("TLX_VALUE_STORE", "1")][..], "TLX_ESCAPE=1"),
    ] {
        let out = run_spec(dir.path(), "Store", &["-workers", "1", "-compile", "-recover", md_on.to_str().unwrap()], env);
        let text = out.text();
        assert_ne!(out.code, 0, "{label} should fail:\n{text}");
        assert!(text.contains(expect), "{label}: expected {expect:?} in:\n{text}");
        assert!(md_on.join("checkpoint/MANIFEST").is_file(), "{label}: failed recovery must keep checkpoint");
    }

    // Take a TLX_VALUE_STORE=0 checkpoint and refuse recovering with TLX_VALUE_STORE=1.
    let md_off = dir.child_path("md-off");
    let r = run_spec(
        dir.path(),
        "Store",
        &["-workers", "1", "-compile", "-metadir", md_off.to_str().unwrap()],
        &[("TLX_VALUE_STORE", "0"), ("TLX_PRERUN_REUSE", "0"), ("TLX_CHECKPOINT_STATES", "300"), ("TLX_CHECKPOINT_ABORT", "1")],
    );
    assert_eq!(r.code, 134, "{}", r.text());
    assert!(!md_off.join("checkpoint/model-store").exists());
    let out =
        run_spec(dir.path(), "Store", &["-workers", "1", "-compile", "-recover", md_off.to_str().unwrap()], &[("TLX_VALUE_STORE", "1")]);
    let text = out.text();
    assert_ne!(out.code, 0, "{text}");
    assert!(text.contains("TLX_VALUE_STORE=0") && text.contains("TLX_VALUE_STORE=1"), "{text}");

    // Flipping a byte inside model-store is rejected cleanly (no panic).
    let store_path = md_on.join("checkpoint/model-store");
    let mut data = std::fs::read(&store_path).unwrap();
    let mid = data.len() / 2;
    data[mid] ^= 0xff;
    std::fs::write(&store_path, &data).unwrap();
    let out =
        run_spec(dir.path(), "Store", &["-workers", "1", "-compile", "-recover", md_on.to_str().unwrap()], &[("TLX_VALUE_STORE", "1")]);
    let text = out.text();
    assert_ne!(out.code, 0, "{text}");
    assert!(!text.contains("panicked"), "corrupt model-store panicked:\n{text}");
    assert!(text.contains("checksum") || text.contains("corrupt"), "{text}");
}

/// 64-bit timestamp window (`> IMM_INT`) stored as an interval value
/// (iterated post-recovery in both a late invariant and a late action choice)
/// and as an interval-backed function `[j \in StartNs..EndNs |-> TRUE]` inside
/// a value-store bag: checkpoints committed by the writer must recover cleanly
/// in a fresh process to the exact model-checking counts.
#[test]
fn recovery_preserves_64bit_interval_bounds_and_interval_function_keys() {
    let base_env = [("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0")];
    let ck_env = [
        ("TLX_VALUE_STORE", "1"),
        ("TLX_PRERUN", "10"),
        ("TLX_PRERUN_REUSE", "0"),
        ("TLX_CHECKPOINT_STATES", "55"),
        ("TLX_CHECKPOINT_ABORT", "1"),
    ];

    let interval_inv_spec = r#"---- MODULE WindowBag ----
EXTENDS Naturals, Sequences, TLC
CONSTANTS StartNs, EndNs
VARIABLES bag, n
K(i) == [id |-> i, log |-> <<i>>]
Window == StartNs..EndNs
Init == bag = (K(0) :> Window) /\ n = 0
Next == n < 80 /\ bag' = bag @@ (K(n + 1) :> Window) /\ n' = n + 1
Inv == n < 60 \/ (\E t \in bag[K(0)] : t = EndNs)
====
"#;
    let interval_inv_cfg = "CONSTANTS StartNs = 1735689600000000000\n          EndNs = 1735689600000000003\nINIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";

    let interval_fcn_spec = r#"---- MODULE WindowBag ----
EXTENDS Naturals, Sequences, TLC
CONSTANTS StartNs, EndNs
VARIABLES bag, n
K(i) == [id |-> i, log |-> <<i>>]
Window == [j \in StartNs..EndNs |-> TRUE]
Init == bag = (K(0) :> Window) /\ n = 0
Next == n < 80 /\ bag' = bag @@ (K(n + 1) :> Window) /\ n' = n + 1
====
"#;
    let interval_fcn_cfg =
        "CONSTANTS StartNs = 1735689600000000000\n          EndNs = 1735689600000000003\nINIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";

    let interval_choice_spec = r#"---- MODULE WindowChoice ----
EXTENDS Naturals, Sequences, TLC
CONSTANTS StartNs, EndNs
VARIABLES bag, n, sample
K(i) == [id |-> i, log |-> <<i>>]
Window == StartNs..EndNs
Init == bag = (K(0) :> Window) /\ n = 0 /\ sample = 0
Next ==
    /\ n < 80
    /\ bag' = bag @@ (K(n + 1) :> Window)
    /\ n' = n + 1
    /\ IF n = 60 THEN sample' \in bag[K(0)] ELSE sample' = sample
====
"#;

    let counts_81 =
        ["81 states generated, 81 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 81."];
    let counts_141 =
        ["141 states generated, 141 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 81."];

    let cases: &[(&str, &str, &str, &str, [&str; 2])] = &[
        ("interval-inv", "WindowBag", interval_inv_spec, interval_inv_cfg, counts_81),
        ("interval-fcn", "WindowBag", interval_fcn_spec, interval_fcn_cfg, counts_81),
        ("interval-choice", "WindowChoice", interval_choice_spec, interval_fcn_cfg, counts_141),
    ];

    for &(label, module, spec, cfg, want_counts) in cases {
        let dir = TempDir::with_spec(&format!("value-store-64bit-{label}"), spec, cfg);
        let want = run_spec(dir.path(), module, &["-workers", "1", "-compile", "-tlc"], &base_env);
        assert_eq!(want.code, 0, "{label}:\n{}", want.text());
        assert_eq!(counts(&want.text()), want_counts, "{label}:\n{}", want.text());

        let md = dir.child_path("md");
        let ck = run_spec(dir.path(), module, &["-workers", "1", "-compile", "-tlc", "-metadir", md.to_str().unwrap()], &ck_env);
        assert_eq!(ck.code, 134, "{label}:\n{}", ck.text());
        assert!(md.join("checkpoint/model-store").is_file(), "{label}: missing model-store");

        let rec = run_spec(dir.path(), module, &["-workers", "1", "-compile", "-tlc", "-recover", md.to_str().unwrap()], &base_env);
        assert_eq!(rec.code, 0, "{label}:\n{}", rec.text());
        assert_eq!(counts(&rec.text()), want_counts, "{label}:\n{}", rec.text());
        assert!(!md.exists(), "{label}: metadir should be cleaned up");
    }
}
