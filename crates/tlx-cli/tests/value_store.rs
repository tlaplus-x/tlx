//! The experimental value store (`TLX_VALUE_STORE`, docs/configuration.md):
//! its byte budget (the run's `-maxmem`, never a fraction of it) is a hard
//! limit, and runs with the store on take both default and explicit
//! checkpoints (`model-store`) and recover cleanly with identical results.

use std::path::Path;

use tlx_testkit::cli::counts;
use tlx_testkit::TempDir;

/// A bag keyed by records with a sequence field (a `Dyn` shape, so a value
/// store slot) growing by one key per step: every state's bag is a new
/// node, so cumulative allocations grow quadratically while the live
/// frontier is a single state (exercising multi-level GC reclamation).
const SPEC: &str = r#"---- MODULE Store ----
EXTENDS Naturals, Sequences, TLC
VARIABLES bag, n
K(i) == [id |-> i, log |-> <<i>>]
Init == bag = (K(0) :> 0) /\ n = 0
Next == n < 1000 /\ bag' = bag @@ (K(n + 1) :> n) /\ n' = n + 1
====
"#;
const CFG: &str = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";

/// A bag spec whose level-251 frontier holds 1,500 distinct 252-key bags
/// simultaneously (~6.5 MiB of live frontier nodes). Even after live-root
/// GC reclaims earlier levels and drops the archive, the live frontier
/// exceeds `-maxmem 4M`, while `-maxmem 32M` completes all 1,751 states.
const WIDE_SPEC: &str = r#"---- MODULE WideStore ----
EXTENDS Naturals, Sequences, TLC
VARIABLES bag, n, branch
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ branch = 0
Next == \/ n < 250 /\ bag' = bag @@ (K(n + 1) :> n) /\ n' = n + 1 /\ branch' = 0
        \/ n = 250 /\ branch = 0 /\ \E b \in 1..1500 :
             bag' = bag @@ (K(1000 + b) :> b) /\ n' = 251 /\ branch' = b
====
"#;
const WIDE_COUNTS: [&str; 2] =
    ["1751 states generated, 1751 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 252."];

/// Mid-level transient churn spec: steps 0..120 build a 121-key bag, step 120
/// fans out to 64 parallel tasks at level 121, step 121 performs 6,400
/// `bag' = bag @@ (...)` merges inside ONE single level (~14.5 MiB cumulative
/// transient `Store` nodes, ~227 KiB per task) filtered by `CONSTRAINT Bound`
/// down to 4 live states, and step 122 reuses `ConstBag` after mid-level GC.
const MID_CHURN_SPEC: &str = r#"---- MODULE MidChurn ----
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
const MID_CHURN_CFG: &str = "INIT Init\nNEXT Next\nCONSTRAINT Bound\nCHECK_DEADLOCK FALSE\n";
const MID_CHURN_COUNTS: [&str; 2] =
    ["6589 states generated, 193 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 124."];

/// Churn spec combining VIEW, SYMMETRY, DOMAIN, 64-bit interval iteration
/// caches, and a compile-time constant `Ref` value under repeated GC cycles.
const CHURN_VIEW_SYM_SPEC: &str = r#"---- MODULE ChurnViewSym ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS P, StartNs, EndNs
VARIABLES bag, p, n, sample
K(i, owner) == [id |-> i, owner |-> owner, log |-> <<i, owner>>]
Window == StartNs..EndNs
CanonP == CHOOSE x \in P : TRUE
ConstBag == (K(0, CanonP) :> Window)
Init == bag = ConstBag /\ p \in P /\ n = 0 /\ sample = 0
Next == /\ n < 120
        /\ \E q \in P :
             \E j \in 1..50 :
               /\ bag' = bag @@ (K(n * 100 + j, q) :> Window)
               /\ p' = q
               /\ n' = n + 1
               /\ sample' = IF n = 60 THEN CHOOSE t \in bag[K(0, CanonP)] : t = EndNs ELSE sample
View == <<n, p, sample, Cardinality(DOMAIN bag), bag[K(0, CanonP)]>>
Sym == Permutations(P)
Inv == (\E t \in bag[K(0, CanonP)] : t = EndNs) /\ (n <= 60 \/ sample = EndNs)
====
"#;
const CHURN_VIEW_SYM_CFG: &str = "CONSTANTS P = {p1, p2}\n          StartNs = 1735689600000000000\n          EndNs = 1735689600000000003\nINIT Init\nNEXT Next\nVIEW View\nSYMMETRY Sym\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";

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
    // 1. Live frontier genuinely exceeding 4 MiB stops cleanly with the budget error.
    let wide = TempDir::with_spec("value-store-wide-budget", WIDE_SPEC, CFG);
    let out = run_spec(wide.path(), "WideStore", &["-workers", "1", "-compile", "-maxmem", "4M"], &[("TLX_VALUE_STORE", "1")]);
    let text = out.text();
    assert_ne!(out.code, 0, "{text}");
    assert!(text.contains("the value store (TLX_VALUE_STORE) exceeded its budget of 4 MiB"), "{text}");
    assert!(text.contains("turn the store off (TLX_VALUE_STORE=0)"), "{text}");
    // Without the store the run completes in the same memory budget, and
    // with the default budget the store holds it.
    let out = run_spec(wide.path(), "WideStore", &["-workers", "1", "-compile", "-maxmem", "4M"], &[("TLX_VALUE_STORE", "0")]);
    assert_eq!(counts(&out.text()), WIDE_COUNTS, "{}", out.text());
    let out = run_spec(wide.path(), "WideStore", &["-workers", "1", "-compile"], &[("TLX_VALUE_STORE", "1")]);
    assert_eq!(counts(&out.text()), WIDE_COUNTS, "{}", out.text());

    // 2. Linear bag churn (>10 MiB cumulative, 1-state live frontier) completes
    //    comfortably inside -maxmem 1M (>= 5x churn) via safepoint reclamation.
    let dir = TempDir::with_spec("value-store-churn-budget", SPEC, CFG);
    let out = check(&dir, "1", &["-maxmem", "1M", "-stats"]);
    let text = out.text();
    assert_eq!(out.code, 0, "{text}");
    assert_eq!(counts(&text), COUNTS, "{text}");
    assert!(text.contains("value store GC cycles"), "expected GC stats in -stats output:\n{text}");
}

#[test]
fn store_exhaustion_preserves_last_checkpoint_for_larger_budget_recovery() {
    let dir = TempDir::with_spec("value-store-exhaust-keep", WIDE_SPEC, CFG);

    // Case 1: recover a 150-state checkpoint under a 4 MiB budget (store loads,
    // then fills when the live level-251 frontier exceeds 4 MiB). The checkpoint
    // must be preserved so a subsequent recovery with 32 MiB finishes all 1,751 states.
    let md1 = dir.child_path("md-recovered-exhaust");
    let ck = run_spec(
        dir.path(),
        "WideStore",
        &["-workers", "1", "-compile", "-tlc", "-metadir", md1.to_str().unwrap()],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN_REUSE", "0"), ("TLX_CHECKPOINT_STATES", "150"), ("TLX_CHECKPOINT_ABORT", "1")],
    );
    assert_eq!(ck.code, 134, "{}", ck.text());
    assert!(md1.join("checkpoint/model-store").is_file());

    let exhausted = run_spec(
        dir.path(),
        "WideStore",
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
        "WideStore",
        &["-workers", "1", "-compile", "-tlc", "-maxmem", "32M", "-recover", md1.to_str().unwrap()],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN_REUSE", "0")],
    );
    assert_eq!(resumed.code, 0, "{}", resumed.text());
    assert_eq!(counts(&resumed.text()), WIDE_COUNTS, "{}", resumed.text());
    assert!(!md1.exists(), "completed recovery should clean up metadir");

    // Case 2: a fresh run takes a checkpoint at 150 states under -maxmem 4M,
    // keeps going until the live frontier fills the store, preserves that checkpoint,
    // and a recovery with -maxmem 32M finishes all 1,751 states.
    let md2 = dir.child_path("md-fresh-exhaust");
    let fresh_exhaust = run_spec(
        dir.path(),
        "WideStore",
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
        "WideStore",
        &["-workers", "1", "-compile", "-tlc", "-maxmem", "32M", "-recover", md2.to_str().unwrap()],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN_REUSE", "0")],
    );
    assert_eq!(resumed2.code, 0, "{}", resumed2.text());
    assert_eq!(counts(&resumed2.text()), WIDE_COUNTS, "{}", resumed2.text());
    assert!(!md2.exists(), "completed recovery should clean up metadir");

    // Case 3: recovering a 25-state checkpoint with a short pre-run triggers a
    // layout-miss restart before the store fills at -maxmem 4M. The committed
    // checkpoint must survive the intermediate layout restart so retrying with
    // -maxmem 32M completes all 1,751 states and cleans up on terminal success.
    let md3 = dir.child_path("md-restart-exhaust");
    let ck3 = run_spec(
        dir.path(),
        "WideStore",
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
        "WideStore",
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
        "WideStore",
        &["-workers", "1", "-compile", "-tlc", "-maxmem", "32M", "-recover", md3.to_str().unwrap()],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0")],
    );
    assert_eq!(resumed3.code, 0, "{}", resumed3.text());
    assert_eq!(counts(&resumed3.text()), WIDE_COUNTS, "{}", resumed3.text());
    assert!(!md3.exists(), "completed recovery after layout restart should clean up metadir");

    // Case 4: after a layout-miss restart, the widened attempt can still take
    // and replace the checkpoint; a subsequent store exhaustion preserves that
    // replacement checkpoint, and recovery resumes from the widened attempt.
    let md4 = dir.child_path("md-restart-replace");
    let ck4 = run_spec(
        dir.path(),
        "WideStore",
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
        "WideStore",
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
        "WideStore",
        &["-workers", "1", "-compile", "-tlc", "-maxmem", "32M", "-recover", md4.to_str().unwrap()],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0")],
    );
    let text = resumed4.text();
    assert_eq!(resumed4.code, 0, "{text}");
    assert!(
        text.contains("recovering with the shapes of attempt ") && !text.contains("recovering with the shapes of attempt 0"),
        "expected replacement checkpoint from a widened attempt (> 0):\n{text}"
    );
    assert_eq!(counts(&text), WIDE_COUNTS, "{text}");
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

/// Safepoint reclamation across closure IR, C, and JIT backends on both
/// multi-level frontier churn (`Store`) and mid-level transient churn
/// (`MidChurn`, single- and multi-worker, with `TLX_PARANOID=1`), plus
/// checkpoint/recovery across multiple GC cycles with VIEW, SYMMETRY,
/// DOMAIN, 64-bit interval caches, and pinned constant `Ref` values.
#[test]
fn safepoint_gc_churn_across_backends_workers_paranoid_and_recovery() {
    let backends: [(&str, &[(&str, &str)]); 3] =
        [("closure", &[("TLX_NO_NATIVE", "1")]), ("C", &[("TLX_JIT", "0"), ("TLX_NATIVE_SYNC", "1")]), ("JIT", &[("TLX_JIT", "1")])];

    // 1. Multi-level frontier churn (> 10 MiB cumulative under -maxmem 1M) across all 3 backends.
    let dir_multi = TempDir::with_spec("value-store-gc-multi", SPEC, CFG);
    for (label, extra) in backends {
        let mut env = vec![("TLX_VALUE_STORE", "1"), ("TLX_PRERUN_REUSE", "0")];
        env.extend_from_slice(extra);
        let out = run_spec(dir_multi.path(), "Store", &["-workers", "1", "-compile", "-maxmem", "1M", "-stats"], &env);
        let text = out.text();
        assert_eq!(out.code, 0, "multi {label}:\n{text}");
        assert_eq!(counts(&text), COUNTS, "multi {label}:\n{text}");
        assert!(text.contains("value store GC cycles"), "multi {label}: expected GC stats:\n{text}");
    }

    // 2. Mid-level transient churn (single- and 4-worker) across all 3 backends + TLX_PARANOID=1.
    let dir_mid = TempDir::with_spec("value-store-gc-mid", MID_CHURN_SPEC, MID_CHURN_CFG);
    for (label, extra) in backends {
        for workers in ["1", "4"] {
            let mut env = vec![("TLX_VALUE_STORE", "1"), ("TLX_PRERUN_REUSE", "0")];
            if workers == "1" {
                env.push(("TLX_PARANOID", "1"));
            }
            env.extend_from_slice(extra);
            let out = run_spec(dir_mid.path(), "MidChurn", &["-workers", workers, "-compile", "-maxmem", "1M", "-stats"], &env);
            let text = out.text();
            assert_eq!(out.code, 0, "mid {label} w={workers}:\n{text}");
            assert_eq!(counts(&text), MID_CHURN_COUNTS, "mid {label} w={workers}:\n{text}");
            assert!(text.contains("value store GC cycles"), "mid {label} w={workers}: expected GC stats:\n{text}");
        }
    }

    // 3. Checkpoint + recovery across multiple GC cycles with VIEW, SYMMETRY,
    //    DOMAIN, 64-bit interval caches, and pinned constant `Ref` values.
    let dir_vs = TempDir::with_spec("value-store-gc-viewsym", CHURN_VIEW_SYM_SPEC, CHURN_VIEW_SYM_CFG);
    let interp = run_spec(dir_vs.path(), "ChurnViewSym", &["-workers", "1", "-tlc"], &[]);
    let interp_text = interp.text();
    assert_eq!(interp.code, 0, "interp:\n{interp_text}");
    let want_vs = counts(&interp_text);

    for workers in ["1", "2"] {
        let md = dir_vs.child_path(&format!("md-vs-gc-w{workers}"));
        let ck1 = run_spec(
            dir_vs.path(),
            "ChurnViewSym",
            &["-workers", workers, "-compile", "-tlc", "-maxmem", "1M", "-stats", "-metadir", md.to_str().unwrap()],
            &[
                ("TLX_VALUE_STORE", "1"),
                ("TLX_PRERUN_REUSE", "0"),
                ("TLX_PARANOID", "1"),
                ("TLX_CHECKPOINT_STATES", "15"),
                ("TLX_CHECKPOINT_ABORT", "1"),
            ],
        );
        assert_eq!(ck1.code, 134, "ck1 w={workers}:\n{}", ck1.text());
        assert!(md.join("checkpoint/model-store").is_file(), "ck1 w={workers}: missing model-store");

        // Second checkpoint after recovery (verifies incremental checkpointing across GC cycles).
        let ck2 = run_spec(
            dir_vs.path(),
            "ChurnViewSym",
            &["-workers", workers, "-compile", "-tlc", "-maxmem", "1M", "-stats", "-recover", md.to_str().unwrap()],
            &[
                ("TLX_VALUE_STORE", "1"),
                ("TLX_PRERUN_REUSE", "0"),
                ("TLX_PARANOID", "1"),
                ("TLX_CHECKPOINT_STATES", "15"),
                ("TLX_CHECKPOINT_ABORT", "1"),
            ],
        );
        assert_eq!(ck2.code, 134, "ck2 w={workers}:\n{}", ck2.text());

        // Final recovery to completion under tight budget + TLX_PARANOID=1.
        let rec = run_spec(
            dir_vs.path(),
            "ChurnViewSym",
            &["-workers", workers, "-compile", "-tlc", "-maxmem", "1M", "-stats", "-recover", md.to_str().unwrap()],
            &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN_REUSE", "0"), ("TLX_PARANOID", "1")],
        );
        let text = rec.text();
        assert_eq!(rec.code, 0, "rec w={workers}:\n{text}");
        assert_eq!(counts(&text), want_vs, "rec w={workers}:\n{text}");
        assert!(text.contains("value store GC cycles"), "rec w={workers}: expected GC stats:\n{text}");
        assert!(!md.exists(), "rec w={workers}: metadir should be cleaned up");
    }
}

/// Regression tests for value-store safepoint GC retry boundaries:
/// 1. First-failure ordering when a later successor's VIEW errors (compiled & interpreted).
/// 2. Counterexample trace replay after GC cycles under a tight budget.
/// 3. Recoverable `StoreFull` during liveness edge atom evaluation preserves the graph.
/// 4. Persistent hard allocation failure drops the layout-miss archive even below 75%.
/// 5. A single action with huge failing-guard intermediates falls back cleanly.
/// 6. Compiled `PrintT` output is committed exactly once across a `VIEW` `StoreFull` retry.
#[test]
fn safepoint_gc_retry_boundaries_and_semantics() {
    // 1. First-failure order (PriorityLate): successor n=241 violates Inv before n=242's VIEW divides by zero.
    const PRIORITY_SPEC: &str = r#"---- MODULE PriorityLate ----
EXTENDS Naturals, Sequences, TLC
VARIABLES bag, n
K(i) == [id |-> i, log |-> <<i>>]
Init == bag = (K(0) :> 0) /\ n = 0
Next == n < 1000 /\ bag' = bag @@ (K(n + 1) :> n) /\ n' \in (IF n = 240 THEN {241, 242} ELSE {n + 1})
Inv == n < 241
V == IF n = 242 THEN 1 \div (242 - n) ELSE n
====
"#;
    const PRIORITY_CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\nVIEW V\n";
    let dir_p = TempDir::with_spec("vs-priority-late", PRIORITY_SPEC, PRIORITY_CFG);
    let interp_p = run_spec(dir_p.path(), "PriorityLate", &["-interp", "-tlc", "-workers", "1"], &[]);
    let interp_p_text = interp_p.text();
    assert_eq!(interp_p.code, 12, "interp:\n{interp_p_text}");
    let want_p = counts(&interp_p_text);
    for (label, extra) in [
        ("closure+nomat", &[("TLX_NO_NATIVE", "1"), ("TLX_NO_MATERIALIZE", "1")][..]),
        ("closure", &[("TLX_NO_NATIVE", "1")][..]),
        ("C", &[("TLX_JIT", "0"), ("TLX_NATIVE_SYNC", "1")][..]),
    ] {
        let mut env = vec![("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0")];
        env.extend_from_slice(extra);
        let out = run_spec(dir_p.path(), "PriorityLate", &["-compile", "-tlc", "-workers", "1", "-maxmem", "32M"], &env);
        let text = out.text();
        assert_eq!(out.code, 12, "PriorityLate {label}:\n{text}");
        assert!(text.contains("Invariant Inv is violated"), "PriorityLate {label}:\n{text}");
        assert!(!text.contains("division by zero"), "PriorityLate {label}:\n{text}");
        assert_eq!(counts(&text), want_p, "PriorityLate {label}:\n{text}");
    }

    // 2. Counterexample replay after GC cycles under -maxmem 1M prints all 161 trace states.
    const REPLAY_SPEC: &str = r#"---- MODULE Replay ----
EXTENDS Naturals, TLC, Sequences
VARIABLES bag, n, tag
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ tag = 1
Next == n < 180 /\ \E j \in 1..100 :
          bag' = ((K(100*n+j) :> j) @@ (K(0) :> 0)) /\ n' = n+1 /\ tag' = j
Bound == tag = 1
Inv == n < 160
====
"#;
    const REPLAY_CFG: &str = "INIT Init\nNEXT Next\nCONSTRAINT Bound\nINVARIANT Inv\n";
    let dir_r = TempDir::with_spec("vs-replay-gc", REPLAY_SPEC, REPLAY_CFG);
    let r_env = [("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0"), ("TLX_NO_NATIVE", "1")];
    let r_big = run_spec(dir_r.path(), "Replay", &["-compile", "-tlc", "-workers", "1", "-maxmem", "8M"], &r_env);
    let r_small = run_spec(dir_r.path(), "Replay", &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M", "-stats"], &r_env);
    assert_eq!(r_big.code, 12, "Replay 8M:\n{}", r_big.text());
    assert_eq!(r_small.code, 12, "Replay 1M:\n{}", r_small.text());
    assert_eq!(counts(&r_small.text()), counts(&r_big.text()), "Replay counts:\n{}", r_small.text());
    assert!(r_small.text().contains("State 161:"), "Replay 1M lost counterexample trace:\n{}", r_small.text());
    assert!(r_small.text().contains("value store GC cycles"), "Replay 1M expected GC:\n{}", r_small.text());

    // 3. Recoverable `StoreFull` during liveness edge atom evaluation preserves the graph (Atom1).
    const ATOM_SPEC: &str = r#"---- MODULE Atom1 ----
EXTENDS FiniteSets, Naturals, Sequences, TLC
VARIABLES bag, n, branch
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ branch = 0
Next == \/ n < 250 /\ bag' = bag @@ (K(n + 1) :> n) /\ n' = n + 1 /\ branch' = 0
        \/ n = 250 /\ branch = 0 /\ \E b \in 1..200 :
             bag' = bag @@ (K(1000 + b) :> b) /\ n' = 251 /\ branch' = b
Eventually == ~[]<><<(DOMAIN bag' = DOMAIN bag)>>_n
====
"#;
    const ATOM_CFG: &str = "INIT Init\nNEXT Next\nPROPERTY Eventually\nCHECK_DEADLOCK FALSE\n";
    let dir_a = TempDir::with_spec("vs-atom-gc", ATOM_SPEC, ATOM_CFG);
    let a_out = run_spec(
        dir_a.path(),
        "Atom1",
        &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M", "-stats"],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0"), ("TLX_NO_NATIVE", "1"), ("TLX_RETAIN_MB", "0")],
    );
    let a_text = a_out.text();
    assert_eq!(a_out.code, 0, "Atom1:\n{a_text}");
    assert_eq!(
        counts(&a_text),
        [
            "451 states generated, 451 distinct states found, 0 states left on queue.",
            "The depth of the complete state graph search is 252."
        ],
        "Atom1:\n{a_text}"
    );
    assert!(a_text.contains("Checking temporal properties for the complete state space with 451"), "Atom1:\n{a_text}");

    // 4. Hard allocation retry drops the layout-miss archive even when post-sweep occupancy <= 75% (Archive).
    const ARCHIVE_SPEC: &str = r#"---- MODULE Archive ----
EXTENDS FiniteSets, Naturals, Sequences, TLC
VARIABLES bag, n, branch
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ branch = 0
Next == \/ n < 250 /\ bag' = bag @@ (K(n + 1) :> n) /\ n' = n + 1 /\ branch' = 0
        \/ n = 250 /\ branch = 0 /\ \E b \in 1..170 :
             bag' = bag @@ (K(1000 + b) :> b) /\ n' = 251 /\ branch' = b
Eventually == <>(Cardinality(DOMAIN (bag @@ (K(9000) :> n))) > 999)
====
"#;
    const ARCHIVE_CFG: &str = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";
    let dir_ar = TempDir::with_spec("vs-archive-drop", ARCHIVE_SPEC, ARCHIVE_CFG);
    let ar_out = run_spec(
        dir_ar.path(),
        "Archive",
        &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M"],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0"), ("TLX_NO_NATIVE", "1")],
    );
    let ar_text = ar_out.text();
    assert_eq!(ar_out.code, 0, "Archive default retain:\n{ar_text}");
    assert_eq!(
        counts(&ar_text),
        [
            "421 states generated, 421 distinct states found, 0 states left on queue.",
            "The depth of the complete state graph search is 252."
        ],
        "Archive default retain:\n{ar_text}"
    );

    // 5. Single action with 4,000 failing-guard transient maps falls back cleanly (Guards).
    const GUARDS_SPEC: &str = r#"---- MODULE Guards ----
EXTENDS FiniteSets, Naturals, Sequences, TLC
VARIABLES bag, n, branch
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ branch = 0
Next == \/ n < 120 /\ bag' = bag @@ (K(n + 1) :> n) /\ n' = n + 1 /\ branch' = 0
        \/ n = 120 /\ \E j \in 1..4000 :
               /\ DOMAIN (bag @@ (K(10000 + j) :> j)) = DOMAIN bag
               /\ bag' = bag /\ n' = 121 /\ branch' = j
====
"#;
    const GUARDS_CFG: &str = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";
    let dir_g = TempDir::with_spec("vs-guards-fallback", GUARDS_SPEC, GUARDS_CFG);
    let g_out = run_spec(
        dir_g.path(),
        "Guards",
        &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M"],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0"), ("TLX_NO_NATIVE", "1"), ("TLX_RETAIN_MB", "0")],
    );
    let g_text = g_out.text();
    assert_eq!(g_out.code, 0, "Guards:\n{g_text}");
    assert_eq!(
        counts(&g_text),
        [
            "121 states generated, 121 distinct states found, 0 states left on queue.",
            "The depth of the complete state graph search is 121."
        ],
        "Guards:\n{g_text}"
    );

    // 6. Printing action (`PrintT`) with a `VIEW` that triggers `StoreFull` GC retries prints each line exactly once.
    const PRINT_VIEW_SPEC: &str = r#"---- MODULE PrintViewGc ----
EXTENDS Naturals, Sequences, TLC
VARIABLES bag, n
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0
Next == n < 280
        /\ PrintT(<<"tick", n>>)
        /\ bag' = bag @@ (K(n + 1) :> n)
        /\ n' = n + 1
V == <<n, bag @@ (K(5000 + n) :> n) @@ (K(6000 + n) :> n) @@ (K(7000 + n) :> n)>>
====
"#;
    const PRINT_VIEW_CFG: &str = "INIT Init\nNEXT Next\nVIEW V\nCHECK_DEADLOCK FALSE\n";
    let dir_pv = TempDir::with_spec("vs-print-view-gc", PRINT_VIEW_SPEC, PRINT_VIEW_CFG);
    let tick_lines = |out: &str| -> Vec<String> {
        let mut ls: Vec<String> = out.lines().filter(|l| l.contains("\"tick\"")).map(str::to_owned).collect();
        ls.sort();
        ls
    };
    let pv_big = run_spec(
        dir_pv.path(),
        "PrintViewGc",
        &["-compile", "-tlc", "-workers", "1", "-maxmem", "32M"],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0"), ("TLX_RETAIN_MB", "0")],
    );
    let pv_big_text = pv_big.text();
    assert_eq!(pv_big.code, 0, "PrintViewGc 32M:\n{pv_big_text}");
    let want_lines = tick_lines(&pv_big_text);
    assert_eq!(want_lines.len(), 280, "expected 280 unique PrintT lines:\n{pv_big_text}");

    for (label, extra) in [
        ("closure", &[("TLX_NO_NATIVE", "1")][..]),
        ("C", &[("TLX_JIT", "0"), ("TLX_NATIVE_SYNC", "1")][..]),
        ("JIT", &[("TLX_JIT", "1")][..]),
    ] {
        let mut env = vec![("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0"), ("TLX_RETAIN_MB", "0")];
        env.extend_from_slice(extra);
        let pv_small = run_spec(dir_pv.path(), "PrintViewGc", &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M", "-stats"], &env);
        let text = pv_small.text();
        assert_eq!(pv_small.code, 0, "PrintViewGc 1M {label}:\n{text}");
        assert_eq!(counts(&text), counts(&pv_big_text), "PrintViewGc 1M {label}:\n{text}");
        assert!(text.contains("value store GC cycles"), "PrintViewGc 1M {label}: expected GC:\n{text}");
        assert_eq!(tick_lines(&text), want_lines, "PrintViewGc 1M {label} duplicated or dropped PrintT output");
    }

    // 7. Per-predicate GC retry (`OnceInvariant`): earlier invariant's `TLCSet` effect is not replayed when a later invariant hits `StoreFull`.
    const ONCE_INV_SPEC: &str = r#"---- MODULE OnceInvariant ----
EXTENDS FiniteSets, Naturals, Sequences, TLC
VARIABLES bag, n, branch
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ branch = 0
Next == \/ n < 250 /\ bag' = bag @@ (K(n + 1) :> n) /\ n' = n + 1 /\ branch' = 0
        \/ n = 250 /\ branch = 0 /\ \E b \in 1..200 :
             bag' = bag @@ (K(1000 + b) :> b) /\ n' = 251 /\ branch' = b
Once == IF n = 250 THEN TLCSet(1, 0) ELSE IF n = 251 THEN TLCGet(1) # branch /\ TLCSet(1, branch) ELSE TRUE
Heavy == n # 251 \/ DOMAIN (bag @@ (K(9000) :> n)) # DOMAIN bag
====
"#;
    const ONCE_INV_CFG: &str = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\nINVARIANTS Once Heavy\n";
    let dir_oi = TempDir::with_spec("vs-once-invariant", ONCE_INV_SPEC, ONCE_INV_CFG);
    let oi_out = run_spec(
        dir_oi.path(),
        "OnceInvariant",
        &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M", "-stats"],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0"), ("TLX_NO_NATIVE", "1"), ("TLX_RETAIN_MB", "0")],
    );
    let oi_text = oi_out.text();
    assert_eq!(oi_out.code, 0, "OnceInvariant 1M:\n{oi_text}");
    assert_eq!(
        counts(&oi_text),
        [
            "451 states generated, 451 distinct states found, 0 states left on queue.",
            "The depth of the complete state graph search is 252."
        ],
        "OnceInvariant 1M:\n{oi_text}"
    );

    // 8. Terminal evaluation error trace replay with default retention under -maxmem 1M (`ErrorTrace`).
    const ERR_TRACE_SPEC: &str = r#"---- MODULE ErrorTrace ----
EXTENDS Naturals, TLC, Sequences
VARIABLES bag, n, tag
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ tag = 1
Next == n < 180 /\ \E j \in 1..100 :
          bag' = ((K(100*n+j) :> j) @@ (K(0) :> 0)) /\ n' = n+1 /\ tag' = j
Bound == tag = 1
Inv == n < 160 \/ Assert(FALSE, "late evaluation error")
====
"#;
    const ERR_TRACE_CFG: &str = "INIT Init\nNEXT Next\nCONSTRAINT Bound\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
    let dir_et = TempDir::with_spec("vs-error-trace", ERR_TRACE_SPEC, ERR_TRACE_CFG);
    let et_env = [("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0"), ("TLX_NO_NATIVE", "1")];
    let et_big = run_spec(dir_et.path(), "ErrorTrace", &["-compile", "-tlc", "-workers", "1", "-maxmem", "8M"], &et_env);
    let et_small = run_spec(dir_et.path(), "ErrorTrace", &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M"], &et_env);
    let et_big_text = et_big.text();
    let et_small_text = et_small.text();
    assert_eq!(et_big.code, 76, "ErrorTrace 8M:\n{et_big_text}");
    assert_eq!(et_small.code, 76, "ErrorTrace 1M:\n{et_small_text}");
    assert_eq!(counts(&et_small_text), counts(&et_big_text), "ErrorTrace counts:\n{et_small_text}");
    assert!(et_small_text.contains("State 161:"), "ErrorTrace 1M with default retention lost trace:\n{et_small_text}");

    // 9. Pre-resume liveness edge reconstruction under -maxmem 1M with default retention (`GraphHolds`).
    const GRAPH_HOLDS_SPEC: &str = r#"---- MODULE GraphHolds ----
EXTENDS Naturals, TLC, Sequences
VARIABLES bag, n, tag
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ tag = 1
Next == n < 180 /\ \E j \in 1..100 :
          bag' = ((K(100*n+j) :> j) @@ (K(0) :> 0)) /\ n' = n+1 /\ tag' = j
Bound == tag = 1
Prop == []<>(n <= 180)
====
"#;
    const GRAPH_HOLDS_CFG: &str = "INIT Init\nNEXT Next\nCONSTRAINT Bound\nPROPERTY Prop\nCHECK_DEADLOCK FALSE\n";
    let dir_gh = TempDir::with_spec("vs-graph-holds", GRAPH_HOLDS_SPEC, GRAPH_HOLDS_CFG);
    let gh_out = run_spec(
        dir_gh.path(),
        "GraphHolds",
        &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M"],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0"), ("TLX_NO_NATIVE", "1")],
    );
    let gh_text = gh_out.text();
    assert_eq!(gh_out.code, 0, "GraphHolds 1M default retain:\n{gh_text}");
    assert!(gh_text.contains("Checking temporal properties for the complete state space with 181"), "GraphHolds 1M:\n{gh_text}");

    // 10. Liveness lasso counterexample replay under -maxmem 1M (`LiveTrace`).
    const LIVE_TRACE_SPEC: &str = r#"---- MODULE LiveTrace ----
EXTENDS Naturals, TLC, Sequences
VARIABLES bag, n, tag
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ tag = 1
Next == n < 180 /\ \E j \in 1..100 :
          bag' = ((K(100*n+j) :> j) @@ (K(0) :> 0)) /\ n' = n+1 /\ tag' = j
Bound == tag = 1
Prop == <>(n = 181)
====
"#;
    const LIVE_TRACE_CFG: &str = "INIT Init\nNEXT Next\nCONSTRAINT Bound\nPROPERTY Prop\nCHECK_DEADLOCK FALSE\n";
    let dir_lt = TempDir::with_spec("vs-live-trace", LIVE_TRACE_SPEC, LIVE_TRACE_CFG);
    let lt_env =
        [("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0"), ("TLX_NO_NATIVE", "1"), ("TLX_RETAIN_MB", "0")];
    let lt_out = run_spec(dir_lt.path(), "LiveTrace", &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M"], &lt_env);
    let lt_text = lt_out.text();
    assert_eq!(lt_out.code, 13, "LiveTrace 1M:\n{lt_text}");
    assert!(lt_text.contains("Temporal property Prop was violated"), "LiveTrace 1M:\n{lt_text}");
    assert!(lt_text.contains("State 181:"), "LiveTrace 1M lost lasso states:\n{lt_text}");

    // 11. First terminal Init violation stops enumeration before a later Init state overflows the store (`InitFirst`).
    const INIT_FIRST_SPEC: &str = r#"---- MODULE InitFirst ----
EXTENDS Naturals, TLC
VARIABLES bag, n
Init == /\ n \in 1..12
        /\ bag = ([id |-> n, log |-> [j \in 1..n |-> j+n]] :> [i \in 1..(IF n < 12 THEN 1 ELSE 150000) |-> i+n])
Next == /\ bag' = bag /\ n' = n
Inv == n # 1
====
"#;
    const INIT_FIRST_CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
    let dir_if = TempDir::with_spec("vs-init-first", INIT_FIRST_SPEC, INIT_FIRST_CFG);
    let if_out = run_spec(
        dir_if.path(),
        "InitFirst",
        &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M"],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0"), ("TLX_NO_NATIVE", "1")],
    );
    let if_text = if_out.text();
    assert_eq!(if_out.code, 12, "InitFirst 1M:\n{if_text}");
    assert!(if_text.contains("Invariant Inv is violated"), "InitFirst 1M:\n{if_text}");
    assert!(!if_text.contains("value store exceeded"), "InitFirst 1M must not latch later Init StoreFull:\n{if_text}");

    // 12. Safety/terminal-error trace survives secondary `find_error` liveness recheck under -maxmem 1M (`InvariantLive` / `ErrorLive`).
    const INV_LIVE_SPEC: &str = r#"---- MODULE InvariantLive ----
EXTENDS Naturals, TLC, Sequences
VARIABLES bag, n, tag
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ tag = 1
Next == n < 180 /\ \E j \in 1..100 :
          bag' = ((K(100*n+j) :> j) @@ (K(0) :> 0)) /\ n' = n+1 /\ tag' = j
Bound == tag = 1
Inv == n < 160
Prop == []<>(n <= 180)
====
"#;
    const INV_LIVE_CFG: &str = "INIT Init\nNEXT Next\nCONSTRAINT Bound\nINVARIANT Inv\nPROPERTY Prop\nCHECK_DEADLOCK FALSE\n";
    const ERR_LIVE_SPEC: &str = r#"---- MODULE ErrorLive ----
EXTENDS Naturals, TLC, Sequences
VARIABLES bag, n, tag
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ tag = 1
Next == n < 180 /\ \E j \in 1..100 :
          bag' = ((K(100*n+j) :> j) @@ (K(0) :> 0)) /\ n' = n+1 /\ tag' = j
Bound == tag = 1
Inv == n < 160 \/ Assert(FALSE, "late evaluation error")
Prop == []<>(n <= 180)
====
"#;
    let base_env = [("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0"), ("TLX_NO_NATIVE", "1")];
    let dir_il = TempDir::with_spec("vs-inv-live", INV_LIVE_SPEC, INV_LIVE_CFG);
    let il_out = run_spec(dir_il.path(), "InvariantLive", &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M"], &base_env);
    let il_text = il_out.text();
    assert_eq!(il_out.code, 12, "InvariantLive 1M:\n{il_text}");
    assert!(il_text.contains("State 161:"), "InvariantLive 1M lost trace after liveness recheck:\n{il_text}");

    let dir_el = TempDir::with_spec("vs-err-live", ERR_LIVE_SPEC, INV_LIVE_CFG);
    let el_out = run_spec(dir_el.path(), "ErrorLive", &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M"], &base_env);
    let el_text = el_out.text();
    assert_eq!(el_out.code, 76, "ErrorLive 1M:\n{el_text}");
    assert!(el_text.contains("State 161:"), "ErrorLive 1M lost trace after liveness recheck:\n{el_text}");

    // 13. Concrete liveness under VIEW with high transient churn completes and replays counterexamples under -maxmem 1M (`ViewChurn`).
    const VIEW_CHURN_SPEC: &str = r#"---- MODULE ViewChurn ----
EXTENDS Naturals, TLC, Sequences
VARIABLES bag, n, tag
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ tag = 1
Next == n < 45 /\ \E j \in 1..100 :
          bag' = ((K(100*n+j) :> j) @@ (K(0) :> 0)) /\ n' = n+1 /\ tag' = j
Bound == tag = 1
Prop == []<>(n <= 45)
FailProp == <>(n = 46)
V == n
====
"#;
    const VIEW_CHURN_CFG: &str = "INIT Init\nNEXT Next\nCONSTRAINT Bound\nPROPERTY Prop\nVIEW V\nCHECK_DEADLOCK FALSE\n";
    const VIEW_CHURN_FAIL_CFG: &str = "INIT Init\nNEXT Next\nCONSTRAINT Bound\nPROPERTY FailProp\nVIEW V\nCHECK_DEADLOCK FALSE\n";
    let dir_vc = TempDir::with_spec("vs-view-churn", VIEW_CHURN_SPEC, VIEW_CHURN_CFG);
    let vc_env =
        [("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0"), ("TLX_NO_NATIVE", "1"), ("TLX_RETAIN_MB", "0")];
    let vc_out = run_spec(dir_vc.path(), "ViewChurn", &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M", "-stats"], &vc_env);
    let vc_text = vc_out.text();
    assert_eq!(vc_out.code, 0, "ViewChurn 1M:\n{vc_text}");
    assert!(vc_text.contains("46 distinct states found"), "ViewChurn 1M:\n{vc_text}");

    let dir_vcf = TempDir::with_spec("vs-view-churn-fail", VIEW_CHURN_SPEC, VIEW_CHURN_FAIL_CFG);
    let vcf_out = run_spec(dir_vcf.path(), "ViewChurn", &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M"], &vc_env);
    let vcf_text = vcf_out.text();
    assert_eq!(vcf_out.code, 13, "ViewChurnFail 1M:\n{vcf_text}");
    assert!(vcf_text.contains("Temporal property FailProp was violated"), "ViewChurnFail 1M:\n{vcf_text}");
    assert!(vcf_text.contains("State 46:"), "ViewChurnFail 1M lost counterexample:\n{vcf_text}");

    // 14. Optional layout-miss archive migration recovers cleanly from `StoreFull` and restarts from scratch (`Migration`).
    const MIGRATION_SPEC: &str = r#"---- MODULE Migration ----
EXTENDS Naturals, Sequences, TLC
VARIABLES n, bag
Payload(j) == [i \in 1..160 |-> IF i = 1 THEN j ELSE i]
K(i) == [id |-> i, log |-> <<i, i+1>>]
Init == n = 0 /\ bag = (K(0) :> Payload(0))
Next == n < 901 /\ n' = n+1 /\ bag' = (K(IF n = 900 THEN n ELSE 0) :> Payload(n+1))
====
"#;
    const MIGRATION_CFG: &str = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";
    let dir_mig = TempDir::with_spec("vs-migration", MIGRATION_SPEC, MIGRATION_CFG);
    let mig_out = run_spec(dir_mig.path(), "Migration", &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M"], &base_env);
    let mig_text = mig_out.text();
    assert_eq!(mig_out.code, 0, "Migration 1M default retain:\n{mig_text}");
    assert_eq!(
        counts(&mig_text),
        [
            "902 states generated, 902 distinct states found, 0 states left on queue.",
            "The depth of the complete state graph search is 902."
        ],
        "Migration 1M:\n{mig_text}"
    );

    // 15. Early temporal checking survives a 4,000-key failing-guard action under -maxmem 1M (`EarlyGuard`).
    const EARLY_GUARD_SPEC: &str = r#"---- MODULE EarlyGuard ----
EXTENDS FiniteSets, Naturals, Sequences, TLC
VARIABLES bag, n, branch
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ branch = 0
Next == \/ n < 125 /\ bag' = bag @@ (K(n + 1) :> n) /\ n' = n+1 /\ branch' = 0
        \/ n = 120 /\ \E j \in 1..4000 :
               /\ DOMAIN (bag @@ (K(10000+j) :> j)) = DOMAIN bag
               /\ bag' = bag /\ n' = 121 /\ branch' = j
P == [](n = 121 => [](n < 123))
Inv == n < 125
====
"#;
    const EARLY_GUARD_CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\nPROPERTY P\nCHECK_DEADLOCK FALSE\n";
    let dir_eg = TempDir::with_spec("vs-early-guard", EARLY_GUARD_SPEC, EARLY_GUARD_CFG);
    let eg_out = run_spec(dir_eg.path(), "EarlyGuard", &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M"], &vc_env);
    let eg_text = eg_out.text();
    assert_eq!(eg_out.code, 12, "EarlyGuard 1M:\n{eg_text}");
    assert!(eg_text.contains("Temporal property P was violated"), "EarlyGuard 1M must report P (not Inv):\n{eg_text}");
    assert!(!eg_text.contains("Invariant Inv is violated"), "EarlyGuard 1M:\n{eg_text}");
    assert!(eg_text.contains("125 distinct states found"), "EarlyGuard 1M:\n{eg_text}");

    // 16. Large rejected fan-out (6,000 candidates, 1 admitted) in concrete liveness under VIEW (`WideView` + fairness variant).
    const WIDE_VIEW_SPEC: &str = r#"---- MODULE WideView ----
EXTENDS Naturals, TLC, Sequences
VARIABLES bag, n, tag
vars == <<bag, n, tag>>
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ tag = 1
Next == n < 45 /\ \E j \in 1..(IF n = 44 THEN 6000 ELSE 100) :
          bag' = ((K(100*n+j) :> j) @@ (K(0) :> 0)) /\ n' = n+1 /\ tag' = j
SpecFair == Init /\ [][Next]_vars /\ WF_vars(Next)
Bound == tag = 1
Prop == []<>(n <= 45)
V == n
====
"#;
    const WIDE_VIEW_CFG: &str = "INIT Init\nNEXT Next\nCONSTRAINT Bound\nPROPERTY Prop\nVIEW V\nCHECK_DEADLOCK FALSE\n";
    const WIDE_VIEW_FAIR_CFG: &str = "SPECIFICATION SpecFair\nCONSTRAINT Bound\nPROPERTY Prop\nVIEW V\nCHECK_DEADLOCK FALSE\n";
    let dir_wv = TempDir::with_spec("vs-wide-view", WIDE_VIEW_SPEC, WIDE_VIEW_CFG);
    let wv_out = run_spec(dir_wv.path(), "WideView", &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M"], &vc_env);
    let wv_text = wv_out.text();
    assert_eq!(wv_out.code, 0, "WideView 1M:\n{wv_text}");
    assert!(wv_text.contains("10401 states generated, 46 distinct states found"), "WideView 1M:\n{wv_text}");

    let dir_wvf = TempDir::with_spec("vs-wide-view-fair", WIDE_VIEW_SPEC, WIDE_VIEW_FAIR_CFG);
    let wvf_out = run_spec(dir_wvf.path(), "WideView", &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M"], &vc_env);
    let wvf_text = wvf_out.text();
    assert_eq!(wvf_out.code, 0, "WideViewFair 1M:\n{wvf_text}");
    assert!(wvf_text.contains("10401 states generated, 46 distinct states found"), "WideViewFair 1M:\n{wvf_text}");

    // 17. Large rejected fan-out (5,000 candidates, 1 admitted) in observed early temporal checking (`EarlyChurn`).
    const EARLY_CHURN_SPEC: &str = r#"---- MODULE EarlyChurn ----
EXTENDS Naturals, TLC, Sequences
VARIABLES bag, n, tag
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ tag = 1
Next == n < 45 /\ \E j \in 1..(IF n = 30 THEN 5000 ELSE 100) :
          bag' = ((K(10000*n+j) :> j) @@ (K(0) :> 0)) /\ n' = n+1 /\ tag' = j
Bound == tag = 1
Prop == [](n = 31 => [](n < 34))
Inv == n < 43
====
"#;
    const EARLY_CHURN_CFG: &str = "INIT Init\nNEXT Next\nCONSTRAINT Bound\nINVARIANT Inv\nPROPERTY Prop\nCHECK_DEADLOCK FALSE\n";
    let dir_ec = TempDir::with_spec("vs-early-churn", EARLY_CHURN_SPEC, EARLY_CHURN_CFG);
    let ec_out = run_spec(dir_ec.path(), "EarlyChurn", &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M"], &vc_env);
    let ec_text = ec_out.text();
    assert_eq!(ec_out.code, 12, "EarlyChurn 1M:\n{ec_text}");
    assert!(ec_text.contains("Temporal property Prop was violated"), "EarlyChurn 1M must report Prop (not Inv):\n{ec_text}");
    assert!(!ec_text.contains("Invariant Inv is violated"), "EarlyChurn 1M:\n{ec_text}");
    assert!(ec_text.contains("36 distinct states found"), "EarlyChurn 1M:\n{ec_text}");

    // 18. Generation-ordered stats (`StatCheck`, `CountGuard`) and register effects (`OrderedCheck`)
    //     on constraint-rejected candidates in observed early temporal searches.
    const STAT_CHECK_SPEC: &str = r#"---- MODULE StatCheck ----
EXTENDS Naturals, TLC, Sequences
VARIABLES bag, n, tag
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ tag = 1
Next == n < 45 /\ \E j \in 1..2 :
          bag' = ((K(10000*n+j) :> j) @@ (K(0) :> 0)) /\ n' = n+1 /\ tag' = j
Bound == tag = 1
Prop == [](n = 31 => [](n < 34))
Inv == n < 43
OrderOk == n # 30 \/ tag = 1 \/ TLCGet("stats").generated >= 61
====
"#;
    const ORDERED_CHECK_SPEC: &str = r#"---- MODULE OrderedCheck ----
EXTENDS Naturals, TLC, Sequences
VARIABLES bag, n, tag
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ tag = 1
Next == n < 45 /\ \E j \in 1..2 :
          bag' = ((K(10000*n+j) :> j) @@ (K(0) :> 0)) /\ n' = n+1 /\ tag' = j
Bound == tag = 1
Prop == [](n = 31 => [](n < 34))
Inv == n < 43
OrderOk == IF n = 29 THEN TLCSet(1, 0) ELSE IF n = 30 THEN (IF tag = 1 THEN TLCSet(1, 30) ELSE TLCGet(1) = 30) ELSE TRUE
====
"#;
    const STAT_ORDERED_CFG: &str = "INIT Init\nNEXT Next\nCONSTRAINT Bound\nINVARIANTS Inv OrderOk\nPROPERTY Prop\nCHECK_DEADLOCK FALSE\n";
    for (name, spec) in [("StatCheck", STAT_CHECK_SPEC), ("OrderedCheck", ORDERED_CHECK_SPEC)] {
        let dir = TempDir::with_spec(&format!("vs-{name}"), spec, STAT_ORDERED_CFG);
        let out = run_spec(dir.path(), name, &["-compile", "-tlc", "-workers", "1", "-maxmem", "64M"], &vc_env);
        let text = out.text();
        assert_eq!(out.code, 12, "{name}:\n{text}");
        assert!(text.contains("Temporal property Prop was violated"), "{name} must report Prop (not Inv):\n{text}");
        assert!(!text.contains("Invariant Inv is violated"), "{name}:\n{text}");
        assert!(text.contains("71 states generated, 36 distinct states found"), "{name}:\n{text}");
    }

    // 19. Wide concrete liveness fan-out (`FanCost`, 16,000 admitted successors) stays linear-time (no O(n^2) root copy).
    const FAN_COST_SPEC: &str = r#"---- MODULE FanCost ----
EXTENDS Naturals, TLC, Sequences
VARIABLES bag, n, tag
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ tag = 1
Next == n < 31 /\ \E j \in 1..(IF n = 30 THEN 16000 ELSE 1) :
          bag' = (IF n = 30 THEN bag ELSE ((K(10000*n+j) :> j) @@ (K(0) :> 0))) /\ n' = n+1 /\ tag' = j
Prop == []<>(n < 32)
V == n
====
"#;
    const FAN_COST_CFG: &str = "INIT Init\nNEXT Next\nPROPERTY Prop\nVIEW V\nCHECK_DEADLOCK FALSE\n";
    let dir_fc = TempDir::with_spec("vs-fan-cost", FAN_COST_SPEC, FAN_COST_CFG);
    let t_fc = std::time::Instant::now();
    let fc_out = run_spec(dir_fc.path(), "FanCost", &["-compile", "-tlc", "-workers", "1", "-maxmem", "64M", "-stats"], &vc_env);
    let fc_elapsed = t_fc.elapsed();
    let fc_text = fc_out.text();
    assert_eq!(fc_out.code, 0, "FanCost:\n{fc_text}");
    assert!(fc_text.contains("16031 states generated, 32 distinct states found"), "FanCost:\n{fc_text}");
    assert!(fc_elapsed.as_secs_f64() < 5.0, "FanCost took {fc_elapsed:?} (expected linear time)");

    // 20. Archive-free `Reader` root scanning marks only the unread suffix of compressed/encoded blocks
    //     (`ReaderFrontier` with default segment size + `-spill off`, and `ReaderSuffix` with default retention).
    const READER_FRONTIER_SPEC: &str = r#"---- MODULE ReaderFrontier ----
EXTENDS Naturals, Sequences, TLC
VARIABLES bag, n, lane
K(i) == [id |-> i, log |-> <<i, i+1>>]
Init == bag = (K(0) :> 0) /\ n = 0 /\ lane = 0
Next == \/ n < 220 /\ bag' = bag @@ (K(n+1) :> n) /\ n' = n+1 /\ lane' = 0
        \/ n = 220 /\ \E i \in 1..180 : bag' = bag @@ (K(1000+i) :> i) /\ lane' = i /\ n' = 221
        \/ n = 221 /\ bag' = bag @@ (K(2000+lane) :> lane) /\ UNCHANGED lane /\ n' = 222
====
"#;
    const READER_FRONTIER_CFG: &str = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";
    let dir_rf = TempDir::with_spec("vs-reader-frontier", READER_FRONTIER_SPEC, READER_FRONTIER_CFG);
    let rf_out =
        run_spec(dir_rf.path(), "ReaderFrontier", &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M", "-spill", "off"], &vc_env);
    let rf_text = rf_out.text();
    assert_eq!(rf_out.code, 0, "ReaderFrontier 1M:\n{rf_text}");
    assert!(rf_text.contains("581 states generated, 581 distinct states found"), "ReaderFrontier 1M:\n{rf_text}");

    const READER_SUFFIX_SPEC: &str = r#"---- MODULE ReaderSuffix ----
EXTENDS Naturals, Sequences, TLC
CONSTANTS Width, Items, Delay, FinalItems
VARIABLES bag, n, lane
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Pack(start, count) == [key \in {K(start+i) : i \in 1..count} |-> key.id]
Init == n = 0 /\ lane = 0 /\ bag = (K(0) :> 0)
Next == \/ n < 20 /\ n' = n+1 /\ lane' = 0 /\ bag' = (K(n+1) :> n)
        \/ n = 20 /\ \E j \in 1..Width : n' = 21 /\ lane' = j /\ bag' = Pack(1000*j,Items)
        \/ n = 21 /\ lane = Width - 1 /\ Delay /\ n' = 22 /\ UNCHANGED <<bag, lane>>
        \/ n = (IF Delay THEN 22 ELSE 21) /\ lane = Width - 1 /\ n' = 23 /\ lane' = lane /\ bag' = Pack(1000*(lane+1), FinalItems)
====
"#;
    const READER_SUFFIX_CFG: &str =
        "CONSTANT Width = 200\nCONSTANT Items = 10\nCONSTANT FinalItems = 3000\nCONSTANT Delay = FALSE\nINIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";
    let dir_rs = TempDir::with_spec("vs-reader-suffix", READER_SUFFIX_SPEC, READER_SUFFIX_CFG);
    let rs_out = run_spec(dir_rs.path(), "ReaderSuffix", &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M"], &base_env);
    let rs_text = rs_out.text();
    assert_eq!(rs_out.code, 0, "ReaderSuffix 1M:\n{rs_text}");
    assert!(rs_text.contains("222 distinct states found"), "ReaderSuffix 1M:\n{rs_text}");

    // 21. `-dump` secondary exploration preserves the original safety counterexample trace (`DumpGC`).
    const DUMP_GC_SPEC: &str = r#"---- MODULE DumpGC ----
EXTENDS Naturals, Sequences, TLC
VARIABLES n, bag
K(i) == [id |-> i, log |-> <<i, i + 1>>]
Init == n = 0 /\ bag = (K(0) :> 0)
Next == n < 40 /\ n' = n + 1 /\ bag' = ((K(n+1) :> n+1) @@ (K(0) :> 0))
Inv == n < 35
====
"#;
    const DUMP_GC_CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
    let dir_dg = TempDir::with_spec("vs-dump-gc", DUMP_GC_SPEC, DUMP_GC_CFG);
    let dump_base = dir_dg.child_path("states");
    let dg_out = run_spec(
        dir_dg.path(),
        "DumpGC",
        &["-compile", "-tlc", "-workers", "1", "-maxmem", "64M", "-dump", dump_base.to_str().unwrap()],
        &[("TLX_VALUE_STORE", "1")],
    );
    let dg_text = dg_out.text();
    assert_eq!(dg_out.code, 12, "DumpGC:\n{dg_text}");
    assert!(dg_text.contains("Invariant Inv is violated"), "DumpGC:\n{dg_text}");
    assert!(dg_text.contains("State 36:"), "DumpGC lost counterexample trace:\n{dg_text}");
    assert!(!dg_text.contains("invalid handle"), "DumpGC dereferenced swept handle:\n{dg_text}");
    let dump_file = dir_dg.path().join("states.dump");
    let dump_contents = std::fs::read_to_string(&dump_file).expect("states.dump must be written");
    assert!(dump_contents.contains("State 36:"), "states.dump missing state 36:\n{dump_contents}");
}

/// A one-state frontier whose final step replaces a small bag with a
/// 2,600-entry map while VIEW reads only `n`: completing the winning SYMMETRY
/// permutation on encodings interns a second copy of the map, which does not
/// fit `-maxmem 1M` although the VIEW-only control does.
const ORBIT_SPEC: &str = r#"---- MODULE Orbit ----
EXTENDS Naturals, Sequences, TLC
CONSTANTS P, N
VARIABLES a, n, bag
K(i, q) == [i |-> i, owner |-> q, seq |-> <<i, q>>]
Small(q, i) == (K(i, q) :> i) @@ (K(0, q) :> 0)
Large(q) == [k \in {K(i, q) : i \in 1..N} |-> k.i]
Init == a \in P /\ n = 0 /\ bag = Small(a, 0)
Next == n < 35 /\ a' \in (IF n = 34 THEN P \ {a} ELSE {a}) /\ n' = n + 1 /\ bag' = IF n = 34 THEN Large(a') ELSE Small(a', n + 1)
V == n
Sym == Permutations(P)
====
"#;
const ORBIT_CFG: &str = "CONSTANTS P = {p1,p2}\n          N = 2600\nINIT Init\nNEXT Next\nVIEW V\nSYMMETRY Sym\nCHECK_DEADLOCK FALSE\n";
const ORBIT_COUNTS: [&str; 2] =
    ["37 states generated, 36 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 36."];

/// `ORBIT` with the large bag on a one-state frontier at `n = 61` and a VIEW
/// that reads a counter and a membership test, so store exhaustion would hide
/// the state-63 invariant violation.
const ORBIT_INV_SPEC: &str = r#"---- MODULE OrbitInv ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS P, N
VARIABLES owner, bag, n
K(i,q) == [id |-> i, route |-> <<q,i>>]
Single(i,q) == (K(i,q) :> i)
Batch(q) == [k \in {K(i,q) : i \in 1..N} |-> k.id]
Init == /\ owner \in P /\ n = 0 /\ bag = Single(0,owner)
Next == \/ /\ n < 60 /\ n' = n+1
           /\ owner' \in P /\ bag' = Single(n+1,owner')
        \/ /\ n = 60 /\ n' = 61 /\ owner' = (CHOOSE q \in P : q # owner) /\ bag' = Batch(owner')
        \/ /\ n = 61 /\ Cardinality(DOMAIN bag) = N /\ n' = 62 /\ UNCHANGED owner /\ bag' = Single(0,owner)
View == <<n, K(1,owner) \in DOMAIN bag>>
Sym == Permutations(P)
Inv == n < 62
====
"#;
const ORBIT_INV_CFG: &str =
    "CONSTANTS P = {p1,p2}\n          N = 2500\nINIT Init\nNEXT Next\nVIEW View\nSYMMETRY Sym\nCHECK_DEADLOCK FALSE\nINVARIANT Inv\n";
const ORBIT_INV_COUNTS: [&str; 2] =
    ["124 states generated, 63 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 63."];

/// Regression for `SymView` fingerprinting under persistent store pressure:
/// completing the winning permutation on encodings interns a permuted copy of
/// a large `Ref` node that cannot fit even after reclamation. `sym_view_fp`
/// must instead select and evaluate the representative on decoded values and
/// fingerprint only the VIEW result, at `-maxmem 1M`, with archive retention
/// both enabled and disabled and on every backend.
#[test]
fn sym_view_store_pressure_preserves_large_ref_results() {
    let inv = TempDir::with_spec("value-store-orbit-inv", ORBIT_INV_SPEC, ORBIT_INV_CFG);
    let backends: [(&str, &[(&str, &str)]); 3] =
        [("closure", &[("TLX_NO_NATIVE", "1")]), ("C", &[("TLX_JIT", "0"), ("TLX_NATIVE_SYNC", "1")]), ("JIT", &[("TLX_JIT", "1")])];
    for (label, extra) in backends {
        for (mode, retain) in [("retained", None), ("dropped", Some(("TLX_RETAIN_MB", "0")))] {
            let mut env = vec![("TLX_VALUE_STORE", "1"), ("TLX_PRERUN_REUSE", "0")];
            env.extend_from_slice(extra);
            if let Some(r) = retain {
                env.push(r);
            }
            let out = run_spec(inv.path(), "OrbitInv", &["-workers", "1", "-compile", "-tlc", "-maxmem", "1M"], &env);
            let text = out.text();
            assert_eq!(out.code, 12, "OrbitInv {label} {mode}:\n{text}");
            assert!(text.contains("Invariant Inv is violated"), "OrbitInv {label} {mode}:\n{text}");
            assert!(text.contains("State 63:"), "OrbitInv {label} {mode} lost the counterexample:\n{text}");
            assert_eq!(counts(&text), ORBIT_INV_COUNTS, "OrbitInv {label} {mode}:\n{text}");
        }
    }

    // A VIEW result containing the large `Ref` itself must encode that
    // position as its semantic digest instead of interning the permuted bag.
    let messages = TempDir::with_spec("value-store-orbit-messages", ORBIT_MESSAGES_SPEC, ORBIT_MESSAGES_CFG);
    for (label, extra) in backends {
        for (mode, retain) in [("retained", None), ("dropped", Some(("TLX_RETAIN_MB", "0")))] {
            let mut env = vec![("TLX_VALUE_STORE", "1"), ("TLX_PRERUN_REUSE", "0")];
            env.extend_from_slice(extra);
            if let Some(r) = retain {
                env.push(r);
            }
            let out = run_spec(messages.path(), "OrbitMessages", &["-workers", "1", "-compile", "-tlc", "-maxmem", "1M"], &env);
            let text = out.text();
            assert_eq!(out.code, 12, "OrbitMessages {label} {mode}:\n{text}");
            assert!(text.contains("Invariant Inv is violated"), "OrbitMessages {label} {mode}:\n{text}");
            assert!(text.contains("State 63:"), "OrbitMessages {label} {mode} lost the counterexample:\n{text}");
            assert_eq!(counts(&text), ORBIT_MESSAGES_COUNTS, "OrbitMessages {label} {mode}:\n{text}");
        }
    }

    // The non-violating control must complete at 1 MiB: with SYMMETRY the
    // completed permutation must not force a second copy of the bag.
    let orbit = TempDir::with_spec("value-store-orbit", ORBIT_SPEC, ORBIT_CFG);
    for retain in [None, Some(("TLX_RETAIN_MB", "0"))] {
        let mut env = vec![("TLX_VALUE_STORE", "1"), ("TLX_PRERUN_REUSE", "0"), ("TLX_PARANOID", "1")];
        if let Some(r) = retain {
            env.push(r);
        }
        let out = run_spec(orbit.path(), "Orbit", &["-workers", "1", "-compile", "-tlc", "-maxmem", "1M"], &env);
        assert_eq!(counts(&out.text()), ORBIT_COUNTS, "Orbit {retain:?}:\n{}", out.text());
    }
}

/// `ORBIT` with SYMMETRY only (no VIEW) and `Inv == n < 35`: the orbit
/// fingerprint must not intern the permuted 2,600-entry bag at 1 MiB.
const ORBIT_ONLY_SPEC: &str = r#"---- MODULE OrbitOnly ----
EXTENDS Naturals, Sequences, TLC
CONSTANTS P, N
VARIABLES a, n, bag
K(i,q) == [i |-> i, owner |-> q, seq |-> <<i,q>>]
Small(q,i) == (K(i,q) :> i) @@ (K(0,q) :> 0)
Large(q) == [k \in {K(i,q) : i \in 1..N} |-> k.i]
Init == a \in P /\ n = 0 /\ bag = Small(a,0)
Next == n < 35 /\ a' \in (IF n=34 THEN P \ {a} ELSE {a}) /\ n' = n+1 /\ bag' = IF n=34 THEN Large(a') ELSE Small(a',n+1)
Inv == n < 35
Sym == Permutations(P)
====
"#;
const ORBIT_ONLY_CFG: &str =
    "CONSTANTS P = {p1,p2}\n          N = 2600\nINIT Init\nNEXT Next\nSYMMETRY Sym\nCHECK_DEADLOCK FALSE\nINVARIANT Inv\n";
const ORBIT_ONLY_COUNTS: [&str; 2] =
    ["37 states generated, 36 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 36."];

/// A VIEW whose result contains the large `Ref` bag itself (`<<n, bag>>`): the
/// VIEW fingerprint must encode the bag's semantic digest, not intern a
/// permuted copy of the bag.
const ORBIT_MESSAGES_SPEC: &str = r#"---- MODULE OrbitMessages ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS P, N
VARIABLES owner, bag, n
K(i,q) == [id |-> i, route |-> <<q,i>>]
Single(i,q) == (K(i,q) :> i)
Batch(q) == [k \in {K(i,q) : i \in 1..N} |-> k.id]
Init == /\ owner \in P /\ n = 0 /\ bag = Single(0,owner)
Next == \/ /\ n < 60 /\ n' = n+1
           /\ owner' \in P /\ bag' = Single(n+1,owner')
        \/ /\ n = 60 /\ n' = 61 /\ owner' = (CHOOSE q \in P : q # owner) /\ bag' = Batch(owner')
        \/ /\ n = 61 /\ Cardinality(DOMAIN bag) = N /\ n' = 62 /\ UNCHANGED owner /\ bag' = Single(0,owner)
View == <<n, bag>>
Sym == Permutations(P)
Inv == n < 62
====
"#;
const ORBIT_MESSAGES_CFG: &str =
    "CONSTANTS P = {p1,p2}\n          N = 2500\nINIT Init\nNEXT Next\nVIEW View\nSYMMETRY Sym\nCHECK_DEADLOCK FALSE\nINVARIANT Inv\n";
const ORBIT_MESSAGES_COUNTS: [&str; 2] =
    ["124 states generated, 63 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 63."];

/// A constant 2,500-entry bag of integers outside `VIEW == <<owner,n>>`: its
/// permutation needs no store space, so crossing the pressure watermark must
/// not send every fingerprint through decoded orbit selection.
const STABLE_BAG_SPEC: &str = r#"---- MODULE StableBag ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS P, N
VARIABLES owner, bag, n
K(i,q) == [id |-> i, route |-> <<i,i+1>>]
Single(i,q) == (K(i,q) :> i)
Batch(q) == [k \in {K(i,q) : i \in 1..N} |-> k.id]
Init == /\ owner \in P /\ n = 0 /\ bag = Single(0,owner)
Next == \/ /\ n < 60 /\ n' = n+1
           /\ owner' \in P /\ bag' = Single(n+1,owner')
        \/ /\ n = 60 /\ n' = 61 /\ owner' = (CHOOSE q \in P : q # owner) /\ bag' = Batch(owner')
        \/ /\ n >= 61 /\ n < 661 /\ n' = n + 1 /\ owner' \in P /\ UNCHANGED bag
View == <<owner,n>>
Sym == Permutations(P)
Inv == n < 62
====
"#;
const STABLE_BAG_CFG: &str =
    "CONSTANTS P = {p1,p2}\n          N = 2500\nINIT Init\nNEXT Next\nVIEW View\nSYMMETRY Sym\nCHECK_DEADLOCK FALSE\n";
const STABLE_BAG_COUNTS: [&str; 2] =
    ["1323 states generated, 662 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 662."];

/// Regression for `Fingerprint::Symmetry` under store pressure: permuting a
/// large `Ref` variable must use its semantic digest from the decoded value
/// instead of interning the image. `ORBIT_ONLY` keeps the counterexample
/// reachable at 1 MiB; `STABLE_BAG` keeps the fast path for a permutation that
/// needs no extra store space.
#[test]
fn symmetry_store_pressure_preserves_large_ref_results() {
    let only = TempDir::with_spec("value-store-orbit-only", ORBIT_ONLY_SPEC, ORBIT_ONLY_CFG);
    let variants: [(&str, &[(&str, &str)]); 3] = [
        ("closure dropped", &[("TLX_NO_NATIVE", "1"), ("TLX_RETAIN_MB", "0")]),
        ("C retained", &[("TLX_JIT", "0"), ("TLX_NATIVE_SYNC", "1")]),
        ("closure paranoid", &[("TLX_NO_NATIVE", "1"), ("TLX_PARANOID", "1")]),
    ];
    for (label, extra) in variants {
        let mut env = vec![("TLX_VALUE_STORE", "1"), ("TLX_PRERUN_REUSE", "0")];
        env.extend_from_slice(extra);
        let out = run_spec(only.path(), "OrbitOnly", &["-workers", "1", "-compile", "-tlc", "-maxmem", "1M"], &env);
        let text = out.text();
        assert_eq!(out.code, 12, "OrbitOnly {label}:\n{text}");
        assert!(text.contains("Invariant Inv is violated"), "OrbitOnly {label}:\n{text}");
        assert!(text.contains("State 36:"), "OrbitOnly {label} lost the counterexample:\n{text}");
        assert_eq!(counts(&text), ORBIT_ONLY_COUNTS, "OrbitOnly {label}:\n{text}");
    }

    let stable = TempDir::with_spec("value-store-stable-bag", STABLE_BAG_SPEC, STABLE_BAG_CFG);
    let out = run_spec(
        stable.path(),
        "StableBag",
        &["-workers", "1", "-compile", "-tlc", "-maxmem", "1M"],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "100"), ("TLX_NO_NATIVE", "1"), ("TLX_RETAIN_MB", "0")],
    );
    assert_eq!(counts(&out.text()), STABLE_BAG_COUNTS, "StableBag:\n{}", out.text());
}

/// An interval-domain function (`f = [i \in 0..2 |-> i]`) kept outside the
/// stable part of the VIEW. Under store pressure the representative must be
/// permuted with the interpreter's witness-preserving `permute_shared`:
/// rebuilding the unchanged function as an enumerated one turns the `EXCEPT`
/// model-value key from an evaluation error into a successful verification.
const ORBIT_WITNESS_SPEC: &str = r#"---- MODULE OrbitWitness ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS P, N
VARIABLES owner, bag, n, f
K(i,q) == [id |-> i, route |-> <<q,i>>]
Single(i,q) == (K(i,q) :> i)
Batch(q) == [k \in {K(i,q) : i \in 1..N} |-> k.id]
Init == /\ f = [i \in 0..2 |-> i] /\ owner \in P /\ n = 0 /\ bag = Single(0,owner)
Moves == \/ /\ n < 60 /\ n' = n+1
           /\ owner' \in P /\ bag' = Single(n+1,owner')
        \/ /\ n = 60 /\ n' = 61 /\ owner' = (CHOOSE q \in P : q # owner) /\ bag' = Batch(owner')
        \/ /\ n = 61 /\ Cardinality(DOMAIN bag) = N /\ n' = 62 /\ UNCHANGED owner /\ bag' = Single(0,owner)
Next == Moves /\ UNCHANGED f
View == <<n, IF n = 61 THEN [f EXCEPT ![owner] = 17] = f ELSE TRUE>>
Sym == Permutations(P)
Inv == n < 62
====
"#;
const ORBIT_WITNESS_CFG: &str =
    "CONSTANTS P = {p1,p2}\n          N = 2500\nINIT Init\nNEXT Next\nVIEW View\nSYMMETRY Sym\nCHECK_DEADLOCK FALSE\n";
const ORBIT_WITNESS_COUNTS: [&str; 2] =
    ["123 states generated, 61 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 61."];

/// The same model with an enumerated `{0,1,2}` constructor: `EXCEPT` with a
/// model-value key is well-defined there, so the run completes.
const ORBIT_WITNESS_ENUM_SPEC: &str = r#"---- MODULE OrbitWitness ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS P, N
VARIABLES owner, bag, n, f
K(i,q) == [id |-> i, route |-> <<q,i>>]
Single(i,q) == (K(i,q) :> i)
Batch(q) == [k \in {K(i,q) : i \in 1..N} |-> k.id]
Init == /\ f = [i \in {0, 1, 2} |-> i] /\ owner \in P /\ n = 0 /\ bag = Single(0,owner)
Moves == \/ /\ n < 60 /\ n' = n+1
           /\ owner' \in P /\ bag' = Single(n+1,owner')
        \/ /\ n = 60 /\ n' = 61 /\ owner' = (CHOOSE q \in P : q # owner) /\ bag' = Batch(owner')
        \/ /\ n = 61 /\ Cardinality(DOMAIN bag) = N /\ n' = 62 /\ UNCHANGED owner /\ bag' = Single(0,owner)
Next == Moves /\ UNCHANGED f
View == <<n, IF n = 61 THEN [f EXCEPT ![owner] = 17] = f ELSE TRUE>>
Sym == Permutations(P)
Inv == n < 62
====
"#;
const ORBIT_WITNESS_ENUM_CFG: &str =
    "CONSTANTS P = {p1,p2}\n          N = 2500\nINIT Init\nNEXT Next\nVIEW View\nSYMMETRY Sym\nCHECK_DEADLOCK FALSE\n";
const ORBIT_WITNESS_ENUM_COUNTS: [&str; 2] =
    ["124 states generated, 63 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 63."];

/// Regression for the `SymView` pressure path: permuting the representative on
/// decoded values must preserve an unchanged function's domain witness, so
/// `EXCEPT`/application with a model-value key keeps TLC's evaluation error.
#[test]
fn sym_view_store_pressure_preserves_function_domain_witnesses() {
    let witness = TempDir::with_spec("value-store-orbit-witness", ORBIT_WITNESS_SPEC, ORBIT_WITNESS_CFG);
    let backends: [(&str, &[(&str, &str)]); 4] = [
        ("closure", &[("TLX_NO_NATIVE", "1")]),
        ("C", &[("TLX_JIT", "0"), ("TLX_NATIVE_SYNC", "1")]),
        ("JIT", &[("TLX_JIT", "1")]),
        ("closure paranoid", &[("TLX_NO_NATIVE", "1"), ("TLX_PARANOID", "1")]),
    ];
    for (label, extra) in backends {
        let mut env = vec![("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "100"), ("TLX_PRERUN_REUSE", "0")];
        env.extend_from_slice(extra);
        let out = run_spec(witness.path(), "OrbitWitness", &["-workers", "1", "-compile", "-tlc", "-maxmem", "1M"], &env);
        let text = out.text();
        assert_eq!(out.code, 75, "OrbitWitness {label}:\n{text}");
        assert!(
            text.contains("Attempted to apply function with integer domain to the non-integer argument p1"),
            "OrbitWitness {label}:\n{text}"
        );
        assert_eq!(counts(&text), ORBIT_WITNESS_COUNTS, "OrbitWitness {label}:\n{text}");
    }

    let enumerated = TempDir::with_spec("value-store-orbit-witness-enum", ORBIT_WITNESS_ENUM_SPEC, ORBIT_WITNESS_ENUM_CFG);
    let out = run_spec(
        enumerated.path(),
        "OrbitWitness",
        &["-workers", "1", "-compile", "-tlc", "-maxmem", "1M"],
        &[("TLX_VALUE_STORE", "1"), ("TLX_PRERUN", "100"), ("TLX_PRERUN_REUSE", "0"), ("TLX_NO_NATIVE", "1")],
    );
    assert_eq!(counts(&out.text()), ORBIT_WITNESS_ENUM_COUNTS, "OrbitWitness enumerated:\n{}", out.text());
}

/// Regression for value-store exhaustion during post-search replay:
/// 1. Recorded liveness replay exhaustion (`ReplayBudget` and `TraceBudget` /
///    `TraceLive.cfg`) preserves the last committed checkpoint instead of
///    deleting it when BFS completes, and recovering with a larger budget
///    reports the full lasso (exit 13) and cleans up the checkpoint normally.
/// 2. Safety counterexample replay exhaustion (`TraceBudget.cfg` concrete and
///    `TraceView.cfg` VIEW/class replay) keeps the established invariant
///    verdict (exit 12), explains why the trace could not be reconstructed,
///    preserves any committed checkpoint, and replays the full trace upon
///    recovery with a larger budget.
#[test]
fn replay_store_exhaustion_preserves_checkpoints_and_explains_missing_trace() {
    const REPLAY_BUDGET_SPEC: &str = r#"---- MODULE ReplayBudget ----
EXTENDS Naturals, TLC, Sequences
VARIABLES bag,n
K(i) == [id |-> i, log |-> <<i,i+1>>]
Batch(i) == [k \in {K(40*i+j) : j \in 1..40} |-> k.id]
Init == /\ n=0 /\ bag=(K(0) :> 0)
Next == /\ n < 180 /\ n'=n+1 /\ bag'=Batch(n+1)
Prop == []<>(n < 180)
====
"#;
    const REPLAY_BUDGET_CFG: &str = "INIT Init\nNEXT Next\nPROPERTY Prop\nCHECK_DEADLOCK FALSE\n";
    let dir_rb = TempDir::with_spec("value-store-replay-budget", REPLAY_BUDGET_SPEC, REPLAY_BUDGET_CFG);
    let md_rb = dir_rb.path().join("md");
    let rb_env =
        [("TLX_VALUE_STORE", "1"), ("TLX_RETAIN_MB", "0"), ("TLX_NO_NATIVE", "1"), ("TLX_PRERUN", "10"), ("TLX_PRERUN_REUSE", "0")];
    let mut rb_env_ck = rb_env.to_vec();
    rb_env_ck.push(("TLX_CHECKPOINT_STATES", "50"));
    let rb_fail = run_spec(
        dir_rb.path(),
        "ReplayBudget",
        &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M", "-metadir", md_rb.to_str().unwrap()],
        &rb_env_ck,
    );
    let rb_fail_text = rb_fail.text();
    assert_eq!(rb_fail.code, 75, "ReplayBudget 1M:\n{rb_fail_text}");
    assert!(
        rb_fail_text.contains("the value store (TLX_VALUE_STORE) exceeded its budget"),
        "ReplayBudget 1M expected budget error:\n{rb_fail_text}"
    );
    assert!(
        rb_fail_text.contains("recovering the last checkpoint, which is kept"),
        "ReplayBudget 1M expected kept-checkpoint hint:\n{rb_fail_text}"
    );
    assert!(md_rb.join("checkpoint/MANIFEST").is_file(), "ReplayBudget 1M deleted MANIFEST");
    assert!(md_rb.join("checkpoint/model-store").is_file(), "ReplayBudget 1M deleted model-store");

    let rb_rec = run_spec(
        dir_rb.path(),
        "ReplayBudget",
        &["-compile", "-tlc", "-workers", "1", "-maxmem", "64M", "-recover", md_rb.to_str().unwrap()],
        &rb_env,
    );
    let rb_rec_text = rb_rec.text();
    assert_eq!(rb_rec.code, 13, "ReplayBudget 64M recover:\n{rb_rec_text}");
    assert!(rb_rec_text.contains("State 182: Stuttering"), "ReplayBudget 64M recover missing lasso end:\n{rb_rec_text}");
    assert!(!md_rb.join("checkpoint").exists(), "ReplayBudget 64M recover should clean up checkpoint");

    // TraceBudget: 1-state frontier fits in 1 MiB, while holding all 81 trace
    // states live during replay exceeds 1 MiB (for temporal, concrete safety,
    // and VIEW/class safety replay).
    const TRACE_BUDGET_SPEC: &str = r#"---- MODULE TraceBudget ----
EXTENDS Naturals, Sequences, TLC
VARIABLES n, bag
K(i) == [id |-> i, log |-> <<i,i+1>>]
Small(i) == (K(0) :> 0) @@ (K(i) :> i)
Batch(j) == [k \in {K(300*j+i) : i \in 1..300} |-> k.id]
Init == n = 0 /\ bag = Small(0)
Next == n < 80 /\ n' = n+1 /\ bag' = IF n < 25 THEN Small(n+1) ELSE Batch(n+1)
V == n
Prop == <>(n = 81)
Inv == n < 80
====
"#;
    const TRACE_LIVE_CFG: &str = "INIT Init\nNEXT Next\nPROPERTY Prop\nCHECK_DEADLOCK FALSE\n";
    const TRACE_SAFETY_CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
    const TRACE_VIEW_CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\nVIEW V\n";
    let dir_tb = TempDir::with_spec("value-store-trace-budget", TRACE_BUDGET_SPEC, TRACE_SAFETY_CFG);
    std::fs::write(dir_tb.path().join("TraceLive.cfg"), TRACE_LIVE_CFG).unwrap();
    std::fs::write(dir_tb.path().join("TraceView.cfg"), TRACE_VIEW_CFG).unwrap();
    let tb_env = [("TLX_VALUE_STORE", "1"), ("TLX_NO_NATIVE", "1"), ("TLX_RETAIN_MB", "0"), ("TLX_PRERUN", "8"), ("TLX_PRERUN_REUSE", "0")];
    let run_tb = |cfg: &str, args: &[&str], extra: &[(&str, &str)]| {
        let mut cmd = tlx_testkit::tlx!();
        cmd.check("TraceBudget.tla").cfg(cfg).args(args).dir(dir_tb.path());
        for (k, v) in tb_env.iter().chain(extra.iter()) {
            cmd.env(k, v);
        }
        cmd.run()
    };

    // 1. TraceLive.cfg: checkpoint survives a 1 MiB recovery whose temporal replay exhausts the store,
    //    then succeeds on a 64 MiB recovery and cleans up.
    let md_live = dir_tb.path().join("md-live");
    let ck_live = run_tb(
        "TraceLive.cfg",
        &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M", "-metadir", md_live.to_str().unwrap()],
        &[("TLX_CHECKPOINT_STATES", "50"), ("TLX_CHECKPOINT_ABORT", "1")],
    );
    assert_eq!(ck_live.code, 134, "TraceLive abort:\n{}", ck_live.text());
    assert!(md_live.join("checkpoint/MANIFEST").is_file(), "TraceLive missing MANIFEST after commit");
    assert!(md_live.join("checkpoint/model-store").is_file(), "TraceLive missing model-store after commit");

    let live_1m =
        run_tb("TraceLive.cfg", &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M", "-recover", md_live.to_str().unwrap()], &[]);
    let live_1m_text = live_1m.text();
    assert_eq!(live_1m.code, 75, "TraceLive 1M recover:\n{live_1m_text}");
    assert!(
        live_1m_text.contains("the value store (TLX_VALUE_STORE) exceeded its budget"),
        "TraceLive 1M recover expected budget error:\n{live_1m_text}"
    );
    assert!(md_live.join("checkpoint/MANIFEST").is_file(), "TraceLive 1M recover deleted MANIFEST");
    assert!(md_live.join("checkpoint/model-store").is_file(), "TraceLive 1M recover deleted model-store");

    let live_64m =
        run_tb("TraceLive.cfg", &["-compile", "-tlc", "-workers", "1", "-maxmem", "64M", "-recover", md_live.to_str().unwrap()], &[]);
    let live_64m_text = live_64m.text();
    assert_eq!(live_64m.code, 13, "TraceLive 64M recover:\n{live_64m_text}");
    assert!(live_64m_text.contains("State 82: Stuttering"), "TraceLive 64M recover missing lasso end:\n{live_64m_text}");
    assert!(!md_live.join("checkpoint").exists(), "TraceLive 64M recover should clean up checkpoint");

    // 2. TraceBudget.cfg (concrete) & TraceView.cfg (VIEW/class): safety replay exhaustion
    //    reports exit 12 + explains the missing trace + preserves any committed checkpoint,
    //    and recovering at 64 MiB prints all 81 trace states and cleans up.
    for (label, cfg) in [("concrete", "TraceBudget.cfg"), ("view", "TraceView.cfg")] {
        let ctrl = run_tb(cfg, &["-compile", "-tlc", "-workers", "1", "-maxmem", "64M"], &[]);
        let ctrl_text = ctrl.text();
        assert_eq!(ctrl.code, 12, "TraceBudget {label} 64M:\n{ctrl_text}");
        assert!(ctrl_text.contains("State 81:"), "TraceBudget {label} 64M missing full trace:\n{ctrl_text}");
        let want_counts = counts(&ctrl_text);

        // Without checkpoints: exit 12 + explicit trace_note explaining budget exhaustion.
        let no_ck = run_tb(cfg, &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M"], &[]);
        let no_ck_text = no_ck.text();
        assert_eq!(no_ck.code, 12, "TraceBudget {label} 1M:\n{no_ck_text}");
        assert_eq!(counts(&no_ck_text), want_counts, "TraceBudget {label} 1M counts:\n{no_ck_text}");
        assert!(no_ck_text.contains("Invariant Inv is violated."), "TraceBudget {label} 1M:\n{no_ck_text}");
        assert!(
            no_ck_text.contains("trace cannot be reconstructed: the value store (TLX_VALUE_STORE) exceeded its budget"),
            "TraceBudget {label} 1M missing trace diagnostic:\n{no_ck_text}"
        );

        // With checkpoints: exit 12 + trace diagnostic + checkpoint preserved for 64 MiB recovery.
        let md_safe = dir_tb.path().join(format!("md-{label}"));
        let with_ck = run_tb(
            cfg,
            &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M", "-metadir", md_safe.to_str().unwrap()],
            &[("TLX_CHECKPOINT_STATES", "50")],
        );
        let with_ck_text = with_ck.text();
        assert_eq!(with_ck.code, 12, "TraceBudget {label} 1M ck:\n{with_ck_text}");
        assert_eq!(counts(&with_ck_text), want_counts, "TraceBudget {label} 1M ck counts:\n{with_ck_text}");
        assert!(
            with_ck_text.contains("trace cannot be reconstructed: the value store (TLX_VALUE_STORE) exceeded its budget")
                && with_ck_text.contains("recovering the last checkpoint, which is kept"),
            "TraceBudget {label} 1M ck missing trace/checkpoint diagnostic:\n{with_ck_text}"
        );
        assert!(md_safe.join("checkpoint/MANIFEST").is_file(), "TraceBudget {label} 1M ck deleted MANIFEST");
        assert!(md_safe.join("checkpoint/model-store").is_file(), "TraceBudget {label} 1M ck deleted model-store");

        let rec_safe = run_tb(cfg, &["-compile", "-tlc", "-workers", "1", "-maxmem", "64M", "-recover", md_safe.to_str().unwrap()], &[]);
        let rec_safe_text = rec_safe.text();
        assert_eq!(rec_safe.code, 12, "TraceBudget {label} 64M recover:\n{rec_safe_text}");
        assert!(rec_safe_text.contains("State 81:"), "TraceBudget {label} 64M recover missing full trace:\n{rec_safe_text}");
        assert!(!md_safe.join("checkpoint").exists(), "TraceBudget {label} 64M recover should clean up checkpoint");
    }

    // 3. `-dumpTrace`: failed low-budget safety replay must not overwrite an
    //    existing valid counterexample file with an empty trace.
    let dump_path = dir_tb.path().join("trace.json");
    let seed_dump = run_tb(
        "TraceBudget.cfg",
        &["-compile", "-tlc", "-workers", "1", "-maxmem", "64M", "-dumpTrace", "json", dump_path.to_str().unwrap()],
        &[],
    );
    assert_eq!(seed_dump.code, 12, "TraceBudget dump seed:\n{}", seed_dump.text());
    let seeded_bytes = std::fs::read(&dump_path).expect("seeded trace.json");
    assert!(seeded_bytes.len() > 1024, "expected full trace.json, got {} bytes", seeded_bytes.len());

    let low_dump = run_tb(
        "TraceBudget.cfg",
        &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M", "-dumpTrace", "json", dump_path.to_str().unwrap()],
        &[],
    );
    let low_dump_text = low_dump.text();
    assert_eq!(low_dump.code, 12, "TraceBudget low-budget dump:\n{low_dump_text}");
    assert!(
        low_dump_text.contains("trace cannot be reconstructed: the value store (TLX_VALUE_STORE) exceeded its budget"),
        "TraceBudget low-budget dump missing diagnostic:\n{low_dump_text}"
    );
    assert!(!low_dump_text.contains("CounterExample written"), "failed replay must not claim to write trace:\n{low_dump_text}");
    assert_eq!(
        std::fs::read(&dump_path).expect("preserved trace.json"),
        seeded_bytes,
        "failed low-budget replay overwrote existing trace.json"
    );

    // 4. Concrete liveness (`TraceLiveView.cfg` with VIEW V): replay exhaustion
    //    preserves `ErrorKind::StoreFull`, prints the recovery hint, skips any
    //    redundant second search, and keeps the checkpoint for 64 MiB recovery.
    const TRACE_LIVE_VIEW_CFG: &str = "INIT Init\nNEXT Next\nPROPERTY Prop\nCHECK_DEADLOCK FALSE\nVIEW V\n";
    std::fs::write(dir_tb.path().join("TraceLiveView.cfg"), TRACE_LIVE_VIEW_CFG).unwrap();
    let md_lv = dir_tb.path().join("md-live-view");
    let ck_lv = run_tb(
        "TraceLiveView.cfg",
        &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M", "-metadir", md_lv.to_str().unwrap()],
        &[("TLX_CHECKPOINT_STATES", "50"), ("TLX_CHECKPOINT_ABORT", "1")],
    );
    assert_eq!(ck_lv.code, 134, "TraceLiveView abort:\n{}", ck_lv.text());
    let lv_1m = run_tb(
        "TraceLiveView.cfg",
        &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M", "-stats", "-recover", md_lv.to_str().unwrap()],
        &[],
    );
    let lv_1m_text = lv_1m.text();
    assert_eq!(lv_1m.code, 75, "TraceLiveView 1M recover:\n{lv_1m_text}");
    assert!(
        lv_1m_text.contains("the value store (TLX_VALUE_STORE) exceeded its budget")
            && lv_1m_text.contains("recovering the last checkpoint, which is kept"),
        "TraceLiveView 1M recover missing kept-checkpoint hint:\n{lv_1m_text}"
    );
    assert!(!lv_1m_text.contains("liveness: search again"), "TraceLiveView 1M recover launched a redundant second search:\n{lv_1m_text}");
    assert!(md_lv.join("checkpoint/MANIFEST").is_file(), "TraceLiveView 1M deleted MANIFEST");
    assert!(md_lv.join("checkpoint/model-store").is_file(), "TraceLiveView 1M deleted model-store");

    let lv_64m =
        run_tb("TraceLiveView.cfg", &["-compile", "-tlc", "-workers", "1", "-maxmem", "64M", "-recover", md_lv.to_str().unwrap()], &[]);
    let lv_64m_text = lv_64m.text();
    assert_eq!(lv_64m.code, 13, "TraceLiveView 64M recover:\n{lv_64m_text}");
    assert!(lv_64m_text.contains("State 82: Stuttering"), "TraceLiveView 64M recover missing lasso end:\n{lv_64m_text}");
    assert!(!md_lv.join("checkpoint").exists(), "TraceLiveView 64M recover should clean up checkpoint");

    // 5. Secondary `live::find_error` trace exhaustion (`AtomReplay`): a
    //    temporal predicate division-by-zero whose secondary trace rebuild
    //    exhausts 1 MiB keeps the primary checkpoint and error verdict, then
    //    recovers at 64 MiB to print all 181 trace states and clean up.
    const ATOM_REPLAY_SPEC: &str = r#"---- MODULE AtomReplay ----
EXTENDS Naturals, TLC, Sequences
VARIABLES bag,n
K(i) == [id |-> i, log |-> <<i,i+1>>]
Batch(i) == [k \in {K(40*i+j) : j \in 1..40} |-> k.id]
Init == /\ n=0 /\ bag=(K(0) :> 0)
Next == /\ n < 180 /\ n'=n+1 /\ bag'=Batch(n+1)
Prop == []<>((1 \div (180-n)) = 0)
====
"#;
    const ATOM_REPLAY_CFG: &str = "INIT Init\nNEXT Next\nPROPERTY Prop\nCHECK_DEADLOCK FALSE\n";
    let dir_ar = TempDir::with_spec("value-store-atom-replay", ATOM_REPLAY_SPEC, ATOM_REPLAY_CFG);
    let md_ar = dir_ar.path().join("md");
    let ar_fail = run_spec(
        dir_ar.path(),
        "AtomReplay",
        &["-compile", "-tlc", "-workers", "1", "-maxmem", "1M", "-metadir", md_ar.to_str().unwrap()],
        &rb_env_ck,
    );
    let ar_fail_text = ar_fail.text();
    assert_eq!(ar_fail.code, 255, "AtomReplay 1M:\n{ar_fail_text}");
    assert!(ar_fail_text.contains("The second argument of \\div is 0."), "AtomReplay 1M missing division error:\n{ar_fail_text}");
    assert!(
        ar_fail_text.contains("trace cannot be reconstructed: the value store (TLX_VALUE_STORE) exceeded its budget")
            && ar_fail_text.contains("recovering the last checkpoint, which is kept"),
        "AtomReplay 1M missing trace/checkpoint diagnostic:\n{ar_fail_text}"
    );
    assert!(md_ar.join("checkpoint/MANIFEST").is_file(), "AtomReplay 1M deleted MANIFEST");
    assert!(md_ar.join("checkpoint/model-store").is_file(), "AtomReplay 1M deleted model-store");

    let ar_rec = run_spec(
        dir_ar.path(),
        "AtomReplay",
        &["-compile", "-tlc", "-workers", "1", "-maxmem", "64M", "-recover", md_ar.to_str().unwrap()],
        &rb_env,
    );
    let ar_rec_text = ar_rec.text();
    assert_eq!(ar_rec.code, 255, "AtomReplay 64M recover:\n{ar_rec_text}");
    assert!(ar_rec_text.contains("The second argument of \\div is 0."), "AtomReplay 64M recover missing division error:\n{ar_rec_text}");
    assert!(ar_rec_text.contains("State 181:"), "AtomReplay 64M recover missing full 181-state trace:\n{ar_rec_text}");
    assert!(!md_ar.join("checkpoint").exists(), "AtomReplay 64M recover should clean up checkpoint");

    // 6. Concrete liveness (`TwoProps`): per-slot typed expansion errors keep
    //    property order so adding Q after P still reports P's division error.
    const TWO_PROPS_SPEC: &str = r#"---- MODULE TwoProps ----
EXTENDS Naturals, TLC, Sequences
VARIABLES n,d,bag
K(x) == [i |-> x, log |-> <<x>>]
Small(x) == (K(x) :> x) @@ (K(0) :> 0)
Init == /\ n = 0 /\ d = 0 /\ bag = Small(0)
Next == /\ IF d >= 2 THEN (IF n = 0 THEN (1 \div (2-d) = 1) ELSE Assert(FALSE, "second node")) ELSE TRUE
        /\ n' \in 0..2 /\ d' = d+1 /\ bag' = Small(n')
V == n
P == []((n = 0) \/ [](n = 0))
Q == <>[]((n = 8) \/ <>(n = 0))
====
"#;
    let dir_tp =
        TempDir::with_spec("value-store-two-props", TWO_PROPS_SPEC, "INIT Init\nNEXT Next\nVIEW V\nPROPERTY P Q\nCHECK_DEADLOCK FALSE\n");
    std::fs::write(dir_tp.path().join("OnlyP.cfg"), "INIT Init\nNEXT Next\nVIEW V\nPROPERTY P\nCHECK_DEADLOCK FALSE\n").unwrap();
    std::fs::write(dir_tp.path().join("OnlyQ.cfg"), "INIT Init\nNEXT Next\nVIEW V\nPROPERTY Q\nCHECK_DEADLOCK FALSE\n").unwrap();
    for (mode, args, env) in [
        ("interp", &["-interp", "-tlc", "-workers", "1"][..], &[][..]),
        ("compile", &["-compile", "-tlc", "-workers", "1", "-maxmem", "64M"][..], &rb_env[..]),
    ] {
        let run_tp = |cfg: &str| {
            let mut cmd = tlx_testkit::tlx!();
            cmd.check("TwoProps.tla").cfg(cfg).args(args).dir(dir_tp.path());
            for (k, v) in env {
                cmd.env(k, v);
            }
            cmd.run()
        };
        let only_p = run_tp("OnlyP.cfg");
        assert_ne!(only_p.code, 0, "TwoProps {mode} OnlyP:\n{}", only_p.text());
        assert!(only_p.text().contains("The second argument of \\div is 0."), "TwoProps {mode} OnlyP:\n{}", only_p.text());

        let only_q = run_tp("OnlyQ.cfg");
        assert_ne!(only_q.code, 0, "TwoProps {mode} OnlyQ:\n{}", only_q.text());
        assert!(only_q.text().contains("second node"), "TwoProps {mode} OnlyQ:\n{}", only_q.text());

        let both = run_tp("TwoProps.cfg");
        let both_text = both.text();
        assert_ne!(both.code, 0, "TwoProps {mode} P+Q:\n{both_text}");
        assert!(both_text.contains("The second argument of \\div is 0."), "TwoProps {mode} P+Q lost P's error:\n{both_text}");
        assert!(!both_text.contains("second node"), "TwoProps {mode} P+Q reported Q's error:\n{both_text}");
    }
}
