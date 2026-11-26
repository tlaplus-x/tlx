//! In-place threshold-counter saturation (`threshold-counter-projection`):
//! positive reductions across all execution tiers with `TLX_PARANOID=1`,
//! concrete un-capped trace lifting, deadlock preservation, `-tlc` bypass,
//! constrained/action-check support, arithmetic-semantics labelling, and
//! deterministic refusals.

use std::path::Path;
use std::time::Duration;

fn read_generated_lean(proof_dir: &Path) -> String {
    for entry in std::fs::read_dir(proof_dir).expect("read proof_dir") {
        let p = entry.unwrap().path();
        if p.is_dir() {
            let candidate = p.join("Optimization.lean");
            if candidate.is_file() {
                return std::fs::read_to_string(candidate).expect("read Optimization.lean");
            }
        } else if p.file_name().is_some_and(|n| n == "Optimization.lean") {
            return std::fs::read_to_string(p).expect("read Optimization.lean");
        }
    }
    panic!("no Optimization.lean found under {}", proof_dir.display());
}

const SCALAR_BOUNDED_SPEC: &str = r#"---- MODULE ThresholdScalar ----
EXTENDS Naturals
VARIABLE phase, count
Init == phase = "idle" /\ count = 0
Step == /\ phase = "idle"
        /\ count < 4
        /\ count' = count + 1
        /\ phase' = "idle"
Jump == /\ phase = "idle"
        /\ count < 4
        /\ count' = count + 5
        /\ phase' = IF count >= 2 THEN "ready" ELSE "idle"
Reset == /\ (phase = "ready" \/ count >= 4)
         /\ phase' = "idle"
         /\ count' = 0
Next == Step \/ Jump \/ Reset
TypeOK == phase \in {"idle", "ready"} /\ count \in Nat
ReadyCheck == (phase = "ready") => (count >= 4)
====
"#;

const SCALAR_BOUNDED_CFG: &str = "INIT Init\nNEXT Next\nINVARIANTS\n  TypeOK\n  ReadyCheck\n";

#[test]
fn scalar_threshold_projection_reduces_in_all_tiers_and_respects_tlc() {
    let dir = tlx_testkit::TempDir::with_spec("threshold-scalar", SCALAR_BOUNDED_SPEC, SCALAR_BOUNDED_CFG);
    let proof_dir = dir.join("proofs");
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let baseline = tlx_testkit::tlx_default!()
            .check("ThresholdScalar.tla")
            .args(args)
            .arg("-noautosymmetry")
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(baseline.code, 0, "{tier} baseline: {}", baseline.text());

        let reduced = tlx_testkit::tlx_default!()
            .check("ThresholdScalar.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry", "-proofdir"])
            .arg(&proof_dir)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(reduced.code, 0, "{tier} reduced: {}", reduced.text());
        assert!(reduced.stdout.contains("threshold-counter-projection"), "{tier}: {}", reduced.text());
        // Statically proved bounded (count <= 8 <= i32::MAX): checked machine arithmetic, NOT mathematical.
        assert!(!reduced.stdout.contains("mathematical counter arithmetic"), "{tier}: {}", reduced.text());

        let tlc = tlx_testkit::tlx_default!()
            .check("ThresholdScalar.tla")
            .args(args)
            .args(["-optimize", "-tlc", "-noautosymmetry"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(tlc.code, 0, "{tier} tlc: {}", tlc.text());
        assert!(!tlc.stdout.contains("threshold-counter-projection"), "{tier}: {}", tlc.text());

        // Baseline: idle x {0,1,2,3,4,5,6} + ready x {7,8} = 9 distinct states.
        // Reduced (cap=4): idle x {0,1,2,3,4} + ready x {4} = 6 distinct states.
        assert!(baseline.stdout.contains("9 distinct states found"), "{tier}: {}", baseline.text());
        assert!(tlc.stdout.contains("9 distinct states found"), "{tier}: {}", tlc.text());
        assert!(reduced.stdout.contains("6 distinct states found"), "{tier}: {}", reduced.text());
    }
    let lean = read_generated_lean(&proof_dir);
    assert!(lean.contains("namespace TlxOptimization.GeneratedThresholdCounter"));
    assert!(lean.contains("Checked machine arithmetic."));
}

#[test]
fn unbounded_multi_counter_and_map_projection_reduces_in_all_tiers() {
    let spec = r#"---- MODULE ThresholdMap ----
EXTENDS Naturals
CONSTANT Actor
VARIABLE phase, retries, fails
Init == phase = "run" /\ retries = 0 /\ fails = [a \in Actor |-> 0]
IncRetry == /\ phase = "run"
            /\ retries' = retries + 1
            /\ phase' = IF retries >= 2 THEN "done" ELSE "run"
            /\ UNCHANGED fails
IncFail == \E a \in Actor :
           /\ phase = "run"
           /\ fails' = [fails EXCEPT ![a] = @ + 1]
           /\ UNCHANGED <<phase, retries>>
Reset == /\ phase = "done"
         /\ phase' = "run"
         /\ retries' = 0
         /\ fails' = [a \in Actor |-> 0]
Next == IncRetry \/ IncFail \/ Reset
TypeOK == phase \in {"run", "done"} /\ retries \in Nat /\ fails \in [Actor -> Nat]
Guard == \A a \in Actor : (fails[a] < 2) \/ (fails[a] >= 2)
Safe == (phase = "done") => (retries >= 3)
====
"#;
    let cfg = "INIT Init\nNEXT Next\nCONSTANT Actor = {\"a1\", \"a2\"}\nINVARIANTS\n  TypeOK\n  Guard\n  Safe\n";
    let dir = tlx_testkit::TempDir::with_spec("threshold-map", spec, cfg);
    let proof_dir = dir.join("proofs");
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("ThresholdMap.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry", "-proofdir"])
            .arg(&proof_dir)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{tier}: {}", run.text());
        assert!(run.stdout.contains("threshold-counter-projection"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("mathematical counter arithmetic"), "{tier}: {}", run.text());
    }
    let lean = read_generated_lean(&proof_dir);
    assert!(lean.contains("namespace TlxOptimization.GeneratedThresholdCounter"));
    assert!(lean.contains("Mathematical natural-number counters; eventual machine overflow need not be preserved."));
}

#[test]
fn counterexample_trace_lifts_uncapped_counter_values_and_deadlock_preserved() {
    // 1. Concrete counterexample where the invariant fails only after the
    //    counter exceeds its cap of 3 (`steps >= 3`): the shortest trace to
    //    `pos = 5` carries the concrete un-capped `steps = 5`, not `3`.
    //    `Linger` also gives several saturated values at one retained position,
    //    so the bounded merge probe still witnesses a merged state.
    let cex_spec = r#"---- MODULE ThresholdCex ----
EXTENDS Naturals
VARIABLE pos, steps
Init == pos = 0 /\ steps = 0
Step == /\ pos < 5
        /\ pos' = pos + 1
        /\ steps' = steps + 1
Linger == /\ pos < 5
          /\ pos' = pos + 1
          /\ steps' = steps + 5
Next == Step \/ Linger
TypeOK == pos \in 0..5 /\ steps \in Nat
NotFive == pos # 5
Debt == (pos = 5) => (steps >= 3)
====
"#;
    let cex_cfg = "INIT Init\nNEXT Next\nINVARIANTS\n  TypeOK\n  NotFive\n  Debt\n";
    let dir = tlx_testkit::TempDir::with_spec("threshold-cex", cex_spec, cex_cfg);
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("ThresholdCex.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 12, "{tier}: {}", run.text());
        assert!(run.stdout.contains("threshold-counter-projection"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("Invariant NotFive is violated"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("steps = 5"), "{tier} must reconstruct un-capped concrete steps = 5: {}", run.text());
    }

    // 2. Deadlock preservation with un-capped values: the shortest deadlock is
    //    reached after `Linger` and `Stop`, and the reconstructed trace must
    //    report the concrete c = 5 although the projection saturates it at 3.
    let dl_spec = r#"---- MODULE ThresholdDeadlock ----
EXTENDS Naturals
VARIABLE mode, tick, c
Init == mode = "go" /\ tick = 0 /\ c = 0
Tick == /\ mode = "go"
        /\ tick < 6
        /\ tick' = tick + 1
        /\ c' = c + 1
        /\ UNCHANGED mode
Linger == /\ mode = "go"
          /\ tick < 6
          /\ tick' = tick + 1
          /\ c' = c + 5
          /\ UNCHANGED mode
Stop == /\ mode = "go"
        /\ c >= 3
        /\ mode' = "stop"
        /\ UNCHANGED <<tick, c>>
Next == Tick \/ Linger \/ Stop
TypeOK == mode \in {"go", "stop"} /\ tick \in Nat /\ c \in Nat
====
"#;
    let dl_cfg = "INIT Init\nNEXT Next\nINVARIANT TypeOK\nCHECK_DEADLOCK TRUE\n";
    let dir_dl = tlx_testkit::TempDir::with_spec("threshold-dl", dl_spec, dl_cfg);
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("ThresholdDeadlock.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir_dl)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 11, "{tier}: {}", run.text());
        assert!(run.stdout.contains("threshold-counter-projection"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("Deadlock reached"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("c = 5"), "{tier} deadlock trace must retain concrete c = 5: {}", run.text());
    }
}

#[test]
fn constrained_state_and_action_checks_work_and_counter_action_check_refuses() {
    let spec = r#"---- MODULE ThresholdConstrained ----
EXTENDS Naturals
CONSTANT Limit
DefaultLimit == 2
VARIABLE phase, c
Init == phase = "a" /\ c = 0
Next == \/ /\ phase = "a" /\ c' = c + 1 /\ phase' = IF c >= Limit THEN "b" ELSE "a"
        \/ /\ phase = "b" /\ c' = c + 1 /\ phase' = "b"
        \/ /\ phase = "b" /\ c' = 0 /\ phase' = "a"
TypeOK == phase \in {"a", "b"} /\ c \in Nat
StateLim == (phase = "a") \/ (c >= Limit)
ActLim == phase' \in {"a", "b"}
ActProp == [][phase' \in {"a", "b"}]_phase
BadActLim == c' <= Limit
BadActProp == [][phase' \in {"a", "b"}]_<<phase, c>>
====
"#;
    let ok_cfg = "INIT Init\nNEXT Next\nCONSTANT Limit <- DefaultLimit\nINVARIANT TypeOK\nCONSTRAINT StateLim\nACTION_CONSTRAINT ActLim\nPROPERTY ActProp\n";
    let dir_ok = tlx_testkit::TempDir::with_spec("threshold-constrained-ok", spec, ok_cfg);
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("ThresholdConstrained.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir_ok)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{tier}: {}", run.text());
        assert!(run.stdout.contains("threshold-counter-projection"), "{tier}: {}", run.text());
    }

    // Action constraint or action property subscript referencing the counter MUST refuse.
    for (label, bad_cfg) in [
        ("action-constraint", "INIT Init\nNEXT Next\nCONSTANT Limit <- DefaultLimit\nINVARIANT TypeOK\nACTION_CONSTRAINT BadActLim\n"),
        (
            "action-prop-subscript",
            "INIT Init\nNEXT Next\nCONSTANT Limit <- DefaultLimit\nINVARIANT TypeOK\nACTION_CONSTRAINT BadActLim\nPROPERTY BadActProp\n",
        ),
    ] {
        let dir_bad = tlx_testkit::TempDir::with_spec(&format!("threshold-constrained-{label}"), spec, bad_cfg);
        let run_bad = tlx_testkit::tlx_default!()
            .check("ThresholdConstrained.tla")
            .args(["-interp", "-optimize", "-noautosymmetry"])
            .dir(&dir_bad)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run_bad.code, 0, "{label}: {}", run_bad.text());
        assert!(!run_bad.stdout.contains("threshold-counter-projection"), "{label}: {}", run_bad.text());
    }
}

#[test]
fn deterministic_refusals_decline_threshold_projection() {
    let cases: &[(&str, &str, &str)] = &[
        // 1. Decrement (`c' = c - 1`)
        (
            "decrement",
            r#"---- MODULE Refusal ----
EXTENDS Naturals
VARIABLE c
Init == c = 0
Next == (c < 5 /\ c' = c + 1) \/ (c > 0 /\ c' = c - 1)
Inv == c \in Nat
====
"#,
            "INIT Init\nNEXT Next\nINVARIANT Inv\n",
        ),
        // 2. Cross-counter comparison (`c1 < c2`)
        (
            "cross-compare",
            r#"---- MODULE Refusal ----
EXTENDS Naturals
VARIABLE c1, c2
Init == c1 = 0 /\ c2 = 0
Next == /\ c1 < 5 /\ c2 < 5
        /\ c1' = c1 + 1 /\ c2' = c2 + 1
Inv == c1 \in Nat /\ c2 \in Nat /\ c1 <= c2
====
"#,
            "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n",
        ),
        // 3. Raw counter escape into retained state (`log' = c`)
        (
            "raw-escape",
            r#"---- MODULE Refusal ----
EXTENDS Naturals
VARIABLE c, last
Init == c = 0 /\ last = 0
Next == c < 5 /\ c' = c + 1 /\ last' = c
Inv == c \in Nat /\ last \in Nat
====
"#,
            "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n",
        ),
        // 4. Primed counter read in guard (`c' < 4`)
        (
            "primed-read",
            r#"---- MODULE Refusal ----
EXTENDS Naturals
VARIABLE c
Init == c = 0
Next == c < 5 /\ c' = c + 1 /\ c' < 6
Inv == c \in Nat
====
"#,
            "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n",
        ),
        // 5. Duplicate binding (`c' = c + 1 /\ c' = c + 1`)
        (
            "duplicate-binding",
            r#"---- MODULE Refusal ----
EXTENDS Naturals
VARIABLE c
Init == c = 0
Next == c < 5 /\ c' = c + 1 /\ c' = c + 1
Inv == c \in Nat
====
"#,
            "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n",
        ),
        // 6. Negative reset literal (`c' = -1`)
        (
            "negative-literal",
            r#"---- MODULE Refusal ----
EXTENDS Integers
VARIABLE c
Init == c = 0
Next == (c < 5 /\ c' = c + 1) \/ (c = 5 /\ c' = -1)
Inv == c \in Int
====
"#,
            "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n",
        ),
        // 7. Cap exceeding `i32::MAX - 1` (`c <= 2147483647` requires cap 2147483648)
        (
            "cap-overflow",
            r#"---- MODULE Refusal ----
EXTENDS Naturals
VARIABLE c
Init == c = 0
Next == c < 5 /\ c' = c + 1
Inv == c \in Nat /\ c <= 2147483647
====
"#,
            "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n",
        ),
        // 8. Non-profitable already-capped counter (`c < 3` with `c = 3` test -> cap = 4 >= ub = 3)
        (
            "non-profitable",
            r#"---- MODULE Refusal ----
EXTENDS Naturals
VARIABLE c
Init == c = 0
Next == (c < 3 /\ c' = c + 1) \/ (c = 3 /\ c' = 0)
Inv == c \in Nat /\ c <= 3
====
"#,
            "INIT Init\nNEXT Next\nINVARIANT Inv\n",
        ),
        // 9. A saturation no reachable value exceeds merges nothing: the static
        //    `Init`/`Next`/`CONSTRAINT` bound cannot see that the phase guard
        //    keeps `c <= cap`, so the bounded merge witness must decline.
        (
            "no-op-saturation",
            r#"---- MODULE Refusal ----
EXTENDS Naturals
VARIABLE phase, c
Init == phase = "run" /\ c = 0
Next == \/ /\ phase = "run" /\ c' = c + 1 /\ phase' = IF c >= 1 THEN "done" ELSE "run"
        \/ /\ phase = "done" /\ phase' = "run" /\ c' = 0
Inv == phase \in {"run", "done"} /\ c \in Nat /\ ((phase = "done") => (c >= 2))
====
"#,
            "INIT Init\nNEXT Next\nINVARIANT Inv\n",
        ),
    ];

    for (name, spec, cfg) in cases {
        let dir = tlx_testkit::TempDir::with_spec(&format!("threshold-refusal-{name}"), spec, cfg);
        let run = tlx_testkit::tlx_default!()
            .check("Refusal.tla")
            .args(["-interp", "-optimize", "-noautosymmetry"])
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{name}: {}", run.text());
        assert!(!run.stdout.contains("threshold-counter-projection"), "{name} must refuse threshold-counter-projection: {}", run.text());
    }
}

#[test]
fn opaque_recursive_capture_preserves_violation_verdict() {
    let cases: &[(&str, &str)] = &[
        (
            "direct",
            r#"---- MODULE Capture ----
EXTENDS Naturals
VARIABLE c
Inspect(x) == LET R[n \in 0..1] == IF n = 0 THEN x < 3 ELSE R[n - 1]
              IN R[1]
Init == c = 0
Next == c' = c + 1
Inv == Inspect(c)
====
"#,
        ),
        (
            "transitive",
            r#"---- MODULE Capture ----
EXTENDS Naturals
VARIABLE c
Inspect(x) == LET Helper == x < 3
                  R[n \in 0..1] == IF n = 0 THEN Helper ELSE R[n - 1]
              IN R[1]
Init == c = 0
Next == c' = c + 1
Inv == Inspect(c)
====
"#,
        ),
    ];
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    for (label, spec) in cases {
        let dir = tlx_testkit::TempDir::with_spec(&format!("threshold-capture-{label}"), spec, cfg);
        let plain = tlx_testkit::tlx_default!()
            .check("Capture.tla")
            .args(["-interp", "-noautosymmetry"])
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(plain.code, 12, "{label} plain: {}", plain.text());
        assert!(plain.stdout.contains("Invariant Inv is violated"), "{label} plain: {}", plain.text());

        for (tier, args, env) in tlx_testkit::cli::TIERS {
            let opt = tlx_testkit::tlx_default!()
                .check("Capture.tla")
                .args(args)
                .args(["-optimize", "-noautosymmetry"])
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            assert_eq!(opt.code, 12, "{label}/{tier} opt must preserve invariant violation: {}", opt.text());
            assert!(opt.stdout.contains("Invariant Inv is violated"), "{label}/{tier}: {}", opt.text());
            assert!(!opt.stdout.contains("threshold-counter-projection"), "{label}/{tier} must decline capture: {}", opt.text());
            assert!(opt.stdout.contains("c = 3"), "{label}/{tier} counterexample must reach c = 3: {}", opt.text());
        }
    }
}

#[test]
fn tuple_bound_choices_and_map_seed_keys_reduce_faithfully() {
    let spec = r#"---- MODULE TupleAndSeed ----
EXTENDS Naturals
VARIABLE pair, flag, m
Init == \E <<x, y>> \in {<<1, 2>>} :
          /\ pair = <<x, y>>
          /\ flag = FALSE
          /\ m = [a \in {1, 2} |-> IF a = 1 THEN 0 ELSE 1]
Step == \E <<x, y>> \in {<<1, 2>>} :
          /\ pair' = <<y, x>>
          /\ flag' = (x = 1 /\ y = 2)
          /\ m' = [m EXCEPT ![1] = @ + 1]
Next == Step
TypeOK == pair \in {<<1, 2>>, <<2, 1>>} /\ flag \in BOOLEAN /\ m \in [{1, 2} -> Nat]
Guard == m[1] < 2 \/ m[1] >= 2
====
"#;
    let cfg = "INIT Init\nNEXT Next\nINVARIANTS\n  TypeOK\n  Guard\n";
    let dir = tlx_testkit::TempDir::with_spec("threshold-tuple-seed", spec, cfg);
    let proof_dir = dir.join("proofs");
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("TupleAndSeed.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry", "-proofdir"])
            .arg(&proof_dir)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{tier}: {}", run.text());
        assert!(run.stdout.contains("threshold-counter-projection"), "{tier}: {}", run.text());
    }
    let lean = read_generated_lean(&proof_dir);
    assert!(lean.contains("namespace TlxOptimization.GeneratedThresholdCounter"));
}

#[test]
fn conjunct_order_governs_checked_vs_mathematical_counter_arithmetic() {
    let make_spec = |inc_branch: &str| {
        format!(
            r#"---- MODULE Boundary ----
EXTENDS Naturals
VARIABLE c
Init == c = 0
Next == \/ {inc_branch}
        \/ c' = 101
        \/ c' = 2147483647
Inv == c \in Nat
====
"#
        )
    };
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";

    // 1. Addition BEFORE guard (`c' = c + 1 /\ c < 100`): evaluating the
    //    disabled increment branch from `c = 2147483647` overflows `i32` in
    //    plain checking, so `-optimize` MUST declare mathematical counter
    //    arithmetic rather than `Checked machine arithmetic.`.
    let spec_after = make_spec("(c' = c + 1 /\\ c < 100)");
    let dir_after = tlx_testkit::TempDir::with_spec("threshold-boundary-after", &spec_after, cfg);
    let plain_after = tlx_testkit::tlx_default!()
        .check("Boundary.tla")
        .args(["-interp", "-noautosymmetry"])
        .dir(&dir_after)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(plain_after.code, 255, "plain add-before-guard must overflow: {}", plain_after.text());

    let proof_after = dir_after.join("proofs");
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("Boundary.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry", "-proofdir"])
            .arg(&proof_after)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir_after)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "add-before-guard/{tier}: {}", run.text());
        assert!(run.stdout.contains("threshold-counter-projection"), "add-before-guard/{tier}: {}", run.text());
        assert!(
            run.stdout.contains("mathematical counter arithmetic"),
            "add-before-guard/{tier} must report mathematical counter arithmetic: {}",
            run.text()
        );
    }
    let lean_after = read_generated_lean(&proof_after);
    assert!(lean_after.contains("Mathematical natural-number counters; eventual machine overflow need not be preserved."));
    assert!(!lean_after.contains("Checked machine arithmetic."));

    // 2. Guard BEFORE addition (`c < 100 /\ c' = c + 1`): short-circuit `And`
    //    skips `c + 1` whenever `c >= 100`, so neither plain nor optimized
    //    checking can overflow and `Checked machine arithmetic.` holds.
    let spec_before = make_spec("(c < 100 /\\ c' = c + 1)");
    let dir_before = tlx_testkit::TempDir::with_spec("threshold-boundary-before", &spec_before, cfg);
    let plain_before = tlx_testkit::tlx_default!()
        .check("Boundary.tla")
        .args(["-interp", "-noautosymmetry"])
        .dir(&dir_before)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(plain_before.code, 0, "plain guard-before-add must not overflow: {}", plain_before.text());

    let proof_before = dir_before.join("proofs");
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("Boundary.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry", "-proofdir"])
            .arg(&proof_before)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir_before)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "guard-before-add/{tier}: {}", run.text());
        assert!(run.stdout.contains("threshold-counter-projection"), "guard-before-add/{tier}: {}", run.text());
        assert!(
            !run.stdout.contains("mathematical counter arithmetic"),
            "guard-before-add/{tier} should certify checked machine arithmetic: {}",
            run.text()
        );
    }
    let lean_before = read_generated_lean(&proof_before);
    assert!(lean_before.contains("Checked machine arithmetic."));
    assert!(!lean_before.contains("Mathematical natural-number counters;"));
}
