//! Cross-tier integration tests for constrained certified reductions:
//! `CONSTRAINT`, `ACTION_CONSTRAINT`, implied-init `PROPERTY`, `[][A]_sub` action
//! `PROPERTY`, and pure zero-arity `CONSTANT C <- Def` substitutions across all
//! four execution tiers (`-interp`, closure IR, Cranelift JIT, C) with
//! `TLX_PARANOID=1` and `TLX_SYMMETRY_PARANOID=1`.

use serde_json::{Map, Value};
use std::path::{Path, PathBuf};
use std::time::Duration;

const ALL_TIERS: [(&str, &[&str], &[(&str, &str)]); 4] = [
    ("interpreter", &["-interp"], &[]),
    ("compiled IR", &["-compile"], &[("TLX_PRERUN_REUSE", "0"), ("TLX_NO_NATIVE", "1")]),
    ("cranelift JIT", &["-compile"], &[("TLX_PRERUN_REUSE", "0"), ("TLX_JIT", "only"), ("TLX_JIT_VERIFY", "1")]),
    ("C backend", &["-compile"], &[("TLX_PRERUN_REUSE", "0"), ("TLX_JIT", "0"), ("TLX_NATIVE_SYNC", "1")]),
];

const CONSTRAINED_SYM_TLA: &str = r#"---- MODULE ConstrainedSym ----
EXTENDS Naturals
CONSTANT Nodes, Cap, n1, n2, n3
DefaultNodes == {n1, n2, n3}
DefaultCap == 2
VARIABLE state, count
Init == state = [n \in Nodes |-> 0] /\ count = 0
Next == /\ \E n \in Nodes :
            /\ state' = [state EXCEPT ![n] = IF @ = 0 THEN 1 ELSE 0]
            /\ count' = IF count < Cap THEN count + 1 ELSE count
Inv == count <= Cap /\ \A n \in Nodes : state[n] \in {0, 1}
InitProp == count = 0
StateLimit == count < Cap
ActLimit == count' >= count
ActProp == [][count' >= count]_<<state, count>>
====
"#;

const CONSTRAINED_SYM_CFG: &str = "\
INIT Init
NEXT Next
CONSTANTS
  n1 = n1
  n2 = n2
  n3 = n3
  Nodes <- DefaultNodes
  Cap <- DefaultCap
INVARIANT Inv
PROPERTY InitProp
PROPERTY ActProp
CONSTRAINT StateLimit
ACTION_CONSTRAINT ActLimit
";

struct TierRun {
    tier: String,
    proof_dir: PathBuf,
    stats_path: PathBuf,
    run: tlx_testkit::cli::Run,
}

fn run_all_tiers(dir: &tlx_testkit::TempDir, module: &str, extra_args: &[&str], sym_paranoid: bool) -> Vec<TierRun> {
    let mut results = Vec::new();
    for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
        let proof_dir = dir.join(format!("proofs-{idx}"));
        let cache_dir = dir.join(format!("cache-{idx}"));
        let stats_path = dir.join(format!("stats-{idx}.json"));
        let stats_arg = format!("json={}", stats_path.display());
        let mut cmd = tlx_testkit::tlx_default!();
        cmd.check(module)
            .args(["-workers", "1", "-stats", &stats_arg])
            .args(*args)
            .args(extra_args)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .env("TLX_PROOF_DIR", &proof_dir)
            .env("TLX_CACHE", &cache_dir)
            .dir(dir)
            .timeout(Duration::from_secs(60));
        if sym_paranoid {
            cmd.env("TLX_SYMMETRY_PARANOID", "1");
        }
        let out = cmd.run();
        results.push(TierRun { tier: tier.to_string(), proof_dir, stats_path, run: out });
    }
    results
}

fn parse_distinct(stdout: &str) -> Option<u64> {
    for line in stdout.lines() {
        if let Some(idx) = line.find(" distinct states found") {
            let prefix = line[..idx].trim_end();
            if let Some(num) = prefix.rsplit(|c: char| !c.is_ascii_digit()).next() {
                if let Ok(v) = num.parse::<u64>() {
                    return Some(v);
                }
            }
        }
    }
    None
}

fn trace_lines(stdout: &str) -> Vec<&str> {
    stdout.lines().filter(|l| l.starts_with("State ") || l.starts_with("/\\ ")).collect()
}

fn parse_stats_json(src: &str) -> Result<Map<String, Value>, String> {
    match serde_json::from_str::<Value>(src).map_err(|e| e.to_string())? {
        Value::Object(map) => Ok(map),
        _ => Err("stats JSON root is not an object".into()),
    }
}

struct RowCalls {
    native: u64,
    ir: u64,
    interp: u64,
    fallback: u64,
    mixed: u64,
}

fn read_row_calls(root: &Map<String, Value>, section: &str, row: &str) -> Result<RowCalls, String> {
    let Some(rows) = root.get(section).and_then(Value::as_array) else {
        return Err(format!("missing array `{section}` in stats JSON"));
    };
    let mut matched = rows.iter().filter_map(|item| {
        let obj = item.as_object()?;
        (obj.get("name").and_then(Value::as_str) == Some(row)).then_some(obj)
    });
    let Some(row_obj) = matched.next() else {
        return Err(format!("missing row `{row}` in `{section}`"));
    };
    if matched.next().is_some() {
        return Err(format!("duplicate row `{row}` in `{section}`"));
    }
    let Some(calls) = row_obj.get("calls").and_then(Value::as_object) else {
        return Err(format!("missing `calls` object on `{section}/{row}`"));
    };
    let get_uint = |key: &str| -> Result<u64, String> {
        let Some(val) = calls.get(key) else {
            return Err(format!("missing counter `{section}/{row}.calls.{key}`"));
        };
        val.as_u64().ok_or_else(|| format!("counter `{section}/{row}.calls.{key}` is not an unsigned integer: {val}"))
    };
    Ok(RowCalls {
        native: get_uint("native")?,
        ir: get_uint("ir")?,
        interp: get_uint("interp")?,
        fallback: get_uint("fallback")?,
        mixed: get_uint("mixed")?,
    })
}

fn check_compiled_rows(root: &Map<String, Value>, want_native: bool) -> Result<(), String> {
    for (section, row) in [
        ("actions", "Next"),
        ("invariants", "Inv"),
        ("invariants", "constraint_0"),
        ("action_properties", "ActProp"),
        ("action_properties", "action_constraint_0"),
    ] {
        let c = read_row_calls(root, section, row)?;
        let (ran, competing) = if want_native { (c.native, c.ir) } else { (c.ir, c.native) };
        let unexpected_interp = section != "actions" && c.interp != 0;
        if ran == 0 || competing != 0 || c.fallback != 0 || c.mixed != 0 || unexpected_interp {
            return Err(format!(
                "{section}/{row}: unexpected call split native={} ir={} interp={} fallback={} mixed={}",
                c.native, c.ir, c.interp, c.fallback, c.mixed
            ));
        }
    }
    Ok(())
}

fn check_tier_execution(tier: &str, run: &tlx_testkit::cli::Run, stats_path: &Path) -> Result<(), String> {
    let raw = std::fs::read_to_string(stats_path).map_err(|e| format!("read {}: {e}", stats_path.display()))?;
    let root = parse_stats_json(&raw)?;
    let Some(phases) = root.get("phases").and_then(Value::as_object) else {
        return Err("missing `phases` object in stats JSON".into());
    };
    match tier {
        "interpreter" => {
            if run.stdout.contains("compile:") {
                return Err("unexpected `compile:` output in interpreter tier".into());
            }
            for (section, row) in [("actions", "Next"), ("invariants", "Inv"), ("action_properties", "ActProp")] {
                let c = read_row_calls(&root, section, row)?;
                if c.interp == 0 || c.native != 0 || c.ir != 0 || c.fallback != 0 || c.mixed != 0 {
                    return Err(format!("{section}/{row}: expected interp-only execution"));
                }
            }
            Ok(())
        }
        "compiled IR" => {
            if run.stdout.contains("native code")
                || phases.contains_key("JIT code bytes")
                || phases.contains_key("native -O2 ready at (since start)")
            {
                return Err("unexpected native phase in compiled IR tier".into());
            }
            check_compiled_rows(&root, false)
        }
        "cranelift JIT" => {
            if !run.stdout.contains("compile: native code (JIT) ready") {
                return Err("missing `compile: native code (JIT) ready` in JIT tier".into());
            }
            if phases.get("JIT code bytes").and_then(Value::as_u64).is_none_or(|n| n == 0) {
                return Err("missing positive `JIT code bytes` in JIT phases".into());
            }
            if phases.contains_key("native -O2 ready at (since start)") {
                return Err("unexpected C `-O2` load in JIT tier".into());
            }
            check_compiled_rows(&root, true)
        }
        "C backend" => {
            if run.stdout.contains("C compilation failed") || run.stdout.contains("C build failed") {
                return Err("C build failed and fell back".into());
            }
            if run.stdout.contains("native code (JIT) ready") || phases.contains_key("JIT code bytes") {
                return Err("unexpected JIT execution in C backend tier".into());
            }
            if !phases.contains_key("native -O2 ready at (since start)") {
                return Err("missing `native -O2 ready at (since start)` in C phases".into());
            }
            check_compiled_rows(&root, true)
        }
        other => Err(format!("unknown tier {other}")),
    }
}

#[test]
fn constrained_symmetry_with_const_subst_and_action_prop_reduces_across_all_tiers() {
    // Verify the structured JSON counter reader handles standard escapes (`\u0009`) and rejects
    // duplicate rows or missing / non-u64 counters.
    let unicode_escape = parse_stats_json(
        r#"{"phases":{"tab\u0009label":1},"actions":[{"name":"Next","calls":{"native":2,"ir":0,"interp":0,"fallback":0,"mixed":0}}]}"#,
    )
    .unwrap();
    assert_eq!(read_row_calls(&unicode_escape, "actions", "Next").unwrap().native, 2);
    let dup_row = parse_stats_json(
        r#"{"actions":[{"name":"Next","calls":{"native":2,"ir":0,"interp":0,"fallback":0,"mixed":0}},{"name":"Next","calls":{"native":1,"ir":0,"interp":0,"fallback":0,"mixed":0}}]}"#,
    )
    .unwrap();
    assert!(read_row_calls(&dup_row, "actions", "Next").is_err());
    let missing_fb = parse_stats_json(r#"{"actions":[{"name":"Next","calls":{"native":2,"ir":0,"interp":0,"mixed":0}}]}"#).unwrap();
    assert!(read_row_calls(&missing_fb, "actions", "Next").is_err());
    let str_fb =
        parse_stats_json(r#"{"actions":[{"name":"Next","calls":{"native":2,"ir":0,"interp":0,"fallback":"0","mixed":0}}]}"#).unwrap();
    assert!(read_row_calls(&str_fb, "actions", "Next").is_err());

    let dir = tlx_testkit::TempDir::with_spec("constrained-sym", CONSTRAINED_SYM_TLA, CONSTRAINED_SYM_CFG);
    let tlc = tlx_testkit::tlx_default!()
        .check("ConstrainedSym.tla")
        .args(["-tlc", "-interp", "-workers", "1"])
        .dir(&dir)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(tlc.code, 0, "{}", tlc.text());
    assert!(!tlc.stdout.contains("Optimizations: symmetry"), "{}", tlc.text());
    let tlc_distinct = parse_distinct(&tlc.stdout).expect("tlc distinct count");

    for tr in run_all_tiers(&dir, "ConstrainedSym.tla", &[], true) {
        let tier = &tr.tier;
        assert_eq!(tr.run.code, 0, "{tier}: {}", tr.run.text());
        assert!(tr.run.stdout.contains("Optimizations: symmetry"), "{tier}: {}", tr.run.text());
        check_tier_execution(tier, &tr.run, &tr.stats_path).unwrap_or_else(|e| panic!("{tier}: {e}\n{}", tr.run.text()));
        let red_distinct = parse_distinct(&tr.run.stdout).expect("reduced distinct count");
        assert!(red_distinct < tlc_distinct, "{tier}: expected {red_distinct} < {tlc_distinct}");

        let mut found_cert = false;
        for entry in std::fs::read_dir(&tr.proof_dir).unwrap() {
            let lean = std::fs::read_to_string(entry.unwrap().path().join("Optimization.lean")).unwrap();
            if lean.contains("theorem constrained_certificate") {
                for expected in [
                    "theorem constrained_optimization_correct",
                    "theorem constrained_init_counterexample_lifts",
                    "theorem constrained_step_counterexample_lifts",
                    "theorem admitted_deadlock_preserved",
                    "theorem const_subst_bindings_match",
                    "theorem const_subst_sound",
                    "theorem const_subst_constrained_sound",
                ] {
                    assert!(lean.contains(expected), "{tier}: missing {expected}");
                }
                assert!(!lean.contains("sorry"), "{tier}");
                found_cert = true;
            }
        }
        assert!(found_cert, "{tier}: expected constrained Lean certificate");
    }

    // Negative control: with `CC=/bin/false` and an empty cache, C compilation falls back
    // to IR and the exact same `check_tier_execution("C backend", ...)` checker must reject it.
    let broken_stats = dir.join("stats-broken-cc.json");
    let broken_stats_arg = format!("json={}", broken_stats.display());
    let broken_c = tlx_testkit::tlx_default!()
        .check("ConstrainedSym.tla")
        .args(["-compile", "-workers", "1", "-stats", &broken_stats_arg])
        .envs([("TLX_PRERUN_REUSE", "0"), ("TLX_JIT", "0"), ("TLX_NATIVE_SYNC", "1"), ("CC", "/bin/false")])
        .env("TLX_CACHE", dir.join("cache-broken-cc"))
        .env("TLX_PROOF_DIR", dir.join("proofs-broken-cc"))
        .dir(&dir)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(broken_c.code, 0, "{}", broken_c.text());
    assert!(
        check_tier_execution("C backend", &broken_c, &broken_stats).is_err(),
        "disabled C compiler control must fail C backend execution check:\n{}",
        broken_c.text()
    );
}

#[test]
fn invariant_and_action_prop_violations_on_unadmitted_successors_lift_concrete_traces() {
    let inv_tla = r#"---- MODULE UnadmittedInvViolation ----
EXTENDS Naturals
CONSTANT Nodes
VARIABLE state, c, bad
Init == state = [n \in Nodes |-> 0] /\ c = 0 /\ bad = FALSE
Next == /\ c < 2
        /\ \E n \in Nodes :
          /\ state' = [state EXCEPT ![n] = 1]
          /\ c' = c + 1
          /\ bad' = (c = 1)
Inv == ~bad
Limit == c < 2
====
"#;
    let inv_cfg = "INIT Init\nNEXT Next\nCONSTANT Nodes = {n1, n2, n3}\nINVARIANT Inv\nCONSTRAINT Limit\n";
    let dir = tlx_testkit::TempDir::with_spec("unadmitted-inv", inv_tla, inv_cfg);
    let tlc = tlx_testkit::tlx_default!().check("UnadmittedInvViolation.tla").args(["-tlc", "-interp", "-workers", "1"]).dir(&dir).run();
    assert_eq!(tlc.code, 12, "{}", tlc.text());
    let expected_inv_trace = [
        "State 1: <Initial predicate>",
        "/\\ state = (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0)",
        "/\\ bad = FALSE",
        "/\\ c = 0",
        "State 2: <Next line 6, col 9 to line 10, col 27 of module UnadmittedInvViolation>",
        "/\\ state = (n1 :> 1 @@ n2 :> 0 @@ n3 :> 0)",
        "/\\ bad = FALSE",
        "/\\ c = 1",
        "State 3: <Next line 6, col 9 to line 10, col 27 of module UnadmittedInvViolation>",
        "/\\ state = (n1 :> 1 @@ n2 :> 0 @@ n3 :> 0)",
        "/\\ bad = TRUE",
        "/\\ c = 2",
    ];
    assert_eq!(trace_lines(&tlc.stdout), expected_inv_trace, "{}", tlc.text());
    for tr in run_all_tiers(&dir, "UnadmittedInvViolation.tla", &[], true) {
        assert_eq!(tr.run.code, 12, "{}: {}", tr.tier, tr.run.text());
        assert!(tr.run.stdout.contains("Optimizations: symmetry"), "{}: {}", tr.tier, tr.run.text());
        assert_eq!(trace_lines(&tr.run.stdout), expected_inv_trace, "{}: {}", tr.tier, tr.run.text());
    }

    let act_tla = r#"---- MODULE UnadmittedActViolation ----
EXTENDS Naturals
CONSTANT Nodes
VARIABLE state, c, tag
Init == state = [n \in Nodes |-> 0] /\ c = 0 /\ tag = 0
Next == /\ c < 2
        /\ \E n \in Nodes :
          /\ state' = [state EXCEPT ![n] = 1]
          /\ c' = c + 1
          /\ tag' = 1
Inv == c \in 0..2
Limit == c < 2
ActLimit == c' < 2
ActProp == [][c' <= 1]_<<state, c>>
====
"#;
    let act_cfg = "INIT Init\nNEXT Next\nCONSTANT Nodes = {n1, n2, n3}\nINVARIANT Inv\nPROPERTY ActProp\nCONSTRAINT Limit\nACTION_CONSTRAINT ActLimit\n";
    let dir = tlx_testkit::TempDir::with_spec("unadmitted-act", act_tla, act_cfg);
    let tlc = tlx_testkit::tlx_default!().check("UnadmittedActViolation.tla").args(["-tlc", "-interp", "-workers", "1"]).dir(&dir).run();
    assert_eq!(tlc.code, 13, "{}", tlc.text());
    let expected_act_trace = [
        "State 1: <Initial predicate>",
        "/\\ state = (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0)",
        "/\\ c = 0",
        "/\\ tag = 0",
        "State 2: <Next line 6, col 9 to line 10, col 21 of module UnadmittedActViolation>",
        "/\\ state = (n1 :> 1 @@ n2 :> 0 @@ n3 :> 0)",
        "/\\ c = 1",
        "/\\ tag = 1",
        "State 3: <Next line 6, col 9 to line 10, col 21 of module UnadmittedActViolation>",
        "/\\ state = (n1 :> 1 @@ n2 :> 0 @@ n3 :> 0)",
        "/\\ c = 2",
        "/\\ tag = 1",
    ];
    assert_eq!(trace_lines(&tlc.stdout), expected_act_trace, "{}", tlc.text());
    for tr in run_all_tiers(&dir, "UnadmittedActViolation.tla", &["-optimize"], true) {
        assert_eq!(tr.run.code, 13, "{}: {}", tr.tier, tr.run.text());
        assert!(tr.run.stdout.contains("unobserved-state-projection"), "{}: {}", tr.tier, tr.run.text());
        assert_eq!(trace_lines(&tr.run.stdout), expected_act_trace, "{}: {}", tr.tier, tr.run.text());
    }
}

#[test]
fn init_prop_violation_on_unadmitted_initial_state_and_admitted_deadlock_match_tlc() {
    let init_tla = r#"---- MODULE UnadmittedInitProp ----
EXTENDS Naturals
CONSTANT Nodes
VARIABLE state, c
Init == state = [n \in Nodes |-> 0] /\ c \in {0, 1}
Next == \E n \in Nodes : state' = [state EXCEPT ![n] = 1 - @] /\ UNCHANGED c
Inv == c \in {0, 1}
InitProp == c = 0
Limit == c = 0
====
"#;
    let init_cfg = "INIT Init\nNEXT Next\nCONSTANT Nodes = {n1, n2, n3}\nINVARIANT Inv\nPROPERTY InitProp\nCONSTRAINT Limit\n";
    let dir = tlx_testkit::TempDir::with_spec("unadmitted-init", init_tla, init_cfg);
    let tlc = tlx_testkit::tlx_default!().check("UnadmittedInitProp.tla").args(["-tlc", "-interp", "-workers", "1"]).dir(&dir).run();
    assert_eq!(tlc.code, 13, "{}", tlc.text());
    let expected_init_trace = ["/\\ state = (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0)", "/\\ c = 1"];
    assert_eq!(trace_lines(&tlc.stdout), expected_init_trace, "{}", tlc.text());
    for tr in run_all_tiers(&dir, "UnadmittedInitProp.tla", &[], true) {
        assert_eq!(tr.run.code, 13, "{}: {}", tr.tier, tr.run.text());
        assert!(tr.run.stdout.contains("Optimizations: symmetry"), "{}: {}", tr.tier, tr.run.text());
        assert_eq!(trace_lines(&tr.run.stdout), expected_init_trace, "{}: {}", tr.tier, tr.run.text());
    }

    let dead_tla = r#"---- MODULE AdmittedDeadlock ----
EXTENDS Naturals
CONSTANT Nodes
VARIABLE state, c
Init == state = [n \in Nodes |-> 0] /\ c = 0
Next == c = 0 /\ \E n \in Nodes : state' = [state EXCEPT ![n] = 1] /\ c' = 1
Inv == c \in {0, 1}
Limit == c <= 1
====
"#;
    let dead_cfg = "INIT Init\nNEXT Next\nCONSTANT Nodes = {n1, n2, n3}\nINVARIANT Inv\nCONSTRAINT Limit\n";
    let dir = tlx_testkit::TempDir::with_spec("admitted-deadlock", dead_tla, dead_cfg);
    let tlc = tlx_testkit::tlx_default!().check("AdmittedDeadlock.tla").args(["-tlc", "-interp", "-workers", "1"]).dir(&dir).run();
    assert_eq!(tlc.code, 11, "{}", tlc.text());
    for tr in run_all_tiers(&dir, "AdmittedDeadlock.tla", &[], true) {
        assert_eq!(tr.run.code, 11, "{}: {}", tr.tier, tr.run.text());
        assert!(tr.run.stdout.contains("Optimizations: symmetry"), "{}: {}", tr.tier, tr.run.text());
        assert_eq!(trace_lines(&tr.run.stdout), trace_lines(&tlc.stdout), "{}: {}", tr.tier, tr.run.text());
    }
}

struct RefusalExpectation<'a> {
    extra_args: &'a [&'a str],
    expected_code: i32,
    expected_diag: Option<&'a str>,
    forbidden_opt: &'a str,
    expect_rule_algebra_record: bool,
}

fn assert_no_generated_cert(tier: &str, proof_dir: &Path) {
    if let Ok(entries) = std::fs::read_dir(proof_dir) {
        for entry in entries {
            let lean = std::fs::read_to_string(entry.unwrap().path().join("Optimization.lean")).unwrap();
            assert!(!lean.contains("theorem certificate : Certificate"), "{tier}: unexpected generated reduction certificate");
            assert!(!lean.contains("theorem constrained_certificate :"), "{tier}: unexpected constrained reduction certificate");
        }
    }
}

fn assert_refused_across_all_tiers(label: &str, tla: &str, cfg: &str, module: &str, exp: RefusalExpectation<'_>) {
    let dir = tlx_testkit::TempDir::with_spec(label, tla, cfg);
    for tr in run_all_tiers(&dir, module, exp.extra_args, false) {
        let tier = &tr.tier;
        assert_eq!(tr.run.code, exp.expected_code, "{label}/{tier}: {}", tr.run.text());
        if let Some(diag) = exp.expected_diag {
            assert!(tr.run.text().contains(diag), "{label}/{tier}: missing `{diag}` in:\n{}", tr.run.text());
        }
        assert!(tr.run.stdout.contains("Optimizations: none applicable."), "{label}/{tier}: {}", tr.run.text());
        assert!(!tr.run.stdout.contains(exp.forbidden_opt), "{label}/{tier}: {}", tr.run.text());
        if exp.expect_rule_algebra_record {
            assert!(tr.run.stdout.contains("no reduction applied; rule algebra only"), "{label}/{tier}: {}", tr.run.text());
            assert_no_generated_cert(tier, &tr.proof_dir);
        } else {
            assert!(!tr.proof_dir.exists(), "{label}/{tier}: expected no proof directory");
        }
    }
}

#[test]
fn refuses_erasure_on_observed_subscript_and_partial_observations_across_all_tiers() {
    let subscript_tla = r#"---- MODULE RefusalCheck ----
EXTENDS Naturals
CONSTANT Nodes
VARIABLE state, tag
Init == state = [n \in Nodes |-> 0] /\ tag = 0
Next == \E n \in Nodes : state' = [state EXCEPT ![n] = 1 - @] /\ tag' = 1
Inv == \A n \in Nodes : state[n] \in {0, 1}
ActProp == [][\A n \in Nodes : state'[n] \in {0, 1}]_<<state, tag>>
====
"#;
    assert_refused_across_all_tiers(
        "refusal-subscript",
        subscript_tla,
        "INIT Init\nNEXT Next\nCONSTANT Nodes = {n1, n2}\nINVARIANT Inv\nPROPERTY ActProp\n",
        "RefusalCheck.tla",
        RefusalExpectation {
            extra_args: &["-optimize", "-noautosymmetry"],
            expected_code: 0,
            expected_diag: None,
            forbidden_opt: "unobserved-state-projection",
            expect_rule_algebra_record: true,
        },
    );

    let partial_cons_tla = r#"---- MODULE PartialConstraintErasure ----
EXTENDS Naturals
VARIABLE x, tag
Init == x = 0 /\ tag = 0
Next == x' = 1 /\ tag' = 1
Limit == \A i \in {0} : (x \div i) >= 0
====
"#;
    assert_refused_across_all_tiers(
        "refusal-partial-constraint",
        partial_cons_tla,
        "INIT Init\nNEXT Next\nCONSTRAINT Limit\n",
        "PartialConstraintErasure.tla",
        RefusalExpectation {
            extra_args: &["-optimize", "-noautosymmetry"],
            expected_code: 75,
            expected_diag: Some("The second argument of \\div is 0."),
            forbidden_opt: "unobserved-state-projection",
            expect_rule_algebra_record: true,
        },
    );

    let partial_act_tla = r#"---- MODULE PartialActionErasure ----
EXTENDS Naturals
VARIABLE x, tag
Init == x = 0 /\ tag = 0
Next == x' = 1 /\ tag' = 1
ActLimit == \A i \in {0} : (x' \div i) >= 0
====
"#;
    let partial_act_cfg = "INIT Init\nNEXT Next\nACTION_CONSTRAINT ActLimit\n";
    let tlc_dir = tlx_testkit::TempDir::with_spec("refusal-partial-action-tlc", partial_act_tla, partial_act_cfg);
    let tlc_act = tlx_testkit::tlx_default!().check("PartialActionErasure.tla").args(["-tlc", "-interp"]).dir(&tlc_dir).run();
    assert_ne!(tlc_act.code, 0, "{}", tlc_act.text());
    assert_refused_across_all_tiers(
        "refusal-partial-action",
        partial_act_tla,
        partial_act_cfg,
        "PartialActionErasure.tla",
        RefusalExpectation {
            extra_args: &["-optimize", "-noautosymmetry"],
            expected_code: tlc_act.code,
            expected_diag: Some("The second argument of \\div is 0."),
            forbidden_opt: "unobserved-state-projection",
            expect_rule_algebra_record: true,
        },
    );
}

#[test]
fn refuses_partial_and_overflowing_sequence_fallback_constraints_across_all_tiers() {
    let partial_seq_tla = r#"---- MODULE PartialSeqFallback ----
EXTENDS Naturals, Sequences
VARIABLE s
Init == s = <<>>
Next == Len(s) < 3 /\ \E v \in {1, 2} : s' = Append(s, v)
Inv == s \in Seq({1, 2})
Limit == \A i \in {0} : (Len(s) \div i) >= 0
====
"#;
    assert_refused_across_all_tiers(
        "refusal-partial-seq",
        partial_seq_tla,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nCONSTRAINT Limit\n",
        "PartialSeqFallback.tla",
        RefusalExpectation {
            extra_args: &["-optimize", "-noautosymmetry"],
            expected_code: 75,
            expected_diag: Some("The second argument of \\div is 0."),
            forbidden_opt: "sequence-length-projection",
            expect_rule_algebra_record: true,
        },
    );

    let overflow_seq_tla = r#"---- MODULE OverflowSeqFallback ----
EXTENDS Naturals, Sequences
VARIABLE s
Init == s = <<>>
Next == Len(s) < 3 /\ \E v \in {1, 2} : s' = Append(s, v)
Inv == s \in Seq({1, 2})
Limit == \A i \in {0} : (2147483647 + Len(s)) >= 0
====
"#;
    let overflow_seq_cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\nCONSTRAINT Limit\n";
    let tlc_dir = tlx_testkit::TempDir::with_spec("refusal-overflow-seq-tlc", overflow_seq_tla, overflow_seq_cfg);
    let tlc_ovf = tlx_testkit::tlx_default!().check("OverflowSeqFallback.tla").args(["-tlc", "-interp"]).dir(&tlc_dir).run();
    assert_ne!(tlc_ovf.code, 0, "{}", tlc_ovf.text());
    assert_refused_across_all_tiers(
        "refusal-overflow-seq",
        overflow_seq_tla,
        overflow_seq_cfg,
        "OverflowSeqFallback.tla",
        RefusalExpectation {
            extra_args: &["-optimize", "-noautosymmetry"],
            expected_code: tlc_ovf.code,
            expected_diag: Some("Overflow"),
            forbidden_opt: "sequence-length-projection",
            expect_rule_algebra_record: true,
        },
    );
}

#[test]
fn refuses_impure_const_subst_and_builtin_override_across_all_tiers() {
    let effect_subst_tla = r#"---- MODULE UnusedEffectSubstCli ----
EXTENDS Naturals, TLC
CONSTANT C
VARIABLE x, tag
DoPrint == PrintT("binding")
Wrapper == DoPrint
PureHelper(n) == n + 1
PureWrapper == PureHelper(1)
Init == x = 0 /\ tag = 0
Next == x' = 1 /\ tag' = 1
Inv == x \in {0, 1}
====
"#;
    assert_refused_across_all_tiers(
        "refusal-effect-subst",
        effect_subst_tla,
        "INIT Init\nNEXT Next\nCONSTANT C <- Wrapper\nINVARIANT Inv\n",
        "UnusedEffectSubstCli.tla",
        RefusalExpectation {
            extra_args: &["-optimize", "-noautosymmetry"],
            expected_code: 0,
            expected_diag: None,
            forbidden_opt: "unobserved-state-projection",
            expect_rule_algebra_record: true,
        },
    );

    let pure_dir = tlx_testkit::TempDir::with_spec(
        "accept-pure-subst",
        effect_subst_tla,
        "INIT Init\nNEXT Next\nCONSTANT C <- PureWrapper\nINVARIANT Inv\n",
    );
    for tr in run_all_tiers(&pure_dir, "UnusedEffectSubstCli.tla", &["-optimize", "-noautosymmetry"], false) {
        assert_eq!(tr.run.code, 0, "{}: {}", tr.tier, tr.run.text());
        assert!(tr.run.stdout.contains("unobserved-state-projection"), "{}: {}", tr.tier, tr.run.text());
    }

    let override_tla = r#"---- MODULE RefusalOverride ----
EXTENDS Naturals
CONSTANT Nodes
VARIABLE state
SmallNat == 0..2
Init == state = [n \in Nodes |-> 0]
Next == \E n \in Nodes : state' = [state EXCEPT ![n] = 1 - @]
Inv == \A n \in Nodes : state[n] \in Nat
====
"#;
    assert_refused_across_all_tiers(
        "refusal-override",
        override_tla,
        "INIT Init\nNEXT Next\nCONSTANTS\n  Nodes = {n1, n2}\n  Nat <- SmallNat\nINVARIANT Inv\n",
        "RefusalOverride.tla",
        RefusalExpectation {
            extra_args: &[],
            expected_code: 0,
            expected_diag: None,
            forbidden_opt: "Optimizations: symmetry",
            expect_rule_algebra_record: false,
        },
    );
}
