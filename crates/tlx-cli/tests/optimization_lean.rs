//! Lean emission is mandatory for opt-in checking; verification is never implicit.

const SPEC: &str = r#"---- MODULE ProofOutput ----
EXTENDS Integers
VARIABLE x, tag
Init == x = 0 /\ tag = "init"
Next == (x' = 1 - x /\ tag' = "flip") \/ (UNCHANGED x /\ tag' = "idle")
Inv == x \in {0, 1}
====
"#;
const CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\n";

fn artifacts(dir: &std::path::Path) -> Vec<std::path::PathBuf> {
    std::fs::read_dir(dir.join("proofs")).unwrap().map(|e| e.unwrap().path().join("Optimization.lean")).collect()
}

#[test]
fn enabled_check_always_emits_and_preserves_previous_runs() {
    let dir = tlx_testkit::TempDir::with_spec("lean-output", SPEC, CFG);
    let mut previous = None;
    for (idx, spec) in [SPEC.to_string(), SPEC.to_string(), SPEC.replace("1 - x", "x")].into_iter().enumerate() {
        dir.write("ProofOutput.tla", &spec);
        let run = tlx_testkit::tlx_default!()
            .check("ProofOutput.tla")
            .args(["-interp", "-optimize", "-noautosymmetry"])
            .env("TLX_PROOF_DIR", dir.join("proofs"))
            .dir(&dir)
            .run();
        assert_eq!(run.code, 0, "{}", run.text());
        assert!(run.stdout.contains("Lean output:"), "{}", run.text());
        assert!(run.stdout.contains("not verified; parametric unobserved-state rule-IR certificate"), "{}", run.text());
        assert!(!dir.join(".tlx-proofs").exists());
        let paths = artifacts(&dir);
        match (idx, &previous) {
            (0, None) => {
                assert_eq!(paths.len(), 1);
                let text = std::fs::read_to_string(&paths[0]).unwrap();
                assert!(text.contains("def rule : String := \"unobserved-state-projection\""));
                assert!(text.contains("theorem safety_iff"));
                assert!(text.contains("namespace TlxOptimization.GeneratedErasure"));
                assert!(!text.contains("sorry"));
                previous = Some((paths[0].clone(), text.into_bytes()));
            }
            (1, Some((path, bytes))) => {
                assert_eq!(paths.len(), 1, "identical certificate should reuse its content-addressed slot");
                assert_eq!(&std::fs::read(path).unwrap(), bytes);
            }
            (2, Some((path, bytes))) => {
                assert_eq!(paths.len(), 2);
                assert_eq!(&std::fs::read(path).unwrap(), bytes);
                let other = paths.iter().find(|p| *p != path).unwrap();
                assert_ne!(&std::fs::read(other).unwrap(), bytes);
            }
            _ => unreachable!(),
        }
    }
}

#[test]
fn refusal_emits_a_no_pass_record_but_disabled_mode_does_not() {
    for flags in [vec![], vec!["-optimize", "-tlc"], vec!["-optimize"]] {
        let spec = SPEC.replace("Inv == x \\in {0, 1}", "Inv == x \\in {0, 1} /\\ tag \\in {\"init\", \"flip\", \"idle\"}");
        let dir = tlx_testkit::TempDir::with_spec("lean-no-pass", &spec, CFG);
        let run = tlx_testkit::tlx_default!()
            .check("ProofOutput.tla")
            .args(["-interp", "-noautosymmetry"])
            .args(flags.clone())
            .env("TLX_PROOF_DIR", dir.join("proofs"))
            .dir(&dir)
            .run();
        assert_eq!(run.code, 0, "{}", run.text());
        assert!(!dir.join(".tlx-proofs").exists());
        if flags == ["-optimize"] {
            let paths = artifacts(&dir);
            assert_eq!(paths.len(), 1);
            assert!(std::fs::read_to_string(&paths[0]).unwrap().contains("def rule : String := \"none\""));
        } else {
            assert!(!dir.join("proofs").exists());
        }
    }
}

#[test]
fn required_output_failure_stops_before_search() {
    let dir = tlx_testkit::TempDir::with_spec("lean-io-error", SPEC, CFG);
    dir.write("blocked-proofs", "preserve this file");
    let blocked = dir.join("blocked-proofs");
    for via_flag in [false, true] {
        let mut cmd = tlx_testkit::tlx_default!();
        cmd.check("ProofOutput.tla").args(["-interp", "-optimize", "-noautosymmetry"]).dir(&dir);
        if via_flag {
            cmd.arg("-proofdir").arg(&blocked);
        } else {
            cmd.env("TLX_PROOF_DIR", &blocked);
        }
        let run = cmd.run();
        assert_eq!(run.code, 2, "{}", run.text());
        assert!(run.stdout.contains("Cannot write mandatory optimization Lean output"), "{}", run.text());
        assert!(!run.stdout.contains("Computing initial states"));
        assert_eq!(std::fs::read_to_string(&blocked).unwrap(), "preserve this file");
    }
}

#[cfg(unix)]
#[test]
fn lean_on_path_is_not_invoked() {
    use std::os::unix::fs::PermissionsExt;
    let dir = tlx_testkit::TempDir::with_spec("lean-no-verification", HISTORY, CFG);
    for name in ["lean", "lake", "elan"] {
        dir.write(name, "#!/bin/sh\n: > verifier-was-run\nexit 99\n");
        std::fs::set_permissions(dir.join(name), std::fs::Permissions::from_mode(0o755)).unwrap();
    }
    let mut paths = vec![dir.to_path_buf()];
    paths.extend(std::env::split_paths(&std::env::var_os("PATH").unwrap_or_default()));
    let run = tlx_testkit::tlx_default!()
        .check("ProofOutput.tla")
        .args(["-interp", "-optimize", "-noautosymmetry"])
        .env("TLX_PROOF_DIR", dir.join("proofs"))
        .env("PATH", std::env::join_paths(paths).unwrap())
        .dir(&dir)
        .run();
    assert_eq!(run.code, 0, "{}", run.text());
    assert_eq!(artifacts(&dir).len(), 1);
    assert!(!dir.join("verifier-was-run").exists());
}

const HISTORY: &str = r#"---- MODULE ProofOutput ----
EXTENDS Naturals, Sequences
VARIABLE h, x
Init == h = <<0>> /\ x = 0
Next == /\ x' = IF x = 0 THEN 1 ELSE 0
        /\ h' = IF x = 0 THEN Append(h, x) ELSE <<x>>
Inv == /\ h \in Seq({0, 1}) /\ x \in {0, 1}
       /\ (h = <<>> \/ \A i \in 1..Len(h):
              h[i] = 0 \/ \E j \in 1..i: h[j] = h[i])
====
"#;

#[test]
fn history_certificate_is_generated_from_the_actual_predicate() {
    for (spec, quantifier) in
        [(HISTORY.to_string(), "∃ l"), (HISTORY.replace("\\E j", "\\A j"), "∀ l"), (HISTORY.replace("\\A i", "\\E i"), "(¬ (s.2")]
    {
        let dir = tlx_testkit::TempDir::with_spec("lean-history", &spec, CFG);
        let run = tlx_testkit::tlx_default!()
            .check("ProofOutput.tla")
            .args(["-interp", "-optimize", "-noautosymmetry"])
            .env("TLX_PROOF_DIR", dir.join("proofs"))
            .dir(&dir)
            .run();
        assert!([0, 12].contains(&run.code), "{}", run.text());
        assert!(run.stdout.contains("not verified; parametric history rule-IR certificate"), "{}", run.text());
        let text = std::fs::read_to_string(&artifacts(&dir)[0]).unwrap();
        let generated = text.split("namespace TlxOptimization.GeneratedHistory").nth(1).unwrap();
        assert!(generated.contains(quantifier));
        assert!(generated.contains("sem.number (0)"));
        assert!(generated.contains("Transfer.append"));
        assert!(generated.contains("Transfer.reset"));
        assert!(generated.contains("if sem.test"));
        assert!(generated.contains("def before :="));
        assert!(generated.contains("theorem certificate : Certificate"));
        assert!(generated.contains("theorem counterexample_lifts"));
        assert!(!text.contains("No model-level Certificate is constructed"));
        assert!(!text.contains("sorry"));
    }
}

#[test]
fn unsupported_certificate_scope_disables_the_rule() {
    let primed = HISTORY.replace(
        r#"Next == /\ x' = IF x = 0 THEN 1 ELSE 0
        /\ h' = IF x = 0 THEN Append(h, x) ELSE <<x>>"#,
        r#"Next == /\ h' = IF x = 0 THEN Append(h, x) ELSE <<x>>
        /\ x' = IF (h = <<>>)' THEN 0 ELSE IF x = 0 THEN 1 ELSE 0"#,
    );
    for (spec, cfg) in [
        (primed, CFG.to_string()),
        (HISTORY.replace("====", "ActLimit == x' <= 1\n===="), format!("{CFG}ACTION_CONSTRAINT ActLimit\n")),
        (HISTORY.replace("====", "MyAlias == [x |-> x]\n===="), format!("{CFG}ALIAS MyAlias\n")),
    ] {
        let dir = tlx_testkit::TempDir::with_spec("lean-history-scope", &spec, &cfg);
        let run = tlx_testkit::tlx_default!()
            .check("ProofOutput.tla")
            .args(["-interp", "-optimize", "-noautosymmetry"])
            .env("TLX_PROOF_DIR", dir.join("proofs"))
            .dir(&dir)
            .run();
        assert_eq!(run.code, 0, "{}", run.text());
        assert!(!run.stdout.contains("history-summary-projection"), "{}", run.text());
        assert!(run.stdout.contains("not verified; no reduction applied; rule algebra only"), "{}", run.text());
        let text = std::fs::read_to_string(&artifacts(&dir)[0]).unwrap();
        assert!(!text.contains("namespace TlxOptimization.GeneratedHistory"));
    }
}

#[test]
fn constrained_history_certificate_emits_constrained_theorems() {
    let spec = HISTORY.replace("====", "Limit == x <= 1\n====");
    let cfg = format!("{CFG}CONSTRAINT Limit\n");
    let dir = tlx_testkit::TempDir::with_spec("lean-history-constrained", &spec, &cfg);
    let run = tlx_testkit::tlx_default!()
        .check("ProofOutput.tla")
        .args(["-interp", "-optimize", "-noautosymmetry"])
        .env("TLX_PROOF_DIR", dir.join("proofs"))
        .dir(&dir)
        .run();
    assert_eq!(run.code, 0, "{}", run.text());
    assert!(run.stdout.contains("history-summary-projection"), "{}", run.text());
    let text = std::fs::read_to_string(&artifacts(&dir)[0]).unwrap();
    assert!(text.contains("namespace TlxOptimization.GeneratedHistory"));
    assert!(text.contains("theorem constrained_certificate"));
    assert!(text.contains("theorem constrained_optimization_correct"));
    assert!(text.contains("theorem admitted_deadlock_preserved"));
}

#[test]
fn history_certificates_support_zero_and_multiple_monitors() {
    for (spec, cfg, count) in [
        (HISTORY.replace("Inv ==", "Unused ==").replace("====", "Inv == h \\in Seq({0, 1}) /\\ x \\in {0, 1}\n===="), CFG.to_string(), 0),
        (HISTORY.replace("====", "More == \\A k \\in 1..Len(h): h[k] # 2\n===="), format!("{CFG}INVARIANT More\n"), 2),
    ] {
        let dir = tlx_testkit::TempDir::with_spec("lean-monitor-count", &spec, &cfg);
        let run = tlx_testkit::tlx_default!()
            .check("ProofOutput.tla")
            .args(["-interp", "-optimize", "-noautosymmetry"])
            .env("TLX_PROOF_DIR", dir.join("proofs"))
            .dir(&dir)
            .run();
        assert_eq!(run.code, 0, "{}", run.text());
        let text = std::fs::read_to_string(&artifacts(&dir)[0]).unwrap();
        assert!(text.contains(&format!("(i : Fin {count})")), "{}", run.text());
        assert!(text.contains("namespace TlxOptimization.GeneratedHistory"));
    }
}
