//! End-to-end abstraction emission and generated-model execution.

use std::time::Duration;

const CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
const SPEC: &str =
    "---- MODULE Counter ----\nEXTENDS Naturals\nVARIABLE c\nInit == c = 0\nNext == c' = c + 1 \\/ c' = 0\nInv == c < 3 \\/ c >= 3\n====\n";

#[test]
fn emits_a_finite_model_checked_by_every_execution_tier() {
    let dir = tlx_testkit::TempDir::with_spec("abstraction-cli", SPEC, CFG);
    let run = tlx_testkit::tlx!().args(["abstract", "Counter.tla", "-output", "out"]).dir(&dir).run();
    assert_eq!(run.code, 0, "{}", run.text());
    assert!(run.stdout.contains("no safety verdict is claimed"));
    assert!(!run.stdout.contains("Model checking completed"));
    let report = std::fs::read_to_string(dir.join("out/abstraction.txt")).unwrap();
    assert!(report.contains("domain 0..3"));
    assert!(report.contains("Invariant0: Inv"));
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx!()
            .check("Abstract.tla")
            .args(args)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(dir.join("out"))
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{tier}: {}", run.text());
        assert!(run.stdout.contains("4 distinct states found"), "{tier}: {}", run.text());
    }
}

#[test]
fn abstract_violation_is_not_misreported_as_a_concrete_trace() {
    let dir = tlx_testkit::TempDir::with_spec("abstraction-violation", &SPEC.replace("c < 3 \\/ c >= 3", "c < 3"), CFG);
    let generated = tlx_testkit::tlx!().args(["abstract", "Counter.tla", "-output", "out"]).dir(&dir).run();
    assert_eq!(generated.code, 0, "{}", generated.text());
    let run = tlx_testkit::tlx!().check("Abstract.tla").dir(dir.join("out")).run();
    assert_eq!(run.code, 12, "{}", run.text());
    assert!(run.stdout.contains("Invariant Invariant0 is violated"), "{}", run.text());
    let report = std::fs::read_to_string(dir.join("out/abstraction.txt")).unwrap();
    assert!(report.contains("abstract representatives, not concrete counter values"));
}

#[test]
fn refusal_leaves_no_artifacts_and_existing_outputs_are_preserved() {
    let dir = tlx_testkit::TempDir::with_spec("abstraction-refusal", &SPEC.replace("c' = c + 1", "c' = c - 1"), CFG);
    let run = tlx_testkit::tlx!().args(["abstract", "Counter.tla", "-output", "out"]).dir(&dir).run();
    assert_eq!(run.code, 2);
    assert!(run.stderr.contains("decrements are unsupported"), "{}", run.text());
    assert!(!dir.join("out").exists());
    dir.write("Counter.tla", SPEC);
    let run = tlx_testkit::tlx!().args(["abstract", "Counter.tla", "-output", "out"]).dir(&dir).run();
    assert_eq!(run.code, 0, "{}", run.text());
    let bytes = std::fs::read(dir.join("out/Abstract.tla")).unwrap();
    let run = tlx_testkit::tlx!().args(["abstract", "Counter.tla", "-output", "out"]).dir(&dir).run();
    assert_eq!(run.code, 2);
    assert_eq!(bytes, std::fs::read(dir.join("out/Abstract.tla")).unwrap());
}

#[test]
fn compatibility_flags_cannot_silently_enable_abstraction() {
    for args in [vec!["abstract", "-tlc"], vec!["check", "-abstract"]] {
        let run = tlx_testkit::tlx!().args(args).run();
        assert_eq!(run.code, 2, "{}", run.text());
    }
    let run = tlx_testkit::tlx!().args(["abstract", "--help"]).run();
    assert_eq!(run.code, 0);
    assert!(run.stdout.contains("does not check or claim safety"));
}

#[test]
fn cleanup_and_saturation_compose_in_every_execution_tier() {
    let spec = "---- MODULE Counter ----\nEXTENDS Naturals\nVARIABLES fixed, c\nInit == fixed = 7 /\\ c = 0\nNext == (fixed /= 7 /\\ c > 2147483647 /\\ c' = c + 1 /\\ UNCHANGED fixed) \\/ (UNCHANGED fixed /\\ c' = c + 1)\nInv == fixed = 7 /\\ (c < 3 \\/ c >= 3)\n====\n";
    let dir = tlx_testkit::TempDir::with_spec("abstraction-cleanup", spec, CFG);
    let run = tlx_testkit::tlx!().args(["abstract", "Counter.tla", "-output", "out"]).dir(&dir).run();
    assert_eq!(run.code, 0, "{}", run.text());
    let report = std::fs::read_to_string(dir.join("out/abstraction.txt")).unwrap();
    for pass in ["constant-state-propagation", "predicate-simplification", "dead-action-elimination", "threshold-counter-saturation"] {
        assert!(report.contains(pass), "{report}");
    }
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx!()
            .check("Abstract.tla")
            .args(args)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(dir.join("out"))
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{tier}: {}", run.text());
        assert!(run.stdout.contains("4 distinct states found"), "{tier}: {}", run.text());
    }
}

#[test]
fn empty_next_still_checks_true_and_false_initial_invariants() {
    for (inv, expected) in [("c = 5", 0), ("c /= 5", 12)] {
        let spec = format!(
            "---- MODULE Counter ----\nEXTENDS Naturals\nVARIABLE c\nInit == c = 5\nNext == c < 0 /\\ c' = c + 1\nInv == {inv}\n====\n"
        );
        let dir = tlx_testkit::TempDir::with_spec("abstraction-empty", &spec, CFG);
        let run = tlx_testkit::tlx!().args(["abstract", "Counter.tla", "-output", "out"]).dir(&dir).run();
        assert_eq!(run.code, 0, "{}", run.text());
        let generated = std::fs::read_to_string(dir.join("out/Abstract.tla")).unwrap();
        assert!(generated.contains("Next == (v0 /= v0) /\\ UNCHANGED <<v0>>"));
        for (tier, args, env) in tlx_testkit::cli::TIERS {
            let run = tlx_testkit::tlx!()
                .check("Abstract.tla")
                .args(args)
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .dir(dir.join("out"))
                .timeout(Duration::from_secs(60))
                .run();
            assert_eq!(run.code, expected, "{tier}: {}", run.text());
        }
    }
}
