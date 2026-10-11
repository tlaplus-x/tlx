//! End-to-end optimization emission and generated-model execution.

use std::time::Duration;

const CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
const SPEC: &str =
    "---- MODULE Counter ----\nEXTENDS Naturals\nVARIABLE c\nInit == c = 0\nNext == c' = c + 1 \\/ c' = 0\nInv == c < 3 \\/ c >= 3\n====\n";

#[test]
fn emits_a_finite_model_checked_by_every_execution_tier() {
    let dir = tlx_testkit::TempDir::with_spec("optimization-cli", SPEC, CFG);
    let run = tlx_testkit::tlx!().args(["optimize", "Counter.tla", "-output", "out"]).dir(&dir).run();
    assert_eq!(run.code, 0, "{}", run.text());
    assert!(run.stdout.contains("no safety verdict is claimed"));
    assert!(!run.stdout.contains("Model checking completed"));
    let report = std::fs::read_to_string(dir.join("out/optimization.txt")).unwrap();
    assert!(report.contains("domain 0..3"));
    assert!(report.contains("Invariant0: Inv"));
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx!()
            .check("Optimized.tla")
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
    let dir = tlx_testkit::TempDir::with_spec("optimization-violation", &SPEC.replace("c < 3 \\/ c >= 3", "c < 3"), CFG);
    let generated = tlx_testkit::tlx!().args(["optimize", "Counter.tla", "-output", "out"]).dir(&dir).run();
    assert_eq!(generated.code, 0, "{}", generated.text());
    let run = tlx_testkit::tlx!().check("Optimized.tla").dir(dir.join("out")).run();
    assert_eq!(run.code, 12, "{}", run.text());
    assert!(run.stdout.contains("Invariant Invariant0 is violated"), "{}", run.text());
    let report = std::fs::read_to_string(dir.join("out/optimization.txt")).unwrap();
    assert!(report.contains("abstract representatives, not concrete counter values"));
}

#[test]
fn refusal_leaves_no_artifacts_and_existing_outputs_are_preserved() {
    let dir = tlx_testkit::TempDir::with_spec("optimization-refusal", &SPEC.replace("c' = c + 1", "c' = c - 1"), CFG);
    let run = tlx_testkit::tlx!().args(["optimize", "Counter.tla", "-output", "out"]).dir(&dir).run();
    assert_eq!(run.code, 2);
    assert!(run.stderr.contains("decrements are unsupported"), "{}", run.text());
    assert!(!dir.join("out").exists());
    dir.write("Counter.tla", SPEC);
    let run = tlx_testkit::tlx!().args(["optimize", "Counter.tla", "-output", "out"]).dir(&dir).run();
    assert_eq!(run.code, 0, "{}", run.text());
    let bytes = std::fs::read(dir.join("out/Optimized.tla")).unwrap();
    let run = tlx_testkit::tlx!().args(["optimize", "Counter.tla", "-output", "out"]).dir(&dir).run();
    assert_eq!(run.code, 2);
    assert_eq!(bytes, std::fs::read(dir.join("out/Optimized.tla")).unwrap());
}

#[test]
fn compatibility_flags_cannot_silently_enable_optimization() {
    for args in [vec!["optimize", "-tlc"], vec!["check", "-abstract"]] {
        let run = tlx_testkit::tlx!().args(args).run();
        assert_eq!(run.code, 2, "{}", run.text());
    }
    let run = tlx_testkit::tlx!().args(["optimize", "--help"]).run();
    assert_eq!(run.code, 0);
    assert!(run.stdout.contains("does not check or claim safety"));
}

#[test]
fn cleanup_and_saturation_compose_in_every_execution_tier() {
    let spec = "---- MODULE Counter ----\nEXTENDS Naturals\nVARIABLES fixed, c\nInit == fixed = 7 /\\ c = 0\nNext == (fixed /= 7 /\\ c > 2147483647 /\\ c' = c + 1 /\\ UNCHANGED fixed) \\/ (UNCHANGED fixed /\\ c' = c + 1)\nInv == fixed = 7 /\\ (c < 3 \\/ c >= 3)\n====\n";
    let dir = tlx_testkit::TempDir::with_spec("optimization-cleanup", spec, CFG);
    let run = tlx_testkit::tlx!().args(["optimize", "Counter.tla", "-output", "out"]).dir(&dir).run();
    assert_eq!(run.code, 0, "{}", run.text());
    let report = std::fs::read_to_string(dir.join("out/optimization.txt")).unwrap();
    for pass in ["constant-state-propagation", "predicate-simplification", "dead-action-elimination", "threshold-counter-saturation"] {
        assert!(report.contains(pass), "{report}");
    }
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx!()
            .check("Optimized.tla")
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
        let dir = tlx_testkit::TempDir::with_spec("optimization-empty", &spec, CFG);
        let run = tlx_testkit::tlx!().args(["optimize", "Counter.tla", "-output", "out"]).dir(&dir).run();
        assert_eq!(run.code, 0, "{}", run.text());
        let generated = std::fs::read_to_string(dir.join("out/Optimized.tla")).unwrap();
        assert!(generated.contains("Next == (v0 /= v0) /\\ UNCHANGED <<v0>>"));
        for (tier, args, env) in tlx_testkit::cli::TIERS {
            let run = tlx_testkit::tlx!()
                .check("Optimized.tla")
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

// Cached TLC output is tied to the exact generated module/config below. An emitter
// change must refresh the oracle, not silently reuse evidence for another model.
fn check_oracle(dir: &std::path::Path, module: &str, oracle: &str, flags: &[&str]) {
    let code: i32 = oracle.lines().next().unwrap().strip_prefix("# exit ").unwrap().parse().unwrap();
    assert!(matches!(code, 0 | 12), "fixture must be a completed safety check");
    let outcome = if code == 0 {
        "Model checking completed. No error has been found.".to_string()
    } else {
        format!("Invariant {} is violated", if module == "Counter" { "Inv" } else { "Invariant0" })
    };
    assert!(oracle.contains(&outcome), "oracle missing outcome: {oracle}");
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .args(["check", &format!("{module}.tla"), "-tool", "-workers", "1"])
            .args(args)
            .args(flags)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, code, "{module}/{tier}: {}", run.text());
        assert!(run.stdout.contains(&outcome), "{module}/{tier}: {}", run.text());
        assert_eq!(
            tlx_testkit::cli::counts(&run.stdout.replace(" (optimization-reduced).", ".")),
            tlx_testkit::cli::counts(oracle),
            "{module}/{tier}: {}",
            run.text()
        );
        let trace_length = |text: &str| text.lines().filter(|line| line.starts_with("@!@!@STARTMSG 2217:4")).count();
        assert_eq!(trace_length(&run.stdout), trace_length(oracle), "{module}/{tier}: {}", run.text());
        // These fixtures have a single deterministic counterexample. Compare
        // actual variable values, not generated names or source-label formatting.
        let values = |text: &str| {
            text.lines()
                .map(|line| line.trim_start_matches("/\\ "))
                .filter(|line| {
                    line.starts_with("c = ") || line.starts_with("fixed = ") || line.starts_with("v0 = ") || line.starts_with("v1 = ")
                })
                .map(str::to_string)
                .collect::<Vec<_>>()
        };
        assert_eq!(values(&run.stdout), values(oracle), "{module}/{tier}: {}", run.text());
    }
}

macro_rules! oracle_case {
    ($test:ident, $case:literal) => {
        #[test]
        fn $test() {
            let dir = tlx_testkit::TempDir::with_spec(
                "optimization-oracle",
                include_str!(concat!("fixtures/optimization/", $case, "/Counter.tla")),
                include_str!(concat!("fixtures/optimization/", $case, "/Counter.cfg")),
            );
            let original = include_str!(concat!("fixtures/optimization/", $case, "/Counter.tlc.out"));
            let abstracted = include_str!(concat!("fixtures/optimization/", $case, "/Optimized.tlc.out"));
            assert_eq!(original.lines().next(), abstracted.lines().next(), "optimization must preserve the verdict");
            if $case == "reset" {
                assert!(original.contains("2 distinct states found"));
                assert!(abstracted.contains("1 distinct states found"));
            }
            let run = tlx_testkit::tlx!().args(["optimize", "Counter.tla", "-output", "out"]).dir(&dir).run();
            assert_eq!(run.code, 0, "{}", run.text());
            assert_eq!(
                std::fs::read_to_string(dir.join("out/Optimized.tla")).unwrap(),
                include_str!(concat!("fixtures/optimization/", $case, "/Optimized.tla")),
                "emission changed; refresh and review the TLC evidence"
            );
            assert_eq!(
                std::fs::read_to_string(dir.join("out/Optimized.cfg")).unwrap(),
                include_str!(concat!("fixtures/optimization/", $case, "/Optimized.cfg"))
            );
            check_oracle(dir.as_ref(), "Counter", original, &["-tlc"]);
            check_oracle(dir.as_ref(), "Counter", original, &["-optimize"]);
            check_oracle(dir.as_ref(), "Counter", original, &["-tlc", "-optimize"]);
            check_oracle(&dir.join("out"), "Optimized", abstracted, &["-tlc"]);
        }
    };
}

oracle_case!(cleanup_matches_tlc, "cleanup");
oracle_case!(empty_next_matches_tlc, "empty-safe");
oracle_case!(initial_violation_matches_tlc, "empty-violation");
oracle_case!(successor_violation_matches_tlc, "violation");
// The original has two states (9, 0); the quotient has one (0). Checking
// Counter with -tlc must retain the original counts/depth in every tier.
oracle_case!(tlc_mode_preserves_original_state_space, "reset");

#[test]
fn check_opt_in_applies_rules_and_tlc_bypasses_unsupported_inputs() {
    let spec = include_str!("fixtures/optimization/cleanup/Counter.tla");
    let dir = tlx_testkit::TempDir::with_spec("optimization-opt-in", spec, CFG);
    let run = tlx_testkit::tlx_default!().check("Counter.tla").args(["-optimize", "-interp"]).dir(&dir).run();
    assert_eq!(run.code, 0, "{}", run.text());
    for rule in ["constant-state-propagation", "predicate-simplification", "dead-action-elimination"] {
        assert!(run.stdout.contains(rule), "{}", run.text());
    }
    assert!(!run.stdout.contains("threshold-counter-saturation"));
    assert!(!dir.join("Optimized.tla").exists());
    // Decrements are valid ordinary TLA+ but outside the optimizer's fragment.
    dir.write(
        "Counter.tla",
        "---- MODULE Counter ----\nEXTENDS Integers\nVARIABLE c\nInit == c = 1\nNext == c > 0 /\\ c' = c - 1\nInv == c >= 0\n====\n",
    );
    let run = tlx_testkit::tlx_default!().check("Counter.tla").arg("-optimize").dir(&dir).run();
    assert_eq!(run.code, 2, "{}", run.text());
    assert!(run.stdout.contains("decrements are unsupported"), "{}", run.text());
    for flags in [["-tlc", "-optimize"], ["-optimize", "-tlc"]] {
        let run = tlx_testkit::tlx!().check("Counter.tla").args(flags).dir(&dir).run();
        assert_eq!(run.code, 0, "{}", run.text());
        assert!(run.stdout.contains("disabled by -tlc"), "{}", run.text());
        assert!(run.stdout.contains("2 distinct states found"), "{}", run.text());
    }
}

#[test]
fn optimized_check_rejects_unsupported_execution_modes() {
    let dir = tlx_testkit::TempDir::with_spec("optimization-modes", SPEC, CFG);
    for flags in [vec!["-simulate"], vec!["-checksymmetry"], vec!["-coverage", "1"], vec!["-checkpoint", "1"], vec!["-recover", "missing"]]
    {
        let run = tlx_testkit::tlx_default!().check("Counter.tla").arg("-optimize").args(flags).dir(&dir).run();
        assert_eq!(run.code, 2, "{}", run.text());
        assert!(run.stderr.contains("supports exhaustive checking"), "{}", run.text());
    }
}

#[test]
fn exact_optimization_retains_counter_boundary_behavior() {
    let spec = "---- MODULE Counter ----\nEXTENDS Naturals\nVARIABLE c\nInit == c = 2147483647\nNext == c <= 2147483647 /\\ c' = c + 1\nInv == c >= 0 /\\ c <= 2147483647\n====\n";
    let dir = tlx_testkit::TempDir::with_spec("optimization-overflow", spec, CFG);
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = |optimize: bool| {
            let mut command = tlx_testkit::tlx_default!();
            command
                .check("Counter.tla")
                .args(args)
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .dir(&dir)
                .timeout(Duration::from_secs(60));
            if optimize {
                command.arg("-optimize");
            }
            command.run()
        };
        let original = run(false);
        let optimized = run(true);
        assert_ne!(original.code, 0, "{tier}: {}", original.text());
        assert_eq!(original.code, optimized.code, "{tier}: {}\n{}", original.text(), optimized.text());
        let errors = |text: &str| text.lines().filter(|line| line.starts_with("Error:")).map(str::to_string).collect::<Vec<_>>();
        assert_eq!(errors(&original.stdout), errors(&optimized.stdout), "{tier}");
        assert!(optimized.stdout.contains("predicate-simplification"), "{tier}: {}", optimized.text());
    }
}
