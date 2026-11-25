//! End-to-end optimization emission and generated-model execution.

use std::time::Duration;

const CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
const SPEC: &str =
    "---- MODULE Counter ----\nEXTENDS Naturals\nVARIABLE c\nInit == c = 0\nNext == c' = c + 1 \\/ c' = 0\nInv == c < 3 \\/ c >= 3\n====\n";

#[test]
fn certified_export_emits_proof_and_never_overwrites_artifacts() {
    let dir = tlx_testkit::TempDir::with_spec("optimization-cli", SPEC, CFG);
    let run = tlx_testkit::tlx!().args(["optimize", "Counter.tla", "-output", "out"]).dir(&dir).run();
    assert_eq!(run.code, 0, "{}", run.text());
    assert!(run.stdout.contains("no safety verdict is claimed"));
    let files = ["Optimized.tla", "Optimized.cfg", "Optimization.lean", "optimization.txt"];
    let original: Vec<_> = files.iter().map(|f| std::fs::read_to_string(dir.join("out").join(f)).unwrap()).collect();
    assert!(original[2].contains("namespace TlxOptimization.GeneratedPipeline"));
    assert!(original[2].contains("theorem certificate : Certificate before after project"));
    assert!(original[3].contains("Lean was NOT run"));
    let run = tlx_testkit::tlx!().args(["optimize", "Counter.tla", "-output", "out"]).dir(&dir).run();
    assert_eq!(run.code, 2, "{}", run.text());
    assert!(run.stderr.contains("cannot create new output directory"));
    for (file, expected) in files.iter().zip(original) {
        assert_eq!(std::fs::read_to_string(dir.join("out").join(file)).unwrap(), expected);
    }
}

#[test]
fn compatibility_flags_cannot_silently_enable_optimization() {
    for args in [vec!["optimize", "-tlc"], vec!["check", "-abstract"]] {
        let run = tlx_testkit::tlx!().args(args).run();
        assert_eq!(run.code, 2, "{}", run.text());
    }
    let run = tlx_testkit::tlx!().args(["optimize", "--help"]).run();
    assert_eq!(run.code, 0);
    assert!(run.stdout.contains("Each applied pass has a connected Lean certificate"));
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
            // Keep the independent TLC oracle tied to the exact emitted module.
            let mut program = tlx_sema::Program::load(&dir.join("Counter.tla"), &[]).unwrap();
            let cfg = tlx_front::cfg::parse_cfg(include_str!(concat!("fixtures/optimization/", $case, "/Counter.cfg"))).unwrap();
            let candidate = tlx_sema::optimize::optimize_model(&mut program, &cfg).unwrap();
            assert!(candidate.certificate.as_ref().unwrap().contains("GeneratedPipeline"));
            assert_eq!(candidate.module, include_str!(concat!("fixtures/optimization/", $case, "/Optimized.tla")));
            assert_eq!(candidate.config, include_str!(concat!("fixtures/optimization/", $case, "/Optimized.cfg")));
            std::fs::create_dir(dir.join("out")).unwrap();
            dir.write("out/Optimized.tla", &candidate.module);
            dir.write("out/Optimized.cfg", &candidate.config);
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
fn state_reduction_retains_counter_boundary_behavior() {
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
        assert!(!optimized.stdout.contains("unobserved-state-projection"), "{tier}: {}", optimized.text());
    }
}

const PROJECTION_SPEC: &str = r#"---- MODULE Counter ----
EXTENDS Integers, TLC
VARIABLES x, tag
vars == <<x, tag>>
Init == x = 0 /\ tag = "init"
Flip == x' = 1 - x /\ tag' = "flip"
Idle == UNCHANGED x /\ tag' = "idle"
Next == Flip \/ Idle
Spec == Init /\ [][Next]_vars
Inv == x \in {0, 1}
Live == <> (x = 1)
TagInv == tag /= "idle"
Bound == tag = "init"
ActionBound == tag' /= "idle"
Observed == <<x, tag>>
====
"#;

#[test]
fn projection_merges_states_in_every_tier_and_tlc_bypasses_it() {
    let dir = tlx_testkit::TempDir::with_spec("optimization-projection", PROJECTION_SPEC, CFG);
    for cfg in [CFG.to_string(), CFG.replace("INIT Init\nNEXT Next", "SPECIFICATION Spec")] {
        dir.write("Counter.cfg", &cfg);
        for (tier, args, env) in tlx_testkit::cli::TIERS {
            for flags in [vec![], vec!["-optimize"], vec!["-tlc", "-optimize"], vec!["-optimize", "-tlc"]] {
                let reduced = flags == ["-optimize"];
                let run = tlx_testkit::tlx_default!()
                    .check("Counter.tla")
                    .args(args)
                    .args(flags)
                    .args(["-noautosymmetry", "-stats", "json"])
                    .envs(env.iter().copied())
                    .env("TLX_PARANOID", "1")
                    .dir(&dir)
                    .timeout(Duration::from_secs(60))
                    .run();
                assert_eq!(run.code, 0, "{tier}: {}", run.text());
                let count = if reduced { "2 distinct states found" } else { "5 distinct states found" };
                assert!(run.stdout.contains(count), "{tier}: {}", run.text());
                assert_eq!(run.stdout.contains("unobserved-state-projection"), reduced, "{tier}: {}", run.text());
                assert!(!run.stdout.contains("exact IR cleanup"));
            }
        }
    }
}

#[test]
fn projection_preserves_concrete_counterexamples_and_deadlocks() {
    let spec = PROJECTION_SPEC.replace("1 - x", "x + 1").replace("Flip == x'", "Flip == x < 2 /\\ x'");
    for (next, inv, deadlock, code) in [("Flip \\/ Idle", "x < 2", false, 12), ("Flip", "x <= 2", true, 11)] {
        let spec =
            spec.replace("Next == Flip \\/ Idle", &format!("Next == {next}")).replace("Inv == x \\in {0, 1}", &format!("Inv == {inv}"));
        let cfg = CFG.replace("FALSE", if deadlock { "TRUE" } else { "FALSE" });
        let dir = tlx_testkit::TempDir::with_spec("projection-trace", &spec, &cfg);
        for (tier, args, env) in tlx_testkit::cli::TIERS {
            let run = tlx_testkit::tlx_default!()
                .check("Counter.tla")
                .args(args)
                .args(["-optimize", "-noautosymmetry", "-tool"])
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            assert_eq!(run.code, code, "{tier}: {}", run.text());
            assert!(run.stdout.contains("unobserved-state-projection"), "{tier}: {}", run.text());
            let values: Vec<_> = run.stdout.lines().filter(|l| l.starts_with("/\\ tag =") || l.starts_with("/\\ x =")).collect();
            assert_eq!(
                values,
                ["/\\ x = 0", "/\\ tag = \"init\"", "/\\ x = 1", "/\\ tag = \"flip\"", "/\\ x = 2", "/\\ tag = \"flip\""],
                "{tier}: {}",
                run.text()
            );
        }
    }
}

#[test]
fn observations_and_temporal_checks_keep_the_full_graph() {
    for (cfg, expected) in [
        (format!("{CFG}INVARIANT TagInv\n"), 12),
        (format!("{CFG}CONSTRAINT Bound\n"), 0),
        (format!("{CFG}ACTION_CONSTRAINT ActionBound\n"), 0),
        (format!("{CFG}VIEW Observed\n"), 0),
        (format!("{CFG}PROPERTY Live\n"), 13),
        (format!("{CFG}CONSTANT Flip <- Idle\n"), 0),
    ] {
        let dir = tlx_testkit::TempDir::with_spec("projection-observations", PROJECTION_SPEC, &cfg);
        let run = tlx_testkit::tlx_default!().check("Counter.tla").args(["-optimize", "-interp", "-noautosymmetry"]).dir(&dir).run();
        assert_eq!(run.code, expected, "{}", run.text());
        assert!(!run.stdout.contains("unobserved-state-projection"), "{}", run.text());
    }
    // Checking only `TagInv` observes `tag` while leaving `x` unobserved with total
    // arithmetic update `x' = 1 - x`, so `x` is erased and `TagInv` still fails concretely.
    let dir = tlx_testkit::TempDir::with_spec("projection-tag-only", PROJECTION_SPEC, &CFG.replace("INVARIANT Inv", "INVARIANT TagInv"));
    let run = tlx_testkit::tlx_default!().check("Counter.tla").args(["-optimize", "-interp", "-noautosymmetry"]).dir(&dir).run();
    assert_eq!(run.code, 12, "{}", run.text());
    assert!(run.stdout.contains("unobserved-state-projection (x;"), "{}", run.text());
}

#[test]
fn optimize_disables_default_checkpointer_and_rejects_checkpoint_abort_env() {
    let dir = tlx_testkit::TempDir::with_spec("optimize-no-checkpoint", PROJECTION_SPEC, CFG);
    let refused =
        tlx_testkit::tlx_default!().check("Counter.tla").args(["-optimize", "-interp"]).env("TLX_CHECKPOINT_ABORT", "1").dir(&dir).run();
    assert_eq!(refused.code, 2, "{}", refused.text());
    assert!(refused.stderr.contains("without simulation, symmetry diagnostics, coverage or checkpoints"), "{}", refused.text());

    // Without `-checkpoint`, `-optimize` must not arm the default 30-minute
    // checkpointer (so `TLX_VALUE_STORE=1` sees `opts.checkpoint.is_none()`
    // rather than logging that it suppressed a default checkpoint timer).
    let run = tlx_testkit::tlx_default!()
        .check("Counter.tla")
        .args(["-optimize", "-compile", "-noautosymmetry"])
        .env("TLX_VALUE_STORE", "1")
        .env("TLX_PRERUN_REUSE", "0")
        .dir(&dir)
        .run();
    assert_eq!(run.code, 0, "{}", run.text());
    assert!(!run.text().contains("this run takes no checkpoints"), "{}", run.text());
}

#[test]
fn projection_removes_an_unobserved_copy_cycle() {
    let spec = r#"---- MODULE Counter ----
EXTENDS Integers
VARIABLES x, a, b
Init == x = 0 /\ a = 0 /\ b = 1
Next == (x' = 1 - x /\ UNCHANGED <<a, b>>)
     \/ (UNCHANGED x /\ a' = b /\ b' = a)
Inv == x \in {0, 1}
====
"#;
    let dir = tlx_testkit::TempDir::with_spec("projection-cycle", spec, CFG);
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        for optimize in [false, true] {
            let run = tlx_testkit::tlx_default!()
                .check("Counter.tla")
                .args(args)
                .args(if optimize { vec!["-optimize"] } else { vec![] })
                .arg("-noautosymmetry")
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            assert_eq!(run.code, 0, "{tier}: {}", run.text());
            assert!(
                run.stdout.contains(if optimize { "2 distinct states found" } else { "4 distinct states found" }),
                "{tier}: {}",
                run.text()
            );
        }
    }
}
