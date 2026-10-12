//! Mathematical clock ages can bound otherwise infinite safety graphs.
use std::time::Duration;

const SPEC: &str = r#"---- MODULE Age ----
EXTENDS Naturals, Sequences
VARIABLE clock, records, h
Empty == [status |-> "empty", payload |-> ""]
Init == /\ clock = 0 /\ records = [k \in {1} |-> Empty] /\ h = <<>>
Tick == /\ clock' = clock + 1 /\ UNCHANGED <<records, h>>
Put == /\ records' = [records EXCEPT ![1] = [created |-> clock, payload |-> "x"]]
       /\ h' = Append(h, "put") /\ UNCHANGED clock
Drop == /\ records[1] # Empty /\ records[1].created + 2 <= clock
        /\ records' = [records EXCEPT ![1] = Empty]
        /\ h' = Append(h, "drop") /\ UNCHANGED clock
Next == Tick \/ Put \/ Drop
Inv == /\ clock \in Nat /\ records \in [{1} -> [created: Nat, payload: {"x"}] \cup {Empty}]
       /\ h \in Seq({"put", "drop"})
====
"#;
const CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\n";

#[test]
fn clock_and_history_finish_in_every_tier_and_emit_lean() {
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let dir = tlx_testkit::TempDir::with_spec("age-finite", SPEC, CFG);
        let run = tlx_testkit::tlx_default!()
            .check("Age.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{tier}: {}", run.text());
        assert!(run.stdout.contains("relative-age-projection"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("8 distinct states found"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("not verified; rule algebra only"), "{tier}: {}", run.text());
        let artifact = std::fs::read_dir(dir.join(".tlx-proofs")).unwrap().next().unwrap().unwrap().path().join("Optimization.lean");
        let lean = std::fs::read_to_string(artifact).unwrap();
        assert!(lean.contains("namespace TlxOptimization.Age"));
        assert!(lean.contains("theorem deadline"));
        assert!(lean.contains("Mathematical natural-number clocks"));
        assert!(lean.contains("relative-age-projection"));
        assert!(lean.contains("No model-level Certificate is constructed"));
        assert!(!lean.contains("sorry"));
    }
}

#[test]
fn age_reduction_preserves_a_concrete_counterexample() {
    let spec = SPEC.replace("====", "Safe == records[1] = Empty \\/ records[1].created + 2 > clock\n====");
    let cfg = format!("{CFG}INVARIANT Safe\n");
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let dir = tlx_testkit::TempDir::with_spec("age-violation", &spec, &cfg);
        let run = tlx_testkit::tlx_default!()
            .check("Age.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 12, "{tier}: {}", run.text());
        assert!(run.stdout.contains("relative-age-projection"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("Invariant Safe is violated"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("clock = 2"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("created |-> 0"), "{tier}: {}", run.text());
    }
}

#[test]
fn compatibility_bypasses_age_reduction_and_absolute_bounds_refuse_it() {
    // A retained operation budget makes all three runs finish, without
    // changing the mathematical-clock proof or relying on a timeout.
    let bounded = SPEC
        .replace("VARIABLE clock, records, h", "VARIABLE clock, records, h, budget")
        .replace("Init ==", "Init == budget = 0 /\\")
        .replace("Next == Tick \\/ Put \\/ Drop", "Next == budget < 5 /\\ budget' = budget + 1 /\\ (Tick \\/ Put \\/ Drop)");
    let cfg = format!("{CFG}CHECK_DEADLOCK FALSE\n");
    let mut counts = Vec::new();
    for flags in [vec![], vec!["-optimize"], vec!["-optimize", "-tlc"], vec!["-tlc", "-optimize"]] {
        let dir = tlx_testkit::TempDir::with_spec("age-bounded", &bounded, &cfg);
        let run = tlx_testkit::tlx_default!()
            .check("Age.tla")
            .args(["-interp", "-noautosymmetry"])
            .args(flags.clone())
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{}", run.text());
        let active = flags == ["-optimize"];
        assert_eq!(run.stdout.contains("relative-age-projection"), active, "{}", run.text());
        assert_eq!(dir.join(".tlx-proofs").exists(), active);
        let line = run.stdout.lines().find(|l| l.contains("distinct states found")).unwrap();
        let count: u64 =
            line.split("distinct states found").next().unwrap().split_whitespace().last().unwrap().replace(',', "").parse().unwrap();
        counts.push(count);
    }
    assert!(counts[1] < counts[0], "{counts:?}");
    assert_eq!(counts[0], counts[2]);
    assert_eq!(counts[0], counts[3]);
    let spec = bounded.replace("Inv ==", "Inv == clock <= 5 /\\");
    let dir = tlx_testkit::TempDir::with_spec("age-refusal", &spec, &cfg);
    let run = tlx_testkit::tlx_default!().check("Age.tla").args(["-interp", "-optimize", "-noautosymmetry"]).dir(&dir).run();
    assert_eq!(run.code, 0, "{}", run.text());
    assert!(!run.stdout.contains("relative-age-projection"), "{}", run.text());
}

#[test]
fn unrelated_evaluation_errors_are_not_suppressed() {
    for error in ["1 \\div 0 = 0", "2147483647 + 1 = 0", "records[1].created + 2 <= clock"] {
        let spec = SPEC.replace("Inv ==", &format!("Inv == ({error}) /\\"));
        let dir = tlx_testkit::TempDir::with_spec("age-error", &spec, CFG);
        let run = tlx_testkit::tlx_default!().check("Age.tla").args(["-interp", "-optimize", "-noautosymmetry"]).dir(&dir).run();
        assert_eq!(run.code, 75, "{}", run.text());
        assert!(run.stdout.contains("relative-age-projection"), "{}", run.text());
    }
}
