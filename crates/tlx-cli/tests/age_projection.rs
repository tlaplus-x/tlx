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
fn certified_age_reduction_preserves_concrete_counterexamples() {
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
    }
}

fn without_history() -> String {
    SPEC.replace("clock, records, h", "clock, records")
        .replace(" /\\ h = <<>>", "")
        .replace("<<records, h>>", "records")
        .replace("/\\ h' = Append(h, \"put\") ", "")
        .replace("/\\ h' = Append(h, \"drop\") ", "")
        .replace("       /\\ h \\in Seq({\"put\", \"drop\"})\n", "")
}

#[test]
fn unbounded_clock_finishes_with_four_states_in_every_executor() {
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let dir = tlx_testkit::TempDir::with_spec("age-finite", &without_history(), CFG);
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
        assert!(run.stdout.contains("4 distinct states found"), "{tier}: {}", run.text());
        let path = std::fs::read_dir(dir.join(".tlx-proofs")).unwrap().next().unwrap().unwrap().path().join("Optimization.lean");
        let proof = std::fs::read_to_string(path).unwrap();
        assert!(proof.contains("namespace TlxOptimization.GeneratedAge"));
        assert!(proof.contains("def caps"));
        assert!(proof.contains("Test.atLeast"));
        assert!(proof.contains("Change.reset"));
        assert!(proof.contains("Change.erase"));
        assert!(!proof.contains("sorry"));
    }
}

#[test]
fn strict_and_exact_deadlines_retain_the_boundary_state() {
    for (comparison, states) in [("<= clock", 4), ("< clock", 5), (">= clock", 5), ("> clock", 4), ("= clock", 5), ("# clock", 5)] {
        let spec = without_history().replace("<= clock", comparison);
        let dir = tlx_testkit::TempDir::with_spec("age-boundaries", &spec, CFG);
        let run = tlx_testkit::tlx_default!().check("Age.tla").args(["-interp", "-optimize", "-noautosymmetry"]).dir(&dir).run();
        assert_eq!(run.code, 0, "{comparison}: {}", run.text());
        assert!(run.stdout.contains(&format!("{states} distinct states found")), "{comparison}: {}", run.text());
    }
}

#[test]
fn timestamp_field_reset_preserves_absent_fields() {
    for update in [
        "![1].created = clock",
        "![1] = Empty, ![1].created = clock",
        "![1] = [created |-> clock, payload |-> \"x\"], ![1].created = clock",
    ] {
        let spec = without_history().replace(
            "Next == Tick \\/ Put \\/ Drop",
            &format!("Reset == records' = [records EXCEPT {update}] /\\ UNCHANGED clock\nNext == Tick \\/ Put \\/ Drop \\/ Reset"),
        );
        let spec = spec
            .replace("VARIABLE clock, records", "VARIABLE clock, records, budget")
            .replace("Init ==", "Init == budget = 0 /\\")
            .replace("Next == Tick", "Next == budget < 8 /\\ budget' = budget + 1 /\\ (Tick")
            .replace("Drop \\/ Reset", "Drop \\/ Reset)");
        let cfg = format!("{CFG}CHECK_DEADLOCK FALSE\n");
        let dir = tlx_testkit::TempDir::with_spec("age-field-reset", &spec, &cfg);
        let run = tlx_testkit::tlx_default!()
            .check("Age.tla")
            .args(["-interp", "-optimize", "-noautosymmetry"])
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{}", run.text());
        assert!(run.stdout.contains("relative-age-projection"), "{}", run.text());
        let path = std::fs::read_dir(dir.join(".tlx-proofs")).unwrap().next().unwrap().unwrap().path().join("Optimization.lean");
        let proof = std::fs::read_to_string(path).unwrap();
        let generated = proof.split("namespace TlxOptimization.GeneratedAge").nth(1).unwrap();
        assert!(generated.contains("(Change.refresh"));
    }
}

#[test]
fn filtered_sets_and_quantified_deadlines_finish_in_every_executor() {
    let spec = include_str!("../../../proofs/age/FilteredAge.tla");
    let cfg = include_str!("../../../proofs/age/FilteredAge.cfg");
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let dir = tlx_testkit::TempDir::with_spec("age-filter", spec, cfg);
        let run = tlx_testkit::tlx_default!()
            .check("FilteredAge.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{tier}: {}", run.text());
        assert!(run.stdout.contains("8 distinct states found"), "{tier}: {}", run.text());
        let path = std::fs::read_dir(dir.join(".tlx-proofs")).unwrap().next().unwrap().unwrap().path().join("Optimization.lean");
        let proof = std::fs::read_to_string(path).unwrap();
        let generated = proof.split("namespace TlxOptimization.GeneratedAge").nth(1).unwrap();
        assert!(generated.contains("Test.select [0]"));
        assert!(generated.contains("sem.filterTest"));
    }
}

#[test]
fn filtered_consumers_preserve_set_operations_and_counterexamples() {
    let base = include_str!("../../../proofs/age/FilteredAge.tla");
    let cfg = include_str!("../../../proofs/age/FilteredAge.cfg");
    let filter = r#"{k \in {1}: records[k] # Empty /\ records[k].created + 2 <= clock}"#;
    for (spec, config, code) in [
        (base.replace(filter, &format!("({filter} \\cup {filter})")), cfg.to_owned(), 0),
        (base.replace("\\A k", "\\E k"), cfg.to_owned(), 0),
        (base.replace("====", &format!("Computed == {filter} \\subseteq {{1}}\n====")), format!("{cfg}INVARIANT Computed\n"), 0),
        (base.replace("====", "Safe == selected = {}\n===="), format!("{cfg}INVARIANT Safe\n"), 12),
        (base.replace("records[k] # Empty /\\ ", ""), cfg.to_owned(), 75),
    ] {
        let dir = tlx_testkit::TempDir::with_spec("age-filter-consumer", &spec, &config);
        let run = tlx_testkit::tlx_default!()
            .check("FilteredAge.tla")
            .args(["-interp", "-optimize", "-noautosymmetry"])
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, code, "{}", run.text());
        assert!(run.stdout.contains("relative-age-projection"), "{}", run.text());
        if code == 12 {
            assert!(run.stdout.contains("Invariant Safe is violated"), "{}", run.text());
            assert!(run.stdout.contains("clock = 2"), "{}", run.text());
            assert!(run.stdout.contains("created |-> 0"), "{}", run.text());
        }
    }
}

#[test]
fn age_and_history_composition_finishes_in_every_executor() {
    let spec = include_str!("../../../proofs/age/AgeHistory.tla");
    let cfg = include_str!("../../../proofs/age/AgeHistory.cfg");
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let dir = tlx_testkit::TempDir::with_spec("age-history", spec, cfg);
        let run = tlx_testkit::tlx_default!()
            .check("AgeHistory.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{tier}: {}", run.text());
        assert!(run.stdout.contains("history.history"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("15 distinct states found, 0 states left on queue"), "{tier}: {}", run.text());
        let path = std::fs::read_dir(dir.join(".tlx-proofs")).unwrap().next().unwrap().unwrap().path().join("Optimization.lean");
        let proof = std::fs::read_to_string(path).unwrap();
        assert!(proof.contains("namespace TlxOptimization.GeneratedAgeHistory\n"));
        assert!(proof.contains("Test.select [0]"));
        assert!(proof.contains("Transfer.append"));
    }
}

#[test]
fn combined_history_monitors_keep_violations_and_reset_semantics() {
    let base = include_str!("../../../proofs/age/AgeHistory.tla");
    let cfg = include_str!("../../../proofs/age/AgeHistory.cfg");
    for (spec, code) in [
        (base.replace("history[i] = \"drop\" =>", "history[i] = \"put\" =>").replace("history[j] = \"put\"", "history[j] = \"drop\""), 12),
        (base.replace("history' = Append(history, \"put\")", "history' = Append(<<>>, \"put\")"), 0),
        (base.replace("Ordered == \\A", "Ordered == history = <<>> \\/ \\E"), 0),
        (base.replace("Past ==", "Past == history = <<>> \\/"), 0),
        (base.replace("Next == Tick \\/ Put \\/ Drop \\/ Scan", "Next == selected = {1} /\\ (Tick \\/ Put \\/ Drop)"), 11),
        (
            base.replace(
                "history' = Append(history, \"put\")",
                "history' = (IF selected = {} THEN Append(history, \"put\") ELSE <<\"put\">>)",
            ),
            0,
        ),
    ] {
        let dir = tlx_testkit::TempDir::with_spec("age-history-observation", &spec, cfg);
        let run = tlx_testkit::tlx_default!()
            .check("AgeHistory.tla")
            .args(["-interp", "-optimize", "-noautosymmetry"])
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, code, "{}", run.text());
        assert!(run.stdout.contains("history.history"), "{}", run.text());
        if code == 12 {
            assert!(run.stdout.contains("Invariant Ordered is violated"), "{}", run.text());
            assert!(run.stdout.contains("history = <<\"put\">>"), "{}", run.text());
        }
    }
}

#[test]
fn combined_history_feedback_finishes_in_every_executor() {
    let spec = include_str!("../../../proofs/age/HistoryFeedback.tla");
    let cfg = include_str!("../../../proofs/age/HistoryFeedback.cfg");
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let dir = tlx_testkit::TempDir::with_spec("age-feedback", spec, cfg);
        let run = tlx_testkit::tlx_default!()
            .check("HistoryFeedback.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{tier}: {}", run.text());
        assert!(run.stdout.contains("history.history"), "{tier}: {}", run.text());
        let path = std::fs::read_dir(dir.join(".tlx-proofs")).unwrap().next().unwrap().unwrap().path().join("Optimization.lean");
        let proof = std::fs::read_to_string(path).unwrap();
        assert!(proof.contains("namespace TlxOptimization.GeneratedAgeHistory"));
        assert!(proof.contains("Decision.branch"));
    }
}

#[test]
fn mixed_age_filters_and_history_predicates_are_certified_in_every_executor() {
    let base = include_str!("../../../proofs/age/MixedHistory.tla");
    let cfg = include_str!("../../../proofs/age/MixedHistory.cfg");
    for (spec, config, code) in [
        (base.to_owned(), cfg.to_owned(), 0),
        (base.replace("records[k] # Empty /\\ records[k].created + 2 <= clock}", "Ready /\\ k = 1}"), cfg.to_owned(), 0),
        (base.replace("IF Ready /\\", "IF ~Ready /\\").replace("Append(history, \"put\")", "Append(history, \"drop\")"), cfg.to_owned(), 0),
        (
            base.replace(
                "IF Ready /\\ history # <<>> THEN Expired ELSE {}",
                "(IF Ready THEN Expired ELSE {}) \\cup (IF history = <<>> THEN Expired ELSE {})",
            ),
            cfg.to_owned(),
            0,
        ),
        (base.replace("====", "Safe == selected = {}\n===="), format!("{cfg}INVARIANT Safe\n"), 12),
    ] {
        for (tier, args, env) in tlx_testkit::cli::TIERS {
            let dir = tlx_testkit::TempDir::with_spec("age-mixed-history", &spec, &config);
            let run = tlx_testkit::tlx_default!()
                .check("MixedHistory.tla")
                .args(args)
                .args(["-optimize", "-noautosymmetry"])
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            assert_eq!(run.code, code, "{tier}: {}", run.text());
            assert!(run.stdout.contains("history.history"), "{tier}: {}", run.text());
            let path = std::fs::read_dir(dir.join(".tlx-proofs")).unwrap().next().unwrap().unwrap().path().join("Optimization.lean");
            let proof = std::fs::read_to_string(path).unwrap();
            let generated = proof.split("namespace TlxOptimization.GeneratedAgeHistory").nth(1).unwrap();
            assert!(generated.contains("Boolean hole"));
            assert!(generated.contains("Test.select [0, 1]"));
            assert!(generated.contains("fun decision0 =>"));
            if code == 12 {
                assert!(run.stdout.contains("Invariant Safe is violated"));
            }
        }
    }
}

#[test]
fn bounded_mixed_consumers_reduce_states_and_compatibility_bypasses() {
    let spec = include_str!("../../../proofs/age/MixedHistory.tla")
        .replace("VARIABLE clock, records, selected, history", "VARIABLE clock, records, selected, history, budget")
        .replace("Init ==", "Init == budget = 0 /\\")
        .replace(
            "Next == Tick \\/ Put \\/ Drop \\/ Scan",
            "Next == budget < 6 /\\ budget' = budget + 1 /\\ (Tick \\/ Put \\/ Drop \\/ Scan)",
        );
    let cfg = format!("{}CHECK_DEADLOCK FALSE\n", include_str!("../../../proofs/age/MixedHistory.cfg"));
    let mut counts = vec![];
    for flags in [vec![], vec!["-optimize"], vec!["-optimize", "-tlc"]] {
        let dir = tlx_testkit::TempDir::with_spec("bounded-mixed-history", &spec, &cfg);
        let run = tlx_testkit::tlx_default!()
            .check("MixedHistory.tla")
            .args(["-interp", "-noautosymmetry"])
            .args(flags.clone())
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{}", run.text());
        assert_eq!(run.stdout.contains("history.history"), flags == ["-optimize"], "{}", run.text());
        let line = run.stdout.lines().find(|l| l.contains("distinct states found")).unwrap();
        let count: u64 =
            line.split("distinct states found").next().unwrap().split_whitespace().last().unwrap().replace(',', "").parse().unwrap();
        counts.push(count);
    }
    assert!(counts[1] < counts[0], "{counts:?}");
    assert_eq!(counts[0], counts[2]);
}

#[test]
fn dependent_transfers_and_dynamic_filters_finish_in_every_executor() {
    let base = include_str!("../../../proofs/age/DependentHistory.tla");
    let cfg = include_str!("../../../proofs/age/DependentHistory.cfg");
    for (spec, cfg, code) in [
        (base.to_owned(), cfg.to_owned(), 0),
        (base.replace("====", "Safe == selected = {}\n===="), format!("{cfg}INVARIANT Safe\n"), 12),
        // Nested payload decisions and event decisions use the same lowering.
        (
            base.replace(
                "IF history = <<>> THEN \"x\" ELSE \"y\"",
                "IF records[k] = Empty THEN \"x\" ELSE IF records[k].created + 2 <= clock THEN \"y\" ELSE \"x\"",
            ),
            cfg.to_owned(),
            0,
        ),
    ] {
        for (tier, args, env) in tlx_testkit::cli::TIERS {
            let dir = tlx_testkit::TempDir::with_spec("age-dependent", &spec, &cfg);
            let run = tlx_testkit::tlx_default!()
                .check("DependentHistory.tla")
                .args(args)
                .args(["-optimize", "-noautosymmetry"])
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            assert_eq!(run.code, code, "{tier}: {}", run.text());
            assert!(run.stdout.contains("history.history"), "{tier}: {}", run.text());
            let path = std::fs::read_dir(dir.join(".tlx-proofs")).unwrap().next().unwrap().unwrap().path().join("Optimization.lean");
            let proof = std::fs::read_to_string(path).unwrap();
            assert!(proof.contains("Decision.branch"));
            assert!(proof.contains("Decision.bindValue"));
            if code == 12 {
                assert!(run.stdout.contains("Invariant Safe is violated"));
                assert!(run.stdout.contains("clock = 2"));
            }
        }
    }
}
