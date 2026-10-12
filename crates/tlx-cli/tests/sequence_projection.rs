//! Length-only sequence keys preserve observations, errors and concrete traces.

use std::time::Duration;

const SPEC: &str = r#"---- MODULE Length ----
EXTENDS Naturals, Sequences
VARIABLE log
Init == log = <<>>
Grow == /\ Len(log) < 4
        /\ \E tx \in {0, 1}: log' = Append(log, tx)
Reset == /\ Len(log) = 4 /\ log' = <<>>
Next == Grow \/ Reset
TypeOK == log \in Seq({0, 1})
Safe == Len(log) < 3
Temporal == []<>TypeOK
Observed == log
====
"#;
const CFG: &str = "INIT Init\nNEXT Next\nINVARIANT TypeOK\n";

#[test]
fn certified_length_projection_reduces_the_graph_in_all_tiers() {
    let dir = tlx_testkit::TempDir::with_spec("sequence-length", SPEC, CFG);
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        for (flags, count) in [(vec![], 31), (vec!["-optimize"], 5), (vec!["-optimize", "-tlc"], 31)] {
            let run = tlx_testkit::tlx_default!()
                .check("Length.tla")
                .args(args)
                .args(flags)
                .arg("-noautosymmetry")
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            assert_eq!(run.code, 0, "{tier}: {}", run.text());
            assert!(run.stdout.contains(&format!("{count} distinct states found")), "{tier}: {}", run.text());
            assert_eq!(run.stdout.contains("sequence-length-projection"), count == 5, "{tier}: {}", run.text());
        }
    }
}

#[test]
fn content_observations_and_conflicting_bindings_refuse_projection() {
    for (spec, cfg, code) in [
        (SPEC.replace("Seq({0, 1})", "Seq({0})"), CFG.to_owned(), 12),
        (
            SPEC.replace("Len(log) < 4", "Len(log) < 4 /\\ (IF Len(log) = 0 THEN TRUE ELSE Head(log) = 0)"),
            format!("{CFG}CHECK_DEADLOCK FALSE\n"),
            0,
        ),
        (SPEC.replace("log' = Append(log, tx)", "log' = Append(log, tx) /\\ log' = Append(log, 0)"), CFG.to_owned(), 0),
        (SPEC.replace("log' = Append(log, tx)", "log' = Append(log, tx) /\\ UNCHANGED log"), format!("{CFG}CHECK_DEADLOCK FALSE\n"), 0),
        (SPEC.to_owned(), format!("{CFG}ALIAS Observed\n"), 0),
        (SPEC.to_owned(), format!("{CFG}VIEW Observed\n"), 0),
        (SPEC.to_owned(), format!("{CFG}PROPERTY Temporal\n"), 0),
    ] {
        let dir = tlx_testkit::TempDir::with_spec("sequence-content", &spec, &cfg);
        let run = tlx_testkit::tlx_default!()
            .check("Length.tla")
            .args(["-interp", "-optimize", "-noautosymmetry"])
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, code, "{}", run.text());
        assert!(!run.stdout.contains("sequence-length-projection"), "{}", run.text());
    }
}

#[test]
fn certified_length_projection_preserves_failures_and_errors() {
    for (spec, cfg, code, message) in [
        (SPEC.to_owned(), format!("{CFG}INVARIANT Safe\n"), 12, "Invariant Safe is violated"),
        (SPEC.replace("Next == Grow \\/ Reset", "Next == Grow"), CFG.to_owned(), 11, "Deadlock reached"),
        (SPEC.replace("Append(log, tx)", "Append(log, 1 \\div tx)"), "INIT Init\nNEXT Next\n".to_owned(), 255, ""),
    ] {
        let dir = tlx_testkit::TempDir::with_spec("sequence-failure", &spec, &cfg);
        for (tier, args, env) in tlx_testkit::cli::TIERS {
            let run = tlx_testkit::tlx_default!()
                .check("Length.tla")
                .args(args)
                .args(["-optimize", "-noautosymmetry"])
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            assert_eq!(run.code, code, "{tier}: {}", run.text());
            if code != 255 {
                assert!(run.stdout.contains("sequence-length-projection"), "{tier}: {}", run.text());
            }
            assert!(run.text().contains(message), "{tier}: {}", run.text());
            if code == 12 {
                assert!(run.stdout.contains("<<0, 0, 0>>") || run.stdout.contains("<<1, 1, 1>>"), "{tier}: {}", run.text());
            }
        }
    }
}

#[test]
fn unproved_field_and_length_candidates_keep_the_full_graph() {
    // This model still has four states: neither field erasure nor length
    // projection has a connected certificate.
    let spec = r#"---- MODULE Length ----
EXTENDS Naturals, Sequences
VARIABLE r, log
Init == r = [mode |-> "idle", data |-> 0] /\ log = <<0>>
Next == /\ UNCHANGED log
        /\ \/ \E n \in {0, 1}: /\ r.mode = "idle"
                                  /\ r' = [r EXCEPT !.mode = "busy", !.data = n]
           \/ /\ r.mode = "busy" /\ r.data >= 0
              /\ r' = [r EXCEPT !.mode = "idle"]
TypeOK == r \in [mode: {"idle", "busy"}, data: {0, 1}] /\ log \in Seq(Nat)
====
"#;
    let dir = tlx_testkit::TempDir::with_spec("sequence-rule-priority", spec, CFG);
    let run = tlx_testkit::tlx_default!()
        .check("Length.tla")
        .args(["-interp", "-optimize", "-noautosymmetry"])
        .dir(&dir)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(run.code, 0, "{}", run.text());
    assert!(!run.stdout.contains("phase-field-projection"), "{}", run.text());
    assert!(run.stdout.contains("4 distinct states found"), "{}", run.text());
}

#[test]
fn unproved_length_composition_keeps_declared_symmetry_only() {
    let spec = r#"---- MODULE Length ----
EXTENDS Naturals, Sequences, TLC
CONSTANT Nodes
VARIABLE log, seen
Init == log = <<>> /\ seen = [n \in Nodes |-> FALSE]
Next == \/ /\ Len(log) < 2
           /\ \E n \in Nodes, tx \in {0, 1}:
                 /\ log' = Append(log, tx)
                 /\ seen' = [seen EXCEPT ![n] = ~@]
        \/ /\ Len(log) = 2 /\ log' = <<>> /\ UNCHANGED seen
TypeOK == log \in Seq({0, 1}) /\ seen \in [Nodes -> BOOLEAN]
Symmetry == Permutations(Nodes)
====
"#;
    let cfg = format!("{CFG}CONSTANT Nodes = {{a, b}}\nSYMMETRY Symmetry\n");
    let dir = tlx_testkit::TempDir::with_spec("sequence-symmetry", spec, &cfg);
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("Length.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{tier}: {}", run.text());
        assert!(!run.stdout.contains("sequence-length-projection"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("12 distinct states found"), "{tier}: {}", run.text());
    }
}
