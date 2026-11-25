//! Automatic field projection must reduce the search and retain failures.

use std::time::Duration;

const SPEC: &str = r#"---- MODULE Phase ----
EXTENDS Integers
VARIABLE r
Init == r = [mode |-> "idle", data |-> 0]
Start == \E n \in {0, 1}: /\ r.mode = "idle"
                              /\ r' = [r EXCEPT !.mode = "busy", !.data = n]
Finish == /\ r.mode = "busy"
          /\ r.data >= 0
          /\ r' = [r EXCEPT !.mode = "idle"]
Next == Start \/ Finish
Inv == r \in [mode: {"idle", "busy"}, data: {0, 1}]
====
"#;
const CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";

#[test]
fn certified_phase_projection_reduces_states_in_every_tier() {
    let dir = tlx_testkit::TempDir::with_spec("phase-projection", SPEC, CFG);
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        for (flags, count) in [(vec![], 4), (vec!["-optimize"], 3), (vec!["-optimize", "-tlc"], 4)] {
            let run = tlx_testkit::tlx_default!()
                .check("Phase.tla")
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
            assert_eq!(run.stdout.contains("phase-field-projection"), count == 3, "{tier}: {}", run.text());
        }
    }
}

#[test]
fn certified_map_field_projection_reduces_each_entry() {
    let spec = SPEC
        .replace("r = [mode |-> \"idle\", data |-> 0]", "r = [s \\in {1, 2} |-> [mode |-> \"idle\", data |-> 0]]")
        .replace("Start ==", "Start(s) ==")
        .replace("Finish ==", "Finish(s) ==")
        .replace("r.mode", "r[s].mode")
        .replace("r.data", "r[s].data")
        .replace("!.", "![s].")
        .replace("Next == Start \\/ Finish", "Next == \\E s \\in {1, 2}: Start(s) \\/ Finish(s)")
        .replace("r \\in [mode: {\"idle\", \"busy\"}, data: {0, 1}]", "r \\in [{1, 2} -> [mode: {\"idle\", \"busy\"}, data: {0, 1}]]");
    let dir = tlx_testkit::TempDir::with_spec("phase-map", &spec, CFG);
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        for optimize in [false, true] {
            let run = tlx_testkit::tlx_default!()
                .check("Phase.tla")
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
                run.stdout.contains(if optimize { "9 distinct states found" } else { "16 distinct states found" }),
                "{tier}: {}",
                run.text()
            );
        }
    }
}

#[test]
fn invariant_failure_and_evaluation_error_remain_visible() {
    for (spec, code) in [(SPEC.replace("data: {0, 1}", "data: {0}"), 12), (SPEC.replace("r.data >= 0", "1 \\div (1 - r.data) >= 0"), 255)] {
        let dir = tlx_testkit::TempDir::with_spec("phase-failures", &spec, CFG);
        for (tier, args, env) in tlx_testkit::cli::TIERS {
            let run = tlx_testkit::tlx_default!()
                .check("Phase.tla")
                .args(args)
                .args(["-optimize", "-noautosymmetry"])
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            assert_eq!(run.code, code, "{tier}: {}", run.text());
        }
    }
}

#[test]
fn certified_model_value_phases_erase_dead_sequence_contents() {
    let spec = SPEC
        .replace("EXTENDS Integers", "EXTENDS Integers, Sequences\nCONSTANTS Idle, Busy")
        .replace("\"idle\"", "Idle")
        .replace("\"busy\"", "Busy")
        .replace("data |-> 0", "data |-> <<0>>")
        .replace("!.data = n", "!.data = <<n>>")
        .replace("r.data >= 0", "Head(r.data) >= 0")
        .replace("data: {0, 1}", "data: Seq(Nat)");
    let cfg = format!("{CFG}CONSTANTS Idle = Idle Busy = Busy\n");
    let dir = tlx_testkit::TempDir::with_spec("phase-model-values", &spec, &cfg);
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        for (flags, count) in [(vec![], 4), (vec!["-optimize"], 3), (vec!["-optimize", "-tlc"], 4)] {
            let run = tlx_testkit::tlx_default!()
                .check("Phase.tla")
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
        }
    }
}

fn symmetric_spec() -> String {
    SPEC.replace("EXTENDS Integers", "EXTENDS Integers, TLC\nCONSTANT Actors")
        .replace("r = [mode |-> \"idle\", data |-> 0]", "r = [s \\in Actors |-> [mode |-> \"idle\", data |-> 0]]")
        .replace("Start ==", "Start(s) ==")
        .replace("Finish ==", "Finish(s) ==")
        .replace("r.mode", "r[s].mode")
        .replace("r.data", "r[s].data")
        .replace("!.", "![s].")
        .replace("Next == Start \\/ Finish", "Next == \\E s \\in Actors: Start(s) \\/ Finish(s)")
        .replace("r \\in [mode: {\"idle\", \"busy\"}, data: {0, 1}]", "r \\in [Actors -> [mode: {\"idle\", \"busy\"}, data: {0, 1}]]")
        .replace("====", "Sym == Permutations(Actors)\nObserved == r\n====")
}

#[test]
fn uncertified_composition_keeps_projection_and_symmetry_separate() {
    for declared in [false, true] {
        let cfg = format!("{CFG}CONSTANT Actors = {{a, b}}\n{}", if declared { "SYMMETRY Sym\n" } else { "" });
        let dir = tlx_testkit::TempDir::with_spec("phase-symmetry", &symmetric_spec(), &cfg);
        for (tier, args, env) in tlx_testkit::cli::TIERS {
            // Four local states give ten multisets; projecting idle data
            // leaves three local states and six multisets of two actors.
            for (flags, count) in [
                (vec![], 10),
                (vec!["-optimize"], if declared { 10 } else { 9 }),
                (vec!["-optimize", "-tlc"], if declared { 10 } else { 16 }),
            ] {
                let run = tlx_testkit::tlx_default!()
                    .check("Phase.tla")
                    .args(args)
                    .args(flags)
                    .envs(env.iter().copied())
                    .env("TLX_PARANOID", "1")
                    .env("TLX_SYMMETRY_PARANOID", "1")
                    .dir(&dir)
                    .timeout(Duration::from_secs(60))
                    .run();
                assert_eq!(run.code, 0, "{tier}: {}", run.text());
                assert!(run.stdout.contains(&format!("{count} distinct states found")), "{tier}: {}", run.text());
                assert!(!run.stdout.contains("composed with symmetry"), "{tier}: {}", run.text());
            }
        }
    }
}

#[test]
fn refused_composition_preserves_errors_failures_and_user_views() {
    for (spec, suffix, code, _projected) in [
        (symmetric_spec().replace("data: {0, 1}", "data: {0}"), "", 12, false),
        (symmetric_spec().replace("====", "Bad == \\A s \\in Actors: r[s].mode = \"idle\"\n===="), "INVARIANT Bad\n", 12, true),
        (symmetric_spec().replace("r[s].data >= 0", "1 \\div (1 - r[s].data) >= 0"), "", 255, true),
        (symmetric_spec(), "VIEW Observed\n", 0, false),
    ] {
        let cfg = format!("{CFG}CONSTANT Actors = {{a, b}}\nSYMMETRY Sym\n{suffix}");
        let dir = tlx_testkit::TempDir::with_spec("phase-symmetry-errors", &spec, &cfg);
        for (tier, args, env) in tlx_testkit::cli::TIERS {
            let run = tlx_testkit::tlx_default!()
                .check("Phase.tla")
                .args(args)
                .args(["-optimize", "-noautosymmetry"])
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            assert_eq!(run.code, code, "{tier}: {}", run.text());
            assert!(!run.stdout.contains("composed with symmetry"), "{tier}: {}", run.text());
        }
    }
}

#[test]
fn moved_phase_constants_decline_composition() {
    let spec = SPEC
        .replace("EXTENDS Integers", "EXTENDS Integers, TLC\nCONSTANTS Idle, Busy")
        .replace("\"idle\"", "Idle")
        .replace("\"busy\"", "Busy")
        .replace("====", "Sym == Permutations({Idle, Busy})\n====");
    // The declaration is deliberately invalid. The projection must not
    // claim equivariance under a group that exchanges its phase constants.
    let cfg = format!("{CFG}CONSTANTS Idle = Idle Busy = Busy\nSYMMETRY Sym\n");
    let dir = tlx_testkit::TempDir::with_spec("phase-moved-constants", &spec, &cfg);
    let run =
        tlx_testkit::tlx_default!().check("Phase.tla").args(["-optimize", "-interp"]).dir(&dir).timeout(Duration::from_secs(60)).run();
    assert_eq!(run.code, 0, "{}", run.text());
    assert!(!run.stdout.contains("phase-field-projection"), "{}", run.text());
}

#[test]
fn whole_variable_projection_declines_declared_symmetry() {
    let spec = r#"---- MODULE Phase ----
EXTENDS TLC
CONSTANT Actors
VARIABLES x, tag
Init == x \in Actors /\ tag = "init"
Next == x' \in Actors /\ (tag' = "one" \/ tag' = "two")
Inv == x \in Actors
Sym == Permutations(Actors)
===="#;
    for declared in [false, true] {
        let cfg = format!("{CFG}CONSTANT Actors = {{a, b}}\n{}", if declared { "SYMMETRY Sym\n" } else { "" });
        let dir = tlx_testkit::TempDir::with_spec("whole-variable-symmetry", spec, &cfg);
        for (tier, args, env) in tlx_testkit::cli::TIERS {
            let run = tlx_testkit::tlx_default!()
                .check("Phase.tla")
                .args(args)
                .args(["-optimize", "-stats", "json=stats.json"])
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            assert_eq!(run.code, 0, "{tier}: {}", run.text());
            assert!(
                run.stdout.contains(if declared { "3 distinct states found" } else { "1 distinct states found" }),
                "{tier}: {}",
                run.text()
            );
            assert_eq!(run.stdout.contains("unobserved-state-projection"), !declared, "{tier}: {}", run.text());
            assert_eq!(run.stdout.contains("composed with symmetry Permutations(Actors)"), !declared, "{tier}: {}", run.text());
            let stats = std::fs::read_to_string(dir.join("stats.json")).unwrap();
            assert_eq!(stats.contains(r#""name":"symmetry""#), !declared, "{stats}");
            if !declared {
                assert!(stats.contains(r#""proof":"generated-lean""#), "{stats}");
            }
            assert_eq!(stats.contains(r#""name":"unobserved-state-projection""#), !declared, "{stats}");
        }
    }
}

#[test]
fn refused_composition_keeps_concrete_counterexample_steps() {
    let spec = symmetric_spec()
        .replace("VARIABLE r", "VARIABLES r, k")
        .replace("Init == r", "Init == k = 0 /\\ r")
        .replace("Next == \\E", "Next == k < 5 /\\ k' = k + 1 /\\ \\E")
        .replace("====", "Bad == k < 4\n====");
    let cfg = format!("{CFG}CONSTANT Actors = {{a, b}}\nSYMMETRY Sym\nINVARIANT Bad\n");
    let dir = tlx_testkit::TempDir::with_spec("composed-replay", &spec, &cfg);
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("Phase.tla")
            .args(args)
            .args(["-optimize", "-workers", "2"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 12, "{tier}: {}", run.text());
        assert!(!run.stdout.contains("composed with symmetry"), "{tier}: {}", run.text());
        assert!(!run.stdout.contains("trace cannot be reconstructed"), "{tier}: {}", run.text());
        let steps: Vec<_> = run.stdout.lines().filter(|s| s.starts_with("/\\ k = ")).collect();
        assert_eq!(steps, ["/\\ k = 0", "/\\ k = 1", "/\\ k = 2", "/\\ k = 3", "/\\ k = 4"], "{tier}: {}", run.text());
        assert!(!run.stdout.contains("data |-> FALSE"), "{tier}: {}", run.text());
    }
}

#[test]
fn projected_view_with_empty_component_between_packed_fields() {
    let spec = r#"---- MODULE Phase ----
EXTENDS TLC
CONSTANT Actors
VARIABLES x, pad, y, tag
Init == x \in Actors /\ pad = <<>> /\ y \in Actors /\ tag = "init"
Next == x' \in Actors /\ pad' = <<>> /\ y' \in Actors /\ (tag' = "one" \/ tag' = "two")
Inv == x \in Actors /\ pad = <<>> /\ y \in Actors
Sym == Permutations(Actors)
===="#;
    let cfg = format!("{CFG}CONSTANT Actors = {{a, b}}\n");
    let dir = tlx_testkit::TempDir::with_spec("packed-empty-middle-view", spec, &cfg);
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("Phase.tla")
            .args(args)
            .args(["-optimize", "-stats", "json=stats.json"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{tier}: {}", run.text());
        assert!(run.stdout.contains("2 distinct states found"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("unobserved-state-projection"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("composed with symmetry Permutations(Actors)"), "{tier}: {}", run.text());
    }
}
