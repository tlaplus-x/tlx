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
    for (label, dom) in [("enum", "{1, 2}"), ("interval", "0..1")] {
        let spec = SPEC
            .replace("r = [mode |-> \"idle\", data |-> 0]", &format!("r = [s \\in {dom} |-> [mode |-> \"idle\", data |-> 0]]"))
            .replace("Start ==", "Start(s) ==")
            .replace("Finish ==", "Finish(s) ==")
            .replace("r.mode", "r[s].mode")
            .replace("r.data", "r[s].data")
            .replace("!.", "![s].")
            .replace("Next == Start \\/ Finish", &format!("Next == \\E s \\in {dom}: Start(s) \\/ Finish(s)"))
            .replace(
                "r \\in [mode: {\"idle\", \"busy\"}, data: {0, 1}]",
                &format!("r \\in [{dom} -> [mode: {{\"idle\", \"busy\"}}, data: {{0, 1}}]]"),
            );
        let dir = tlx_testkit::TempDir::with_spec(&format!("phase-map-{label}"), &spec, CFG);
        for (tier, args, env) in tlx_testkit::cli::TIERS {
            for optimize in [false, true] {
                let run = tlx_testkit::tlx_default!()
                    .check("Phase.tla")
                    .args(args)
                    .args(if optimize { vec!["-optimize"] } else { vec![] })
                    .arg("-noautosymmetry")
                    .envs(env.iter().copied())
                    .env("TLX_PARANOID", "1")
                    .env("TLX_PRERUN_REUSE", "0")
                    .dir(&dir)
                    .timeout(Duration::from_secs(60))
                    .run();
                assert_eq!(run.code, 0, "{label}/{tier}: {}", run.text());
                assert!(
                    run.stdout.contains(if optimize { "9 distinct states found" } else { "16 distinct states found" }),
                    "{label}/{tier}: {}",
                    run.text()
                );
            }
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
fn declared_symmetry_stays_separate_while_automatic_symmetry_composes() {
    for declared in [false, true] {
        let cfg = format!("{CFG}CONSTANT Actors = {{a, b}}\n{}", if declared { "SYMMETRY Sym\n" } else { "" });
        let dir = tlx_testkit::TempDir::with_spec("phase-symmetry", &symmetric_spec(), &cfg);
        for (tier, args, env) in tlx_testkit::cli::TIERS {
            // Four local states give ten multisets; projecting idle data
            // leaves three local states (9 concrete projected states) and
            // six multisets of two actors when composed with automatic symmetry.
            for (flags, count, expect_composed) in [
                (vec![], 10, false),
                (vec!["-optimize"], if declared { 10 } else { 6 }, !declared),
                (vec!["-optimize", "-noautosymmetry"], if declared { 10 } else { 9 }, false),
                (vec!["-optimize", "-tlc"], if declared { 10 } else { 16 }, false),
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
                assert_eq!(run.stdout.contains("composed with symmetry"), expect_composed, "{tier}: {}", run.text());
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

const ALL_FOUR_TIERS: [(&str, &[&str], &[(&str, &str)]); 4] = [
    ("interpreter", &["-interp"], &[]),
    ("compiled IR", &["-compile"], &[("TLX_PRERUN_REUSE", "0"), ("TLX_NO_NATIVE", "1")]),
    ("cranelift JIT", &["-compile"], &[("TLX_PRERUN_REUSE", "0"), ("TLX_JIT", "only"), ("TLX_JIT_VERIFY", "1")]),
    ("C backend", &["-compile"], &[("TLX_PRERUN_REUSE", "0"), ("TLX_JIT", "0"), ("TLX_NATIVE_SYNC", "1")]),
];

#[test]
fn whole_record_and_parallel_maps_reduce_and_compile_monomorphically_across_all_tiers() {
    // 1. Whole-record map entry replacement (`[r EXCEPT ![s] = [mode |-> ..., data |-> ...]]`).
    let whole_map = r#"---- MODULE WholeMap ----
EXTENDS Integers
VARIABLE r
Init == r = [s \in {1, 2} |-> [mode |-> "idle", data |-> 0]]
Start(s) == \E n \in {0, 1}: /\ r[s].mode = "idle"
                             /\ r' = [r EXCEPT ![s] = [mode |-> "busy", data |-> n]]
Finish(s) == /\ r[s].mode = "busy"
             /\ r[s].data >= 0
             /\ r' = [r EXCEPT ![s] = [mode |-> "idle", data |-> r[s].data]]
Next == \E s \in {1, 2}: Start(s) \/ Finish(s)
Inv == r \in [{1, 2} -> [mode: {"idle", "busy"}, data: {0, 1}]]
====
"#;
    let dir = tlx_testkit::TempDir::with_spec("phase-whole-map", whole_map, CFG);
    for (tier, args, env) in ALL_FOUR_TIERS {
        for (flags, count) in [(vec![], 16), (vec!["-optimize"], 9), (vec!["-optimize", "-tlc"], 16)] {
            let run = tlx_testkit::tlx_default!()
                .check("WholeMap.tla")
                .args(args)
                .args(flags)
                .args(["-workers", "1", "-noautosymmetry"])
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            assert_eq!(run.code, 0, "{tier}: {}", run.text());
            assert!(run.stdout.contains(&format!("{count} distinct states found")), "{tier}: {}", run.text());
            assert_eq!(run.stdout.contains("phase-field-projection"), count == 9, "{tier}: {}", run.text());
        }
    }

    // 2. Parallel fixed-domain maps with phase-guarded invariant (`pc[k] = "busy" => buf[k] >= 0`).
    let parallel = r#"---- MODULE ParallelMaps ----
EXTENDS Integers
VARIABLES pc, buf, done
Init == /\ pc = [k \in {1, 2} |-> "idle"]
        /\ buf = [k \in {1, 2} |-> 0]
        /\ done = FALSE
Start(k) == \E n \in {0, 1, 2}:
              /\ pc[k] = "idle"
              /\ pc' = [pc EXCEPT ![k] = "busy"]
              /\ buf' = [buf EXCEPT ![k] = n]
              /\ UNCHANGED done
Finish(k) == /\ pc[k] = "busy"
             /\ buf[k] >= 0
             /\ pc' = [pc EXCEPT ![k] = "idle"]
             /\ done' = (done \/ buf[k] = 2)
             /\ UNCHANGED buf
Next == \E k \in {1, 2}: Start(k) \/ Finish(k)
Inv == /\ pc \in [{1, 2} -> {"idle", "busy"}]
       /\ done \in BOOLEAN
       /\ \A k \in {1, 2}: pc[k] = "busy" => buf[k] \in {0, 1, 2}
====
"#;
    let dir = tlx_testkit::TempDir::with_spec("phase-parallel-maps", parallel, CFG);
    for (tier, args, env) in ALL_FOUR_TIERS {
        let base = tlx_testkit::tlx_default!()
            .check("ParallelMaps.tla")
            .args(args)
            .args(["-workers", "1", "-noautosymmetry"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(base.code, 0, "base/{tier}: {}", base.text());

        let opt = tlx_testkit::tlx_default!()
            .check("ParallelMaps.tla")
            .args(args)
            .args(["-workers", "1", "-optimize", "-noautosymmetry"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(opt.code, 0, "opt/{tier}: {}", opt.text());
        assert!(opt.stdout.contains("phase-field-projection (buf[*]"), "{tier}: {}", opt.text());
        assert!(opt.stdout.contains("32 distinct states found"), "{tier}: {}", opt.text());
        assert!(base.stdout.contains("61 distinct states found"), "{tier}: {}", base.text());
        if matches!(tier, "cranelift JIT" | "C backend") {
            assert!(
                opt.stdout.contains("view: fingerprints of the encoded VIEW (native)"),
                "{tier}: expected monomorphic native VIEW compilation:\n{}",
                opt.text()
            );
        }

        let tlc = tlx_testkit::tlx_default!()
            .check("ParallelMaps.tla")
            .args(args)
            .args(["-workers", "1", "-optimize", "-tlc"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(tlc.code, 0, "tlc/{tier}: {}", tlc.text());
        assert!(!tlc.stdout.contains("phase-field-projection"), "tlc/{tier}: {}", tlc.text());
        assert!(tlc.stdout.contains("61 distinct states found"), "tlc/{tier}: {}", tlc.text());
    }
}

#[test]
fn parallel_maps_preserve_concrete_counterexamples_deadlocks_and_refusals() {
    // Concrete counterexample trace lifting: bug triggers when `buf[k] = 2` is used in `Finish`.
    let cex_spec = r#"---- MODULE ParallelCex ----
EXTENDS Integers
VARIABLES pc, buf, bad
Init == pc = [k \in {1, 2} |-> "idle"] /\ buf = [k \in {1, 2} |-> 0] /\ bad = FALSE
Start(k) == \E n \in {0, 1, 2}:
              /\ pc[k] = "idle"
              /\ pc' = [pc EXCEPT ![k] = "busy"]
              /\ buf' = [buf EXCEPT ![k] = n]
              /\ UNCHANGED bad
Finish(k) == /\ pc[k] = "busy"
             /\ pc' = [pc EXCEPT ![k] = "idle"]
             /\ bad' = (buf[k] = 2)
             /\ UNCHANGED buf
Next == \E k \in {1, 2}: Start(k) \/ Finish(k)
Inv == ~bad /\ (\A k \in {1, 2}: pc[k] = "busy" => buf[k] \in {0, 1, 2})
====
"#;
    let dir = tlx_testkit::TempDir::with_spec("phase-parallel-cex", cex_spec, CFG);
    for (tier, args, env) in ALL_FOUR_TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("ParallelCex.tla")
            .args(args)
            .args(["-workers", "1", "-optimize", "-noautosymmetry"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 12, "{tier}: {}", run.text());
        assert!(run.stdout.contains("phase-field-projection (buf[*]"), "{tier}: {}", run.text());
        assert!(!run.stdout.contains("trace cannot be reconstructed"), "{tier}: {}", run.text());
        // The concrete violating trace must show the real value `2` in `buf`, not a masked `0`.
        assert!(run.stdout.contains("bad = TRUE"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("buf = <<2, 0>>") || run.stdout.contains("buf = <<0, 2>>"), "{tier}: {}", run.text());
    }

    // Deadlock preservation on scalar companion projection.
    let deadlock_spec = r#"---- MODULE ScalarDeadlock ----
EXTENDS Integers
VARIABLES pc, buf
Init == pc = "idle" /\ buf = 0
Start == \E n \in {0, 1}: pc = "idle" /\ pc' = "busy" /\ buf' = n
Stop == pc = "busy" /\ buf = 1 /\ pc' = "done" /\ UNCHANGED buf
Back == pc = "busy" /\ buf = 0 /\ pc' = "idle" /\ UNCHANGED buf
Next == Start \/ Stop \/ Back
Inv == pc \in {"idle", "busy", "done"} /\ (pc = "busy" => buf \in {0, 1})
====
"#;
    let deadlock_cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK TRUE\n";
    let dir = tlx_testkit::TempDir::with_spec("phase-scalar-deadlock", deadlock_spec, deadlock_cfg);
    for (tier, args, env) in ALL_FOUR_TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("ScalarDeadlock.tla")
            .args(args)
            .args(["-workers", "1", "-optimize", "-noautosymmetry"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 11, "{tier}: expected deadlock exit code 11:\n{}", run.text());
        assert!(run.stdout.contains("phase-field-projection (buf;"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("Deadlock reached"), "{tier}: {}", run.text());
    }

    // Deterministic refusals on invalid parallel-map / companion shapes.
    let refusal_cases: [(&str, &str, &str); 6] = [
        (
            "mismatched-actor",
            r#"---- MODULE Refusal ----
EXTENDS Integers
VARIABLES pc, buf
Init == pc = [k \in {1, 2} |-> "idle"] /\ buf = [k \in {1, 2} |-> 0]
Start(a, b) == \E n \in {0, 1}: pc[a] = "idle" /\ pc' = [pc EXCEPT ![a] = "busy"] /\ buf' = [buf EXCEPT ![b] = n]
Finish(a) == pc[a] = "busy" /\ buf[a] >= 0 /\ pc' = [pc EXCEPT ![a] = "idle"] /\ UNCHANGED buf
Next == (\E a, b \in {1, 2}: Start(a, b)) \/ (\E a \in {1, 2}: Finish(a))
Inv == pc \in [{1, 2} -> {"idle", "busy"}]
====
"#,
            CFG,
        ),
        (
            "singleton-dead",
            r#"---- MODULE Refusal ----
EXTENDS Integers
VARIABLES pc, buf
Init == pc = "idle" /\ buf = 0
Start == pc = "idle" /\ pc' = "busy" /\ buf' = 0
Finish == pc = "busy" /\ buf >= 0 /\ pc' = "idle" /\ UNCHANGED buf
Next == Start \/ Finish
Inv == pc \in {"idle", "busy"}
====
"#,
            CFG,
        ),
        (
            "singleton-empty-set",
            r#"---- MODULE Refusal ----
EXTENDS Integers
VARIABLES pc, buf
Init == pc = "idle" /\ buf = {}
Start == pc = "idle" /\ pc' = "busy" /\ buf' = {}
Finish == pc = "busy" /\ buf = {} /\ pc' = "idle" /\ UNCHANGED buf
Next == Start \/ Finish
Inv == pc \in {"idle", "busy"}
====
"#,
            CFG,
        ),
        (
            "singleton-empty-seq",
            r#"---- MODULE Refusal ----
EXTENDS Integers, Sequences
VARIABLES pc, buf
Init == pc = "idle" /\ buf = <<>>
Start == pc = "idle" /\ pc' = "busy" /\ buf' = <<>>
Finish == pc = "busy" /\ buf = <<>> /\ pc' = "idle" /\ UNCHANGED buf
Next == Start \/ Finish
Inv == pc \in {"idle", "busy"}
====
"#,
            CFG,
        ),
        (
            "action-sub-mentions-companion",
            r#"---- MODULE Refusal ----
EXTENDS Integers
VARIABLES pc, buf
Init == pc = "idle" /\ buf = 0
Start == \E n \in {0, 1}: pc = "idle" /\ pc' = "busy" /\ buf' = n
Finish == pc = "busy" /\ buf >= 0 /\ pc' = "idle" /\ UNCHANGED buf
Next == Start \/ Finish
Inv == pc \in {"idle", "busy"}
ActProp == [][pc' \in {"idle", "busy"}]_<<pc, buf>>
====
"#,
            "INIT Init\nNEXT Next\nINVARIANT Inv\nPROPERTY ActProp\nCHECK_DEADLOCK FALSE\n",
        ),
        (
            "unoverwritten-dead-to-live",
            r#"---- MODULE Refusal ----
EXTENDS Integers
VARIABLES pc, buf
Init == pc = "idle" /\ buf = 0
Start == \E n \in {0, 1}: pc = "idle" /\ pc' = "busy" /\ buf' = n
Skip == pc = "idle" /\ pc' = "busy" /\ UNCHANGED buf
Finish == pc = "busy" /\ buf >= 0 /\ pc' = "idle" /\ UNCHANGED buf
Next == Start \/ Skip \/ Finish
Inv == pc \in {"idle", "busy"}
====
"#,
            CFG,
        ),
    ];
    for (label, spec, cfg) in refusal_cases {
        let dir = tlx_testkit::TempDir::with_spec(&format!("phase-refuse-{label}"), spec, cfg);
        for (tier, args, env) in [ALL_FOUR_TIERS[0], ALL_FOUR_TIERS[3]] {
            let run = tlx_testkit::tlx_default!()
                .check("Refusal.tla")
                .args(args)
                .args(["-workers", "1", "-optimize", "-noautosymmetry"])
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            assert_eq!(run.code, 0, "{label}/{tier}: {}", run.text());
            assert!(!run.stdout.contains("phase-field-projection"), "{label}/{tier}: {}", run.text());
        }
    }
}

#[test]
fn parallel_maps_compose_with_certified_symmetry_and_fixed_domain_action_constraints() {
    // 1. With automatic symmetry enabled, `phase-field-projection (buf[*])`
    // composes with `Permutations(Actors)` (`GeneratedFieldSymmetry`),
    // delivering multiplicative reduction strictly below both standalone
    // symmetry (378 for 5 actors; 36 for 2 actors) and standalone projection
    // (2,048 for 5 actors; 32 for 2 actors).
    let sym_parallel = r#"---- MODULE ParallelSym ----
EXTENDS Integers
CONSTANT Actors
VARIABLES pc, buf, done
Init == /\ pc = [k \in Actors |-> "idle"]
        /\ buf = [k \in Actors |-> 0]
        /\ done = FALSE
Start(k) == \E n \in {0, 1, 2}:
              /\ pc[k] = "idle"
              /\ pc' = [pc EXCEPT ![k] = "busy"]
              /\ buf' = [buf EXCEPT ![k] = n]
              /\ UNCHANGED done
Finish(k) == /\ pc[k] = "busy"
             /\ buf[k] >= 0
             /\ pc' = [pc EXCEPT ![k] = "idle"]
             /\ done' = (done \/ buf[k] = 2)
             /\ UNCHANGED buf
Next == \E k \in Actors: Start(k) \/ Finish(k)
Inv == /\ pc \in [Actors -> {"idle", "busy"}]
       /\ done \in BOOLEAN
       /\ \A k \in Actors: pc[k] = "busy" => buf[k] \in {0, 1, 2}
====
"#;
    let parse_distinct = |stdout: &str| -> u64 {
        for line in stdout.lines() {
            if let Some(idx) = line.find(" distinct states found") {
                let prefix = line[..idx].trim_end();
                if let Some(num) = prefix.rsplit(|c: char| !c.is_ascii_digit()).next() {
                    if let Ok(v) = num.parse::<u64>() {
                        return v;
                    }
                }
            }
        }
        panic!("missing distinct state count in:\n{stdout}");
    };

    let cfg5 = format!("{CFG}CONSTANT Actors = {{a1, a2, a3, a4, a5}}\n");
    let dir5 = tlx_testkit::TempDir::with_spec("phase-parallel-sym5", sym_parallel, &cfg5);
    for (tier, args, env) in [ALL_FOUR_TIERS[0], ALL_FOUR_TIERS[2]] {
        let base = tlx_testkit::tlx_default!()
            .check("ParallelSym.tla")
            .args(args)
            .args(["-workers", "1"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .env("TLX_SYMMETRY_PARANOID", "1")
            .dir(&dir5)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(base.code, 0, "base5/{tier}: {}", base.text());
        assert!(base.stdout.contains("378 distinct states found"), "base5/{tier}: {}", base.text());

        let opt = tlx_testkit::tlx_default!()
            .check("ParallelSym.tla")
            .args(args)
            .args(["-workers", "1", "-optimize"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .env("TLX_SYMMETRY_PARANOID", "1")
            .dir(&dir5)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(opt.code, 0, "opt5/{tier}: {}", opt.text());
        let opt5_distinct = parse_distinct(&opt.stdout);
        assert!(opt5_distinct < 378, "opt5/{tier}: expected {opt5_distinct} < 378:\n{}", opt.text());
        assert!(opt.stdout.contains("phase-field-projection (buf[*]"), "opt5/{tier}: {}", opt.text());
        assert!(opt.stdout.contains("composed with symmetry Permutations(Actors)"), "opt5/{tier}: {}", opt.text());
    }

    let cfg2 = format!("{CFG}CONSTANT Actors = {{a1, a2}}\n");
    let dir2 = tlx_testkit::TempDir::with_spec("phase-parallel-sym2", sym_parallel, &cfg2);
    let opt2 = tlx_testkit::tlx_default!()
        .check("ParallelSym.tla")
        .args(["-interp", "-workers", "1", "-optimize"])
        .env("TLX_PARANOID", "1")
        .env("TLX_SYMMETRY_PARANOID", "1")
        .dir(&dir2)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(opt2.code, 0, "opt2: {}", opt2.text());
    let opt2_distinct = parse_distinct(&opt2.stdout);
    assert!(opt2_distinct < 32, "opt2: expected {opt2_distinct} < 32:\n{}", opt2.text());
    assert!(opt2.stdout.contains("phase-field-projection (buf[*]"), "opt2: {}", opt2.text());
    assert!(opt2.stdout.contains("composed with symmetry Permutations(Actors)"), "opt2: {}", opt2.text());

    // 1b. Deterministic startup prefix also composes `phase-field-projection`
    // with `Permutations(Actors)` instead of choosing only one reduction.
    let startup_parallel = r#"---- MODULE ParallelStartupSym ----
EXTENDS Integers
CONSTANT Actors
VARIABLES boot, pc, buf, done
Init == /\ boot = 0
        /\ pc = [k \in Actors |-> "idle"]
        /\ buf = [k \in Actors |-> 0]
        /\ done = FALSE
Boot == boot < 8 /\ boot' = boot + 1 /\ UNCHANGED <<pc, buf, done>>
Start(k) == \E n \in {0, 1, 2}:
              /\ boot = 8
              /\ pc[k] = "idle"
              /\ pc' = [pc EXCEPT ![k] = "busy"]
              /\ buf' = [buf EXCEPT ![k] = n]
              /\ UNCHANGED <<boot, done>>
Finish(k) == /\ boot = 8
             /\ pc[k] = "busy"
             /\ buf[k] >= 0
             /\ pc' = [pc EXCEPT ![k] = "idle"]
             /\ done' = (done \/ buf[k] = 2)
             /\ UNCHANGED <<boot, buf>>
Next == Boot \/ (\E k \in Actors: Start(k) \/ Finish(k))
Inv == /\ boot \in 0..8
       /\ pc \in [Actors -> {"idle", "busy"}]
       /\ done \in BOOLEAN
       /\ \A k \in Actors: pc[k] = "busy" => buf[k] \in {0, 1, 2}
====
"#;
    let dir_boot = tlx_testkit::TempDir::with_spec("phase-parallel-boot-sym5", startup_parallel, &cfg5);
    for (tier, args, env) in [ALL_FOUR_TIERS[0], ALL_FOUR_TIERS[2]] {
        let base = tlx_testkit::tlx_default!()
            .check("ParallelStartupSym.tla")
            .args(args)
            .args(["-workers", "1"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .env("TLX_SYMMETRY_PARANOID", "1")
            .dir(&dir_boot)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(base.code, 0, "boot-base/{tier}: {}", base.text());
        assert!(base.stdout.contains("386 distinct states found"), "boot-base/{tier}: {}", base.text());

        let opt = tlx_testkit::tlx_default!()
            .check("ParallelStartupSym.tla")
            .args(args)
            .args(["-workers", "1", "-optimize"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .env("TLX_SYMMETRY_PARANOID", "1")
            .dir(&dir_boot)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(opt.code, 0, "boot-opt/{tier}: {}", opt.text());
        let boot_distinct = parse_distinct(&opt.stdout);
        assert!(boot_distinct < 386, "boot-opt/{tier}: expected {boot_distinct} < 386:\n{}", opt.text());
        assert!(opt.stdout.contains("phase-field-projection (buf[*]"), "boot-opt/{tier}: {}", opt.text());
        assert!(opt.stdout.contains("composed with symmetry Permutations(Actors)"), "boot-opt/{tier}: {}", opt.text());
    }

    // 2. Fixed-domain `DOMAIN buf = {1, 2}` in `ACTION_CONSTRAINT` certifies
    // `buf[*]` and reduces 61 -> 32 distinct states.
    let dom_act = r#"---- MODULE ParallelDomAct ----
EXTENDS Integers
VARIABLES pc, buf, done
Init == /\ pc = [k \in {1, 2} |-> "idle"]
        /\ buf = [k \in {1, 2} |-> 0]
        /\ done = FALSE
Start(k) == \E n \in {0, 1, 2}:
              /\ pc[k] = "idle"
              /\ pc' = [pc EXCEPT ![k] = "busy"]
              /\ buf' = [buf EXCEPT ![k] = n]
              /\ UNCHANGED done
Finish(k) == /\ pc[k] = "busy"
             /\ buf[k] >= 0
             /\ pc' = [pc EXCEPT ![k] = "idle"]
             /\ done' = (done \/ buf[k] = 2)
             /\ UNCHANGED buf
Next == \E k \in {1, 2}: Start(k) \/ Finish(k)
Inv == /\ pc \in [{1, 2} -> {"idle", "busy"}]
       /\ done \in BOOLEAN
       /\ \A k \in {1, 2}: pc[k] = "busy" => buf[k] \in {0, 1, 2}
ActDom == DOMAIN buf = {1, 2}
====
"#;
    let dom_cfg = format!("{CFG}ACTION_CONSTRAINT ActDom\n");
    let dir_dom = tlx_testkit::TempDir::with_spec("phase-parallel-dom-act", dom_act, &dom_cfg);
    for (tier, args, env) in [ALL_FOUR_TIERS[0], ALL_FOUR_TIERS[2]] {
        let opt = tlx_testkit::tlx_default!()
            .check("ParallelDomAct.tla")
            .args(args)
            .args(["-workers", "1", "-optimize", "-noautosymmetry"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir_dom)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(opt.code, 0, "dom-act/{tier}: {}", opt.text());
        assert!(opt.stdout.contains("phase-field-projection (buf[*]"), "dom-act/{tier}: {}", opt.text());
        assert!(opt.stdout.contains("32 distinct states found"), "dom-act/{tier}: {}", opt.text());
    }
}
