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
fn phase_projection_reduces_states_in_every_tier_and_respects_tlc_mode() {
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
fn each_map_entry_has_its_own_control_phase() {
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
fn model_valued_phases_project_sequences_with_proved_element_types() {
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
