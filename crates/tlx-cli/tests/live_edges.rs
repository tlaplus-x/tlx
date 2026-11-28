//! The liveness behavior graph recorded during the search (design.md §7.4)
//! is the only graph liveness checks: its verdicts and counts are TLC's
//! (tests/specs/expected.json), in both tiers and with several workers, and
//! the violated property is that of one interpreter worker.

use crate::common::{liveness_lines, liveness_specs, run_spec};
use tlx_testkit::cli::tests_specs as specs;

/// What TLC reports for spec `name` (tests/specs/expected.json): exit code,
/// distinct states and depth (None: not reported).
fn tlc(name: &str) -> Option<(i32, Option<u64>, Option<u64>)> {
    let text = std::fs::read_to_string(specs().join("expected.json")).expect("expected.json");
    let mut lines = text.lines().skip_while(|l| l.trim() != format!("\"{name}\": {{"));
    lines.next()?;
    let (mut exit, mut distinct, mut depth) = (None, None, None);
    for l in lines.take_while(|l| !l.trim_start().starts_with('}')) {
        let Some((key, value)) = l.trim().trim_end_matches(',').split_once(": ") else { continue };
        let number = value.parse::<u64>().ok();
        match key {
            "\"exit\"" => exit = number.map(|n| n as i32),
            "\"distinct\"" => distinct = number,
            "\"depth\"" => depth = number,
            _ => {}
        }
    }
    Some((exit?, distinct, depth))
}

/// Check spec `name` with `args`: exit code, the result lines of the output
/// and its distinct state count and depth.
fn run(name: &str, args: &[&str]) -> (i32, Vec<String>, Option<u64>, Option<u64>) {
    let out = run_spec(name, args);
    let text = out.text();
    let distinct = text
        .lines()
        .find(|l| l.contains(" distinct states found, ") && !l.starts_with("Progress"))
        .and_then(|l| l.split(" distinct states found").next()?.rsplit(' ').next()?.parse().ok());
    let depth =
        text.lines().find_map(|l| l.strip_prefix("The depth of the complete state graph search is ")?.trim_end_matches('.').parse().ok());
    (out.code, liveness_lines(&text), distinct, depth)
}

#[test]
fn recorded_graph_gives_tlcs_verdicts() {
    let names = liveness_specs(&["L", "LC", "LE", "LF"]);
    assert!(names.len() >= 20, "{names:?}");
    let mut violations = 0;
    for name in &names {
        let (exit, distinct, depth) = tlc(name).unwrap_or_else(|| panic!("{name} is not in expected.json"));
        // One interpreter worker: the baseline, which the first entry reuses
        // (it is checked like the other runs).
        let one = run(name, &["-workers", "1"]);
        for args in [&["-workers", "1"][..], &["-workers", "3"], &["-compile", "-workers", "2"]] {
            let other;
            let r = if args == ["-workers", "1"] {
                &one
            } else {
                other = run(name, args);
                &other
            };
            assert_eq!(r.0, exit, "{name} {args:?}: exit code (TLC)");
            if distinct.is_some() {
                assert_eq!((r.2, r.3), (distinct, depth), "{name} {args:?}: distinct states and depth (TLC)");
            }
            // (Which of several shortest counterexamples several workers
            // find is not determined; the violated property is.)
            let first_error = |lines: &[String]| lines.iter().find(|l| l.starts_with("Error:")).cloned();
            assert_eq!(first_error(&r.1), first_error(&one.1), "{name} {args:?}: vs one worker");
        }
        violations += usize::from(exit == 13);
    }
    assert!(violations >= 10, "{violations} violations");
}

/// After `TLCSet("exit", TRUE)`, liveness checks the graph of the states the
/// search expanded, not the whole state space (LX*: TLC's verdicts
/// are in tests/specs/expected.json). One worker: with more, where the
/// search stops is a race.
#[test]
fn liveness_after_exit_checks_the_expanded_states() {
    let names = liveness_specs(&["LX"]);
    assert!(names.len() >= 5, "{names:?}");
    for name in &names {
        let (exit, ..) = tlc(name).unwrap_or_else(|| panic!("{name} is not in expected.json"));
        let interpreted = run(name, &["-workers", "1"]);
        assert_eq!(interpreted.0, exit, "{name}: exit code (TLC)");
        let compiled = run(name, &["-compile", "-workers", "1"]);
        assert_eq!(compiled, interpreted, "{name}: compiled vs interpreted");
    }
}

/// An atom that fails during the search is reported from the search's own
/// record (`Report::live_error`), and TLC's search for the error follows.
#[test]
fn atom_errors_come_from_the_search() {
    for name in ["LE1", "LE2", "LE3"] {
        for args in [&["-workers", "1"][..], &["-workers", "3"], &["-compile", "-workers", "2"]] {
            let out = run_spec(name, &[&["-stats"][..], args].concat());
            let text = out.text();
            assert_eq!(out.code, 255, "{name} {args:?}: {text}");
            assert!(text.contains("liveness: search again"), "{name} {args:?}: {text}");
        }
    }
}

const PROGRESS: &str = r#"---- MODULE Progress ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Step == x < 80 /\ x' = x + 1
Spec == Init /\ [][Step]_x
Fair == Spec /\ WF_x(Step)
Goal == <>(x = 80)
====
"#;

#[test]
fn periodic_checks_stop_at_a_closed_lasso_and_allow_frontier_progress() {
    for (behavior, expected) in [("Fair", 0), ("Spec", 13)] {
        let cfg = format!("SPECIFICATION {behavior}\nPROPERTY Goal\nCHECK_DEADLOCK FALSE\n");
        let dir = tlx_testkit::TempDir::with_spec("periodic", PROGRESS, &cfg);
        for tier in ["-interp", "-compile"] {
            for workers in ["1", "4"] {
                let out = tlx_testkit::tlx!()
                    .dir(&dir)
                    .args(["check", "Progress.tla", tier, "-workers", workers, "-stats"])
                    .env("TLX_LIVE_CHECK_FIRST", "4")
                    .env("TLX_PARANOID", "1")
                    .timeout(std::time::Duration::from_secs(30))
                    .run();
                let text = out.text();
                assert_eq!(out.code, expected, "{tier} {workers}: {text}");
                assert!(text.contains("liveness: periodic checks"), "{text}");
                if expected == 0 {
                    assert!(text.contains("81 distinct states found"), "{text}");
                } else {
                    assert!(text.contains("5 distinct states found") && text.contains("Temporal property Goal was violated."), "{text}");
                    assert!(text.contains("Stuttering") && !text.contains("absence of a fairness constraint"), "{text}");
                }
            }
        }
    }
}

#[test]
fn tight_budget_defers_periodic_lasso_to_final_check() {
    let dir = tlx_testkit::TempDir::with_spec("periodic-budget", PROGRESS, "SPECIFICATION Spec\nPROPERTY Goal\nCHECK_DEADLOCK FALSE\n");
    let out = tlx_testkit::tlx!()
        .dir(&dir)
        .args(["check", "Progress.tla", "-interp", "-workers", "1", "-stats", "-maxmem", "1M"])
        .env("TLX_LIVE_CHECK_FIRST", "4")
        .timeout(std::time::Duration::from_secs(30))
        .run();
    let text = out.text();
    assert_eq!(out.code, 13, "{text}");
    assert!(!text.contains("liveness: periodic checks"), "{text}");
    assert!(text.contains("81 distinct states found") && text.contains("Temporal property Goal was violated."), "{text}");
    assert!(text.contains("Stuttering"), "{text}");
}
