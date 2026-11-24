//! `-coverage` with several workers (representatives chosen in BFS order)
//! records the liveness behavior graph during the search too:
//! verdicts, counterexamples and counts are those of one worker, the
//! coverage statistics those of one worker with `-coverage`, in both tiers
//! (and a recorded graph checks every one that has no VIEW or SYMMETRY). (LS3: the search evaluates the liveness atoms,
//! which create run-time strings, in the order one worker does; without
//! them, the interpreter's CHOOSE picked another string and Inv failed.)

use crate::common::{coverage_lines, liveness_lines, liveness_specs, run_spec};

/// Check spec `name` with `args`: exit code, the result lines and the
/// coverage statistics of the output, and the output.
fn run(name: &str, args: &[&str]) -> (i32, Vec<String>, Vec<String>, String) {
    let out = run_spec(name, args);
    let text = out.text();
    (out.code, liveness_lines(&text), coverage_lines(&text), text)
}

#[test]
fn coverage_with_several_workers_records_the_graph() {
    let names = liveness_specs(&["L", "LC", "LE", "LF", "LS"]);
    assert!(names.len() >= 20, "{names:?}");
    let (mut violations, mut checked) = (0, 0);
    for name in &names {
        for tier in [&[][..], &["-compile"]] {
            let one = run(name, &[tier, &["-workers", "1"]].concat());
            let one_cov = run(name, &[tier, &["-coverage", "1", "-workers", "1"]].concat());
            let args = [tier, &["-coverage", "1", "-workers", "3", "-stats"]].concat();
            let (code, lines, coverage, text) = run(name, &args);
            assert_eq!((code, &lines), (one.0, &one.1), "{name} {args:?}: vs one worker\n{text}");
            assert_eq!(coverage, one_cov.2, "{name} {args:?}: coverage vs one worker\n{text}");
            checked += usize::from(text.contains("liveness: check (recorded graph)"));
            violations += usize::from(code == 13);
        }
    }
    assert!(violations >= 10, "{violations} violations");
    assert!(checked >= 20, "{checked} checked on the recorded graph");
}
