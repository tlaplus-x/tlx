//! Falsification probes for the temporal and refinement property shapes of
//! the >100x speedup cohort (docs/research/speedup-audit.md F5).
//!
//! Each `tests/specs/TP*.tla` is a reduced model whose configured property is
//! false: the probe reproduces the shape of a corpus property (a conjunction
//! of leads-to obligations under WF/SF, an explicit `[]<>` obligation, the
//! `[]`-wrapped ordered-pair leads-to of RaftMongo, MisraReachability's
//! `Termination`, and the initial, action and fairness conjuncts of a
//! refinement `R!Spec`) and changes one consequent or fairness conjunct at a
//! time. Every execution tier in both modes must report the violation by name
//! together with a counterexample, and the name must equal the cached TLC
//! oracle's (tests/specs/expected.json); `scripts/spectest.py` validates the
//! lassos against TLC.

use serde_json::Value;
use tlx_testkit::cli::{result_lines, tests_specs, Run};

/// A reduced probe and the counterexample it must produce.
struct Probe {
    /// The spec name in `tests/specs`.
    name: &'static str,
    /// The `Error:` line that names the violated property (TP6's action
    /// property is named by a source range, so the two halves pin the form).
    error: (&'static str, &'static str),
    /// The lasso close marker of a liveness counterexample (None: the
    /// property fails in the initial state or on a step).
    lasso: Option<&'static str>,
    /// The tableau line, for the quantified shapes.
    branches: Option<&'static str>,
}

const PROBES: &[Probe] = &[
    // MultiCarElevator TemporalInvariant: a conjunction of leads-to
    // obligations under WF and SF (the corpus config prints 6 branches with
    // two people and two elevators; this reduces it to four with three
    // people and one mutated consequent).
    Probe {
        name: "TP1",
        error: ("Error: Temporal property TemporalInvariantProbe", " was violated."),
        lasso: Some("Stuttering"),
        branches: Some("Checking 4 branches of temporal properties"),
    },
    // MultiCarElevator's liveness obligation as an explicit []<> under the
    // same fairness, with strong fairness of Serve dropped.
    Probe {
        name: "TP2",
        error: ("Error: Temporal property TemporalInvariant", " was violated."),
        lasso: Some("Stuttering"),
        branches: None,
    },
    // RaftMongo CommitPointEventuallyPropagates: the ordered-pair leads-to
    // obligations inside [] under SF (two servers reduce the corpus's nine
    // branches to four), with a mutated inner <> consequent.
    Probe {
        name: "TP3",
        error: ("Error: Temporal property CommitPointEventuallyPropagatesProbe", " was violated."),
        lasso: Some("Stuttering"),
        branches: Some("Checking 4 branches of temporal properties"),
    },
    // MisraReachability Termination: <>(pc = "Done") under weak fairness,
    // with the finishing action removed from Next.
    Probe { name: "TP4", error: ("Error: Temporal property Termination", " was violated."), lasso: Some("Stuttering"), branches: None },
    // Refines == R!RSpec: the initial conjunct R!RInit is false.
    Probe { name: "TP5", error: ("Error: Property RInit", " is violated by the initial state:"), lasso: None, branches: None },
    // Refines == R!RSpec: the [][R!RNext]_R!vars conjunct is false on the
    // concrete step.
    Probe { name: "TP6", error: ("Error: Action property ", " of module TPRefAbs is violated."), lasso: None, branches: None },
    // Refines == R!RSpec: WF_R!vars(R!RNext) is false on a stuttering
    // behavior of the concrete specification without its fairness.
    Probe { name: "TP7", error: ("Error: Temporal property Refines", " was violated."), lasso: Some("Stuttering"), branches: None },
];

/// The three modes the probes must check: default, TLC compatibility with the
/// interpreter, and TLC compatibility with compiled execution.
const MODES: &[(&str, &[&str])] = &[("default", &[]), ("-interp -tlc", &["-tlc", "-interp"]), ("-compile -tlc", &["-tlc", "-compile"])];

/// Check spec `name` in `mode` with one worker.
fn run(name: &str, args: &[&str]) -> Run {
    tlx_testkit::tlx_default!()
        .check(format!("{name}.tla"))
        .cfg(format!("{name}.cfg"))
        .args(["-workers", "1"])
        .args(args)
        .dir(tests_specs())
        .run()
}

/// The violated property name of a `tlx` error line (the temporal, initial
/// and action property messages all end in `violated`).
fn violated(text: &str) -> Option<&str> {
    let line = text.lines().find(|l| {
        l.starts_with("Error: Temporal property ") || l.starts_with("Error: Property ") || l.starts_with("Error: Action property ")
    })?;
    let rest = line
        .strip_prefix("Error: Temporal property ")
        .or_else(|| line.strip_prefix("Error: Property "))
        .or_else(|| line.strip_prefix("Error: Action property "))?;
    rest.split(" was violated.").next().and_then(|r| r.split(" is violated").next())
}

/// TLC's cached verdicts (tests/specs/expected.json), written by
/// `python3 scripts/spectest.py --refresh`.
fn tlc_oracles() -> Value {
    let path = tests_specs().join("expected.json");
    serde_json::from_str(&std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))).expect("expected.json")
}

/// Check `probe` in every mode and against TLC's cached verdict.
fn check_probe(probe: &Probe) {
    let oracles = tlc_oracles();
    let (prefix, suffix) = probe.error;
    let want = oracles[probe.name]["violated"].as_str().unwrap_or_else(|| panic!("{}: expected.json has no violated name", probe.name));
    assert_eq!(oracles[probe.name]["exit"], 13, "{}: TLC's cached exit code", probe.name);
    let mut baseline: Option<Vec<String>> = None;
    for (mode_name, args) in MODES {
        let out = run(probe.name, args);
        let text = out.text();
        let at = format!("{} [{mode_name}]", probe.name);
        assert_eq!(out.code, 13, "{at}: exit code\n{text}");
        assert!(text.contains(prefix), "{at}: missing `{prefix}`\n{text}");
        assert!(text.contains(suffix), "{at}: missing `{suffix}`\n{text}");
        assert_eq!(violated(&text), Some(want), "{at}: violated name\n{text}");
        if let Some(marker) = probe.lasso {
            assert!(
                text.contains("Error: The following behavior constitutes a counter-example:"),
                "{at}: no liveness counterexample\n{text}"
            );
            assert!(text.contains(marker), "{at}: no lasso close `{marker}`\n{text}");
            assert!(text.contains("State 1:"), "{at}: no first state\n{text}");
        }
        if let Some(branches) = probe.branches {
            assert!(text.contains(branches), "{at}: missing `{branches}`\n{text}");
        }
        // The three modes must agree on the error, the counterexample and the
        // state counts; only compilation and timing lines may differ.
        let lines = result_lines(&text).into_iter().map(String::from).collect::<Vec<_>>();
        match &baseline {
            None => baseline = Some(lines),
            Some(want) => assert_eq!(&lines, want, "{at}: differs from the previous mode\n{text}"),
        }
    }
}

/// The probe named `name` (the spec name in `tests/specs`).
fn probe(name: &str) -> &'static Probe {
    PROBES.iter().find(|p| p.name == name).unwrap_or_else(|| panic!("no probe {name}"))
}

macro_rules! probe_test {
    ($test:ident, $name:literal) => {
        #[test]
        fn $test() {
            check_probe(probe($name));
        }
    };
}

probe_test!(elevator_leads_to_conjunction, "TP1");
probe_test!(elevator_always_eventually, "TP2");
probe_test!(raft_commit_point_propagates, "TP3");
probe_test!(misra_termination, "TP4");
probe_test!(refines_initial_conjunct, "TP5");
probe_test!(refines_action_conjunct, "TP6");
probe_test!(refines_fairness_conjunct, "TP7");
