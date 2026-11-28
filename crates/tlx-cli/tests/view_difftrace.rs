//! `-view` and `-difftrace` state rendering (docs/configuration.md): TLC's
//! presentation of counterexample states and `-dump` node labels, in the
//! interpreter and the compiled tier, with one and several workers.

use std::time::Duration;

use tlx_testkit::cli::TIERS;

/// Run the fixture `spec` with `args` in `tier` and `workers`, returning
/// the run's output and exit code.
macro_rules! run_case {
    ($spec:literal, $args:expr, $tier:expr, $workers:expr) => {{
        let (_, tier_args, tier_env) = $tier;
        let dir = tlx_testkit::TempDir::new(concat!("view-difftrace-", $spec));
        std::fs::write(dir.join(concat!($spec, ".tla")), include_str!(concat!("fixtures/view-difftrace/", $spec, ".tla"))).unwrap();
        std::fs::write(dir.join(concat!($spec, ".cfg")), include_str!(concat!("fixtures/view-difftrace/", $spec, ".cfg"))).unwrap();
        let mut cmd = tlx_testkit::tlx_default!();
        cmd.args(["check", concat!($spec, ".tla"), "-tlc", "-workers", $workers]).args(tier_args).args($args).dir(&dir);
        cmd.envs([("TLX_PARANOID", "1")]);
        cmd.envs(tier_env.iter().copied());
        cmd.timeout(Duration::from_secs(60)).run()
    }};
}

/// The body of every state a counterexample shows, in order (empty for a
/// `Stuttering` line); the statistics that follow are not part of them.
fn state_bodies(text: &str) -> Vec<String> {
    let is_state = |line: &str| {
        line.strip_prefix("State ")
            .and_then(|rest| rest.split_once(':'))
            .is_some_and(|(n, _)| !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()))
    };
    let stops = |line: &str| {
        line.starts_with("Back to state")
            || line.starts_with("Finished")
            || line.starts_with("The number of states generated")
            || line.contains(" states generated, ")
            || line.starts_with("Error:")
    };
    let mut out = Vec::new();
    let mut cur: Option<String> = None;
    for line in text.lines() {
        if is_state(line) || stops(line) {
            if let Some(body) = cur.take() {
                out.push(body);
            }
            if !stops(line) {
                cur = Some(String::new());
            }
            continue;
        }
        if let Some(body) = &mut cur {
            if !line.is_empty() {
                if !body.is_empty() {
                    body.push('\n');
                }
                body.push_str(line);
            }
        }
    }
    if let Some(body) = cur {
        out.push(body);
    }
    out
}

/// Assert the counterexample's state bodies in every tier, with one and four
/// workers.
macro_rules! check_states {
    ($spec:literal, $args:expr, $want:expr) => {{
        for (name, tier_args, tier_env) in TIERS.iter().copied() {
            for workers in ["1", "4"] {
                let out = run_case!($spec, $args, (name, tier_args, tier_env), workers);
                assert_eq!(out.code, 12, "{} {name} -workers {workers}: {}", $spec, out.text());
                let got = state_bodies(&out.text());
                assert_eq!(got, $want, "{} {name} -workers {workers}:\n{}", $spec, out.text());
            }
        }
    }};
}

#[test]
fn view_prints_a_tuple_views_variables_in_declaration_order() {
    // (Only the VIEW's variables: `z` is not part of it.)
    check_states!(
        "ViewTuple",
        &["-view"],
        &["/\\ x = 0\n/\\ y = 0", "/\\ x = 1\n/\\ y = 1", "/\\ x = 2\n/\\ y = 2", "/\\ x = 3\n/\\ y = 3"]
    );
}

#[test]
fn view_labels_a_component_by_declaration_order() {
    // (TLC pairs the tuple's components with the variables in declaration
    // order: `x` shows the first component of `<<y, x>>`.)
    check_states!("ViewRev", &["-view"], &["/\\ x = 0\n/\\ y = 0", "/\\ x = 10\n/\\ y = 1", "/\\ x = 20\n/\\ y = 2"]);
}

#[test]
fn view_prints_a_scalar_view_as_the_value() {
    check_states!("ViewScalar", &["-view"], &["0", "2", "4"]);
}

#[test]
fn view_always_bullets_a_tuple_view_of_one_variable() {
    check_states!("ViewOneVar", &["-view"], &["/\\ x = 0", "/\\ x = 1", "/\\ x = 2"]);
}

#[test]
fn view_bullets_a_one_element_tuple_and_hides_other_variables() {
    check_states!("ViewTupleOne", &["-view"], &["/\\ x = 0", "/\\ x = 1", "/\\ x = 2"]);
}

#[test]
fn view_prints_the_value_when_its_tuple_does_not_match_its_variables() {
    check_states!("ViewComputed", &["-view"], &["<<0>>", "<<2>>", "<<4>>"]);
}

#[test]
fn view_collects_variables_through_parameterized_operators_and_functions() {
    // (TLC's `allParams` adds the applied definition's free variables
    // whatever its arity: `F(a) == <<a, y>>` under `F(x)` shows `x` and `y`.)
    check_states!("ViewOp", &["-view"], &["/\\ x = 0\n/\\ y = 5", "/\\ x = 1\n/\\ y = 5", "/\\ x = 2\n/\\ y = 5"]);
    // (The definition's free variables make the count 3 against a 2-tuple, so
    // the value is printed instead of mislabeled fields.)
    check_states!("ViewOpComputed", &["-view"], &["<<1, 2>>", "<<2, 2>>", "<<3, 2>>"]);
    check_states!("ViewFn", &["-view"], &["<<1, 2>>", "<<2, 2>>", "<<3, 2>>"]);
}

#[test]
fn alias_takes_precedence_over_view() {
    check_states!("ViewAlias", &["-view"], &["/\\ ax = 0\n/\\ k = 5", "/\\ ax = 1\n/\\ k = 5", "/\\ ax = 2\n/\\ k = 5"]);
    // (-difftrace omits the ALIAS field that does not change, after State 1.)
    check_states!("ViewAlias", &["-view", "-difftrace"], &["/\\ ax = 0\n/\\ k = 5", "/\\ ax = 1", "/\\ ax = 2"]);
}

#[test]
fn view_prints_a_violation_by_the_initial_state() {
    for (name, tier_args, tier_env) in TIERS.iter().copied() {
        let out = run_case!("ViewInit", &["-view"], (name, tier_args, tier_env), "1");
        assert_eq!(out.code, 12, "{name}: {}", out.text());
        assert!(out.text().contains("Invariant Inv is violated by the initial state:\n/\\ x = 5\n/\\ y = 0\n"), "{name}: {}", out.text());
    }
}

#[test]
fn view_without_a_view_in_the_cfg_changes_nothing() {
    let dir = tlx_testkit::TempDir::new("view-none");
    std::fs::write(dir.join("ViewNone.tla"), include_str!("fixtures/view-difftrace/ViewNone.tla")).unwrap();
    std::fs::write(dir.join("ViewNone.cfg"), include_str!("fixtures/view-difftrace/ViewNone.cfg")).unwrap();
    for (name, tier_args, tier_env) in TIERS.iter().copied() {
        let run = |args: &[&str]| {
            let mut cmd = tlx_testkit::tlx_default!();
            cmd.args(["check", "ViewNone.tla", "-tlc", "-workers", "1"]).args(tier_args).args(args).dir(&dir);
            cmd.envs([("TLX_PARANOID", "1")]);
            cmd.envs(tier_env.iter().copied());
            cmd.timeout(Duration::from_secs(60)).run()
        };
        let plain = run(&[]);
        let viewed = run(&["-view"]);
        assert_eq!(viewed.code, plain.code, "{name}");
        let states = |text: &str| state_bodies(text);
        assert_eq!(states(&viewed.text()), states(&plain.text()), "{name}:\n{}", viewed.text());
        assert_eq!(states(&plain.text()), ["/\\ x = 0\n/\\ y = 0", "/\\ x = 1\n/\\ y = 1", "/\\ x = 2\n/\\ y = 2"]);
    }
}

#[test]
fn difftrace_omits_unchanged_variables() {
    check_states!("DiffMulti", &["-difftrace"], &["/\\ x = 0\n/\\ y = 0", "/\\ x = 1", "/\\ x = 2\n/\\ y = 1", "/\\ x = 3"]);
}

#[test]
fn difftrace_prints_a_single_variable_state_without_a_bullet() {
    check_states!("DiffOne", &["-difftrace"], &["x = 0", "x = 1", "x = 2", "x = 3"]);
}

#[test]
fn difftrace_prints_state_one_in_full() {
    // (A two-state behavior: TLC's own `printTrace` passes State 1 itself as
    // its predecessor there and prints it blank; tlx intentionally does not,
    // docs/compat.md D-36.)
    check_states!("DiffShort", &["-difftrace"], &["/\\ x = 0\n/\\ y = 0", "/\\ x = 1\n/\\ y = 1"]);
}

#[test]
fn difftrace_omits_unchanged_alias_fields() {
    check_states!("DiffAlias", &["-difftrace"], &["/\\ ax = 0\n/\\ k = 5", "/\\ ax = 1", "/\\ ax = 2"]);
    // (Without -difftrace every ALIAS field is shown.)
    check_states!("DiffAlias", &[] as &[&str], &["/\\ ax = 0\n/\\ k = 5", "/\\ ax = 1\n/\\ k = 5", "/\\ ax = 2\n/\\ k = 5"]);
}

#[test]
fn difftrace_evaluates_the_predecessor_with_its_own_trace_path() {
    // (`sum` changes at every step: the predecessor's `Len(Trace)` is
    // evaluated on the path up to that predecessor, not on the current one.)
    check_states!("ViewTraceSum", &["-difftrace"], &["/\\ x = 0\n/\\ sum = 1", "/\\ x = 1\n/\\ sum = 3", "/\\ x = 2\n/\\ sum = 5"]);
}

#[test]
fn difftrace_omits_unchanged_view_fields() {
    check_states!("DiffView", &["-view", "-difftrace"], &["/\\ x = 0\n/\\ y = 0", "/\\ x = 1", "/\\ x = 2\n/\\ y = 1", "/\\ x = 3"]);
}

#[test]
fn difftrace_omits_unchanged_variables_in_a_liveness_lasso() {
    for (name, tier_args, tier_env) in TIERS.iter().copied() {
        for workers in ["1", "4"] {
            let out = run_case!("LassoTwo", &["-difftrace"], (name, tier_args, tier_env), workers);
            assert_eq!(out.code, 13, "{name} -workers {workers}: {}", out.text());
            let got = state_bodies(&out.text());
            assert_eq!(got, ["/\\ x = 0\n/\\ y = 7", "/\\ x = 1", "/\\ x = 2", ""], "{name} -workers {workers}:\n{}", out.text());
            assert!(out.text().contains("State 4: Stuttering"), "{name} -workers {workers}: {}", out.text());
        }
    }
}

#[test]
fn difftrace_uses_the_shown_level_in_a_liveness_lasso() {
    // (The lasso walks states at BFS depths 2 and 3 in turn after the first
    // step; the alias's `TLCGet("level")` makes `sum` change at every shown
    // state, so no changed field is dropped.)
    for (name, tier_args, tier_env) in TIERS.iter().copied() {
        let out = run_case!("LevelLasso", &["-difftrace"], (name, tier_args, tier_env), "1");
        assert_eq!(out.code, 13, "{name}: {}", out.text());
        assert_eq!(
            state_bodies(&out.text()),
            [
                "/\\ x = 0\n/\\ y = 0\n/\\ sum = 1",
                "/\\ x = 1\n/\\ sum = 3",
                "/\\ x = 2\n/\\ sum = 5",
                "/\\ x = 5\n/\\ y = 1\n/\\ sum = 9",
                "/\\ x = 2\n/\\ sum = 7"
            ],
            "{name}:\n{}",
            out.text()
        );
        assert!(out.text().contains("Back to state 2"), "{name}: {}", out.text());
    }
}

#[test]
fn view_exports_a_simulated_behavior() {
    for (name, tier_args, tier_env) in TIERS.iter().copied() {
        let out = run_case!("ViewRev", &["-simulate", "num=1", "-seed", "1", "-view"], (name, tier_args, tier_env), "1");
        assert_eq!(out.code, 12, "{name}: {}", out.text());
        let got = state_bodies(&out.text());
        assert_eq!(got, ["/\\ x = 0\n/\\ y = 0", "/\\ x = 10\n/\\ y = 1", "/\\ x = 20\n/\\ y = 2"], "{name}:\n{}", out.text());
    }
}

#[test]
fn difftrace_exports_a_simulated_behavior() {
    for (name, tier_args, tier_env) in TIERS.iter().copied() {
        let out = run_case!("DiffMulti", &["-simulate", "num=1", "-seed", "1", "-difftrace"], (name, tier_args, tier_env), "1");
        assert_eq!(out.code, 12, "{name}: {}", out.text());
        let got = state_bodies(&out.text());
        assert_eq!(got, ["/\\ x = 0\n/\\ y = 0", "/\\ x = 1", "/\\ x = 2\n/\\ y = 1", "/\\ x = 3"], "{name}:\n{}", out.text());
        assert!(out.text().contains("The number of states generated: 4"), "{name}: {}", out.text());
    }
}

#[test]
fn view_ignores_the_optimize_projection() {
    for (name, tier_args, tier_env) in TIERS.iter().copied() {
        let dir = tlx_testkit::TempDir::new("view-difftrace-optimize");
        std::fs::write(dir.join("OptimizeView.tla"), include_str!("fixtures/view-difftrace/OptimizeView.tla")).unwrap();
        std::fs::write(dir.join("OptimizeView.cfg"), include_str!("fixtures/view-difftrace/OptimizeView.cfg")).unwrap();
        let run = |args: &[&str]| {
            let mut cmd = tlx_testkit::tlx_default!();
            cmd.args(["check", "OptimizeView.tla", "-workers", "1"]).args(tier_args).args(args).dir(&dir);
            cmd.envs(tier_env.iter().copied()).timeout(Duration::from_secs(60)).run()
        };
        let out = run(&["-optimize", "-view", "-proofdir", "proofs"]);
        assert_eq!(out.code, 12, "{name}: {}", out.text());
        assert!(out.text().contains("Optimizations: unobserved-state-projection"), "{name}: {}", out.text());
        // (The certified projection is internal: the concrete states are shown,
        // not the synthetic projected tuple.)
        assert_eq!(
            state_bodies(&out.text()),
            ["/\\ x = 0\n/\\ y = 0", "/\\ x = 1\n/\\ y = 0", "/\\ x = 2\n/\\ y = 1", "/\\ x = 3\n/\\ y = 2"],
            "{name}:\n{}",
            out.text()
        );
        let dumped = run(&["-optimize", "-view", "-proofdir", "proofs", "-dump", "dot", "o.dot"]);
        assert_eq!(dumped.code, 12, "{name}: {}", dumped.text());
        let dot = std::fs::read_to_string(dir.join("o.dot")).expect("the dot file");
        for (label, _) in dot_nodes(&dot) {
            assert!(label.starts_with("/\\ x = "), "{name}: {label:?} in {dot}");
        }
    }
}

/// The GraphViz node label and tooltip of every node, in file order
/// (GraphViz's `\\` and `\n` escapes undone).
fn dot_nodes(text: &str) -> Vec<(String, Option<String>)> {
    fn decode(s: &str) -> String {
        s.replace("\\n", "\n").replace("\\\\", "\\")
    }
    let mut nodes = Vec::new();
    for line in text.lines().filter(|l| l.contains("[label=") && !l.contains(" -> ")) {
        let value = |key: &str| {
            let start = line.find(&format!("{key}=\""))? + key.len() + 2;
            let rest = &line[start..];
            let end = rest.find('"')?;
            Some(decode(&rest[..end]))
        };
        if let Some(label) = value("label") {
            nodes.push((label, value("tooltip")));
        }
    }
    nodes
}

#[test]
fn difftrace_labels_dot_nodes_with_the_diff_and_keeps_the_full_tooltip() {
    for (name, tier_args, tier_env) in TIERS.iter().copied() {
        for workers in ["1", "4"] {
            let dir = tlx_testkit::TempDir::new("view-difftrace-dot");
            std::fs::write(dir.join("DiffMulti.tla"), include_str!("fixtures/view-difftrace/DiffMulti.tla")).unwrap();
            std::fs::write(dir.join("DiffMulti.cfg"), include_str!("fixtures/view-difftrace/DiffMulti.cfg")).unwrap();
            let mut cmd = tlx_testkit::tlx_default!();
            cmd.args(["check", "DiffMulti.tla", "-tlc", "-workers", workers]).args(tier_args).args(["-difftrace", "-dump", "dot", "g.dot"]);
            cmd.dir(&dir).envs(tier_env.iter().copied()).timeout(Duration::from_secs(60));
            let out = cmd.run();
            assert_eq!(out.code, 12, "{name} -workers {workers}: {}", out.text());
            let dot = std::fs::read_to_string(dir.join("g.dot")).expect("the dot file");
            let nodes = dot_nodes(&dot);
            let labels: Vec<&str> = nodes.iter().map(|(label, _)| label.as_str()).collect();
            assert_eq!(
                labels,
                ["/\\ x = 0\n/\\ y = 0", "/\\ x = 1", "/\\ x = 2\n/\\ y = 1", "/\\ x = 3"],
                "{name} -workers {workers}: {dot}"
            );
            let tooltips: Vec<Option<&str>> = nodes.iter().map(|(_, t)| t.as_deref()).collect();
            assert_eq!(
                tooltips,
                [None, Some("/\\ x = 1\n/\\ y = 0"), Some("/\\ x = 2\n/\\ y = 1"), Some("/\\ x = 3\n/\\ y = 1")],
                "{name} -workers {workers}: {dot}"
            );
        }
    }
}

#[test]
fn difftrace_labels_dot_nodes_with_a_view_and_several_workers() {
    // (With a `.cfg` `VIEW` and several workers the search resolves the
    // representatives at the end of a level: the diffs must still label the
    // nodes, as with one worker.)
    for (name, tier_args, tier_env) in TIERS.iter().copied() {
        for workers in ["1", "4"] {
            let dir = tlx_testkit::TempDir::new("view-difftrace-dot-ordered");
            std::fs::write(dir.join("DiffView.tla"), include_str!("fixtures/view-difftrace/DiffView.tla")).unwrap();
            std::fs::write(dir.join("DiffView.cfg"), include_str!("fixtures/view-difftrace/DiffView.cfg")).unwrap();
            let mut cmd = tlx_testkit::tlx_default!();
            cmd.args(["check", "DiffView.tla", "-tlc", "-workers", workers]).args(tier_args).args([
                "-view",
                "-difftrace",
                "-dump",
                "dot",
                "d.dot",
            ]);
            cmd.dir(&dir).envs(tier_env.iter().copied()).timeout(Duration::from_secs(60));
            let out = cmd.run();
            assert_eq!(out.code, 12, "{name} -workers {workers}: {}", out.text());
            let dot = std::fs::read_to_string(dir.join("d.dot")).expect("the dot file");
            let nodes = dot_nodes(&dot);
            let labels: Vec<&str> = nodes.iter().map(|(label, _)| label.as_str()).collect();
            assert_eq!(
                labels,
                ["/\\ x = 0\n/\\ y = 0", "/\\ x = 1", "/\\ x = 2\n/\\ y = 1", "/\\ x = 3"],
                "{name} -workers {workers}: {dot}"
            );
            let tooltips: Vec<Option<&str>> = nodes.iter().map(|(_, t)| t.as_deref()).collect();
            assert_eq!(
                tooltips,
                [None, Some("/\\ x = 1\n/\\ y = 0"), Some("/\\ x = 2\n/\\ y = 1"), Some("/\\ x = 3\n/\\ y = 1")],
                "{name} -workers {workers}: {dot}"
            );
        }
    }
}

#[test]
fn view_labels_dot_nodes_through_the_view() {
    for (name, tier_args, tier_env) in TIERS.iter().copied() {
        for workers in ["1", "4"] {
            let dir = tlx_testkit::TempDir::new("view-difftrace-dot-view");
            std::fs::write(dir.join("ViewRev.tla"), include_str!("fixtures/view-difftrace/ViewRev.tla")).unwrap();
            std::fs::write(dir.join("ViewRev.cfg"), include_str!("fixtures/view-difftrace/ViewRev.cfg")).unwrap();
            let mut cmd = tlx_testkit::tlx_default!();
            cmd.args(["check", "ViewRev.tla", "-tlc", "-workers", workers]).args(tier_args).args(["-view", "-dump", "dot", "v.dot"]);
            cmd.dir(&dir).envs(tier_env.iter().copied()).timeout(Duration::from_secs(60));
            let out = cmd.run();
            assert_eq!(out.code, 12, "{name} -workers {workers}: {}", out.text());
            let dot = std::fs::read_to_string(dir.join("v.dot")).expect("the dot file");
            let labels: Vec<String> = dot_nodes(&dot).into_iter().map(|(label, _)| label).collect();
            assert_eq!(
                labels,
                ["/\\ x = 0\n/\\ y = 0", "/\\ x = 10\n/\\ y = 1", "/\\ x = 20\n/\\ y = 2"],
                "{name} -workers {workers}: {dot}"
            );
        }
    }
}
