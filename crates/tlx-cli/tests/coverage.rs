//! `-coverage N`: the action-level coverage statistics are TLC's (expected
//! lines taken from TLC 2026.10.02 with `-workers 1 -coverage 1`, without
//! the lines tlx does not print: variables, invariants, constraints,
//! properties and subexpressions), in every tier and with any number of
//! workers.

use crate::common::coverage_lines;

/// Run `spec` (files `(name, text)`, the first the root module, `cfg` its
/// configuration) with `-coverage 1` and `args`: the lines of the coverage
/// statistics (without the header's date) and the whole output.
fn run(files: &[(&str, &str)], cfg: &str, args: &[&str], env: &[(&str, &str)]) -> (Vec<String>, String) {
    let dir = tlx_testkit::TempDir::new("coverage");
    for (name, text) in files {
        std::fs::write(dir.join(format!("{name}.tla")), text).unwrap();
    }
    std::fs::write(dir.join("M.cfg"), cfg).unwrap();
    let mut cmd = tlx_testkit::tlx!();
    cmd.args(["check", &format!("{}.tla", files[0].0), "-config", "M.cfg", "-coverage", "1"]).args(args).dir(&dir);
    let out = cmd.envs(env.iter().copied()).run();
    let text = out.text();
    let lines = coverage_lines(&text);
    assert!(text.contains("End of statistics."), "{text}");
    (lines, text)
}

use tlx_testkit::cli::TIERS;

/// The coverage of `files` with `cfg` is `want` in every tier.
fn check(files: &[(&str, &str)], cfg: &str, want: &[&str]) {
    let native_env = TIERS.iter().find(|(name, _, _)| *name == "native").unwrap().2;
    for (_, args, env) in TIERS
        .iter()
        .copied()
        .chain([("parallel", &["-workers", "4"][..], &[][..]), ("parallel native", &["-compile", "-workers", "3"][..], native_env)])
    {
        let (got, out) = run(files, cfg, args, env);
        assert_eq!(got, want, "{args:?} {env:?}:\n{out}");
    }
}

const C1: &str = r#"---- MODULE C1 ----
EXTENDS Naturals
CONSTANT N
VARIABLES x, y
vars == <<x, y>>
Init == x \in 0..1 /\ y = 0
Inc(i) == x < N /\ x' = x + i /\ UNCHANGED y
Dec == x > 0 /\ x' = x - 1 /\ y' = y
Both == \/ /\ y < 2
           /\ y' = y + 1
           /\ x' = x
        \/ /\ y > 0
           /\ y' \in {0, y - 1}
           /\ x' = x
Next == \E i \in 1..2 : Inc(i) \/ Dec \/ Both
Spec == Init /\ [][Next]_vars
Inv == x <= N + 1
Constr == x < 4
====
"#;

#[test]
fn actions_with_parameters_disjuncts_and_a_constraint() {
    check(
        &[("C1", C1)],
        "CONSTANT N = 5\nINIT Init\nNEXT Next\nINVARIANT Inv\nCONSTRAINT Constr\n",
        &[
            "<Init line 6, col 1 to line 6, col 4 of module C1>: 2:2",
            "<Inc line 7, col 1 to line 7, col 6 of module C1>: 6:24",
            "<Dec line 8, col 1 to line 8, col 3 of module C1>: 0:18",
            "<Both line 9, col 1 to line 9, col 4 of module C1 (9 12 11 20)>: 4:16",
            "<Both line 9, col 1 to line 9, col 4 of module C1 (12 12 14 20)>: 0:24",
        ],
    );
}

const C2: &str = r#"---- MODULE C2 ----
EXTENDS Naturals
VARIABLES x, y
vars == <<x, y>>
Init == x \in 0..3 /\ y \in 0..3 /\ x < y
A == x < 5 /\ x' = x + 1 /\ y' = y
B == y > 0 /\ y' = y - 1 /\ x' = x
Next == A \/ B
Spec == Init /\ [][Next]_vars
C1 == x < 5
C2 == y < 3
AC == x' # 4 \/ y = 0
P1 == [](x < 10)
P2 == [][x' >= x]_vars
====
"#;

#[test]
fn initial_assignments_rejected_and_constraints() {
    // Init: 6 initial states of the 16 complete assignments.
    check(
        &[("C2", C2)],
        "SPECIFICATION Spec\nCONSTRAINT C1 C2\nACTION_CONSTRAINT AC\nPROPERTY P1 P2\nCHECK_DEADLOCK FALSE\n",
        &[
            "<Init line 5, col 1 to line 5, col 4 of module C2>: 6:16",
            "<A line 6, col 1 to line 6, col 1 of module C2>: 6:13",
            "<B line 7, col 1 to line 7, col 1 of module C2>: 4:8",
        ],
    );
}

const T3: &str = r#"---- MODULE T3 ----
EXTENDS Naturals
VARIABLES x, y
Out(p) == IF p = 1 THEN {} ELSE {p, p + 1}
Recv(p) == \E e \in Out(p) :
             /\ x < 4
             /\ x' = x + e
             /\ y' = y
Wrap(A) == A /\ x' >= x
Step(p) ==
  LET d == p + 1
  IN
    /\ y < 2
    /\ y' = y + d
    /\ UNCHANGED x

(***************************************************************************)
(* A comment box after the junction list.                                  *)
(***************************************************************************)

Next == \/ \E p \in {1, 2} : Recv(p) \/ Step(p)
        \/ Wrap(y = 3 /\ y' = 0 /\ x' = x)
Spec == x = 0 /\ y \in {0, 1} /\ [][Next]_<<x, y>>
====
"#;

#[test]
fn empty_existentials_operators_of_actions_and_initial_conjuncts() {
    // An existential over an empty set is an action without states; an
    // operator applied to an action names the action; the location of a
    // junction list ends before the comments after it; each initial
    // conjunct of the SPECIFICATION is an entry (the last counts).
    check(
        &[("T3", T3)],
        "SPECIFICATION Spec\nCHECK_DEADLOCK FALSE\n",
        &[
            "<Action line 23, col 9 to line 23, col 13 of module T3>: 0:0",
            "<Action line 23, col 18 to line 23, col 29 of module T3>: 2:2",
            "<Recv line 5, col 1 to line 5, col 7 of module T3>: 0:0",
            "<Recv line 5, col 1 to line 5, col 7 of module T3 (6 14 8 22)>: 15:30",
            "<Step line 10, col 1 to line 10, col 7 of module T3 (13 5 15 18)>: 13:24",
            "<Wrap line 9, col 1 to line 9, col 7 of module T3 (22 12 22 42)>: 0:6",
        ],
    );
}

const IM: &str = r#"---- MODULE IM ----
EXTENDS Naturals
CONSTANT N
VARIABLES x, y
Init == x = 0 /\ y = 0
A == x < N /\ x' = x + 1 /\ y' = y
B(k) == y < k /\ y' = y + 1 /\ x' = x
Next == A \/ \E k \in {1, 2} : B(k)
Wrap(Act) == Act /\ x' >= x
Spec == Init /\ [][Next]_<<x, y>>
====
"#;

const MI: &str = r#"---- MODULE MI ----
EXTENDS Naturals
VARIABLES x, y
INSTANCE IM WITH N <- 2
MySpec == Init /\ [][Next \/ Wrap(x' = x /\ y' = y + 5 /\ y = 0)]_<<x, y>>
====
"#;

#[test]
fn actions_under_an_instance() {
    // TLC does not split an action under the substitutions of an INSTANCE,
    // and locates it at the INSTANCE statement.
    let files = [("MI", MI), ("IM", IM)];
    check(
        &files,
        "SPECIFICATION Spec\nCHECK_DEADLOCK FALSE\n",
        &[
            "<Init line 5, col 1 to line 5, col 4 of module IM (4 1 4 23)>: 1:1",
            "<Action line 4, col 1 to line 4, col 23 of module MI>: 8:15",
        ],
    );
    check(
        &files,
        "SPECIFICATION MySpec\nCHECK_DEADLOCK FALSE\n",
        &[
            "<Init line 4, col 1 to line 4, col 23 of module MI>: 1:1",
            "<Next line 4, col 1 to line 4, col 23 of module MI>: 8:17",
            "<Wrap line 4, col 1 to line 4, col 23 of module MI (5 30 5 64)>: 3:3",
        ],
    );
    check(
        &files,
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n",
        &["<Init line 4, col 1 to line 4, col 23 of module MI>: 1:1", "<Next line 4, col 1 to line 4, col 23 of module MI>: 8:15"],
    );
}

const NI: &str = r#"---- MODULE NI ----
EXTENDS Naturals
VARIABLES x, y
I == INSTANCE IM WITH N <- 3
Never == FALSE
Op(A, k) == A /\ k > 0
Next == \/ \E k \in {1, 2} : I!B(k)
        \/ I!A
        \/ Never
        \/ \E k \in {} : x' = k /\ y' = y
        \/ Op(x' = x + 7 /\ y' = y, 1) /\ x = 2
        \/ LET d == 2 IN \E k \in {d} : x = 3 /\ x' = x + k /\ y' = y
        \/ Op(x = 4 /\ x' = 0 /\ y' = y, 2)
Spec == I!Init /\ [][Next]_<<x, y>>
====
"#;

#[test]
fn actions_under_a_named_instance() {
    // The actions of a named instance are named `I!Op` and declared at the
    // instance's name; TLC keeps one entry per location (I!B, not I!A); a
    // 0-ary constant definition and an operator applied to an action are
    // actions named after them.
    check(
        &[("NI", NI), ("IM", IM)],
        "SPECIFICATION Spec\nCHECK_DEADLOCK FALSE\n",
        &[
            "<I!Init line 4, col 1 to line 4, col 1 of module NI>: 1:1",
            "<I!B line 4, col 1 to line 4, col 1 of module NI>: 2:18",
            "<Never line 5, col 1 to line 5, col 5 of module NI (9 12 9 16)>: 0:0",
            "<Next line 7, col 1 to line 7, col 4 of module NI (10 12 10 41)>: 0:0",
            "<Next line 7, col 1 to line 7, col 4 of module NI (11 12 11 47)>: 3:3",
            "<Next line 7, col 1 to line 7, col 4 of module NI (12 41 12 69)>: 3:3",
            "<Op line 6, col 1 to line 6, col 8 of module NI (13 12 13 43)>: 0:0",
        ],
    );
}

const NS: &str = r#"---- MODULE NS ----
EXTENDS Naturals
VARIABLES x, y
J == INSTANCE IM WITH N <- 2
Spec == J!Spec
====
"#;

#[test]
fn a_specification_through_a_named_instance() {
    // TLC sees `[][Next]_vars` and the initial predicate under the
    // instance's substitutions: Next is one unnamed action.
    check(
        &[("NS", NS), ("IM", IM)],
        "SPECIFICATION Spec\nCHECK_DEADLOCK FALSE\n",
        &[
            "<Init line 5, col 1 to line 5, col 4 of module IM (4 1 4 28)>: 1:1",
            "<Action line 4, col 1 to line 4, col 28 of module NS>: 8:15",
        ],
    );
}

#[test]
fn coverage_is_printed_before_the_statistics() {
    let (_, out) = run(&[("C2", C2)], "SPECIFICATION Spec\nCHECK_DEADLOCK FALSE\n", &[], &[]);
    let cov = out.find("The coverage statistics at ").expect("coverage");
    let end = out.find("End of statistics.").expect("end");
    let stats = out.find("states generated, ").expect("statistics");
    assert!(cov < end && end < stats, "{out}");
    assert!(
        out[cov..].starts_with("The coverage statistics at ")
            && out[cov..end]
                .contains("(see https://explain.tlapl.us/module-coverage-statistics for how to interpret the following statistics).\n"),
        "{out}"
    );
}
