//! Public frontend tests: every observation is translated or refused.

use tlx_front::cfg::parse_cfg;
use tlx_sema::optimize::{abstract_model, Artifact, Diagnostic};
use tlx_sema::Program;

const CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";

fn abstract_source(body: &str, cfg: &str) -> Result<Artifact, Diagnostic> {
    let dir = tlx_testkit::TempDir::new("abstraction-sema");
    let path = dir.write("Counter.tla", &format!("---- MODULE Counter ----\nEXTENDS Naturals\n{body}\n====\n"));
    let mut program = Program::load(&path, &[]).unwrap();
    abstract_model(&mut program, &parse_cfg(cfg).unwrap())
}

#[test]
fn thresholds_include_strict_and_exact_boundaries() {
    for (observation, cap) in
        [("c >= 3", 3), ("c < 3", 3), ("c > 3", 4), ("c <= 3", 4), ("c = 3", 4), ("c /= 3", 4), ("3 < c", 4), ("3 <= c", 3)]
    {
        let a = abstract_source(&format!("VARIABLE c\nInit == c = 0\nNext == c' = c + 1\nInv == {observation}"), CFG).unwrap();
        assert!(a.module.contains(&format!("IF v0 < {cap} THEN v0 + 1 ELSE {cap}")), "{observation}: {}", a.module);
    }
}

#[test]
fn guards_properties_aliases_parameters_and_let_share_analysis() {
    let a = abstract_source(
        "CONSTANT K\nVARIABLE c\nInit == c = 100\nInc(x) == x + 1\nAt(x) == x >= K\nNext == (At(c) /\\ c' = 0) \\/ (~At(c) /\\ c' = Inc(c)) \\/ UNCHANGED c\nInv == LET Bound(x) == x <= 5 IN Bound(c)",
        &format!("{CFG}CONSTANT K = 8\n"),
    ).unwrap();
    assert!(a.module.contains("v0 = 8"), "{}", a.module);
    assert!(a.module.contains("IF v0 < 8 THEN v0 + 1 ELSE 8"));
    assert!(a.report.contains("domain 0..8"));
    assert!(a.report.contains("model checking has NOT been performed"));
}

#[test]
fn independent_counters_have_independent_partitions() {
    let a = abstract_source(
        "VARIABLES x, y\nInit == x = 0 /\\ y = 0\nNext == (x' = x + 1 /\\ UNCHANGED y) \\/ (y' = y + 1 /\\ UNCHANGED x)\nInv == x >= 2 /\\ y /= 4",
        CFG,
    ).unwrap();
    assert!(a.report.contains("domain 0..2"));
    assert!(a.report.contains("domain 0..5"));
}

#[test]
fn no_observation_and_zero_threshold_collapse_to_one_state() {
    for inv in ["TRUE", "c >= 0"] {
        let a = abstract_source(&format!("VARIABLE c\nInit == c = 12\nNext == c' = c + 1\nInv == {inv}"), CFG).unwrap();
        assert!(a.report.contains("domain 0..0"));
        assert!(a.module.contains("v0 = 0"));
        assert!(a.module.contains("IF v0 < 0 THEN v0 + 1 ELSE 0"));
    }
}

#[test]
fn unsupported_uses_are_not_lost_during_lowering() {
    for body in [
        "VARIABLE c\nInit == c = 0\nNext == c' = c - 1\nInv == c >= 0",
        "VARIABLES c, d\nInit == c = 0 /\\ d = 0\nNext == c' = c + 1 /\\ d' = c\nInv == c >= 0",
        "VARIABLES c, d\nInit == c = 0 /\\ d = 0\nNext == c' = c + 1 /\\ UNCHANGED d\nInv == c < d",
        "VARIABLE c\nInit == c = 0\nNext == c' = c + 1\nExact(x) == x % 2\nInv == Exact(c) = 0",
        "VARIABLE c\nInit == c = 0\nNext == c' = c + 1\nInv == <<TRUE, FALSE>>[c]",
        "VARIABLE c\nInit == c = 0\nNext == c' = c + 1\nInv == c' >= 0",
        "VARIABLE c\nInit == c = 0\nNext == TRUE\nInv == c >= 0",
        "VARIABLE c\nInit == c = 0\nNext == c' = c + 1 /\\ c' = 0\nInv == c >= 0",
        "VARIABLE c\nInit == c \\in Nat\nNext == c' = c + 1\nInv == c >= 0",
        "VARIABLES c, h\nInit == c = 0 /\\ h = <<>>\nNext == c' = c + 1 /\\ UNCHANGED h\nInv == c >= 0",
        "VARIABLE c\nInit == c = 0\nNext == c' = c + 1\nInv == [c EXCEPT ![1] = @ + 1] = c",
        "VARIABLE c\nInit == c = 0\nNext == c' = c + 1\nInv == \\A x \\in {c}: x >= 0",
    ] {
        let error = abstract_source(body, CFG).unwrap_err();
        assert!(error.span.is_some(), "{body}: {error:?}");
    }
}

#[test]
fn configuration_observations_and_overrides_are_not_ignored() {
    let body = "VARIABLE c\nInit == c = 0\nNext == c' = c + 1\nInv == c >= 0";
    for extra in [
        "PROPERTY Inv",
        "CONSTRAINT Inv",
        "ACTION_CONSTRAINT Inv",
        "VIEW Inv",
        "SYMMETRY Inv",
        "ALIAS Inv",
        "POSTCONDITION Inv",
        "_POSSIBLE Inv",
        "SPECIFICATION Inv",
        "CONSTANT Next <- Init",
    ] {
        assert!(abstract_source(body, &format!("{CFG}{extra}\n")).is_err(), "{extra}");
    }
    assert!(abstract_source(body, &CFG.replace("CHECK_DEADLOCK FALSE\n", "")).is_err());
    assert!(abstract_source(body, &CFG.replace("CHECK_DEADLOCK FALSE", "CHECK_DEADLOCK TRUE")).is_err());
    assert!(abstract_source(body, &CFG.replace("INVARIANT Inv\n", "")).is_err());
}

#[test]
fn assumptions_and_integer_boundaries_are_checked() {
    let body = "VARIABLE c\nInit == c = 0\nNext == c' = c + 1\nInv == c >= 0";
    assert!(abstract_source(&format!("ASSUME FALSE\n{body}"), CFG).is_err());
    assert!(abstract_source(&format!("ASSUME 1 < 2\n{body}"), CFG).is_ok());
    assert!(abstract_source(&body.replace("Inv == c >= 0", "Inv == c >= 2147483647"), CFG).is_ok());
    assert!(abstract_source(&body.replace("Inv == c >= 0", "Inv == c = 2147483647"), CFG).is_err());
    assert!(abstract_source(&body.replace("c = 0", "c = 2147483648"), CFG).is_err());
}

#[test]
fn recursive_operators_refuse_instead_of_looping() {
    let body = "VARIABLE c\nRECURSIVE R(_)\nR(x) == R(x)\nInit == c = 0\nNext == c' = c + 1\nInv == R(c)";
    let error = abstract_source(body, CFG).unwrap_err();
    assert!(error.message.contains("recursive"), "{error:?}");
}

#[test]
fn unused_actual_arguments_cannot_hide_external_effects() {
    let dir = tlx_testkit::TempDir::new("abstraction-effects");
    let root = dir.write("M.tla", "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE c\nIgnore(x) == TRUE\nInit == c = 0\nNext == c' = c + 1\nInv == Ignore(PrintT(c))\n====\n");
    let mut program = Program::load(&root, &[]).unwrap();
    let error = abstract_model(&mut program, &parse_cfg(CFG).unwrap()).unwrap_err();
    assert!(error.message.contains("effectful"), "{error:?}");
}

#[test]
fn all_selected_properties_participate_and_normalization_has_a_budget() {
    let body = "VARIABLE c\nInit == c = 0\nNext == c' = c + 1\nInv == c >= 1\nExtra == c = 9";
    let artifact = abstract_source(body, &format!("{CFG}INVARIANT Extra\n")).unwrap();
    assert!(artifact.report.contains("domain 0..10"));
    assert!(artifact.config.contains("INVARIANT Invariant1"));
    assert!(abstract_source(&body.replace("Extra == c = 9", "Extra == c % 2 = 0"), &format!("{CFG}INVARIANT Extra\n")).is_err());
    let mut chain = String::from("VARIABLE c\nInit == c = 0\nNext == c' = c + 1\nP0 == c >= 0\n");
    for i in 1..140 {
        chain.push_str(&format!("P{i} == P{}\n", i - 1));
    }
    chain.push_str("Inv == P139\n");
    let error = abstract_source(&chain, CFG).unwrap_err();
    assert!(error.message.contains("budget exceeded"), "{error:?}");
}

#[test]
fn instance_substitutions_are_analyzed_after_resolution() {
    let dir = tlx_testkit::TempDir::new("abstraction-instance");
    let root = dir.write_modules(&[
        ("Counter", "---- MODULE Counter ----\nEXTENDS Naturals\nVARIABLE c\nI == INSTANCE Inner WITH x <- c, K <- 3\nInit == I!Init\nNext == I!Next\nInv == I!Inv\n====\n"),
        ("Inner", "---- MODULE Inner ----\nEXTENDS Naturals\nCONSTANT K\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\nInv == x < K\n====\n"),
    ]);
    let mut program = Program::load(&root, &[]).unwrap();
    let a = abstract_model(&mut program, &parse_cfg(CFG).unwrap()).unwrap();
    assert!(a.report.contains("domain 0..3"), "{}", a.report);
}

#[test]
fn cleanup_removes_irrelevant_thresholds_before_saturation() {
    let a = abstract_source(
        "VARIABLE c\nInit == c = 0\nNext == (FALSE /\\ c > 2147483647 /\\ c' = c + 1) \\/ (c < 2 /\\ c' = c + 1) \\/ (c >= 2 /\\ c' = 0)\nInv == c <= 2",
        CFG,
    ).unwrap();
    assert!(!a.module.contains("2147483647"));
    assert!(a.report.contains("domain 0..3"));
    assert!(a.report.contains("dead-action-elimination/v1"));
    assert_eq!(a.module.matches(" ==\n    /\\").count(), 3); // Init and two live actions.
    let a = abstract_source("VARIABLE c\nInit == c = 0\nNext == c' = c + 1\nInv == TRUE \\/ c = 2147483647", CFG).unwrap();
    assert!(a.report.contains("domain 0..0"));
    assert!(a.module.contains("Invariant0 == TRUE"));
}

#[test]
fn constant_propagation_composes_with_counter_saturation() {
    let a = abstract_source(
        "VARIABLES fixed, c\nInit == fixed = 7 /\\ c = 0\nNext == UNCHANGED fixed /\\ c' = c + 1\nInv == fixed = 7 /\\ (c < 3 \\/ c >= 3)",
        CFG,
    )
    .unwrap();
    assert!(a.report.contains("constant 7; alpha(n) = n"));
    assert!(a.report.contains("domain 0..3"));
    assert!(a.module.contains("Invariant0 == ((v1 < 3) \\/ (v1 >= 3))"), "{}", a.module);
}

#[test]
fn no_enabled_actions_retains_initial_property_checks() {
    for inv in ["c = 5", "c /= 5"] {
        let a = abstract_source(&format!("VARIABLE c\nInit == c = 5\nNext == c < 0 /\\ c' = c + 1\nInv == {inv}"), CFG).unwrap();
        assert!(a.module.contains("Next == (v0 /= v0) /\\ UNCHANGED <<v0>>"));
        assert!(a.report.contains("constant 5"));
        assert!(a.module.contains(if inv == "c = 5" { "Invariant0 == TRUE" } else { "Invariant0 == (v0 /= v0)" }));
    }
}

#[test]
fn cleanup_does_not_make_unsupported_dead_code_acceptable() {
    let body = "VARIABLE c\nInit == c = 0\nNext == (FALSE /\\ c' = c - 1) \\/ c' = c + 1\nInv == TRUE";
    assert!(abstract_source(body, CFG).is_err());
}
