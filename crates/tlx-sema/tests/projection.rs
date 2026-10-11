use tlx_sema::hir::{Expr, ExprKind, OpRef, RootSymbol};
use tlx_sema::{optimize::unobserved_variables, Program};

fn project(next: &str, observed: &str, helpers: &str) -> Vec<String> {
    let dir = tlx_testkit::TempDir::new("projection-sema");
    let path = dir.write(
        "Projection.tla",
        &format!(
            "---- MODULE Projection ----\nEXTENDS Integers, TLC\nVARIABLES x, tag\nInit == x = 0 /\\ tag = 0\n{helpers}\nNext == {next}\nInv == x >= 0 /\\ ({observed})\n====\n"
        ),
    );
    let mut p = Program::load(&path, &[]).unwrap();
    p.resolve_all_root();
    let roots = ["Init", "Next", "Inv"].map(|name| {
        let Some(RootSymbol::Def(id)) = p.lookup_root(name) else { panic!("missing {name}") };
        Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
    });
    unobserved_variables(&p, &roots[0], &roots[1], &roots[2..]).iter().map(|v| p.vars[v.idx()].name.to_string()).collect()
}

#[test]
fn follows_actions_binders_and_unchanged_aliases() {
    for next in [
        "(x' = 1 /\\ tag' = 1) \\/ (x' = 0 /\\ tag' = 2)",
        "IF x = 0 THEN (x' = 1 /\\ tag' = 1) ELSE UNCHANGED all",
        "\\E n \\in {0, 1}: x' = n /\\ (tag' = 1 \\/ tag' = 2)",
        "LET SetTag == tag' = 1 IN x' = 1 /\\ SetTag",
        "SetX(1) /\\ tag' = 1",
        "CASE x = 0 -> (x' = 1 /\\ tag' = 1) [] OTHER -> UNCHANGED all",
    ] {
        assert_eq!(project(next, "x >= 0", "all == <<x, tag>>\nSetX(n) == x' = n"), ["tag"], "{next}");
    }
}

#[test]
fn retains_every_read_and_potential_implicit_guard() {
    for (next, observed, helpers) in [
        ("tag = 0 /\\ x' = 1 /\\ tag' = 1", "x >= 0", ""),
        ("x' = tag /\\ tag' = 1", "x >= 0", ""),
        ("x' = 1 /\\ tag' = 1", "tag = 0", ""),
        ("x' = 1 /\\ tag' = 1", "Read >= 0", "Read == tag"),
        ("x' = 1 /\\ UNCHANGED tag /\\ tag' = 1", "x >= 0", ""),
        ("x' = 1 /\\ Keep /\\ tag' = 1", "x >= 0", "Keep == UNCHANGED tag"),
        ("x' = 1 /\\ tag' = 1 /\\ tag' = 2", "x >= 0", ""),
        ("tag' = 1 /\\ x' = tag'", "x >= 0", ""),
        ("tag' = 1 /\\ (UNCHANGED tag \\/ x' = 1)", "x >= 0", ""),
        ("tag' = tag + 1 /\\ x' = 1", "x >= 0", ""),
        ("x' = 1 /\\ tag' \\in {0, 1}", "x >= 0", ""),
        ("\\E n \\in {tag}: x' = n /\\ tag' = 1", "x >= 0", ""),
        ("x' = 1 /\\ tag' = 1", "Use(Read)", "Use(F(_)) == F(0) >= 0\nRead(n) == tag"),
        ("x' = 1 /\\ tag' = 1", "F[1] >= 0", "F[n \\in {0, 1}] == IF n = 0 THEN tag ELSE F[n-1]"),
        ("tag' = 2147483648 /\\ x' = 1", "x >= 0", ""),
    ] {
        assert!(project(next, observed, helpers).is_empty(), "{next}; {observed}; {helpers}");
    }
}

#[test]
fn effects_block_reduction_only_when_referenced() {
    for (next, inv, helpers) in [
        ("x' = 1 /\\ tag' = 1 /\\ PrintT(x)", "x >= 0", ""),
        ("x' = 1 /\\ tag' = 1", "TLCGet(0) = 0", ""),
        ("x' = 1 /\\ tag' = 1", "Use(E)", "Use(F(_)) == F(x)\nE(n) == PrintT(n)"),
    ] {
        assert!(project(next, inv, helpers).is_empty());
    }
    assert_eq!(project("x' = 1 /\\ tag' = 1", "x >= 0", "Unused == PrintT(tag)"), ["tag"]);
}

#[test]
fn incomplete_action_analysis_does_not_authorize_projection() {
    assert!(project("Step", "x >= 0", "RECURSIVE Step\nStep == Step \\/ (x' = 1 /\\ tag' = 1)").is_empty());
    let mut helpers = "Step140 == x' = 1 /\\ tag' = 1\n".to_string();
    helpers.extend((0..140).rev().map(|i| format!("Step{i} == Step{}\n", i + 1)));
    assert!(project("Step0", "x >= 0", &helpers).is_empty());
}

#[test]
fn backward_liveness_handles_copy_cycles_and_transitive_dependencies() {
    assert_eq!(project("x' = 1 /\\ tag' = tag", "x >= 0", ""), ["tag"]);
    assert_eq!(project("x' = 1 /\\ tag' = x", "x >= 0", ""), ["tag"]);
    assert!(project("x' = tag /\\ tag' = x", "x >= 0", "").is_empty());

    let dir = tlx_testkit::TempDir::new("projection-dataflow");
    let path = dir.write(
        "Flow.tla",
        r#"---- MODULE Flow ----
EXTENDS Naturals
VARIABLES x, a, b
Init == x = 0 /\ a = 0 /\ b = 1
Next == x' = 1 /\ a' = b /\ b' = a
Inv == x >= 0
Read == a >= 0
====
"#,
    );
    let mut p = Program::load(&path, &[]).unwrap();
    let roots = ["Init", "Next", "Inv", "Read"].map(|name| {
        let Some(RootSymbol::Def(id)) = p.lookup_root(name) else { panic!("missing {name}") };
        Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
    });
    let names = |vars: Vec<tlx_sema::hir::VarId>| vars.iter().map(|v| &*p.vars[v.idx()].name).collect::<Vec<_>>();
    assert_eq!(names(unobserved_variables(&p, &roots[0], &roots[1], &roots[2..3])), ["a", "b"]);
    assert!(unobserved_variables(&p, &roots[0], &roots[1], &roots[2..]).is_empty());
}
