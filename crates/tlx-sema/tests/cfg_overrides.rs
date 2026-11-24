//! Regression tests for canonical `.cfg` binding, override, arity, and
//! `sym_totality` / `ordered` resolution.

use tlx_front::cfg::parse_cfg;
use tlx_sema::{
    hir::{Expr, ExprKind, OpRef, RootSymbol},
    optimize::{ordered_projection, symmetry_certificate},
    CfgNameError, CfgSubstError, Program,
};

fn load_spec(files: &[(&str, &str)], root: &str) -> Program {
    let dir = tlx_testkit::TempDir::new("sema-cfg-overrides");
    let mut root_path = None;
    for (name, src) in files {
        let p = dir.write(name, src);
        if *name == root {
            root_path = Some(p);
        }
    }
    let mut prog = Program::load(&root_path.expect("root file"), &[]).unwrap();
    prog.resolve_all_root();
    prog
}

fn root_call(prog: &mut Program, name: &str) -> Expr {
    let Some(RootSymbol::Def(id)) = prog.lookup_root(name) else {
        panic!("missing root def {name}");
    };
    Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, prog.defs[id.idx()].span)
}

#[test]
fn sym_totality_rejects_anonymous_instance_overrides() {
    let helper = r#"---- MODULE Helper ----
Flag == TRUE
====
"#;
    let main = r#"---- MODULE AnonInstOvr ----
CONSTANT Proc
VARIABLE owner
INSTANCE Helper
BadFlag == FALSE
Init == owner \in Proc
Next == owner' \in Proc /\ Flag
Inv == owner \in Proc
====
"#;
    let mut prog = load_spec(&[("Helper.tla", helper), ("AnonInstOvr.tla", main)], "AnonInstOvr.tla");
    let init = root_call(&mut prog, "Init");
    let next = root_call(&mut prog, "Next");
    let inv = root_call(&mut prog, "Inv");

    // Baseline without overrides certifies.
    let cfg_plain = parse_cfg("CONSTANT Proc = {p1, p2}\nINIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap();
    assert!(
        symmetry_certificate(&prog, &cfg_plain, &init, &next, std::slice::from_ref(&inv), &[vec!["p1".into(), "p2".into()]]).is_some(),
        "baseline without override should certify"
    );

    // Value override of an operator imported via anonymous INSTANCE.
    let cfg_val = parse_cfg("CONSTANT Proc = {p1, p2}\nCONSTANT Flag = FALSE\nINIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap();
    assert!(
        symmetry_certificate(&prog, &cfg_val, &init, &next, std::slice::from_ref(&inv), &[vec!["p1".into(), "p2".into()]]).is_none(),
        "must reject .cfg value override of anonymous INSTANCE operator"
    );

    // Subst override of an operator imported via anonymous INSTANCE.
    let cfg_subst = parse_cfg("CONSTANT Proc = {p1, p2}\nCONSTANT Flag <- BadFlag\nINIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap();
    assert!(
        symmetry_certificate(&prog, &cfg_subst, &init, &next, std::slice::from_ref(&inv), &[vec!["p1".into(), "p2".into()]]).is_none(),
        "must reject .cfg subst override of anonymous INSTANCE operator"
    );
}

#[test]
fn sym_totality_rejects_named_instance_override_but_allows_same_named_root_const() {
    let sub = r#"---- MODULE SubMod ----
Flag == TRUE
Proc == {1}
====
"#;
    let main = r#"---- MODULE NamedInstOvr ----
CONSTANT Proc
VARIABLE owner
M == INSTANCE SubMod
BadFlag == FALSE
Init == owner \in Proc
Next == owner' \in Proc /\ M!Flag
Inv == owner \in Proc
====
"#;
    let mut prog = load_spec(&[("SubMod.tla", sub), ("NamedInstOvr.tla", main)], "NamedInstOvr.tla");
    let init = root_call(&mut prog, "Init");
    let next = root_call(&mut prog, "Next");
    let inv = root_call(&mut prog, "Inv");

    // Overriding `Flag` (defined only inside named INSTANCE `M`) must be rejected.
    let cfg_ovr = parse_cfg("CONSTANT Proc = {p1, p2}\nCONSTANT Flag <- BadFlag\nINIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap();
    assert!(
        symmetry_certificate(&prog, &cfg_ovr, &init, &next, std::slice::from_ref(&inv), &[vec!["p1".into(), "p2".into()]]).is_none(),
        "must reject .cfg subst override of named INSTANCE operator"
    );

    // Binding root `CONSTANT Proc` even though `SubMod` also defines `Proc` is NOT an override.
    let cfg_plain = parse_cfg("CONSTANT Proc = {p1, p2}\nINIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap();
    assert!(
        symmetry_certificate(&prog, &cfg_plain, &init, &next, std::slice::from_ref(&inv), &[vec!["p1".into(), "p2".into()]]).is_some(),
        "root CONSTANT sharing a name with a named-instance def must still certify"
    );
}

#[test]
fn sym_totality_subst_ignores_let_defs_and_survives_cycles() {
    // 1. A `LET` definition named `Hidden` must never be picked as a `Subst` target.
    let let_spec = r#"---- MODULE LetSubstTarget ----
CONSTANT Proc, N
VARIABLE owner
Init == owner \in Proc
Next == LET Hidden == 1 IN owner' \in Proc /\ N = Hidden
Inv == owner \in Proc
====
"#;
    let mut prog = load_spec(&[("LetSubstTarget.tla", let_spec)], "LetSubstTarget.tla");
    let init = root_call(&mut prog, "Init");
    let next = root_call(&mut prog, "Next");
    let inv = root_call(&mut prog, "Inv");
    let cfg = parse_cfg("CONSTANT Proc = {p1, p2}\nCONSTANT N <- Hidden\nINIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap();
    assert!(
        symmetry_certificate(&prog, &cfg, &init, &next, &[inv], &[vec!["p1".into(), "p2".into()]]).is_none(),
        "must not resolve ConstBinding::Subst to a LET definition"
    );

    // 2. Cyclic `CONSTANT C <- Cyc` where `Cyc == C` must not stack overflow.
    let cyc_spec = r#"---- MODULE CycSubst ----
EXTENDS Naturals
CONSTANT Proc, C
VARIABLE f
Cyc == C
Init == f = [p \in Proc |-> 1]
Next == f' = [p \in Proc |-> IF p \in C THEN 1 ELSE 1] /\ 1 \in (1..C)
Inv == \A p \in Proc : f[p] = 1
====
"#;
    let mut prog = load_spec(&[("CycSubst.tla", cyc_spec)], "CycSubst.tla");
    let init = root_call(&mut prog, "Init");
    let next = root_call(&mut prog, "Next");
    let inv = root_call(&mut prog, "Inv");
    let cfg = parse_cfg("CONSTANT Proc = {p1, p2}\nCONSTANT C <- Cyc\nINIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap();
    assert!(
        symmetry_certificate(&prog, &cfg, &init, &next, &[inv], &[vec!["p1".into(), "p2".into()]]).is_none(),
        "cyclic ConstInfo::Subst must terminate cleanly and fail closed"
    );
}

#[test]
fn ordered_lift_frames_uses_last_constant_binding() {
    // If `S` is first `{1}` and later overwritten to `{}`, `\A x \in S : UNCHANGED flag`
    // is vacuously TRUE (does NOT constrain `flag'`), so lifting `UNCHANGED flag` out
    // would be unsound.
    let spec = r#"---- MODULE DupConstEmptyFrame ----
EXTENDS Naturals
CONSTANT S
VARIABLES ver, flag
Init == ver = 1 /\ flag = 0
Next == ver' = ver + 1 /\ \A x \in S : (flag' = flag /\ UNCHANGED flag)
Inv == flag = 0
====
"#;
    let mut prog = load_spec(&[("DupConstEmptyFrame.tla", spec)], "DupConstEmptyFrame.tla");
    let init = root_call(&mut prog, "Init");
    let next = root_call(&mut prog, "Next");
    let inv = root_call(&mut prog, "Inv");
    let cfg = parse_cfg("CONSTANT S = {1}\nCONSTANT S = {}\nINIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap();
    assert!(
        ordered_projection(&prog, &cfg, &init, &next, &[inv]).is_none(),
        "ordered_projection must not lift UNCHANGED out of a vacuously empty last-bound constant set"
    );
}

#[test]
fn check_cfg_substitutions_validates_constant_arity() {
    let spec = r#"---- MODULE ConstArity ----
CONSTANT F(_, _), C, D
VARIABLE x
G(a) == a
H == 1
Init == x = 0
Next == UNCHANGED x
====
"#;
    let mut prog = load_spec(&[("ConstArity.tla", spec)], "ConstArity.tla");

    // 2-ary constant replaced by 1-ary def -> WrongNumberOfArgs.
    let cfg = parse_cfg("CONSTANT F <- G\nCONSTANT C = 1\nCONSTANT D = 1\n").unwrap();
    assert_eq!(prog.check_cfg_substitutions(&cfg), Some(CfgSubstError::WrongNumberOfArgs { lhs: "F".into(), rhs: "G".into() }));

    // 0-ary constant replaced by 1-ary def -> WrongNumberOfArgs.
    let cfg = parse_cfg("CONSTANT C <- G\n").unwrap();
    assert_eq!(prog.check_cfg_substitutions(&cfg), Some(CfgSubstError::WrongNumberOfArgs { lhs: "C".into(), rhs: "G".into() }));

    // 2-ary constant replaced by 0-ary valued constant -> WrongNumberOfArgs.
    let cfg = parse_cfg("CONSTANT D = 1\nCONSTANT F <- D\n").unwrap();
    assert_eq!(prog.check_cfg_substitutions(&cfg), Some(CfgSubstError::WrongNumberOfArgs { lhs: "F".into(), rhs: "D".into() }));

    // 0-ary constant replaced by 0-ary def or 0-ary valued constant -> valid.
    let cfg = parse_cfg("CONSTANT D = 1\nCONSTANT C <- D\n").unwrap();
    assert_eq!(prog.check_cfg_substitutions(&cfg), None);
    let cfg = parse_cfg("CONSTANT C <- H\n").unwrap();
    assert_eq!(prog.check_cfg_substitutions(&cfg), None);
}

#[test]
fn check_cfg_defs_validates_substituted_targets_and_last_value() {
    let spec = r#"---- MODULE CfgDefChecks ----
CONSTANT F(_), C, D, P
VARIABLE x
G(a) == a = 0
Ok == x = 0
Init == x = 0
Next == UNCHANGED x
====
"#;
    let mut prog = load_spec(&[("CfgDefChecks.tla", spec)], "CfgDefChecks.tla");

    // INVARIANT naming a 1-ary constant substituted by a 1-ary def -> RequiresNoArg.
    let cfg = parse_cfg("CONSTANT F <- G\nINIT Init\nNEXT Next\nINVARIANT F\n").unwrap();
    assert_eq!(prog.check_cfg_defs(&cfg), Some(CfgNameError::RequiresNoArg { what: "invariant", name: "F".into() }));

    // INIT naming a constant substituted by a TRUE-valued constant -> IsConstant.
    let cfg = parse_cfg("CONSTANT D = TRUE\nCONSTANT C <- D\nINIT C\nNEXT Next\n").unwrap();
    assert_eq!(prog.check_cfg_defs(&cfg), Some(CfgNameError::IsConstant { what: "initial predicate", name: "C".into() }));

    // INVARIANT naming a constant substituted by a FALSE-valued constant -> IsConstant.
    let cfg = parse_cfg("CONSTANT D = FALSE\nCONSTANT C <- D\nINIT Init\nNEXT Next\nINVARIANT C\n").unwrap();
    assert_eq!(prog.check_cfg_defs(&cfg), Some(CfgNameError::IsConstant { what: "invariant", name: "C".into() }));

    // INVARIANT naming a constant substituted by a TRUE-valued constant -> allowed.
    let cfg = parse_cfg("CONSTANT D = TRUE\nCONSTANT C <- D\nINIT Init\nNEXT Next\nINVARIANT C\n").unwrap();
    assert_eq!(prog.check_cfg_defs(&cfg), None);

    // Duplicate CONSTANT P = TRUE then P = FALSE under INVARIANT P -> IsConstant (last wins).
    let cfg = parse_cfg("CONSTANT P = TRUE\nCONSTANT P = FALSE\nINIT Init\nNEXT Next\nINVARIANT P\n").unwrap();
    assert_eq!(prog.check_cfg_defs(&cfg), Some(CfgNameError::IsConstant { what: "invariant", name: "P".into() }));

    // INVARIANT naming a 0-ary constant substituted by a 0-ary def -> allowed.
    let cfg = parse_cfg("CONSTANT C <- Ok\nINIT Init\nNEXT Next\nINVARIANT C\n").unwrap();
    assert_eq!(prog.check_cfg_defs(&cfg), None);
}
