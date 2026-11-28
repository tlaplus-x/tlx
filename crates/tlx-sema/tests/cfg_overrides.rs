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
fn sym_totality_applies_anonymous_instance_overrides() {
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

    // A value assignment on an operator imported via anonymous INSTANCE is a
    // zero-arity root definition the runtime binds (`bind_value`), so the
    // certified lowering replaces it with the configured literal.
    let cfg_val = parse_cfg("CONSTANT Proc = {p1, p2}\nCONSTANT Flag = FALSE\nINIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap();
    let cert = symmetry_certificate(&prog, &cfg_val, &init, &next, std::slice::from_ref(&inv), &[vec!["p1".into(), "p2".into()]])
        .expect("zero-arity Def = value on an anonymous-INSTANCE operator must certify");
    assert!(cert.contains("def_subst_model_slice"), "value-override obligation missing");

    // A pure substitution of an operator imported via anonymous INSTANCE is
    // what the runtime applies (`bind_cfg` looks it up in root scope), so the
    // certified lowering follows the replacement and records the obligation.
    let cfg_subst = parse_cfg("CONSTANT Proc = {p1, p2}\nCONSTANT Flag <- BadFlag\nINIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap();
    let cert = symmetry_certificate(&prog, &cfg_subst, &init, &next, std::slice::from_ref(&inv), &[vec!["p1".into(), "p2".into()]])
        .expect("pure anonymous-INSTANCE substitution must certify the applied replacement");
    assert!(cert.contains("def_subst_model_slice"), "override obligation missing");
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

fn cert_for(prog: &Program, cfg_src: &str, inv_name: &str) -> Option<String> {
    let cfg = parse_cfg(cfg_src).unwrap();
    let init = root_call_prog(prog, "Init");
    let next = root_call_prog(prog, "Next");
    let inv = root_call_prog(prog, inv_name);
    symmetry_certificate(prog, &cfg, &init, &next, std::slice::from_ref(&inv), &[vec!["p1".into(), "p2".into()]])
}

fn root_call_prog(prog: &Program, name: &str) -> Expr {
    let Some(RootSymbol::Def(id)) = prog.lookup_resolved_root(name) else {
        panic!("missing root def {name}");
    };
    Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, prog.defs[id.idx()].span)
}

#[test]
fn certifies_pure_operator_and_parameterized_constant_overrides() {
    let tla = r#"---- MODULE OverrideCert ----
EXTENDS Naturals
CONSTANTS Proc, F(_, _)
Same(a, b) == a = b
VARIABLE owner
Init == owner \in Proc
Next == \E p \in Proc : F(owner, p) /\ owner' = p
Inv == owner \in Proc
====
"#;
    let prog = load_spec(&[("OverrideCert.tla", tla)], "OverrideCert.tla");
    // `F(owner, p)` replaced by a pure definition: the lowering must follow the
    // configured body and record the higher-arity obligation.
    let cert = cert_for(&prog, "CONSTANT Proc = {p1, p2}\nCONSTANT F <- Same\nINIT Init\nNEXT Next\nINVARIANT Inv\n", "Inv")
        .expect("parameterized constant substitution must certify");
    assert!(cert.contains("def_subst_model_slice"), "{cert}");
    assert!(cert.contains("defSubstApplied"), "{cert}");
    assert!(cert.contains("certificate_with_overrides"), "{cert}");

    // A definition override on a root operator certifies the replacement body.
    let prog = load_spec(&[("OverrideCert.tla", tla)], "OverrideCert.tla");
    let cert = cert_for(&prog, "CONSTANT Proc = {p1, p2}\nCONSTANT Same <- F\nINIT Init\nNEXT Next\nINVARIANT Inv\n", "Inv");
    // `Same <- F` has matching arity; `F` itself is a parameterized constant,
    // so this binding names no root definition and stays unbound/refused.
    assert!(cert.is_none(), "binding a parameterized-constant name as a definition must be refused");
}

#[test]
fn operator_override_chain_resolves_to_terminal_replacement() {
    let tla = r#"---- MODULE OverrideChain ----
EXTENDS Naturals
CONSTANT Proc
A == FALSE
B == TRUE
C == TRUE
VARIABLE owner
Init == owner \in Proc
Next == owner' \in Proc /\ A
Inv == owner \in Proc
====
"#;
    let prog = load_spec(&[("OverrideChain.tla", tla)], "OverrideChain.tla");
    // A -> B -> C; the lowering must use C, not A's or B's body. `A = 3` still
    // holds because `A` is replaced by `C == 3`; a wrong chain would make it false
    // but certification here only checks the connected obligation.
    assert!(
        cert_for(&prog, "CONSTANT Proc = {p1, p2}\nINIT Init\nNEXT Next\nINVARIANT Inv\n", "Inv").is_some(),
        "baseline without override must certify"
    );
    let cfg = parse_cfg("CONSTANT Proc = {p1, p2}\nCONSTANT A <- C\nINIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap();
    assert!(tlx_sema::optimize::cfg_constants_supported(&prog, &cfg), "cfg gate must accept the pure override");
    let cert = cert_for(&prog, "CONSTANT Proc = {p1, p2}\nCONSTANT A <- C\nINIT Init\nNEXT Next\nINVARIANT Inv\n", "Inv")
        .expect("terminal replacement must certify");
    assert!(cert.contains("def_subst_model_slice"), "{cert}");
}

#[test]
fn refuses_recursive_override_target() {
    let tla = r#"---- MODULE RecursiveOverrideTarget ----
EXTENDS Naturals
VARIABLE x, y
Orig(n) == TRUE
RECURSIVE RecY(_)
RecY(n) == IF n = 0 THEN y < 5 ELSE RecY(n - 1)
Init == x = 0 /\ y = 0
Next == x' = x /\ y' = IF y < 5 THEN y + 1 ELSE 5
Inv == Orig(0) /\ x >= 0
====
"#;
    let prog = load_spec(&[("RecursiveOverrideTarget.tla", tla)], "RecursiveOverrideTarget.tla");
    let cfg = parse_cfg("INIT Init\nNEXT Next\nCONSTANT Orig <- RecY\nINVARIANT Inv\n").unwrap();
    assert!(
        !tlx_sema::optimize::cfg_constants_supported(&prog, &cfg),
        "a recursive replacement target must be outside the certified subset"
    );
}

fn certify(name: &str, tla: &str, cfg: &str, groups: &[Vec<String>]) -> Option<String> {
    let dir = tlx_testkit::TempDir::new("cfg-value-override");
    let path = dir.write(&format!("{name}.tla"), tla);
    let mut p = Program::load(&path, &[]).unwrap();
    p.resolve_all_root();
    let roots = ["Init", "Next", "Inv"].map(|root| {
        let Some(RootSymbol::Def(id)) = p.lookup_root(root) else { panic!("missing {root}") };
        Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
    });
    symmetry_certificate(&p, &parse_cfg(cfg).unwrap(), &roots[0], &roots[1], &roots[2..], groups)
}

const VALUE_OVERRIDE_TLA: &str = include_str!("../../../proofs/symmetry/CfgValueOverride.tla");
const VALUE_OVERRIDE_CFG: &str = include_str!("../../../proofs/symmetry/CfgValueOverride.cfg");
const FIXED_ATOM_TLA: &str = include_str!("../../../proofs/symmetry/FixedAtomSubsets.tla");
const FIXED_ATOM_CFG: &str = include_str!("../../../proofs/symmetry/FixedAtomSubsets.cfg");

#[test]
fn cfg_value_override_on_zero_arity_definitions_certifies() {
    let cert = certify("CfgValueOverride", VALUE_OVERRIDE_TLA, VALUE_OVERRIDE_CFG, &[vec!["p1".into(), "p2".into(), "p3".into()]])
        .expect("Def = value overrides must certify");
    // One obligation row per applied definition, declared == applied.
    assert!(cert.contains("def defSubstDeclared"), "missing override obligation");
    assert!(cert.contains("theorem certificate_with_overrides"), "override certificate missing");
    for lit in ["Lit(Model(\\\"NoVal\\\"))", "Lit(Set([Int(0),Int(1)]))", "Lit(Str(\\\"idle\\\"))"] {
        assert!(cert.contains(lit), "missing recorded literal {lit}");
    }
    // Declared, applied-canonical, applied and the model occurrence all carry it.
    assert!(cert.matches("Lit(Model(\\\"NoVal\\\"))").count() >= 3, "declared/applied/recorded rows");
}

#[test]
fn cfg_value_override_rejects_builtin_definition_assignments() {
    // Uses of standard-module builtin definitions are `ExprKind::Builtin`, not
    // `Apply{Def}`; the certified lowering cannot splice the configured literal
    // in, so these bindings must fail closed instead of certifying the
    // un-overridden builtin (the runtime does apply them).
    let nat = r#"---- MODULE BuiltinNat ----
EXTENDS Naturals
CONSTANT Proc
VARIABLE x
Init == x = 1
Next == x' = x
Inv == x \in Nat
====
"#;
    let groups = [vec!["p1".to_string(), "p2".to_string()]];
    let cfg = "CONSTANTS\n  Proc = {p1, p2}\n  Nat = {p1}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    assert!(certify("BuiltinNat", nat, cfg, &groups).is_none(), "`Nat = {{p1}}` must not certify");
    let cfg = "CONSTANTS\n  Proc = {p1, p2}\n  Nat = {\"a\"}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    assert!(certify("BuiltinNat", nat, cfg, &groups).is_none(), "`Nat = {{\"a\"}}` must not certify");

    let bags = r#"---- MODULE BuiltinBag ----
EXTENDS Bags
CONSTANT Proc
VARIABLE x
Init == x = EmptyBag
Next == x' = x
Inv == x # EmptyBag
====
"#;
    let cfg = "CONSTANTS\n  Proc = {p1, p2}\n  EmptyBag = p1\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    assert!(certify("BuiltinBag", bags, cfg, &groups).is_none(), "`EmptyBag = p1` must not certify");
}

#[test]
fn cfg_value_override_keeps_builtin_constant_assignments() {
    // A value binding on a builtin *constant* is a plain cfg value (no
    // definition override) and stays supported.
    let nat = r#"---- MODULE BuiltinNatConst ----
EXTENDS Naturals
CONSTANT Proc, Limit
VARIABLES x, y
Init == /\ x = 0
        /\ y = 0
Next == /\ \E p \in Proc : y' = 1
        /\ x' = x
Inv == x \in Limit
====
"#;
    let groups = [vec!["p1".to_string(), "p2".to_string()]];
    let cfg = "CONSTANTS\n  Proc = {p1, p2}\n  Limit = {0, 1}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    assert!(certify("BuiltinNatConst", nat, cfg, &groups).is_some(), "`CONSTANT Limit = {{0, 1}}` must still certify");
}

#[test]
fn cfg_value_override_rejects_arity_and_ambiguous_bindings() {
    let tla = r#"---- MODULE Ambiguous ----
CONSTANT Proc
VARIABLES owner
Op(v) == v
NoVal == CHOOSE v : v \notin Proc
Init == owner = NoVal
Next == \E p \in Proc : owner' = p
Inv == owner \in Proc \cup {NoVal}
====
"#;
    let groups = [vec!["p1".to_string(), "p2".to_string()]];
    let base = "CONSTANTS\n  Proc = {p1, p2}\n";
    // Baseline: the zero-arity definition bound to a model value certifies.
    let ok = certify("Ambiguous", tla, &format!("{base}  NoVal = NoVal\nINIT Init\nNEXT Next\nINVARIANT Inv\n"), &groups);
    assert!(ok.is_some(), "zero-arity Def = value must certify");
    // An operator with parameters cannot be replaced by a value here.
    assert!(
        certify("Ambiguous", tla, &format!("{base}  Op = NoVal\nINIT Init\nNEXT Next\nINVARIANT Inv\n"), &groups).is_none(),
        "arity-changing Def = value must be refused"
    );
    // Both `=` and `<-` bind the same definition: `bind_cfg` keeps the two
    // maps apart, so the certified path refuses instead of guessing.
    assert!(
        certify("Ambiguous", tla, &format!("{base}  NoVal = NoVal\n  NoVal <- Init\nINIT Init\nNEXT Next\nINVARIANT Inv\n"), &groups)
            .is_none(),
        "a definition bound by both `=` and `<-` must be refused"
    );
    // Module-scoped value bindings stay outside the certified subset.
    assert!(
        certify("Ambiguous", tla, &format!("{base}  NoVal = [Ambiguous] NoVal\nINIT Init\nNEXT Next\nINVARIANT Inv\n"), &groups).is_none(),
        "module-scoped Def = value must be refused"
    );
}

#[test]
fn filtered_tagged_record_union_narrows_its_element_shape() {
    // `msgs` is a union of two record variants; only the "crit" variant carries
    // `val`. A field read of a member of `{mm \in msgs : mm.type = "crit"}`
    // must use the filtered variant, or `val` infers `Top` and the totality
    // check refuses the certificate.
    let tla = r#"---- MODULE TaggedMsgFilter ----
EXTENDS Naturals, FiniteSets
CONSTANT Proc
VARIABLES msgs, sent
Round == Nat
Init == /\ msgs = {}
        /\ sent = [p \in Proc |-> {}]
Log(p) == /\ msgs' = msgs \cup {[type |-> "crit", val |-> p, bal |-> 0]}
          /\ UNCHANGED sent
Note(p) == /\ msgs' = msgs \cup {[type |-> "note", bal |-> 0]}
           /\ UNCHANGED sent
Copy(p) == /\ \E m \in {mm \in msgs : mm.type = "crit"} :
                 sent' = [sent EXCEPT ![p] = sent[p] \cup {[val |-> m.val, bal |-> 0]}]
           /\ UNCHANGED msgs
Shuffle(p) == /\ \E S \in SUBSET {r \in sent[p] : r.bal \in Round} :
                   sent' = [sent EXCEPT ![p] = S]
              /\ UNCHANGED msgs
Next == \E p \in Proc : Log(p) \/ Note(p) \/ Copy(p) \/ Shuffle(p)
Inv == /\ \A p \in Proc : \A r \in sent[p] : r.val \in Proc
       /\ \A m \in msgs : m.type \in {"crit", "note"}
====
"#;
    let cfg = "CONSTANTS\n  Proc = {p1, p2, p3}\n  Round = {0, 1, 2}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    let cert = certify("TaggedMsgFilter", tla, cfg, &[vec!["p1".into(), "p2".into(), "p3".into()]])
        .expect("a filtered tagged-record union must narrow its element shape");
    assert!(cert.contains("namespace TlxOptimization.GeneratedEquivSymmetry"), "unexpected certificate");
    assert!(!cert.contains("sorry"), "certificate must be complete");
}

#[test]
fn fixed_atom_stratified_k_subsets_certify() {
    let groups = [vec!["v1".to_string(), "v2".to_string()], vec!["a1".to_string(), "a2".to_string(), "a3".to_string()]];
    let cert = certify("FixedAtomSubsets", FIXED_ATOM_TLA, FIXED_ATOM_CFG, &groups).expect("stratified k-subsets must certify");
    // The `{fa1}` strata union `fa1` into every k-subset of the acceptor group;
    // the empty stratum keeps the plain filter.
    assert!(cert.contains("Expr.setMap"), "missing stratified setMap lowering");
    assert!(cert.contains("(Expr.cup (Expr.localVar 0) (Expr.setEnum [(Expr.atom"), "fixed atoms must be united into each moved subset");
    assert!(cert.contains("Expr.powerset (Expr.groupSet"), "missing powerset filter");
    assert_eq!(cert.matches("Expr.setMap").count(), 2, "one setMap per fixed-atom stratum");
}

#[test]
fn stratified_k_subsets_reject_broken_strata() {
    let groups = [vec!["v1".to_string(), "v2".to_string()], vec!["a1".to_string(), "a2".to_string(), "a3".to_string()]];
    let replace = |from: &str, to: &str| FIXED_ATOM_CFG.replace(from, to);
    let certify_with = |cfg: &str| {
        let dir = tlx_testkit::TempDir::new("cfg-k-subset-neg");
        let path = dir.write("FixedAtomSubsets.tla", FIXED_ATOM_TLA);
        let mut p = Program::load(&path, &[]).unwrap();
        p.resolve_all_root();
        let roots = ["Init", "Next", "Inv"].map(|root| {
            let Some(RootSymbol::Def(id)) = p.lookup_root(root) else { panic!("missing {root}") };
            Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
        });
        symmetry_certificate(&p, &parse_cfg(cfg).unwrap(), &roots[0], &roots[1], &roots[2..], &groups)
    };
    // Baseline.
    assert!(certify_with(FIXED_ATOM_CFG).is_some(), "baseline must certify");
    // Omitting `{a2, a3, fa1}` leaves the `{fa1}` stratum short of the exact
    // 2-subsets of `Acceptor`, so the family cannot be lowered as a filter.
    let missing = replace("{a2, a3, fa1}, ", "");
    assert_ne!(missing, FIXED_ATOM_CFG);
    assert!(certify_with(&missing).is_none(), "an incomplete fixed-atom stratum must be refused");
    // Mixing two groups inside one inner set is not one stratum's k-subset family.
    let mixed = replace("{a1, a2, a3}", "{a1, v1, v2}");
    assert_ne!(mixed, FIXED_ATOM_CFG);
    assert!(certify_with(&mixed).is_none(), "a mixed-group inner set must be refused");
    // A stratum that is not the exact k-subsets of its group (here only one of
    // the three 2-subsets in the empty stratum) must be refused.
    let short = replace("{a1, a2}, {a1, a3}, {a2, a3}", "{a1, a2}, {a1, a3}");
    assert_ne!(short, FIXED_ATOM_CFG);
    assert!(certify_with(&short).is_none(), "an incomplete empty stratum must be refused");
}
