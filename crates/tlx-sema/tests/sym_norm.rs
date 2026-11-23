use tlx_front::cfg::parse_cfg;
use tlx_sema::{
    hir::{BoundVars, ExceptKey, Expr, ExprKind, OpRef, RootSymbol, VarId},
    optimize::{infer_var_domains, proves_var_membership, symmetry_certificate, SymNormalizer},
    visit, Program,
};

fn load_module(name: &str, spec: &str) -> (tlx_testkit::TempDir, Program) {
    let dir = tlx_testkit::TempDir::new("sym-norm");
    let path = dir.write(&format!("{name}.tla"), spec);
    let mut p = Program::load(&path, &[]).unwrap();
    p.resolve_all_root();
    (dir, p)
}

fn root_call(p: &mut Program, name: &str) -> Expr {
    let Some(RootSymbol::Def(id)) = p.lookup_root(name) else { panic!("missing def {name}") };
    Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
}

fn var_id(p: &mut Program, name: &str) -> VarId {
    let Some(RootSymbol::Var(id)) = p.lookup_root(name) else { panic!("missing var {name}") };
    id
}

fn any_node(e: &Expr, pred: &mut impl FnMut(&Expr) -> bool) -> bool {
    if pred(e) {
        return true;
    }
    let mut found = false;
    visit::children(e, &mut |c| found |= any_node(c, pred));
    found
}

#[test]
fn expands_let_case_other_and_instance_operators() {
    let dir = tlx_testkit::TempDir::new("sym-norm-inst");
    dir.write(
        "Sub.tla",
        r#"---- MODULE Sub ----
EXTENDS Naturals
VARIABLE v
Bump(x) == CASE x = 0 -> 1 [] x = 1 -> 2 [] OTHER -> 0
Step == LET next == Bump(v) IN v' = next
====
"#,
    );
    let main = r#"---- MODULE Main ----
EXTENDS Naturals
CONSTANT Proc
VARIABLE pc
Init == pc = [p \in Proc |-> 0]
I(p) == INSTANCE Sub WITH v <- pc[p]
Step(p) == LET next == I(p)!Bump(pc[p]) IN pc' = [pc EXCEPT ![p] = next]
Next == \E p \in Proc : Step(p)
Inv == \A p \in Proc : pc[p] \in {0, 1, 2}
====
"#;
    let path = dir.write("Main.tla", main);
    let mut p = Program::load(&path, &[]).unwrap();
    p.resolve_all_root();
    let cfg = parse_cfg("CONSTANT Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap();

    let next_raw = root_call(&mut p, "Next");
    let init_raw = root_call(&mut p, "Init");
    let inv_raw = root_call(&mut p, "Inv");
    let next_norm = SymNormalizer::new(&p).normalize(&next_raw).expect("normalize Next");
    assert!(!any_node(&next_norm, &mut |e| matches!(&*e.kind, ExprKind::Let { .. } | ExprKind::Case { .. })));
    assert!(any_node(&next_norm, &mut |e| matches!(&*e.kind, ExprKind::If { .. })));

    let domains = infer_var_domains(&p, &cfg, &init_raw, &next_raw).unwrap();
    assert_eq!(domains[0].1, "Function({@p1, @p2, @p3} -> Atoms({0, 1, 2}))");

    let cert = symmetry_certificate(&p, &cfg, &init_raw, &next_raw, &[inv_raw], &[vec!["p1".into(), "p2".into(), "p3".into()]]);
    assert!(cert.is_some(), "CASE...OTHER + LET + INSTANCE should certify via KeyedCertificate");
}

#[test]
fn case_without_other_preserves_missing_arm_error_node() {
    let spec = r#"---- MODULE CaseNoOther ----
VARIABLE x
Init == x = 0
Next == x' = CASE x = 0 -> 1 [] x = 1 -> 0
====
"#;
    let (_dir, mut p) = load_module("CaseNoOther", spec);
    let next_raw = root_call(&mut p, "Next");
    let norm = SymNormalizer::new(&p).normalize(&next_raw).unwrap();
    assert!(
        any_node(&norm, &mut |e| matches!(&*e.kind, ExprKind::Case { other: None, .. })),
        "CASE without OTHER must not be rewritten into IF (would drop no-arm-matched error)"
    );
}

#[test]
fn higher_order_lambda_and_op_arg_beta_reduce_and_certify() {
    let spec = r#"---- MODULE HigherOrder ----
EXTENDS Naturals
CONSTANT Proc
VARIABLE flag
Apply(F(_), v) == F(v)
Neg(b) == ~b
Init == flag = [p \in Proc |-> FALSE]
FlipLambda(p) == flag' = [flag EXCEPT ![p] = Apply(LAMBDA b : ~b, @)]
FlipOpArg(p) == flag' = [flag EXCEPT ![p] = Apply(Neg, @)]
Next == \E p \in Proc : FlipLambda(p) \/ FlipOpArg(p)
Inv == \A p \in Proc : flag[p] \in BOOLEAN
====
"#;
    let (_dir, mut p) = load_module("HigherOrder", spec);
    let cfg = parse_cfg("CONSTANT Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap();
    let init_raw = root_call(&mut p, "Init");
    let next_raw = root_call(&mut p, "Next");
    let inv_raw = root_call(&mut p, "Inv");

    let next_norm = SymNormalizer::new(&p).normalize(&next_raw).unwrap();
    assert!(!any_node(&next_norm, &mut |e| matches!(&*e.kind, ExprKind::Lambda { .. } | ExprKind::OpArg(_))));

    let domains = infer_var_domains(&p, &cfg, &init_raw, &next_raw).unwrap();
    assert_eq!(domains[0].1, "Function({@p1, @p2, @p3} -> Atoms({FALSE, TRUE}))");

    let cert = symmetry_certificate(&p, &cfg, &init_raw, &next_raw, &[inv_raw], &[vec!["p1".into(), "p2".into(), "p3".into()]]);
    assert!(cert.is_some(), "higher-order LAMBDA/OpArg + boolean negation should certify");
}

#[test]
fn cigarette_smokers_choose_one_lambda_normalizes_cleanly() {
    let spec = r#"---- MODULE SmokersNorm ----
CONSTANT Ingredients, Offers
VARIABLE smokers, dealer
ChooseOne(S, P(_)) == CHOOSE x \in S : P(x) /\ \A y \in S : P(y) => y = x
Init == /\ smokers = [r \in Ingredients |-> [smoking |-> FALSE]]
        /\ dealer \in Offers
Start == /\ dealer /= {}
         /\ smokers' = [r \in Ingredients |-> [smoking |-> {r} \cup dealer = Ingredients]]
         /\ dealer' = {}
Stop == /\ dealer = {}
        /\ LET r == ChooseOne(Ingredients, LAMBDA x : smokers[x].smoking)
           IN smokers' = [smokers EXCEPT ![r].smoking = FALSE]
        /\ dealer' \in Offers
Next == Start \/ Stop
====
"#;
    let (_dir, mut p) = load_module("SmokersNorm", spec);
    let cfg = parse_cfg("CONSTANTS Ingredients = {i1, i2, i3} Offers = {{i1, i2}, {i1, i3}, {i2, i3}}\nINIT Init\nNEXT Next\n").unwrap();
    let init_raw = root_call(&mut p, "Init");
    let next_raw = root_call(&mut p, "Next");
    let norm = SymNormalizer::new(&p).normalize(&next_raw).expect("ChooseOne with LAMBDA normalizes");
    assert!(!any_node(&norm, &mut |e| matches!(&*e.kind, ExprKind::Lambda { .. } | ExprKind::Let { .. })));
    let domains = infer_var_domains(&p, &cfg, &init_raw, &next_raw).unwrap();
    assert_eq!(domains[0].1, "Function({@i1, @i2, @i3} -> Record(smoking: Atoms({FALSE, TRUE})))");
    assert_eq!(domains[1].1, "Set(Atoms({@i1, @i2, @i3}))");
}

#[test]
fn tuple_destructuring_desugars_only_when_arity_is_provable() {
    let spec = r#"---- MODULE TupleDestruct ----
EXTENDS Naturals
CONSTANT Proc
VARIABLE pc, mixed
Init == /\ pc = [p \in Proc |-> 0]
        /\ mixed = {<<1, 2, 3>>}
StepTimes == \E <<p, v>> \in Proc \X {0, 1} : pc' = [pc EXCEPT ![p] = v] /\ UNCHANGED mixed
FilterTimes == {<<p, v>> \in Proc \X {0, 1} : v = 1}
UnsafeTuple == \E <<a, b>> \in mixed : a = b /\ UNCHANGED <<pc, mixed>>
Next == StepTimes
Inv == \A <<p, q>> \in Proc \X Proc : pc[p] \in {0, 1} /\ pc[q] \in {0, 1}
====
"#;
    let (_dir, mut p) = load_module("TupleDestruct", spec);
    let cfg = parse_cfg("CONSTANT Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap();
    let step_raw = root_call(&mut p, "StepTimes");
    let filt_raw = root_call(&mut p, "FilterTimes");
    let unsafe_raw = root_call(&mut p, "UnsafeTuple");
    let init_raw = root_call(&mut p, "Init");
    let next_raw = root_call(&mut p, "Next");
    let inv_raw = root_call(&mut p, "Inv");

    // Provably exact-arity `Proc \X {0, 1}` splits cleanly into `Many` bounds.
    let step_norm = SymNormalizer::new(&p).normalize(&step_raw).unwrap();
    assert!(!any_node(&step_norm, &mut |e| matches!(
        &*e.kind,
        ExprKind::Quant { bounds, .. } if bounds.iter().any(|b| matches!(b.vars, BoundVars::Tuple(_)))
    )));

    // SetFilter over `Proc \X {0, 1}` desugars to a single tuple variable + `[1]`/`[2]`.
    let filt_norm = SymNormalizer::new(&p).normalize(&filt_raw).unwrap();
    assert!(!any_node(&filt_norm, &mut |e| matches!(
        &*e.kind,
        ExprKind::SetFilter { bound, .. } if matches!(bound.vars, BoundVars::Tuple(_))
    )));

    // Unsafe tuple destructuring over a non-tuple / variable set MUST preserve BoundVars::Tuple!
    let unsafe_norm = SymNormalizer::new(&p).normalize(&unsafe_raw).unwrap();
    assert!(any_node(&unsafe_norm, &mut |e| matches!(
        &*e.kind,
        ExprKind::Quant { bounds, .. } if bounds.iter().any(|b| matches!(b.vars, BoundVars::Tuple(_)))
    )));

    // And StepTimes + Inv certifies via KeyedCertificate!
    let cert = symmetry_certificate(&p, &cfg, &init_raw, &next_raw, &[inv_raw], &[vec!["p1".into(), "p2".into(), "p3".into()]]);
    assert!(cert.is_some(), "tuple destructuring over Proc \\X {{0, 1}} should certify");
}

#[test]
fn multi_arg_except_nested_flattening_and_aliasing_refusal() {
    let spec = r#"---- MODULE ExceptNorm ----
EXTENDS Naturals
CONSTANT P
VARIABLE m, g, aux
Init == /\ m = [p \in P |-> [x |-> 0, f |-> [q \in P |-> 0]]]
        /\ g = [p \in P, q \in P |-> 0]
        /\ aux = [p \in P |-> 0]
Nested == \E i, j \in P :
            /\ m' = [m EXCEPT ![i] = [@ EXCEPT !.f = [@ EXCEPT ![j] = 1]]]
            /\ g' = [g EXCEPT ![i, j] = g[i, j] + 1]
            /\ aux' = [aux EXCEPT ![i] = 1, ![j] = [aux EXCEPT ![i] = @ + 1][i]]
Aliasing == \E i, j \in P : aux' = [aux EXCEPT ![i] = 1, ![j] = @ + 1] /\ UNCHANGED <<m, g>>
FallibleInner == \E i \in P : m' = [m EXCEPT ![i] = [@ EXCEPT ![1 \div 0] = 2]] /\ UNCHANGED <<g, aux>>
====
"#;
    let (_dir, mut p) = load_module("ExceptNorm", spec);
    let nested_raw = root_call(&mut p, "Nested");
    let alias_raw = root_call(&mut p, "Aliasing");
    let fallible_raw = root_call(&mut p, "FallibleInner");

    let nested = SymNormalizer::new(&p).normalize(&nested_raw).expect("nested + multi-arg EXCEPT");
    // Multi-arg FnApp & ExceptKey::Index must be canonicalized to 1-arg Tuple.
    assert!(!any_node(&nested, &mut |e| match &*e.kind {
        ExprKind::FnApp { args, .. } => args.len() > 1,
        ExprKind::Except { updates, .. } =>
            updates.iter().any(|(path, _)| path.iter().any(|k| matches!(k, ExceptKey::Index(args) if args.len() > 1))),
        _ => false,
    }));
    // Nested infallible `[@ EXCEPT !.f = [@ EXCEPT ![j] = 1]]` flattens to path len 3 (`![i].f[j]`).
    assert!(any_node(&nested, &mut |e| matches!(
        &*e.kind,
        ExprKind::Except { updates, .. } if updates.iter().any(|(path, _)| path.len() == 3)
    )));

    // Potentially aliasing sequential `@` MUST still refuse!
    assert!(SymNormalizer::new(&p).normalize(&alias_raw).is_none());

    // Inner EXCEPT with a fallible index expression MUST NOT be flattened into the outer path!
    let fallible = SymNormalizer::new(&p).normalize(&fallible_raw).unwrap();
    assert!(!any_node(&fallible, &mut |e| matches!(
        &*e.kind,
        ExprKind::Except { updates, .. } if updates.iter().any(|(path, _)| path.len() >= 2)
    )));
}

#[test]
fn domain_inference_handles_sets_sequences_domain_and_const_substs() {
    let spec = r#"---- MODULE DomainRich ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS Proc, Zero
ProcDef == Proc
VARIABLES pc, sset, flat, seqv, doms, cardv, mapv, pair_el, flag
Init == /\ pc = [p \in ProcDef |-> 0]
        /\ sset \in SUBSET ProcDef
        /\ flat = UNION {{p} : p \in ProcDef}
        /\ seqv = <<0, 1>>
        /\ doms = DOMAIN pc
        /\ cardv = Cardinality(sset)
        /\ mapv = ("a" :> 1) @@ ("b" :> 2)
        /\ pair_el = 0
        /\ flag = FALSE
Next == /\ \E p \in DOMAIN pc : pc' = [pc EXCEPT ![p] = @ + 1]
        /\ sset' \in (SUBSET ProcDef) \ {{}}
        /\ flat' = UNION {sset, {p \in ProcDef : pc[p] > 0}}
        /\ seqv' = Tail(Append(seqv, Head(seqv))) \o SubSeq(seqv, 1, 1)
        /\ doms' = DOMAIN pc \cap ProcDef
        /\ cardv' = Cardinality(flat) + (cardv % 3)
        /\ mapv' = [mapv EXCEPT !["a"] = 3]
        /\ \E <<a, b>> \in ProcDef \X (1..3) : pair_el' = b
        /\ flag' = (~flag /\ (cardv < 5))
Inv == /\ pc \in [Proc -> Nat]
       /\ sset \in SUBSET Proc
       /\ seqv \in Seq(Nat)
       /\ pair_el \in 0..3
       /\ flag \in BOOLEAN
====
"#;
    let (_dir, mut p) = load_module("DomainRich", spec);
    let cfg = parse_cfg("CONSTANTS Proc = {p1, p2} Zero = 0\nINIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap();
    let init = root_call(&mut p, "Init");
    let next = root_call(&mut p, "Next");
    let domains: std::collections::HashMap<String, String> =
        infer_var_domains(&p, &cfg, &init, &next).unwrap().into_iter().map(|(k, v)| (k.to_string(), v)).collect();

    assert_eq!(domains["pc"], "Function({@p1, @p2} -> Integer(>=0))");
    assert_eq!(domains["sset"], "Set(Atoms({@p1, @p2}))");
    assert_eq!(domains["flat"], "Set(Atoms({@p1, @p2}))");
    assert_eq!(domains["seqv"], "Seq(Atoms({0, 1}))");
    assert_eq!(domains["doms"], "Set(Atoms({@p1, @p2}))");
    assert_eq!(domains["cardv"], "Integer(>=0)");
    assert_eq!(domains["mapv"], r#"Function({"a", "b"} -> Atoms({1, 2, 3}))"#);
    assert_eq!(domains["pair_el"], "Atoms({0, 1, 2, 3})");
    assert_eq!(domains["flag"], "Atoms({FALSE, TRUE})");

    // Verify `proves_var_membership` succeeds on proved structural types.
    let spec_sets = [("pc", "[Proc -> Nat]"), ("sset", "SUBSET Proc"), ("seqv", "Seq(Nat)"), ("pair_el", "0..3"), ("flag", "BOOLEAN")];
    for (vname, set_src) in spec_sets {
        let check_spec = format!("{spec}\n").replace("====", &format!("CheckSet == {set_src}\n===="));
        let (_d2, mut p2) = load_module("DomainRich", &check_spec);
        let i2 = root_call(&mut p2, "Init");
        let n2 = root_call(&mut p2, "Next");
        let v2 = var_id(&mut p2, vname);
        let s2 = root_call(&mut p2, "CheckSet");
        let proved = proves_var_membership(&p2, &cfg, &i2, &n2, v2, &s2);
        assert_eq!(proved, Some(true), "expected {vname} \\in {set_src} to be proved");
    }
}

#[test]
fn domain_inference_const_subst_in_cfg_resolves_set_constant() {
    let spec = r#"---- MODULE ConstSubst ----
CONSTANTS Proc, p1, p2, p3
ProcVal == {p1, p2, p3}
VARIABLE pc
Init == pc = [p \in Proc |-> 0]
Next == \E p \in Proc : pc' = [pc EXCEPT ![p] = 1]
====
"#;
    let (_dir, mut p) = load_module("ConstSubst", spec);
    let cfg = parse_cfg("CONSTANTS p1 = p1 p2 = p2 p3 = p3\nCONSTANT Proc <- ProcVal\nINIT Init\nNEXT Next\n").unwrap();
    let init = root_call(&mut p, "Init");
    let next = root_call(&mut p, "Next");
    let domains = infer_var_domains(&p, &cfg, &init, &next).unwrap();
    assert_eq!(domains[0].1, "Function({@p1, @p2, @p3} -> Atoms({0, 1}))");
}

#[test]
fn domain_inference_soundness_negative_tests() {
    // 1. Unconstrained variable in Next MUST widen to Top even if an invariant constrains it!
    let unconstrained = r#"---- MODULE Unconstrained ----
VARIABLE x
Init == x = 0
Next == TRUE
Inv == x \in {0, 1}
CheckSet == {0, 1}
====
"#;
    let (_d1, mut p1) = load_module("Unconstrained", unconstrained);
    let cfg1 = parse_cfg("INIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap();
    let (i1, n1, v1, s1) = (root_call(&mut p1, "Init"), root_call(&mut p1, "Next"), var_id(&mut p1, "x"), root_call(&mut p1, "CheckSet"));
    let dom1 = infer_var_domains(&p1, &cfg1, &i1, &n1).unwrap();
    assert_eq!(dom1[0].1, "Top");
    assert_eq!(proves_var_membership(&p1, &cfg1, &i1, &n1, v1, &s1), Some(false));

    // 2. `p :> 0` where `p` ranges over multi-element set `Proc` MUST infer `Mapping`, NOT `Function(Proc, ...)`!
    let singleton_map = r#"---- MODULE SingletonMap ----
EXTENDS TLC
CONSTANT Proc
VARIABLE m
Init == \E p \in Proc : m = (p :> 0)
Next == m' = m
CheckSet == [Proc -> {0}]
====
"#;
    let (_d2, mut p2) = load_module("SingletonMap", singleton_map);
    let cfg2 = parse_cfg("CONSTANT Proc = {p1, p2}\nINIT Init\nNEXT Next\n").unwrap();
    let (i2, n2, v2, s2) = (root_call(&mut p2, "Init"), root_call(&mut p2, "Next"), var_id(&mut p2, "m"), root_call(&mut p2, "CheckSet"));
    let dom2 = infer_var_domains(&p2, &cfg2, &i2, &n2).unwrap();
    assert_eq!(dom2[0].1, "Mapping(Atoms({0}))");
    assert_eq!(proves_var_membership(&p2, &cfg2, &i2, &n2, v2, &s2), Some(false));

    // 3. `CHOOSE` widens to Top (never guesses).
    let choose_spec = r#"---- MODULE ChooseWidens ----
CONSTANT Proc
VARIABLE x
Init == x = CHOOSE p \in Proc : TRUE
Next == x' = x
====
"#;
    let (_d3, mut p3) = load_module("ChooseWidens", choose_spec);
    let cfg3 = parse_cfg("CONSTANT Proc = {p1, p2}\nINIT Init\nNEXT Next\n").unwrap();
    let (i3, n3) = (root_call(&mut p3, "Init"), root_call(&mut p3, "Next"));
    let dom3 = infer_var_domains(&p3, &cfg3, &i3, &n3).unwrap();
    assert_eq!(dom3[0].1, "Top");

    // 4. Heterogeneous union `Nat \cup {"bad"}` must refuse `belongs`, and `0..2` must refuse when value reaches 3.
    let bad_types = r#"---- MODULE BadTypes ----
EXTENDS Naturals
VARIABLE n
Init == n = 0
Next == n' = 3
BadUnion == Nat \cup {"bad"}
TooSmallRange == 0..2
====
"#;
    let (_d4, mut p4) = load_module("BadTypes", bad_types);
    let cfg4 = parse_cfg("INIT Init\nNEXT Next\n").unwrap();
    let (i4, n4, v4) = (root_call(&mut p4, "Init"), root_call(&mut p4, "Next"), var_id(&mut p4, "n"));
    for check in ["BadUnion", "TooSmallRange"] {
        let s4 = root_call(&mut p4, check);
        assert_eq!(proves_var_membership(&p4, &cfg4, &i4, &n4, v4, &s4), Some(false), "{check} must NOT be proved");
    }

    // 5. Effectful builtins, recursive operators, and escaping lambdas must refuse normalization.
    let refused = r#"---- MODULE Refused ----
EXTENDS Naturals, Sequences, TLC
VARIABLE x
RECURSIVE Fact(_)
Fact(n) == IF n = 0 THEN 1 ELSE n * Fact(n - 1)
WithPrint == PrintT(x) /\ x' = x
WithRec == x' = Fact(2)
WithEscapingLambda == x' = SelectSeq(<<1, 2>>, LAMBDA a : a > 1)
====
"#;
    let (_d5, mut p5) = load_module("Refused", refused);
    for op in ["WithPrint", "WithRec", "WithEscapingLambda"] {
        let raw = root_call(&mut p5, op);
        assert!(SymNormalizer::new(&p5).normalize(&raw).is_none(), "{op} must refuse normalization");
    }
}

#[test]
fn domain_of_fixed_map_certifies_through_keyed() {
    let spec = r#"---- MODULE DomainKeyed ----
EXTENDS Naturals
CONSTANT Proc
VARIABLE pc
Init == pc = [p \in Proc |-> 0]
Step(p) == pc[p] < 2 /\ pc' = [pc EXCEPT ![p] = @ + 1]
Reset == (\A p \in DOMAIN pc : pc[p] = 2) /\ pc' = [p \in DOMAIN pc |-> 0]
Next == (\E p \in DOMAIN pc : Step(p)) \/ Reset
Inv == \A p \in DOMAIN pc : pc[p] \in 0..2
====
"#;
    let (_dir, mut p) = load_module("DomainKeyed", spec);
    let cfg = parse_cfg("CONSTANT Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap();
    let (init, next, inv) = (root_call(&mut p, "Init"), root_call(&mut p, "Next"), root_call(&mut p, "Inv"));
    let cert = symmetry_certificate(&p, &cfg, &init, &next, &[inv], &[vec!["p1".into(), "p2".into(), "p3".into()]]);
    assert!(cert.is_some(), "DOMAIN pc over fixed map should certify via KeyedCertificate");
}

#[test]
fn corpus_specs_normalize_and_infer_structured_domains() {
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    for (spec_rel, cfg_rel, var_name, expected_prefix) in [
        ("../../tests/specs/PC1.tla", "../../tests/specs/PC1.cfg", "st", "Function({@p1, @p2}"),
        ("../../tests/specs/PC1.tla", "../../tests/specs/PC1.cfg", "msgs", "Set(Records("),
        ("../../tests/specs/PC1.tla", "../../tests/specs/PC1.cfg", "n", "Integer(>=0)"),
        ("../../tests/specs/NeonLowering.tla", "../../tests/specs/NeonLowering.cfg", "f", "Function({@a1, @a2}"),
        ("../../tests/specs/NeonLowering.tla", "../../tests/specs/NeonLowering.cfg", "h", "Mapping(Integer(>=0))"),
    ] {
        let tla = manifest.join(spec_rel);
        let cfg_text = std::fs::read_to_string(manifest.join(cfg_rel)).unwrap();
        let cfg = parse_cfg(&cfg_text).unwrap();
        let mut p = Program::load(&tla, &[]).unwrap();
        p.resolve_all_root();
        let (init, next) = (root_call(&mut p, "Init"), root_call(&mut p, "Next"));
        let domains = infer_var_domains(&p, &cfg, &init, &next).unwrap();
        let (_, dom) = domains.iter().find(|(n, _)| &**n == var_name).unwrap();
        assert!(dom.starts_with(expected_prefix), "{spec_rel}:{var_name} got {dom}, expected prefix {expected_prefix}");
    }
}

#[test]
fn multi_bound_fn_construct_preserves_tuple_binder_grouping() {
    let spec = r#"---- MODULE FnTupleGroup ----
EXTENDS Naturals
A == {1, 2}
B == {3, 4}
C == {5, 6}
Multi == [<<x, y>> \in A \X B, z \in C |-> x + y + z]
Single == [<<x, y>> \in A \X B |-> x + y]
====
"#;
    let (_dir, mut p) = load_module("FnTupleGroup", spec);
    let multi_raw = root_call(&mut p, "Multi");
    let multi_norm = SymNormalizer::new(&p).normalize(&multi_raw).expect("normalize Multi");
    let ExprKind::FnConstruct { bounds, .. } = &*multi_norm.kind else {
        panic!("expected FnConstruct, got {multi_norm:?}");
    };
    assert_eq!(bounds.len(), 2, "multi-bound FnConstruct must preserve 2 outer argument slots (<<<<x,y>>,z>>), got {bounds:?}");
    assert!(
        matches!(&bounds[0].vars, BoundVars::Many(ids) if ids.len() == 1),
        "first slot should bind a single tuple local, got {:?}",
        bounds[0].vars
    );
    assert!(
        matches!(&*bounds[0].set.kind, ExprKind::Builtin { op: tlx_sema::builtins::Builtin::Times, args } if args.len() == 2),
        "first slot domain must stay A \\X B, got {:?}",
        bounds[0].set
    );
    assert!(matches!(&bounds[1].vars, BoundVars::Many(ids) if ids.len() == 1), "second slot should bind z, got {:?}", bounds[1].vars);

    // Single-bound `[<<x, y>> \in A \X B |-> x + y]` still splits into 2 bounds (same domain `A \X B`).
    let single_raw = root_call(&mut p, "Single");
    let single_norm = SymNormalizer::new(&p).normalize(&single_raw).expect("normalize Single");
    let ExprKind::FnConstruct { bounds: single_bounds, .. } = &*single_norm.kind else {
        panic!("expected FnConstruct, got {single_norm:?}");
    };
    assert_eq!(single_bounds.len(), 2, "sole tuple binder over A \\X B splits cleanly into two bounds");
}

#[test]
fn filtered_const_subst_is_not_treated_as_exact_set() {
    let spec = r#"---- MODULE FilteredConst ----
CONSTANT C
Filtered == {i \in {1, 2} : i = 1}
VARIABLES x, y, f
Init == x = 1 /\ y \in C /\ f = [k \in C |-> 0]
Next == x' \in {1, 2} /\ y' = y /\ f' = f
CheckC == C
====
"#;
    let (_dir, mut p) = load_module("FilteredConst", spec);
    let cfg = parse_cfg("CONSTANT C <- Filtered\nINIT Init\nNEXT Next\n").unwrap();
    let init = root_call(&mut p, "Init");
    let next = root_call(&mut p, "Next");
    let x_var = var_id(&mut p, "x");
    let check_c = root_call(&mut p, "CheckC");

    // `x` reaches {1, 2}, whereas `C = {1}`, so `x \in C` MUST NOT be proved!
    assert_eq!(
        proves_var_membership(&p, &cfg, &init, &next, x_var, &check_c),
        Some(false),
        "filtered constant C <- {{i \\in {{1, 2}} : i = 1}} must NOT be treated as exact {{1, 2}}"
    );

    let domains: std::collections::HashMap<String, String> =
        infer_var_domains(&p, &cfg, &init, &next).unwrap().into_iter().map(|(k, v)| (k.to_string(), v)).collect();
    // Overapproximated may-domain for `y \in C` is still soundly `Atoms({1, 2})`.
    assert_eq!(domains["y"], "Atoms({1, 2})");
    // Function over filtered constant `C` must NOT infer exact domain `Function({1, 2} -> ...)`.
    assert_eq!(domains["f"], "Mapping(Atoms({0}))");
}

#[test]
fn except_at_preserves_lexical_scope_across_lambda_and_let() {
    let spec = r#"---- MODULE LexicalAt ----
EXTENDS Naturals, Sequences
Put(F(_)) == [<<1>> EXCEPT ![1] = F(0)]
LamOuter == [<<0>> EXCEPT ![1] = Put(LAMBDA u : @)]
LetOuter == [<<0>> EXCEPT ![1] = LET x == @ IN [<<1>> EXCEPT ![1] = x]]
AliasedOuter == [<<0>> EXCEPT ![1] = 9, ![1] = Put(LAMBDA u : @)]
====
"#;
    let (_dir, mut p) = load_module("LexicalAt", spec);

    for name in ["LamOuter", "LetOuter"] {
        let raw = root_call(&mut p, name);
        let norm = SymNormalizer::new(&p).normalize(&raw).unwrap_or_else(|| panic!("{name} should normalize"));
        let dbg = format!("{norm:?}");
        assert!(
            dbg.contains("Num(0)") && dbg.contains("FnApp") && !dbg.contains("At"),
            "{name} must bind @ to outer <<0>>[1] rather than inner <<1>>[1], got {dbg}"
        );
        // Verify the inner EXCEPT replacement is `<<0>>[1]`, never `<<1>>[1]`.
        let ExprKind::Except { updates, .. } = &*norm.kind else { panic!("expected outer Except, got {norm:?}") };
        let ExprKind::Except { updates: inner_updates, .. } = &*updates[0].1.kind else {
            panic!("expected inner Except, got {:?}", updates[0].1)
        };
        let ExprKind::FnApp { func, .. } = &*inner_updates[0].1.kind else {
            panic!("expected FnApp for outer @, got {:?}", inner_updates[0].1)
        };
        let ExprKind::Tuple(elems) = &*func.kind else { panic!("expected <<0>> tuple, got {func:?}") };
        assert!(matches!(&*elems[0].kind, ExprKind::Num(0)), "{name} captured wrong @ base: {elems:?}");
    }

    let aliased_raw = root_call(&mut p, "AliasedOuter");
    assert!(
        SymNormalizer::new(&p).normalize(&aliased_raw).is_none(),
        "reading outer @ inside a lambda after an aliasing update must fail closed"
    );
}

#[test]
fn init_membership_seeds_preserved_under_reversed_and_cyclic_equalities() {
    // R11-#1: `Init == x \in {1, 2} /\ y = x` must retain `1, 2` for both `x` and `y`
    // rather than collapsing to `{0}` via reversed equality `x := y`.
    let spec = r#"---- MODULE ReversedInitEq ----
VARIABLES x, y
Init == x \in {1, 2} /\ y = x
Next == x' = 0 /\ y' = 0
ZeroSet == {0}
====
"#;
    let (_dir, mut p) = load_module("ReversedInitEq", spec);
    let cfg = parse_cfg("INIT Init\nNEXT Next\n").unwrap();
    let init = root_call(&mut p, "Init");
    let next = root_call(&mut p, "Next");
    let x_var = var_id(&mut p, "x");
    let zero_set = root_call(&mut p, "ZeroSet");

    assert_eq!(
        proves_var_membership(&p, &cfg, &init, &next, x_var, &zero_set),
        Some(false),
        "R11-#1 must NOT prove x \\in {{0}} when Init allows x \\in {{1, 2}}"
    );
    let domains: std::collections::HashMap<String, String> =
        infer_var_domains(&p, &cfg, &init, &next).unwrap().into_iter().map(|(k, v)| (k.to_string(), v)).collect();
    assert_eq!(domains["x"], "Atoms({0, 1, 2})");
    assert_eq!(domains["y"], "Atoms({0, 1, 2})");

    // Guard equality after both memberships (`x \in {1, 2} /\ y \in {1, 2} /\ x = y`) must also keep `{0, 1, 2}`.
    let guard_spec = r#"---- MODULE GuardInitEq ----
VARIABLES x, y
Init == x \in {1, 2} /\ y \in {1, 2} /\ x = y
Next == x' = 0 /\ y' = 0
====
"#;
    let (_dir2, mut p2) = load_module("GuardInitEq", guard_spec);
    let i2 = root_call(&mut p2, "Init");
    let n2 = root_call(&mut p2, "Next");
    let d2: std::collections::HashMap<String, String> =
        infer_var_domains(&p2, &cfg, &i2, &n2).unwrap().into_iter().map(|(k, v)| (k.to_string(), v)).collect();
    assert_eq!(d2["x"], "Atoms({0, 1, 2})");
    assert_eq!(d2["y"], "Atoms({0, 1, 2})");

    // Ungrounded cycle (`Init == x = y /\ y = x`) must fail closed to `Top`, never `Atoms({0})`.
    let cycle_spec = r#"---- MODULE CycleInitEq ----
VARIABLES x, y
Init == x = y /\ y = x
Next == x' = 0 /\ y' = 0
====
"#;
    let (_dir3, mut p3) = load_module("CycleInitEq", cycle_spec);
    let i3 = root_call(&mut p3, "Init");
    let n3 = root_call(&mut p3, "Next");
    let d3: std::collections::HashMap<String, String> =
        infer_var_domains(&p3, &cfg, &i3, &n3).unwrap().into_iter().map(|(k, v)| (k.to_string(), v)).collect();
    assert_eq!(d3["x"], "Top");
    assert_eq!(d3["y"], "Top");

    // R12-#2: Reconvergent Fibonacci-style equality DAG (`x2 = x0 + x1`, ..., `x44 = x42 + x43`)
    // must memoize groundedness per branch in linear time rather than taking exponential time.
    let mut vars = vec!["x0".to_string(), "x1".to_string()];
    let mut init_terms = vec!["x0 = 0".to_string(), "x1 = x0".to_string()];
    let mut next_terms = vec!["x0' = 0".to_string(), "x1' = 0".to_string()];
    for i in 2..45 {
        vars.push(format!("x{i}"));
        init_terms.push(format!("x{i} = x{} + x{}", i - 2, i - 1));
        next_terms.push(format!("x{i}' = 0"));
    }
    let dag_spec = format!(
        "---- MODULE DagInitEq ----\nEXTENDS Naturals\nVARIABLES {}\nInit == {}\nNext == {}\n====\n",
        vars.join(", "),
        init_terms.join(" /\\ "),
        next_terms.join(" /\\ "),
    );
    let (_dir4, mut p4) = load_module("DagInitEq", &dag_spec);
    let i4 = root_call(&mut p4, "Init");
    let n4 = root_call(&mut p4, "Next");
    let t0 = std::time::Instant::now();
    let d4: std::collections::HashMap<String, String> =
        infer_var_domains(&p4, &cfg, &i4, &n4).unwrap().into_iter().map(|(k, v)| (k.to_string(), v)).collect();
    assert!(t0.elapsed().as_secs() < 5, "DAG grounding took too long: {:?}", t0.elapsed());
    assert_eq!(d4["x44"], "Integer(>=0)");

    // R13-#3: Long linear chain (`x0 = 0 /\ x1 = x0 /\ ... /\ x199 = x198`) indexes bindings
    // once per branch and reuses completed groundedness results across all 200 variables.
    let mut chain_vars = vec!["x0".to_string()];
    let mut chain_init = vec!["x0 = 0".to_string()];
    let mut chain_next = vec!["x0' = 0".to_string()];
    for i in 1..200 {
        chain_vars.push(format!("x{i}"));
        chain_init.push(format!("x{i} = x{}", i - 1));
        chain_next.push(format!("x{i}' = 0"));
    }
    let chain_spec = format!(
        "---- MODULE ChainInitEq ----\nVARIABLES {}\nInit == {}\nNext == {}\n====\n",
        chain_vars.join(", "),
        chain_init.join(" /\\ "),
        chain_next.join(" /\\ "),
    );
    let (_dir5, mut p5) = load_module("ChainInitEq", &chain_spec);
    let i5 = root_call(&mut p5, "Init");
    let n5 = root_call(&mut p5, "Next");
    let t1 = std::time::Instant::now();
    let d5: std::collections::HashMap<String, String> =
        infer_var_domains(&p5, &cfg, &i5, &n5).unwrap().into_iter().map(|(k, v)| (k.to_string(), v)).collect();
    assert!(t1.elapsed().as_secs() < 5, "200-var chain took too long: {:?}", t1.elapsed());
    assert_eq!(d5["x60"], "Atoms({0})");
}
