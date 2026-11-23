use tlx_front::cfg::parse_cfg;
use tlx_sema::{
    hir::{Expr, ExprKind, OpRef, RootSymbol},
    optimize::{equiv_symmetry_certificate, symmetry_certificate},
    Program,
};

fn certify(name: &str, spec: &str, cfg: &str, groups: &[Vec<String>]) -> Option<String> {
    let dir = tlx_testkit::TempDir::new("equiv-sema");
    let path = dir.write(&format!("{name}.tla"), spec);
    let mut p = Program::load(&path, &[]).unwrap();
    p.resolve_all_root();
    let roots = ["Init", "Next", "Inv"].map(|root| {
        let Some(RootSymbol::Def(id)) = p.lookup_root(root) else { panic!("missing {root}") };
        Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
    });
    symmetry_certificate(&p, &parse_cfg(cfg).unwrap(), &roots[0], &roots[1], &roots[2..], groups)
}

fn certify_equiv_direct(name: &str, spec: &str, cfg: &str, groups: &[Vec<String>]) -> Option<String> {
    let dir = tlx_testkit::TempDir::new("equiv-direct");
    let path = dir.write(&format!("{name}.tla"), spec);
    let mut p = Program::load(&path, &[]).unwrap();
    p.resolve_all_root();
    let roots = ["Init", "Next", "Inv"].map(|root| {
        let Some(RootSymbol::Def(id)) = p.lookup_root(root) else { panic!("missing {root}") };
        Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
    });
    equiv_symmetry_certificate(&p, &parse_cfg(cfg).unwrap(), &roots[0], &roots[1], &roots[2..], groups)
}

#[test]
fn multi_key_records_and_sequences_certify_via_equiv_fallback() {
    let proof = certify(
        "MultiKeyMsgs",
        include_str!("../../../proofs/symmetry/MultiKeyMsgs.tla"),
        include_str!("../../../proofs/symmetry/MultiKeyMsgs.cfg"),
        &[vec!["n1".into(), "n2".into(), "n3".into()]],
    )
    .expect("MultiKeyMsgs should certify");
    for needle in [
        "namespace TlxOptimization.GeneratedEquivSymmetry",
        "EquivRule.Model",
        "Expr.recLit",
        "Expr.append",
        "Expr.head",
        "Expr.tail",
        "Expr.len",
        "Expr.card",
        "theorem certificate",
        "theorem optimization_correct",
        "theorem specification_correct",
        "theorem counterexample_lifts",
        "theorem deadlock_preserved",
        "theorem orbit_key_equivalent",
    ] {
        assert!(proof.contains(needle), "missing {needle}");
    }
}

#[test]
fn key_valued_maps_nested_maps_and_comprehensions_certify() {
    let proof = certify(
        "KeyValMaps",
        include_str!("../../../proofs/symmetry/KeyValMaps.tla"),
        include_str!("../../../proofs/symmetry/KeyValMaps.cfg"),
        &[vec!["p1".into(), "p2".into(), "p3".into()]],
    )
    .expect("KeyValMaps should certify");
    for needle in [
        "namespace TlxOptimization.GeneratedEquivSymmetry",
        "Expr.fnConstruct",
        "Expr.except",
        "Expr.domain",
        "Expr.setFilter",
        "SetPred.fnSet",
        "SetPred.subset",
        "theorem orbit_key_equivalent",
    ] {
        assert!(proof.contains(needle), "missing {needle}");
    }
}

#[test]
fn product_groups_tuples_case_setmap_and_symmetric_quorums_certify() {
    let spec = r#"---- MODULE QuorumVote ----
EXTENDS Naturals, FiniteSets
CONSTANTS Acceptor, Value, Quorum
VARIABLE votes, decided
Init == votes = [a \in Acceptor |-> {}] /\ decided = {}
Vote(a, v) ==
  /\ votes' = [votes EXCEPT ![a] = @ \cup {<<a, v>>}]
  /\ decided' = CASE (\E Q \in Quorum : \A x \in Q : <<x, v>> \in votes'[x]) -> decided \cup {v}
                  [] OTHER -> decided
Next == \E a \in Acceptor, v \in Value : Vote(a, v)
Inv ==
  /\ decided \subseteq Value
  /\ \A a \in Acceptor : {v : <<x, v>> \in votes[a]} \subseteq Value
====
"#;
    let cfg = "CONSTANTS\n  Acceptor = {a1, a2, a3}\n  Value = {v1, v2}\n  Quorum = {{a1, a2}, {a1, a3}, {a2, a3}}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    let proof = certify("QuorumVote", spec, cfg, &[vec!["a1".into(), "a2".into(), "a3".into()], vec!["v1".into(), "v2".into()]])
        .expect("QuorumVote should certify");
    assert!(proof.contains("namespace TlxOptimization.GeneratedEquivSymmetry"));
    assert!(proof.contains("abbrev GroupCount : Nat := 2"));
    assert!(proof.contains("Expr.powerset"));
    assert!(proof.contains("Expr.setMap"));
}

#[test]
fn unsound_choose_pinned_constants_overlapping_and_unused_groups_refuse() {
    let base = include_str!("../../../proofs/symmetry/KeyValMaps.tla");
    let cfg = include_str!("../../../proofs/symmetry/KeyValMaps.cfg");
    let group = &[vec!["p1".into(), "p2".into(), "p3".into()]];

    // CHOOSE over moved keys must refuse.
    let bad_choose = base.replace("parent[p] = p", "parent[p] = (CHOOSE r \\in Proc : TRUE)");
    assert!(certify_equiv_direct("KeyValMaps", &bad_choose, cfg, group).is_none());

    // Primed variable in Inv must refuse.
    let bad_inv = base.replace("DOMAIN parent = Proc", "parent' = parent");
    assert!(certify_equiv_direct("KeyValMaps", &bad_inv, cfg, group).is_none());

    // Pinned model value constant must refuse.
    let pinned_spec = r#"---- MODULE Pinned ----
CONSTANTS Proc, Leader
VARIABLE x
Init == x = Leader
Next == x' \in Proc
Inv == x \in Proc
====
"#;
    let pinned_cfg = "CONSTANTS Proc = {p1, p2, p3} Leader = p1\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    assert!(certify_equiv_direct("Pinned", pinned_spec, pinned_cfg, group).is_none());

    // Asymmetric quorum constant must refuse.
    let asym_spec = r#"---- MODULE AsymQuorum ----
CONSTANTS Proc, Q
VARIABLE x
Init == x = {}
Next == x' \in Q
Inv == TRUE
====
"#;
    let asym_cfg = "CONSTANTS Proc = {p1, p2, p3} Q = {{p1, p2}, {p1, p3}}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    assert!(certify_equiv_direct("AsymQuorum", asym_spec, asym_cfg, group).is_none());

    // Overlapping product groups must refuse.
    assert!(certify_equiv_direct("KeyValMaps", base, cfg, &[vec!["p1".into(), "p2".into()], vec!["p2".into(), "p3".into()]],).is_none());

    // Unused group in product must refuse.
    assert!(certify_equiv_direct("KeyValMaps", base, cfg, &[vec!["p1".into(), "p2".into(), "p3".into()], vec!["x1".into(), "x2".into()]],)
        .is_none());
}

#[test]
fn ksubset_and_is_injective_certify() {
    let spec = r#"---- MODULE KSubsetInj ----
EXTENDS Naturals, FiniteSets, FiniteSetsExt, Functions
CONSTANTS Proc
VARIABLE pair, perm
Init ==
  /\ pair \in kSubset(2, Proc)
  /\ perm = [p \in Proc |-> p]
Next ==
  /\ pair' \in kSubset(2, Proc)
  /\ perm' \in [Proc -> Proc]
  /\ IsInjective(perm')
Inv ==
  /\ Cardinality(pair) = 2
  /\ Cardinality(kSubset(2, Proc)) = 3
  /\ IsInjective(perm)
====
"#;
    let cfg = "CONSTANTS Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    let proof = certify("KSubsetInj", spec, cfg, &[vec!["p1".into(), "p2".into(), "p3".into()]]).expect("KSubsetInj should certify");
    assert!(proof.contains("namespace TlxOptimization.GeneratedEquivSymmetry"));
    assert!(proof.contains("Expr.powerset"));
    assert!(proof.contains("Expr.card"));
    assert!(proof.contains("Form.all"));
}

#[test]
fn finding1_quantified_partial_ops_refuse_and_corpus_specs_certify() {
    let group = &[vec!["p1".into(), "p2".into(), "p3".into()]];
    let cfg = "CONSTANTS Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";

    // Codex Astra's exact non-CHOOSE 0^0 counterexample must refuse.
    let zero_pow_zero = r#"---- MODULE QuantZeroPow ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLE parent
Init == \E r \in Proc : parent = [p \in Proc |-> r]
Next == UNCHANGED parent
Inv == \E p \in Proc :
         LET n == IF parent[p] = p THEN 1 ELSE 0
         IN n ^ n = 1
====
"#;
    assert!(certify_equiv_direct("QuantZeroPow", zero_pow_zero, cfg, group).is_none());
    assert!(certify("QuantZeroPow", zero_pow_zero, cfg, group).is_none());

    // Division and modulo by potentially zero divisor inside quantifier must refuse.
    let div_zero = r#"---- MODULE QuantDivZero ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLE parent
Init == \E r \in Proc : parent = [p \in Proc |-> r]
Next == UNCHANGED parent
Inv == \E p \in Proc : (1 \div (IF parent[p] = p THEN 1 ELSE 0)) = 1
====
"#;
    assert!(certify_equiv_direct("QuantDivZero", div_zero, cfg, group).is_none());

    let mod_zero = div_zero.replace("QuantDivZero", "QuantModZero").replace(r"1 \div", "1 %").replace("= 1", "= 0");
    assert!(certify_equiv_direct("QuantModZero", &mod_zero, cfg, group).is_none());

    // Out-of-domain indexing inside quantifier must refuse.
    let oob_idx = r#"---- MODULE QuantOobIdx ----
CONSTANTS Proc
VARIABLE parent
Init == \E r \in Proc : parent = [q \in {r} |-> r]
Next == UNCHANGED parent
Inv == \E p \in Proc : parent[p] = p
====
"#;
    assert!(certify_equiv_direct("QuantOobIdx", oob_idx, cfg, group).is_none());

    // Non-boolean quantifier body must refuse.
    let non_bool = r#"---- MODULE QuantNonBool ----
CONSTANTS Proc
VARIABLE x
Init == \E r \in Proc : x = [p \in Proc |-> IF p = r THEN TRUE ELSE 1]
Next == UNCHANGED x
Inv == \E p \in Proc : x[p]
====
"#;
    assert!(certify_equiv_direct("QuantNonBool", non_bool, cfg, group).is_none());

    // Unchecked arithmetic overflow inside quantifier must refuse.
    let overflow = r#"---- MODULE QuantOverflow ----
EXTENDS Integers
CONSTANTS Proc
VARIABLE n
Init == n \in 0..1
Next == n' = n + 1
Inv == \A p \in Proc : n + 1 > 0
====
"#;
    assert!(certify_equiv_direct("QuantOverflow", overflow, cfg, group).is_none());

    // Corpus specs PC1, PredMemberCup, and NeonLowering must continue to certify.
    let pc1 = certify_roots(
        "PC1",
        include_str!("../../../tests/specs/PC1.tla"),
        include_str!("../../../tests/specs/PC1.cfg"),
        "Init",
        "Next",
        &["TypeOK"],
        &[vec!["p1".into(), "p2".into()]],
    );
    assert!(pc1.is_some(), "PC1 must certify");

    let pmc = certify_roots(
        "PredMemberCup",
        include_str!("../../../tests/specs/PredMemberCup.tla"),
        include_str!("../../../tests/specs/PredMemberCup.cfg"),
        "Init",
        "Next",
        &["TypeOK", "NoE"],
        &[vec!["k1".into(), "k2".into(), "k3".into()]],
    );
    assert!(pmc.is_some(), "PredMemberCup must certify");

    let neon = certify_roots(
        "NeonLowering",
        include_str!("../../../tests/specs/NeonLowering.tla"),
        include_str!("../../../tests/specs/NeonLowering.cfg"),
        "Init",
        "Next",
        &["TypeOk", "ConfigSafety", "Size"],
        &[vec!["a1".into(), "a2".into()]],
    );
    assert!(neon.is_some(), "NeonLowering must certify");
}

fn certify_roots(name: &str, spec: &str, cfg: &str, init: &str, next: &str, invs: &[&str], groups: &[Vec<String>]) -> Option<String> {
    let dir = tlx_testkit::TempDir::new("equiv-roots");
    let path = dir.write(&format!("{name}.tla"), spec);
    let mut p = Program::load(&path, &[]).unwrap();
    p.resolve_all_root();
    let mut resolve = |root: &str| {
        let Some(RootSymbol::Def(id)) = p.lookup_root(root) else { panic!("missing {root}") };
        Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
    };
    let init_e = resolve(init);
    let next_e = resolve(next);
    let inv_es: Vec<Expr> = invs.iter().map(|r| resolve(r)).collect();
    equiv_symmetry_certificate(&p, &parse_cfg(cfg).unwrap(), &init_e, &next_e, &inv_es, groups)
}

#[test]
fn finding2_and_3_seq_fn_extensional_eq_and_oob_except_certify() {
    let spec = r#"---- MODULE SeqFnExcept ----
EXTENDS Naturals, Sequences, FiniteSets
CONSTANTS Proc
VARIABLE s
Init == s \in {<<p>> : p \in Proc}
Next == \E p \in Proc : s' = [<<p>> EXCEPT ![2] = 1]
Inv ==
  /\ \A p \in Proc : <<p>> = [i \in 1..1 |-> p]
  /\ \A p \in Proc : Cardinality({<<p>>, [i \in 1..1 |-> p]}) = 1
  /\ [s EXCEPT ![2] = 1 \div 0] = s
====
"#;
    let cfg = "CONSTANTS Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    let proof =
        certify_equiv_direct("SeqFnExcept", spec, cfg, &[vec!["p1".into(), "p2".into(), "p3".into()]]).expect("SeqFnExcept should certify");
    assert!(proof.contains("theorem Val.seq_singleton_eq_fn"));
    assert!(proof.contains("theorem Val.card_seq_fn_singleton"));
    assert!(proof.contains("theorem Val.update_seq_oob"));
}

#[test]
fn finding4_tuple_arity_validation() {
    let group = &[vec!["p1".into(), "p2".into(), "p3".into()]];
    let cfg = "CONSTANTS Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";

    // Wrong tuple arity in quantifier, SetFilter, SetMap, and FnConstruct must all refuse.
    for (name, inv) in [
        ("QuantArity", r"\A <<a, b>> \in {<<1, 2, 3>>} : TRUE"),
        ("FilterArity", r"{<<a, b>> \in {<<1, 2, 3>>} : TRUE} = {}"),
        ("MapArity", r"{a : <<a, b>> \in {<<1, 2, 3>>}} = {}"),
        ("FnArity", r"DOMAIN [<<a, b>> \in {<<1, 2, 3>>} |-> a] = {}"),
        ("MixedArity", r"\E <<a, b>> \in {<<1, 2>>, <<1, 2, 3>>} : a = 1"),
    ] {
        let spec =
            format!("---- MODULE {name} ----\nCONSTANTS Proc\nVARIABLE x\nInit == x \\in Proc\nNext == UNCHANGED x\nInv == {inv}\n====\n");
        assert!(certify_equiv_direct(name, &spec, cfg, group).is_none(), "{name} must refuse");
    }

    // Exact tuple arity must certify.
    let ok_spec = r#"---- MODULE GoodArity ----
CONSTANTS Proc
VARIABLE x
Init == x \in Proc
Next == x' \in Proc
Inv == \A <<a, b>> \in Proc \X Proc : a = b \/ a # b
====
"#;
    assert!(certify_equiv_direct("GoodArity", ok_spec, cfg, group).is_some());
}

#[test]
fn finding5_and_6_is_finite_set_semantics_and_linear_nested_size() {
    let group = &[vec!["p1".into(), "p2".into(), "p3".into()]];
    let cfg = "CONSTANTS Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";

    // IsFiniteSet on tuple, record, function, and set certifies using Form.isFiniteSet.
    let spec = r#"---- MODULE FiniteKinds ----
EXTENDS FiniteSets
CONSTANTS Proc
VARIABLE x
Init == x \in Proc
Next == x' \in Proc
Inv ==
  /\ IsFiniteSet(<<x>>)
  /\ IsFiniteSet([a |-> x])
  /\ IsFiniteSet([p \in Proc |-> p])
  /\ IsFiniteSet(Proc)
====
"#;
    let proof = certify_equiv_direct("FiniteKinds", spec, cfg, group).expect("FiniteKinds should certify");
    assert!(proof.contains("Form.isFiniteSet"));
    assert!(proof.contains("theorem Val.isFinite_seq"));

    // IsFiniteSet on non-set/fn inside quantifier must refuse (errors at runtime on integer 1).
    let bad_fin = r#"---- MODULE BadFinite ----
EXTENDS FiniteSets
CONSTANTS Proc
VARIABLE x
Init == x \in Proc
Next == UNCHANGED x
Inv == \E y \in {1, <<x>>} : IsFiniteSet(y)
====
"#;
    assert!(certify_equiv_direct("BadFinite", bad_fin, cfg, group).is_none());

    // Deeply nested IsFiniteSet({IsFiniteSet({...})}) must scale linearly (no exponential blowup).
    let mut nested = String::from("Proc");
    for _ in 0..25 {
        nested = format!("{{IsFiniteSet({nested})}}");
    }
    let nested_spec = format!(
        "---- MODULE NestedFinite ----\nEXTENDS FiniteSets\nCONSTANTS Proc\nVARIABLE x\n\
         Init == x \\in Proc\nNext == UNCHANGED x\nInv == IsFiniteSet({nested})\n====\n"
    );
    let nested_proof = certify_equiv_direct("NestedFinite", &nested_spec, cfg, group).expect("25-deep IsFiniteSet should certify linearly");
    assert!(nested_proof.contains("Form.isFiniteSet"));
    // Without single-operand lowering, 25 levels would be > 2^25 bytes (~1 GiB).
    assert!(nested_proof.len() < 300_000, "unexpectedly large certificate: {} bytes", nested_proof.len());

    // Verify emitted-size budget refuses pathological expansion cleanly without OOM.
    // A short 18-level LET doubling chain parses in < 1 ms but expands past MAX_EMITTED_BYTES.
    let mut defs = String::from("S0 == Proc\n");
    for i in 1..=18 {
        defs.push_str(&format!("S{i} == S{} \\cup S{}\n", i - 1, i - 1));
    }
    let blowup_spec = format!(
        "---- MODULE Blowup ----\nCONSTANTS Proc\nVARIABLE x\n{defs}Init == x \\in Proc\nNext == UNCHANGED x\nInv == x \\in S18\n====\n"
    );
    assert!(certify_equiv_direct("Blowup", &blowup_spec, cfg, group).is_none());
}

#[test]
fn round2_codex_astra_all_15_soundness_regressions_refuse() {
    let group = &[vec!["p1".into(), "p2".into(), "p3".into()]];
    let cfg = "CONSTANTS Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";

    // R2-#1a: keyed path must be gated by totality (`1 \div 0` under short-circuiting `\E`).
    let r2_1a = r#"---- MODULE R2KeyedDivZero ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = p \/ 1 \div 0 = 0
====
"#;
    assert!(certify("R2KeyedDivZero", r2_1a, cfg, group).is_none(), "R2-#1a must refuse");

    // R2-#1b: choose_sym path must be gated by totality (`1 \div 0` alongside a certified CHOOSE).
    let r2_1b = r#"---- MODULE R2ChooseDivZero ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == (\E p \in Proc : owner = p \/ 1 \div 0 = 0) /\ (CHOOSE p \in Proc : p = owner) = owner
====
"#;
    assert!(certify("R2ChooseDivZero", r2_1b, cfg, group).is_none(), "R2-#1b must refuse");

    // R2-#2: top-level observation equality/inequality without explicit quantifier (`f # [p \in Proc |-> 1]`).
    let r2_2 = r#"---- MODULE R2TopLevelNeq ----
CONSTANTS Proc
VARIABLE f
Init == \E r \in Proc : f = [p \in Proc |-> IF p = r THEN 0 ELSE "a"]
Next == UNCHANGED f
Inv == f # [p \in Proc |-> 1]
====
"#;
    assert!(certify("R2TopLevelNeq", r2_2, cfg, group).is_none(), "R2-#2 must refuse");

    // R2-#3: 32-bit signed arithmetic overflow (`2147483647 + 1`).
    let r2_3 = r#"---- MODULE R2Overflow ----
EXTENDS Integers
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = p \/ (2147483647 + 1 = 0)
====
"#;
    assert!(certify("R2Overflow", r2_3, cfg, group).is_none(), "R2-#3 must refuse");

    // R2-#4: conservative `\div` across both divisor endpoints (`1 \div (1 \div d)` for `d \in {1, 2}`).
    let r2_4 = r#"---- MODULE R2DivUpper ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLE parent
Init == \E r \in Proc : parent = [p \in Proc |-> r]
Next == UNCHANGED parent
Inv == \E p \in Proc : (1 \div (1 \div (IF parent[p] = p THEN 1 ELSE 2))) = 1
====
"#;
    assert!(certify("R2DivUpper", r2_4, cfg, group).is_none(), "R2-#4 must refuse");

    // R2-#5: dependent Init assignment (`a = "x" /\ b = a`).
    let r2_5 = r#"---- MODULE R2DepInit ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLES a, b, owner
Init == a = "x" /\ b = a /\ owner \in Proc
Next == UNCHANGED <<a, b, owner>>
Inv == \E p \in Proc : owner = p \/ b + 1 = 0
====
"#;
    assert!(certify("R2DepInit", r2_5, cfg, group).is_none(), "R2-#5 must refuse");

    // R2-#6: 14-variable chain must converge or fail closed (never drop unpropagated 0).
    let r2_6 = r#"---- MODULE R2Chain14 ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLES owner, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13
Init ==
  /\ owner \in Proc
  /\ v0 = 1 /\ v1 = 1 /\ v2 = 1 /\ v3 = 1 /\ v4 = 1 /\ v5 = 1 /\ v6 = 1
  /\ v7 = 1 /\ v8 = 1 /\ v9 = 1 /\ v10 = 1 /\ v11 = 1 /\ v12 = 1 /\ v13 = 1
Next ==
  /\ UNCHANGED owner
  /\ v0' = 0 /\ v1' = v0 /\ v2' = v1 /\ v3' = v2 /\ v4' = v3 /\ v5' = v4 /\ v6' = v5
  /\ v7' = v6 /\ v8' = v7 /\ v9' = v8 /\ v10' = v9 /\ v11' = v10 /\ v12' = v11 /\ v13' = v12
Inv == \E p \in Proc : owner = p \/ (1 \div v13 = 1)
====
"#;
    assert!(certify("R2Chain14", r2_6, cfg, group).is_none(), "R2-#6 must refuse");

    // R2-#7: value-position Boolean `\E` in `Next` (`ok' = (\E p \in Proc : ...)`).
    let r2_7 = r#"---- MODULE R2ValPosExists ----
CONSTANTS Proc
VARIABLES parent, ok
Init == (\E r \in Proc : parent = [p \in Proc |-> r]) /\ ok = TRUE
Next == parent' = parent /\ ok' = (\E p \in Proc : parent'[p] = p \/ parent[1] = p)
Inv == ok
====
"#;
    assert!(certify("R2ValPosExists", r2_7, cfg, group).is_none(), "R2-#7 must refuse");

    // R2-#8: typed model values (`P_1`, `P_2`, `P_3`) are incomparable with integers and `Nat`.
    let typed_group = &[vec!["P_1".into(), "P_2".into(), "P_3".into()]];
    let typed_cfg = "CONSTANTS Proc = {P_1, P_2, P_3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    let r2_8 = r#"---- MODULE R2TypedMv ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = p \/ 1 = p
====
"#;
    assert!(certify("R2TypedMv", r2_8, typed_cfg, typed_group).is_none(), "R2-#8 eq must refuse");
    let r2_8_mem = r2_8.replace("R2TypedMv", "R2TypedMvMem").replace("1 = p", r"p \in Nat");
    assert!(certify("R2TypedMvMem", &r2_8_mem, typed_cfg, typed_group).is_none(), "R2-#8 mem must refuse");

    // R2-#9: `slot # A` must NOT remove unrelated unmoved model value `B`.
    let ab_cfg = "CONSTANTS Proc = {p1, p2, p3} A = A B = B\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    let r2_9 = r#"---- MODULE R2SlotNotA ----
CONSTANTS Proc, A, B
VARIABLES slot, f
Init == slot \in Proc \cup {A, B} /\ f = [p \in Proc |-> 1]
Next == UNCHANGED <<slot, f>>
Inv == \E p \in Proc : slot = p \/ (slot # A /\ f[slot] = 1)
====
"#;
    assert!(certify("R2SlotNotA", r2_9, ab_cfg, group).is_none(), "R2-#9 must refuse");

    // R2-#10: `a.val > 0` must NOT refine `@` in unrelated record `[b EXCEPT !.val = 1 \div @]`.
    let r2_10 = r#"---- MODULE R2CrossRecAt ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLES a, b, owner
Init == a = [val |-> 1] /\ b = [val |-> 0] /\ owner \in Proc
Next == UNCHANGED <<a, b, owner>>
Inv == \E p \in Proc : owner = p \/ (a.val > 0 /\ [b EXCEPT !.val = 1 \div @] = b)
====
"#;
    assert!(certify("R2CrossRecAt", r2_10, cfg, group).is_none(), "R2-#10 must refuse");

    // R2-#11: string-indexed record EXCEPT `!["n"] = 0` must update field `n`'s shape.
    let r2_11 = r#"---- MODULE R2StrIdxExcept ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLES rec, owner
Init == rec = [n |-> 1] /\ owner \in Proc
Next == rec' = [rec EXCEPT !["n"] = 0] /\ UNCHANGED owner
Inv == \E p \in Proc : owner = p \/ 1 \div rec.n = 1
====
"#;
    assert!(certify("R2StrIdxExcept", r2_11, cfg, group).is_none(), "R2-#11 must refuse");

    // R2-#12: `SUBSET Nat` is non-enumerable and must refuse inside quantifiers.
    let r2_12 = r#"---- MODULE R2SubsetNat ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = p \/ (\E i \in SUBSET Nat : TRUE)
====
"#;
    assert!(certify("R2SubsetNat", r2_12, cfg, group).is_none(), "R2-#12 must refuse");

    // R2-#13: `Cardinality(SUBSET (1..31))` overflows 32-bit int and must refuse.
    let r2_13 = r#"---- MODULE R2CardOverflow ----
EXTENDS Naturals, FiniteSets
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = p \/ Cardinality(SUBSET (1..31)) >= 0
====
"#;
    assert!(certify("R2CardOverflow", r2_13, cfg, group).is_none(), "R2-#13 must refuse");

    // R2-#14: `CASE` without `OTHER` and `Assert` must refuse.
    let r2_14a = r#"---- MODULE R2CaseNoOther ----
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = p \/ ~(CASE FALSE -> TRUE)
====
"#;
    assert!(certify("R2CaseNoOther", r2_14a, cfg, group).is_none(), "R2-#14a must refuse");

    let r2_14b = r#"---- MODULE R2Assert ----
EXTENDS TLC
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = p \/ ~Assert(FALSE, "bad")
====
"#;
    assert!(certify("R2Assert", r2_14b, cfg, group).is_none(), "R2-#14b must refuse");

    // R2-#15: empty-witness `CHOOSE` equality must refuse in both equiv_sym and top-level symmetry.
    let r2_15 = r#"---- MODULE R2EmptyChoose ----
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = p \/ ((CHOOSE x \in {} : TRUE) = (CHOOSE x \in {} : TRUE))
====
"#;
    assert!(certify_equiv_direct("R2EmptyChoose", r2_15, cfg, group).is_none(), "R2-#15 equiv must refuse");
    assert!(certify("R2EmptyChoose", r2_15, cfg, group).is_none(), "R2-#15 top-level must refuse");
}

#[test]
fn round3_codex_astra_all_regressions_refuse_and_terminate() {
    let group = &[vec!["p1".into(), "p2".into(), "p3".into()]];
    let cfg = "CONSTANTS Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";

    // R3-#1: primed equality after `UNCHANGED` is a comparison, not an assignment.
    let r3_1 = r#"---- MODULE R3BoundPrimedEq ----
CONSTANTS Proc
VARIABLES owner, f
Init == owner \in Proc /\ f = [p \in Proc |-> 1]
Next == UNCHANGED <<owner, f>> /\ f' = [p \in Proc |-> IF p = owner THEN 0 ELSE "a"]
Inv == TRUE
====
"#;
    assert!(certify("R3BoundPrimedEq", r3_1, cfg, group).is_none(), "R3-#1 must refuse");

    // R3-#2: computed expression inside `UNCHANGED` must be checked in both states.
    let r3_2 = r#"---- MODULE R3UnchangedExpr ----
CONSTANTS Proc
VARIABLES owner, f
Init == owner \in Proc /\ f = [p \in Proc |-> 1]
Next == UNCHANGED <<owner, f>> /\ UNCHANGED (f # [p \in Proc |-> IF p = owner THEN 0 ELSE "a"])
Inv == TRUE
====
"#;
    assert!(certify("R3UnchangedExpr", r3_2, cfg, group).is_none(), "R3-#2 must refuse");

    // R3-#3: `p \in SUBSET Proc` errors on untyped model value `p` (must not use equality comparability).
    let r3_3 = r#"---- MODULE R3SubsetMember ----
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = p \/ p \in SUBSET Proc
====
"#;
    assert!(certify("R3SubsetMember", r3_3, cfg, group).is_none(), "R3-#3 must refuse");

    // R3-#4: EXCEPT index type must match container (string index on tuple, int index on record).
    let r3_4a = r#"---- MODULE R3ExceptTupleStr ----
CONSTANTS Proc
VARIABLES owner, f
Init == owner \in Proc /\ f = <<1>>
Next == UNCHANGED <<owner, f>>
Inv == \E p \in Proc : owner = p \/ [f EXCEPT !["a"] = 1] = f
====
"#;
    assert!(certify("R3ExceptTupleStr", r3_4a, cfg, group).is_none(), "R3-#4a must refuse");

    let r3_4b = r#"---- MODULE R3ExceptRecInt ----
CONSTANTS Proc
VARIABLES owner, f
Init == owner \in Proc /\ f = [a |-> 1]
Next == UNCHANGED <<owner, f>>
Inv == \E p \in Proc : owner = p \/ [f EXCEPT ![1] = 2] = f
====
"#;
    assert!(certify("R3ExceptRecInt", r3_4b, cfg, group).is_none(), "R3-#4b must refuse");

    // R3-#5: Boolean singleton `TRUE :> 1` must not claim `exact_dom` over all of `BOOLEAN`.
    let r3_5 = r#"---- MODULE R3BoolSingleton ----
EXTENDS TLC
CONSTANTS Proc
VARIABLES owner, f
Init == owner \in Proc /\ f = (TRUE :> 1)
Next == UNCHANGED <<owner, f>>
Inv == \E p \in Proc : owner = p \/ f[FALSE] = 1
====
"#;
    assert!(certify("R3BoolSingleton", r3_5, cfg, group).is_none(), "R3-#5 must refuse");

    // R3-#6: Union of tuples `({"a"} \X {"a"}) \cup ({"b"} \X {"b"})` must not lose correlation.
    let r3_6 = r#"---- MODULE R3TupleCup ----
CONSTANTS Proc
VARIABLES owner, f
Init == owner \in Proc /\ f = [x \in ({"a"} \X {"a"}) \cup ({"b"} \X {"b"}) |-> 1]
Next == UNCHANGED <<owner, f>>
Inv == \E p \in Proc : owner = p \/ f[<<"a", "b">>] = 1
====
"#;
    assert!(certify("R3TupleCup", r3_6, cfg, group).is_none(), "R3-#6 must refuse");

    // R3-#7: Extensionally equal `Func` and `Tuple` must not be treated as disjoint in narrowing.
    let r3_7 = r#"---- MODULE R3ExtEqNarrow ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLES owner, f
Init == owner \in Proc /\ f = [i \in 1..1 |-> 0]
Next == UNCHANGED owner /\ f' = owner
Inv == \E p \in Proc : owner = p \/ (f = <<0>> /\ f)
====
"#;
    assert!(certify("R3ExtEqNarrow", r3_7, cfg, group).is_none(), "R3-#7 must refuse");

    // R3-#8: Recursive CHOOSE fold defined on `SUBSET leaders` applied to `Proc` must refuse.
    let r3_8 = r#"---- MODULE R3FoldDomIncl ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLES owner, leaders, votes
Sum(T) ==
  LET s[S \in SUBSET leaders] ==
        IF S = {} THEN 0
        ELSE LET p == CHOOSE x \in S : TRUE IN votes[p] + s[S \ {p}]
  IN s[T]
Init == owner \in Proc /\ leaders = {owner} /\ votes = [p \in Proc |-> 1]
Next == UNCHANGED <<owner, leaders, votes>>
Inv == Sum(Proc) >= 0
====
"#;
    assert!(certify("R3FoldDomIncl", r3_8, cfg, group).is_none(), "R3-#8 must refuse");

    // R3-#9: `Len("abc")` on a string must not emit sequence `Expr.len`.
    let r3_9 = r#"---- MODULE R3StrLen ----
EXTENDS Sequences
CONSTANTS Proc
VARIABLES owner, f
Init == owner \in {<<p>> : p \in Proc} /\ f = 0
Next == UNCHANGED owner /\ f' = Len("abc")
Inv == TRUE
====
"#;
    assert!(certify_equiv_direct("R3StrLen", r3_9, cfg, group).is_none(), "R3-#9 must refuse");

    // R3-#10 & #11: Self-nesting tuple growth (`f' = <<f, f>>`) and `SUBSET (1..32)` must not OOM or panic.
    let r3_10 = r#"---- MODULE R3GrowthAndShift ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLES owner, f, s
Init == owner \in Proc /\ f = 0 /\ s = SUBSET (1..32)
Next == UNCHANGED <<owner, s>> /\ (FALSE /\ f' = <<f, f>>)
Inv == TRUE
====
"#;
    let _ = certify("R3GrowthAndShift", r3_10, cfg, group);
}

#[test]
fn round4_codex_astra_all_regressions_refuse() {
    let group = &[vec!["p1".into(), "p2".into(), "p3".into()]];
    let cfg = "CONSTANTS Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";

    // R4-#1: Caller `@` passed into an operator containing another `EXCEPT` must not be captured.
    let r4_1 = r#"---- MODULE R4AtCapture ----
EXTENDS Integers, Sequences
CONSTANTS Proc
VARIABLE owner
Box(v) == [<<1>> EXCEPT ![1] = v]
N == [<<0>> EXCEPT ![1] = Box(@)[1]][1]
Init == owner \in {<<p>> : p \in Proc}
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = <<p>> \/ 1 \div N = 0
====
"#;
    assert!(certify("R4AtCapture", r4_1, cfg, group).is_none(), "R4-#1 must refuse");

    // R4-#2: Record-set membership checks matching prefix fields before stopping at a name mismatch.
    let r4_2 = r#"---- MODULE R4RecSetOrder ----
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = p \/ [a |-> "bad", c |-> 0] \in [a : {1}, b : {0}]
====
"#;
    assert!(certify("R4RecSetOrder", r4_2, cfg, group).is_none(), "R4-#2 must refuse");

    // R4-#3: `IsInjective` on assignment RHS must check range self-comparability.
    let r4_3 = r#"---- MODULE R4IsInjRhs ----
EXTENDS Functions, FiniteSets
CONSTANTS Proc
VARIABLES owner, ok
Init == owner \in {S \in SUBSET Proc : Cardinality(S) = 2} /\ ok = TRUE
Next == UNCHANGED owner /\ ok' = IsInjective([p \in Proc |-> IF p \in owner THEN "a" ELSE 0])
Inv == ok \in BOOLEAN
====
"#;
    assert!(certify("R4IsInjRhs", r4_3, cfg, group).is_none(), "R4-#3 must refuse");

    // R4-#4: Orbit-canonicalized state variable with incomparable mixed range must refuse.
    let r4_4 = r#"---- MODULE R4OrbitCmp ----
CONSTANTS Proc
VARIABLE f
Init == f = [p \in Proc |-> 1]
Next == \E r \in Proc : f' = [p \in Proc |-> IF p = r THEN 1 ELSE "no"]
Inv == TRUE
====
"#;
    assert!(certify("R4OrbitCmp", r4_4, cfg, group).is_none(), "R4-#4 must refuse");

    // R4-#5: String `Tail`/`Concat`/`SubSeq` must not lower to sequence-only Lean IR.
    let r4_5 = r#"---- MODULE R4StrTail ----
EXTENDS Sequences
CONSTANTS Proc
VARIABLES owner, s
Init == owner \in {<<p>> : p \in Proc} /\ s = "ab"
Next == UNCHANGED owner /\ s' = Tail("ab")
Inv == TRUE
====
"#;
    assert!(certify_equiv_direct("R4StrTail", r4_5, cfg, group).is_none(), "R4-#5 must refuse");
}

#[test]
fn round5_codex_astra_all_regressions_refuse() {
    let group = &[vec!["p1".into(), "p2".into(), "p3".into()]];
    let cfg = "CONSTANTS Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";

    // R5-#1: Nested membership `<<p>> \in Seq(SUBSET {1})` errors on non-set `p`.
    let r5_1 = r#"---- MODULE R5NestedSeqMember ----
EXTENDS Sequences
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = p \/ <<p>> \in Seq(SUBSET {1})
====
"#;
    assert!(certify("R5NestedSeqMember", r5_1, cfg, group).is_none(), "R5-#1 must refuse");

    // R5-#2: Set comparison `[1..32 -> BOOLEAN] = {}` overflows 32-bit cardinality.
    let r5_2 = r#"---- MODULE R5SetCardEq ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = p \/ [1..32 -> BOOLEAN] = {}
====
"#;
    assert!(certify("R5SetCardEq", r5_2, cfg, group).is_none(), "R5-#2 must refuse");

    // R5-#3: Extra Init guard constraining nondeterministic flags must refuse.
    let r5_3 = r#"---- MODULE R5InitFlagGuard ----
CONSTANTS Proc, Offers
VARIABLES owner, leaders
Init == owner \in Proc /\ leaders \in Offers /\ ~(owner \notin leaders)
Next == owner' = (CHOOSE q \in Proc : q \in leaders) /\ UNCHANGED leaders
Inv == owner \in leaders
====
"#;
    let r5_3_cfg = "CONSTANTS Proc = {p1, p2, p3} Offers = {{p1}, {p2}, {p3}}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    assert!(certify("R5InitFlagGuard", r5_3, r5_3_cfg, group).is_none(), "R5-#3 must refuse");

    // R5-#4: Guard after potentially failing CHOOSE must not be hoisted into preGuard.
    let r5_4 = r#"---- MODULE R5ChooseGuardOrder ----
CONSTANTS Proc, Offers
VARIABLES owner, leaders
Init == owner \in Proc /\ (leaders = {} \/ leaders \in Offers)
Next == owner' = (CHOOSE q \in Proc : q \in leaders) /\ FALSE /\ UNCHANGED leaders
Inv == owner \in Proc
====
"#;
    let r5_4_cert = certify("R5ChooseGuardOrder", r5_4, r5_3_cfg, group);
    if let Some(proof) = r5_4_cert {
        assert!(!proof.contains("preGuard := (PureTest.truth false)"), "R5-#4 must not hoist FALSE before CHOOSE:\n{proof}");
    }

    // R5-#5: Assignment RHS `n' = 1 \div 0` must refuse.
    let r5_5 = r#"---- MODULE R5RhsDivZero ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLES s, n
Init == s \in {<<p>> : p \in Proc} /\ n = 0
Next == UNCHANGED s /\ n' = 1 \div 0
Inv == TRUE
====
"#;
    assert!(certify("R5RhsDivZero", r5_5, cfg, group).is_none(), "R5-#5 must refuse");
}

#[test]
fn round6_codex_astra_all_regressions_refuse() {
    let group = &[vec!["p1".into(), "p2".into(), "p3".into()]];
    let cfg = "CONSTANTS Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";

    // R6-#1: Eager union construction `{1} \cup {"a"}` errors even if membership is checked per operand.
    let r6_1 = r#"---- MODULE R6CupMerge ----
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : p = owner \/ p \in ({1} \cup {"a"})
====
"#;
    assert!(certify("R6CupMerge", r6_1, cfg, group).is_none(), "R6-#1 must refuse");

    // R6-#2: Lazy-set membership preconditions through IF (`p \in IF ... THEN SUBSET {1} ELSE SUBSET {2}`).
    let r6_2 = r#"---- MODULE R6IfSubset ----
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : p = owner \/ p \in (IF TRUE THEN SUBSET {1} ELSE SUBSET {2})
====
"#;
    assert!(certify("R6IfSubset", r6_2, cfg, group).is_none(), "R6-#2 must refuse");

    // R6-#3: Nested set-cardinality overflow during set normalization `{[1..32 -> BOOLEAN], {}}`.
    let r6_3 = r#"---- MODULE R6SetNormCard ----
EXTENDS Naturals, FiniteSets
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : p = owner \/ Cardinality({[1..32 -> BOOLEAN], {}}) > 0
====
"#;
    assert!(certify("R6SetNormCard", r6_3, cfg, group).is_none(), "R6-#3 must refuse");

    // R6-#4: Empty-domain function set `[D -> {}]` has cardinality 1 (overflows `2147483647 + ...`).
    let r6_4 = r#"---- MODULE R6EmptyFnSetCard ----
EXTENDS Integers, FiniteSets
CONSTANTS Proc
VARIABLE holder
D == {q \in Proc : q # q}
Init == holder \in Proc
Next == UNCHANGED holder
Inv == \E p \in Proc : p = holder \/ 2147483647 + Cardinality([D -> {}]) = 0
====
"#;
    assert!(certify("R6EmptyFnSetCard", r6_4, cfg, group).is_none(), "R6-#4 must refuse");

    // R6-#5: Post-CHOOSE guard after a CHOOSE-bearing assignment must refuse.
    let r6_5_cfg = "CONSTANTS Proc = {p1, p2, p3} Offers = {{p1}, {p2}, {p3}}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    let r6_5 = r#"---- MODULE R6ChooseSlotOrder ----
CONSTANTS Proc, Offers
VARIABLES owner, leaders
Init == owner \in Proc /\ (leaders = {} \/ leaders \in Offers)
Next == owner' = (CHOOSE q \in Proc : q \in leaders) /\ FALSE /\ UNCHANGED leaders
Inv == owner \in Proc
====
"#;
    assert!(certify("R6ChooseSlotOrder", r6_5, r6_5_cfg, group).is_none(), "R6-#5 must refuse");

    // R6-#6: Fresh `n' \in Nat` in `Next` is not finitely enumerable and must refuse.
    let r6_6 = r#"---- MODULE R6NextInNat ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLES owner, n
Init == owner \in Proc /\ n = 0
Next == UNCHANGED owner /\ n' \in Nat
Inv == TRUE
====
"#;
    assert!(certify("R6NextInNat", r6_6, cfg, group).is_none(), "R6-#6 must refuse");
}

#[test]
fn round7_codex_astra_all_regressions_refuse() {
    let cfg = "CONSTANTS Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    let group = &[vec!["p1".into(), "p2".into(), "p3".into()]];

    // R7-#1: DOMAIN over a record with a partial field must not be treated as a total exact_set.
    let r7_1_cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    let r7_1 = r#"---- MODULE R7DomainPartialRecord ----
EXTENDS Integers, Sequences
VARIABLE q
Init == q = <<>>
Next == Len(q) = 0 /\ (q' = Append(q, "a") \/ q' = Append(q, "b"))
Inv == Len(q) = 0 \/ q \in Seq(DOMAIN [a |-> IF q[1] = "a" THEN 1 ELSE 1 \div 0, b |-> 0])
====
"#;
    let dir_r7_1 = tlx_testkit::TempDir::new("r7-domain-partial");
    let path_r7_1 = dir_r7_1.write("R7DomainPartialRecord.tla", r7_1);
    let mut p_r7_1 = Program::load(&path_r7_1, &[]).unwrap();
    p_r7_1.resolve_all_root();
    let roots_r7_1 = ["Init", "Next", "Inv"].map(|root| {
        let Some(RootSymbol::Def(id)) = p_r7_1.lookup_root(root) else { panic!("missing {root}") };
        Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p_r7_1.defs[id.idx()].span)
    });
    let plan_r7_1 = tlx_sema::optimize::sequence_length_projection(
        &p_r7_1,
        &parse_cfg(r7_1_cfg).unwrap(),
        &roots_r7_1[0],
        &roots_r7_1[1],
        &roots_r7_1[2..],
    );
    assert!(plan_r7_1.is_none(), "R7-#1 must not project away partial DOMAIN record check");

    // R7-#2: Nested lazy membership hidden behind function application `[x \in {1} |-> [Proc -> SUBSET {1}]][1]`.
    let r7_2 = r#"---- MODULE R7NestedLazyApp ----
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = p \/ [q \in Proc |-> p] \in [x \in {1} |-> [Proc -> SUBSET {1}]][1]
====
"#;
    assert!(certify("R7NestedLazyApp", r7_2, cfg, group).is_none(), "R7-#2 must refuse");

    // R7-#3: IsInjective compares range values via eq_tlc, so range set cardinalities must be <= i32::MAX.
    let r7_3 = r#"---- MODULE R7IsInjectiveCard ----
EXTENDS Naturals, Functions
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = p \/ IsInjective([q \in Proc |-> IF p = q THEN [1..32 -> BOOLEAN] ELSE {}])
====
"#;
    assert!(certify("R7IsInjectiveCard", r7_3, cfg, group).is_none(), "R7-#3 must refuse");

    // R7-#4: CHOOSE inside a conditionally evaluated EXCEPT update must not be hoisted unconditionally.
    let r7_4 = r#"---- MODULE R7ChooseInExcept ----
EXTENDS Naturals, Sequences
CONSTANTS Proc
VARIABLE msgs
Init == msgs = {[from |-> p, val |-> 7] : p \in Proc}
Next == UNCHANGED msgs
Inv == [<<0>> EXCEPT ![2] = (CHOOSE m \in msgs : m.val = 8).val] = <<0>>
====
"#;
    assert!(certify("R7ChooseInExcept", r7_4, cfg, group).is_none(), "R7-#4 must refuse");

    // R7-#5: Assignment RHS arithmetic must be overflow-free (`2147483647 + 1` overflows i32).
    let r7_5 = r#"---- MODULE R7RhsArithOverflow ----
EXTENDS Integers
CONSTANTS Proc
VARIABLES owner, x
Init == \E p \in Proc : owner = <<p>> /\ x = <<0>>
Next == UNCHANGED owner /\ x' = <<2147483647 + 1>>
Inv == TRUE
====
"#;
    assert!(certify("R7RhsArithOverflow", r7_5, cfg, group).is_none(), "R7-#5 must refuse");
}

#[test]
fn round8_codex_astra_all_regressions_refuse() {
    let cfg = "CONSTANTS Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    let group = &[vec!["p1".into(), "p2".into(), "p3".into()]];

    // R8-#1: Self-read of unbound primed variable inside assignment RHS `ok' = (... \/ ok')`.
    let r8_1 = r#"---- MODULE R8UnboundPrimedRead ----
CONSTANTS Proc
VARIABLES owner, ok
Init == owner \in Proc /\ ok = TRUE
Next == ok' = (\E p \in Proc : owner = p \/ ok') /\ UNCHANGED owner
Inv == TRUE
====
"#;
    assert!(certify("R8UnboundPrimedRead", r8_1, cfg, group).is_none(), "R8-#1 must refuse");

    // R8-#2: Eager union construction `{1} \cup {"s"}` inside a RecordSet membership domain.
    let r8_2 = r#"---- MODULE R8RecordSetCup ----
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = p \/ p \in [k : {1} \cup {"s"}]
====
"#;
    assert!(certify("R8RecordSetCup", r8_2, cfg, group).is_none(), "R8-#2 must refuse");

    // R8-#3: Record membership shared-field comparison regardless of Sym intern order.
    let r8_3 = r#"---- MODULE R8RecordInternOrder ----
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = p \/ [z |-> "x", a |-> 7] \in [z : {1}, b : {2}]
====
"#;
    assert!(certify("R8RecordInternOrder", r8_3, cfg, group).is_none(), "R8-#3 must refuse");

    // R8-#4: Lazy RecordSet membership hidden behind function application.
    let r8_4 = r#"---- MODULE R8LazyRecordSetApp ----
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = p \/ [a |-> "x", c |-> 7] \in ([i \in Proc |-> [a : {1}, b : {2}]])[p]
====
"#;
    assert!(certify("R8LazyRecordSetApp", r8_4, cfg, group).is_none(), "R8-#4 must refuse");

    // R8-#5: Nested EXCEPT reading original `m[p]` must not flatten onto earlier overlapping `![p].a = 1`.
    let r8_5 = r#"---- MODULE R8NestedExceptSourceBase ----
CONSTANTS Proc
VARIABLE m
Init == m = [p \in Proc |-> [a |-> 0, b |-> 0]]
Next == \E p \in Proc : m' = [m EXCEPT ![p].a = 1, ![p] = [m[p] EXCEPT !.b = 2]]
Inv == \A p \in Proc : m[p].a = 0
====
"#;
    let dir_r8_5 = tlx_testkit::TempDir::new("r8-nested-except");
    let path_r8_5 = dir_r8_5.write("R8NestedExceptSourceBase.tla", r8_5);
    let mut p_r8_5 = Program::load(&path_r8_5, &[]).unwrap();
    p_r8_5.resolve_all_root();
    let Some(RootSymbol::Def(next_id)) = p_r8_5.lookup_root("Next") else { panic!("missing Next") };
    let next_expr = Expr::new(ExprKind::Apply { op: OpRef::Def(next_id), args: vec![] }, p_r8_5.defs[next_id.idx()].span);
    let mut norm = tlx_sema::optimize::SymNormalizer::new(&p_r8_5);
    let expanded = norm.normalize(&next_expr).expect("normalize");
    // The second update must remain a replacement `![p] = [m[p] EXCEPT !.b = 2]`, not flattened `![p].b = 2`.
    let dbg = format!("{expanded:?}");
    assert!(dbg.contains("FnApp"), "R8-#5 must preserve original m[p] base in second EXCEPT update: {dbg}");

    // R8-#6: Already-bound `UNCHANGED x` after `x' \in {1}` and a CHOOSE-bearing assignment must refuse.
    let r8_6 = r#"---- MODULE R8UnchangedAfterChoose ----
CONSTANTS Proc
VARIABLES owner, x
Init == owner \in Proc /\ x = 0
Next == x' \in {1} /\ owner' = (CHOOSE p \in Proc : p = owner /\ FALSE) /\ UNCHANGED x
Inv == TRUE
====
"#;
    assert!(certify("R8UnchangedAfterChoose", r8_6, cfg, group).is_none(), "R8-#6 must refuse");

    // Self-audit #1: Unbound self-read in Init `ok = (\E p \in Proc : owner = p \/ ok)` must refuse.
    let self_1 = r#"---- MODULE SelfAuditInitUnboundRead ----
CONSTANTS Proc
VARIABLES owner, ok
Init == owner \in Proc /\ ok = (\E p \in Proc : owner = p \/ ok)
Next == UNCHANGED <<owner, ok>>
Inv == TRUE
====
"#;
    assert!(certify("SelfAuditInitUnboundRead", self_1, cfg, group).is_none(), "Self-audit #1 must refuse");

    // Self-audit #2: `[1..32 -> BOOLEAN] \in SUBSET [1..32 -> BOOLEAN]` overflows enumeration and must refuse.
    let self_2 = r#"---- MODULE SelfAuditSubsetOverflow ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = p \/ [1..32 -> BOOLEAN] \in SUBSET [1..32 -> BOOLEAN]
====
"#;
    assert!(certify("SelfAuditSubsetOverflow", self_2, cfg, group).is_none(), "Self-audit #2 must refuse");
}

#[test]
fn round9_codex_astra_all_regressions_refuse() {
    let cfg = "CONSTANTS Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    let group = &[vec!["p1".into(), "p2".into(), "p3".into()]];

    let seq_projection = |name: &str, tla: &str| -> bool {
        let dir = tlx_testkit::TempDir::new(name);
        let path = dir.write(&format!("{name}.tla"), tla);
        let mut prog = Program::load(&path, &[]).unwrap();
        prog.resolve_all_root();
        let roots = ["Init", "Next", "Inv"].map(|root| {
            let Some(RootSymbol::Def(id)) = prog.lookup_root(root) else { panic!("missing {root}") };
            Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, prog.defs[id.idx()].span)
        });
        tlx_sema::optimize::sequence_length_projection(
            &prog,
            &parse_cfg("INIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap(),
            &roots[0],
            &roots[1],
            &roots[2..],
        )
        .is_some()
    };

    // R9-#1: `Cap` and `SetMinus` call `member` on the other operand (`{p} \cap SUBSET {1}`, `{p} \ SUBSET {1}`).
    for (name, set_op) in [
        ("R9CapSubsetMember", "({p} \\cap SUBSET {1}) = {}"),
        ("R9CapSubsetMemberRev", "(SUBSET {1} \\cap {p}) = {}"),
        ("R9DiffSubsetMember", "({p} \\ SUBSET {1}) = {p}"),
    ] {
        let src = format!(
            "---- MODULE {name} ----\nEXTENDS Naturals\nCONSTANTS Proc\nVARIABLE owner\n\
             Init == \\E p \\in Proc : owner = <<p>>\nNext == UNCHANGED owner\n\
             Inv == \\E p \\in Proc : owner = <<p>> \\/ {set_op}\n====\n"
        );
        assert!(certify(name, &src, cfg, group).is_none(), "{name} must refuse");
    }

    // R9-#2 + structural lazy sets: `UNION`, `SetFilter`, `kSubset`, and `Product` lazy membership checks.
    for (name, expr) in [
        ("R9UnionLazySubset", "p \\in UNION {SUBSET Proc}"),
        ("R9FilterLazySubset", "p \\in {x \\in SUBSET {1} : TRUE}"),
        ("R9KSubsetMember", "p \\in kSubset(1, {1, 2})"),
        ("R9UnionLazyProductFcn", "[q \\in Proc |-> 1] \\in UNION {{1} \\X {1}}"),
        ("R9DomainLazyFcnSubset", "p \\in DOMAIN [x \\in SUBSET {1} |-> 0]"),
    ] {
        let src = format!(
            "---- MODULE {name} ----\nEXTENDS Naturals, FiniteSets, FiniteSetsExt\nCONSTANTS Proc\nVARIABLE owner\n\
             Init == \\E p \\in Proc : owner = <<p>>\nNext == UNCHANGED owner\n\
             Inv == \\E p \\in Proc : owner = <<p>> \\/ {expr}\n====\n"
        );
        assert!(certify(name, &src, cfg, group).is_none(), "{name} must refuse");
    }

    // R9-#3: `EXCEPT` index must inhabit the runtime domain representation (never untyped model values on
    // interval/empty/string functions, nor incompatible shared record fields on lazy record-domain functions).
    for (name, expr) in [
        ("R9ExceptIntInterval", "[[i \\in 2..3 |-> i] EXCEPT ![p] = 0] = [i \\in 2..3 |-> i]"),
        ("R9ExceptEmptyInterval", "[[i \\in 2..1 |-> i] EXCEPT ![p] = 0] = <<>>"),
        ("R9ExceptStrDomain", "[[s \\in {\"a\"} |-> 0] EXCEPT ![p] = 0] = [s \\in {\"a\"} |-> 0]"),
        (
            "R9ExceptLazyRecordDom",
            "[[r \\in [a : {1}, b : {2}] |-> 0] EXCEPT ![[a |-> \"x\", c |-> 7]] = 1] = [r \\in [a : {1}, b : {2}] |-> 0]",
        ),
    ] {
        let src = format!(
            "---- MODULE {name} ----\nEXTENDS Naturals\nCONSTANTS Proc\nVARIABLE owner\n\
             Init == \\E p \\in Proc : owner = <<p>>\nNext == UNCHANGED owner\n\
             Inv == \\E p \\in Proc : owner = <<p>> \\/ {expr}\n====\n"
        );
        assert!(certify(name, &src, cfg, group).is_none(), "{name} must refuse");
    }

    // R9-#4 + structural set-cardinality ban: oversized `FnSet`, `Times`, `RecordSet`, and `FnConstruct` domains must refuse.
    for (name, expr) in [
        ("R9FnSetDomCardOverflow", "<<>> \\in [[1..32 -> BOOLEAN] -> Nat]"),
        ("R9FnSetSingletonRangeOverflow", "<<>> \\in [[1..32 -> BOOLEAN] -> {0}]"),
        ("R9FnSetValueCardOverflow", "[1..32 -> BOOLEAN] = {}"),
        ("R9TimesCardOverflow", "((1..50000) \\X (1..50000)) = {}"),
        ("R9RecordSetCardOverflow", "[a : 1..50000, b : 1..50000] = {}"),
        ("R9FnConstructCardOverflow", "([x \\in 1..50000, y \\in 1..50000 |-> 0])[1, 1] = 0"),
    ] {
        let src = format!(
            "---- MODULE {name} ----\nEXTENDS Naturals, Sequences\nCONSTANTS Proc\nVARIABLE owner\n\
             Init == \\E p \\in Proc : owner = <<p>>\nNext == UNCHANGED owner\n\
             Inv == \\E p \\in Proc : owner = <<p>> \\/ {expr}\n====\n"
        );
        assert!(certify(name, &src, cfg, group).is_none(), "{name} must refuse");
    }

    // R9-#5: Partial `IF` interval endpoint in `domain.rs` must not let sequence-length projection erase `1 \div 0`.
    let r9_5 = r#"---- MODULE R9PartialIntervalEndpoint ----
EXTENDS Integers, Sequences
VARIABLE q
Init == q = <<>>
Next == Len(q) = 0 /\ q' = Append(q, 2)
Inv == Len(q) = 0 \/ q \in Seq(0..(IF 1 \div (q[1] - 2) = 4 THEN 2 ELSE 2))
====
"#;
    assert!(!seq_projection("R9PartialIntervalEndpoint", r9_5), "R9-#5 must not project away partial interval endpoint");

    // R9-#6: Incompatible shared field `a` across equal-length record-union alternatives in `domain.rs` must refuse.
    let r9_6 = r#"---- MODULE R9RecordUnionSharedField ----
EXTENDS Naturals, Sequences
VARIABLE q
Init == q = <<>>
Next == Len(q) = 0 /\ (q' = Append(q, [a |-> 1, b |-> 0]) \/ q' = Append(q, [a |-> "x", c |-> 0]))
Inv == Len(q) = 0 \/ q \in Seq([a : {1}, b : {0}] \cup [a : {"x"}, c : {0}])
====
"#;
    assert!(!seq_projection("R9RecordUnionSharedField", r9_6), "R9-#6 must refuse incompatible shared record field");

    // R9-#7: Incomplete variable assignments on a disjunct (`Init == ... \/ TRUE`, `Next == ... \/ TRUE`) must refuse.
    let r9_7_init = r#"---- MODULE R9IncompleteInit ----
CONSTANTS Proc
VARIABLE owner
Init == (\E p \in Proc : owner = <<p>>) \/ TRUE
Next == UNCHANGED owner
Inv == TRUE
====
"#;
    assert!(certify("R9IncompleteInit", r9_7_init, cfg, group).is_none(), "R9-#7 incomplete Init must refuse");

    let r9_7_next = r#"---- MODULE R9IncompleteNext ----
CONSTANTS Proc
VARIABLE owner
Init == \E p \in Proc : owner = <<p>>
Next == (\E p \in Proc : owner' = <<p>>) \/ TRUE
Inv == TRUE
====
"#;
    assert!(certify("R9IncompleteNext", r9_7_next, cfg, group).is_none(), "R9-#7 incomplete Next must refuse");

    // R10-#3: Lexical `EXCEPT` `@` inside a `LAMBDA` or `LET` definition must not rebind to an inner `EXCEPT`.
    let r10_3_lambda = r#"---- MODULE R10ExceptLambdaAt ----
EXTENDS Naturals, Sequences
CONSTANTS Proc
VARIABLE owner
Put(F(_)) == [<<1>> EXCEPT ![1] = F(0)]
Init == \E p \in Proc : owner = <<p>>
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = <<p>> \/ 1 \div ([<<0>> EXCEPT ![1] = Put(LAMBDA u : @)][1][1]) = 1
====
"#;
    assert!(certify("R10ExceptLambdaAt", r10_3_lambda, cfg, group).is_none(), "R10-#3 lambda @ across nested EXCEPT must refuse");

    let r10_3_let = r#"---- MODULE R10ExceptLetAt ----
EXTENDS Naturals, Sequences
CONSTANTS Proc
VARIABLE owner
Init == \E p \in Proc : owner = <<p>>
Next == UNCHANGED owner
Inv == \E p \in Proc : owner = <<p>> \/ 1 \div ([<<0>> EXCEPT ![1] = LET x == @ IN [<<1>> EXCEPT ![1] = x]][1][1]) = 1
====
"#;
    assert!(certify("R10ExceptLetAt", r10_3_let, cfg, group).is_none(), "R10-#3 LET @ across nested EXCEPT must refuse");

    // R13-#2: Provably absent non-model EXCEPT key on a non-empty exact untyped model-value map
    // (`[m EXCEPT ![0] = 0]` on `m = [p \in Proc |-> p]`) is total and certifies, while typed
    // model values, possibly-empty dynamic maps, and out-of-domain `FnApp` (`m[0]`) still refuse.
    let r13_2_ok = r#"---- MODULE R13UntypedModelAbsentExcept ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLE m
Init == m = [p \in Proc |-> p]
Next == m' = [m EXCEPT ![0] = 0]
Inv == \A p \in Proc : m[p] = p
====
"#;
    assert!(
        certify("R13UntypedModelAbsentExcept", r13_2_ok, cfg, group).is_some(),
        "R13-#2 absent integer EXCEPT key on non-empty untyped model-value map should certify"
    );

    let typed_cfg = "CONSTANTS Proc = {P_1, P_2, P_3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    let typed_group = &[vec!["P_1".into(), "P_2".into(), "P_3".into()]];
    assert!(
        certify("R13UntypedModelAbsentExcept", r13_2_ok, typed_cfg, typed_group).is_none(),
        "R13-#2 typed model-value map must refuse non-model EXCEPT key"
    );

    // R13-#2 / R15-#4: Dynamic subset `s \in SUBSET Proc` actively exercises `Proc` and makes both
    // empty (`<<>>` in -compile) and non-empty maps reachable: string `EXCEPT` refuses, while a
    // safe update on the identical initial state certifies.
    let r13_2_empty_dyn = r#"---- MODULE R13DynamicEmptyModelMapExcept ----
CONSTANTS Proc
VARIABLES s, m
Init == s \in SUBSET Proc /\ m = [p \in s |-> p]
Next == s' = s /\ m' = [m EXCEPT !["a"] = "a"]
Inv == m = [p \in s |-> p]
====
"#;
    assert!(
        certify("R13DynamicEmptyModelMapExcept", r13_2_empty_dyn, cfg, group).is_none(),
        "R13-#2 possibly-empty map (decoded as <<>> in -compile) must refuse string EXCEPT key"
    );
    let r13_2_empty_dyn_safe = r#"---- MODULE R13DynamicEmptyModelMapSafe ----
CONSTANTS Proc
VARIABLES s, m
Init == s \in SUBSET Proc /\ m = [p \in s |-> p]
Next == s' = s /\ m' = m
Inv == m = [p \in s |-> p]
====
"#;
    assert!(
        certify("R13DynamicEmptyModelMapSafe", r13_2_empty_dyn_safe, cfg, group).is_some(),
        "R15-#4 control fixture with safe update must certify so R13DynamicEmptyModelMapExcept tests EXCEPT"
    );

    let r13_2_fnapp = r#"---- MODULE R13UntypedModelOobFnApp ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLE m
Init == m = [p \in Proc |-> p]
Next == UNCHANGED m
Inv == m[0] = 0
====
"#;
    assert!(
        certify("R13UntypedModelOobFnApp", r13_2_fnapp, cfg, group).is_none(),
        "R13-#2 out-of-domain function application m[0] must still refuse"
    );

    // R14-#1: Signed interval `[-1, 1]` straddling valid index `1` of a 1-element tuple must NOT
    // wrap `-1 as usize` into `usize::MAX > 1` and skip totality checking on `1 \div 0`.
    let r14_1 = r#"---- MODULE R14StraddlingTupleExcept ----
EXTENDS Integers
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == UNCHANGED owner
Inv == \A p \in Proc : owner = p \/ (\A i \in -1..1 : [<<0>> EXCEPT ![i] = 1 \div 0] = <<0>>)
====
"#;
    assert!(
        certify("R14StraddlingTupleExcept", r14_1, cfg, group).is_none(),
        "R14-#1 signed interval [-1, 1] straddling tuple index 1 must refuse partial EXCEPT rhs"
    );

    // R15-#1: Right-hand target variable (`Next == owner = owner'` or `Init == p = owner`) is
    // evaluated as a test on an unassigned variable by `Enumerator::assign_eq` and must refuse.
    let r15_1_next = r#"---- MODULE R15ReversedNextEq ----
CONSTANTS Proc
VARIABLE owner
Init == owner \in Proc
Next == owner = owner'
Inv == owner \in Proc
====
"#;
    assert!(certify("R15ReversedNextEq", r15_1_next, cfg, group).is_none(), "R15-#1 reversed primed equality `owner = owner'` must refuse");

    let r15_1_init = r#"---- MODULE R15ReversedInitEq ----
CONSTANTS Proc
VARIABLE owner
Init == \E p \in Proc : p = owner
Next == owner' \in Proc
Inv == owner \in Proc
====
"#;
    assert!(certify("R15ReversedInitEq", r15_1_init, cfg, group).is_none(), "R15-#1 reversed Init equality `p = owner` must refuse");

    // R15-#2: Freshly bound `Init` variable `s = SUBSET {1}` holds a lazy powerset during `Init`
    // enumeration before `to_state` normalizes it, so `p \in s` in `Init` must refuse.
    let r15_2_init_lazy = r#"---- MODULE R15InitLazyVarMembership ----
CONSTANTS Proc
VARIABLES s, owner
Init == s = SUBSET {1} /\ owner \in Proc /\ (\E p \in Proc : p = owner \/ p \in s)
Next == UNCHANGED <<s, owner>>
Inv == owner \in Proc
====
"#;
    assert!(
        certify("R15InitLazyVarMembership", r15_2_init_lazy, cfg, group).is_none(),
        "R15-#2 freshly bound lazy powerset variable in Init must refuse non-enumerable model-value membership"
    );

    // R16-#1: Same-kind `EXCEPT` key (`p \in Proc`) on a possibly-empty map (`s \in SUBSET Proc`,
    // `m = [p \in s |-> p]`, decoded as `<<>>` when `s = {}` in `-compile`) must refuse unless
    // `p \in DOMAIN m` proves `m` non-empty.
    let r16_1_same_kind_empty = r#"---- MODULE R16DynamicEmptySameKindExcept ----
CONSTANTS Proc
VARIABLES s, m
Init == s \in SUBSET Proc /\ m = [p \in s |-> p]
Next == \E p \in Proc : s' = s /\ m' = [m EXCEPT ![p] = p]
Inv == m = [p \in s |-> p]
====
"#;
    assert!(
        certify("R16DynamicEmptySameKindExcept", r16_1_same_kind_empty, cfg, group).is_none(),
        "R16-#1 same-kind EXCEPT key on possibly-empty dynamic map must refuse"
    );

    let r16_1_dom_guarded = r#"---- MODULE R16DynamicDomGuardedExcept ----
CONSTANTS Proc
VARIABLES s, m
Init == s \in SUBSET Proc /\ m = [p \in s |-> p]
Next == (\E p \in DOMAIN m : s' = s /\ m' = [m EXCEPT ![p] = p]) \/ UNCHANGED <<s, m>>
Inv == m = [p \in s |-> p]
====
"#;
    assert!(
        certify("R16DynamicDomGuardedExcept", r16_1_dom_guarded, cfg, group).is_some(),
        "R16-#1 EXCEPT guarded by `p \\in DOMAIN m` proves non-emptiness and must certify"
    );

    // R16-#2: `s \subseteq Proc` / `s' \subseteq Proc` target assignments enumerate `powerset(Proc)`
    // (`|Proc| <= 30`) and certify, whereas `|S| > 30` (`1..31`) and reversed `Proc \subseteq s'` refuse.
    let r16_2_subseteq_ok = r#"---- MODULE R16SubsetEqAssignOk ----
CONSTANTS Proc
VARIABLE s
Init == s \subseteq Proc
Next == s' \subseteq Proc
Inv == s \subseteq Proc
====
"#;
    assert!(
        certify("R16SubsetEqAssignOk", r16_2_subseteq_ok, cfg, group).is_some(),
        "R16-#2 fresh `s \\subseteq Proc` and `s' \\subseteq Proc` assignments must certify"
    );

    let r16_2_subseteq_overflow = r#"---- MODULE R16SubsetEqOverflow ----
EXTENDS Naturals
CONSTANTS Proc
VARIABLES owner, nums
Init == owner \in Proc /\ nums \subseteq (1..31)
Next == UNCHANGED <<owner, nums>>
Inv == owner \in Proc
====
"#;
    assert!(
        certify("R16SubsetEqOverflow", r16_2_subseteq_overflow, cfg, group).is_none(),
        "R16-#2 `nums \\subseteq (1..31)` overflows 2^30 powerset enumeration and must refuse"
    );

    let r16_2_subseteq_rev = r#"---- MODULE R16SubsetEqReversed ----
CONSTANTS Proc
VARIABLE s
Init == s \subseteq Proc
Next == Proc \subseteq s'
Inv == s \subseteq Proc
====
"#;
    assert!(
        certify("R16SubsetEqReversed", r16_2_subseteq_rev, cfg, group).is_none(),
        "R16-#2 reversed `Proc \\subseteq s'` tests unassigned `s'` and must refuse"
    );

    // R17-#1: Non-nullary operator call `Id(owner') = owner` or `UNCHANGED Id(owner)` is evaluated
    // as a test on unassigned `owner'` by `Enumerator::target`/`unchanged` and must refuse, whereas
    // call-by-name action `Step(owner)` (`Step(x) == x' = x`) and already-assigned `owner' = owner /\ Id(owner') = owner` certify.
    let r17_1_id_lhs = r#"---- MODULE R17NonNullaryCallTarget ----
CONSTANTS Proc
VARIABLE owner
Id(t) == t
Init == owner \in Proc
Next == Id(owner') = owner
Inv == owner \in Proc
====
"#;
    assert!(certify("R17NonNullaryCallTarget", r17_1_id_lhs, cfg, group).is_none(), "R17-#1 `Id(owner') = owner` must refuse");

    let r17_1_unchanged_id = r#"---- MODULE R17UnchangedNonNullaryCall ----
CONSTANTS Proc
VARIABLE owner
Id(t) == t
Init == owner \in Proc
Next == UNCHANGED Id(owner)
Inv == owner \in Proc
====
"#;
    assert!(certify("R17UnchangedNonNullaryCall", r17_1_unchanged_id, cfg, group).is_none(), "R17-#1 `UNCHANGED Id(owner)` must refuse");

    let r17_1_action_call_ok = r#"---- MODULE R17ByNameActionCallOk ----
CONSTANTS Proc
VARIABLE owner
Id(t) == t
Step(x) == x' = x /\ Id(x') = x
Init == owner \in Proc
Next == Step(owner)
Inv == owner \in Proc
====
"#;
    assert!(
        certify("R17ByNameActionCallOk", r17_1_action_call_ok, cfg, group).is_some(),
        "R17-#1 call-by-name `Step(owner)` with post-assignment `Id(owner') = owner` test must certify"
    );
}
