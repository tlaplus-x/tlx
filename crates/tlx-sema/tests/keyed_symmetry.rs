use tlx_front::cfg::parse_cfg;
use tlx_sema::{
    hir::{Expr, ExprKind, OpRef, RootSymbol},
    optimize::symmetry_certificate,
    Program,
};

fn certificate_with(name: &str, spec: &str, cfg: &str, groups: &[Vec<String>]) -> Option<String> {
    let dir = tlx_testkit::TempDir::new("keyed-sema");
    let path = dir.write(&format!("{name}.tla"), spec);
    let mut p = Program::load(&path, &[]).unwrap();
    p.resolve_all_root();
    let roots = ["Init", "Next", "Inv"].map(|root| {
        let Some(RootSymbol::Def(id)) = p.lookup_root(root) else { panic!("missing {root}") };
        Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
    });
    symmetry_certificate(&p, &parse_cfg(cfg).unwrap(), &roots[0], &roots[1], &roots[2..], groups)
}

fn certificate(spec: &str) -> Option<String> {
    certificate_with("Keyed", spec, include_str!("../../../proofs/symmetry/Keyed.cfg"), &[vec!["p1".into(), "p2".into(), "p3".into()]])
}

#[test]
fn fixed_maps_have_connected_key_operations() {
    let proof = certificate(include_str!("../../../proofs/symmetry/Keyed.tla")).unwrap();
    for needle in [
        "Test.equal",
        "Test.all",
        "ValueExpr.branch",
        "Payload holes",
        "abbrev MapId := Fin 2",
        "abbrev SlotId := Fin 0",
        "theorem orbit_key_equivalent",
        "theorem counterexample_lifts",
    ] {
        assert!(proof.contains(needle), "{needle}");
    }
}

#[test]
fn scalar_optional_slot_and_slot_indexed_map_certify() {
    let proof = certificate_with(
        "ScalarSlot",
        include_str!("../../../proofs/symmetry/ScalarSlot.tla"),
        include_str!("../../../proofs/symmetry/ScalarSlot.cfg"),
        &[vec!["p1".into(), "p2".into(), "p3".into()]],
    )
    .unwrap();
    for needle in [
        "abbrev GroupCount : Nat := 1",
        "abbrev MapId := Fin 1",
        "abbrev SlotId := Fin 1",
        "KeyRef.slot",
        "KeyRef.fixed",
        "SlotExpr.fixedVal",
        "Write.point",
        "theorem orbit_key_equivalent",
    ] {
        assert!(proof.contains(needle), "missing {needle}");
    }
}

#[test]
fn product_group_sets_records_and_cardinality_certify() {
    let proof = certificate_with(
        "ProductSets",
        include_str!("../../../proofs/symmetry/ProductSets.tla"),
        include_str!("../../../proofs/symmetry/ProductSets.cfg"),
        &[vec!["c1".into(), "c2".into()], vec!["s1".into(), "s2".into()]],
    )
    .unwrap();
    for needle in [
        "abbrev GroupCount : Nat := 2",
        "Test.inGroup",
        "Test.bindCount",
        "Write.point",
        "theorem orbit_key_equivalent",
        "theorem deadlock_preserved",
    ] {
        assert!(proof.contains(needle), "missing {needle}");
    }
}

#[test]
fn multi_writer_and_whole_map_updates_certify() {
    let spec = r#"---- MODULE MultiWrite ----
EXTENDS Naturals
CONSTANT Proc
VARIABLE pc
Init == pc = [p \in Proc |-> 0]
Swap(p, q) == pc' = [pc EXCEPT ![p] = pc[q], ![q] = pc[p]]
Reset == pc = [p \in Proc |-> 1] /\ pc' = [p \in Proc |-> 0]
Next == (\E p, q \in Proc : Swap(p, q)) \/ Reset
Inv == \A p \in Proc : pc[p] \in {0, 1}
====
"#;
    let cfg = "CONSTANT Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    let proof = certificate_with("MultiWrite", spec, cfg, &[vec!["p1".into(), "p2".into(), "p3".into()]]).unwrap();
    assert!(proof.contains("Write.point"));
    assert!(proof.contains("Write.all"));
}

#[test]
fn unsupported_key_escapes_and_aliasing_are_refused() {
    let spec = include_str!("../../../proofs/symmetry/Keyed.tla");
    // Unsound CHOOSE, type-unsafe integer comparisons on keys, and primed-variable invariants must be refused by every certifier.
    for changed in [
        spec.replace("![p].n = @ + 1", "![p].n = @ + 1, ![CHOOSE q \\in Proc : TRUE].done = TRUE"),
        spec.replace("pc[p].n <= Limit", "pc[p].n <= Limit /\\ (CHOOSE q \\in Proc : TRUE) = p"),
        spec.replace("audit[p] = audit[q]", "pc' = pc"),
        // Putting a key into `pc[p].n` makes `pc[p].n <= Limit` a runtime type error inside `\A`.
        spec.replace("![p].n = @ + 1", "![p].n = p"),
        // Reading unbound `pc'` inside `pc'`'s own assignment RHS is a runtime error.
        spec.replace("![p].n = @ + 1", "![p].n = @ + 1, ![p].done = pc'[p].done"),
    ] {
        assert!(certificate(&changed).is_none(), "accepted {changed}");
    }
    // Shapes outside KeyedCertificate must NOT produce GeneratedSymmetry (they fall back to GeneratedEquivSymmetry).
    for changed in [
        // Storing keys in `audit` (only compared with `=` and `\in Nat`, never `<=`) is total and certifies via equiv_sym.
        spec.replace("audit' = [audit EXCEPT ![p] = 1]", "audit' = [audit EXCEPT ![p] = p]"),
        // Multi-actor partial field patches could alias when p = q.
        spec.replace("![p] = [n |-> 0, done |-> FALSE]", "![p].n = 0, ![q].done = FALSE"),
    ] {
        let proof = certificate(&changed).expect("equiv fallback should certify");
        assert!(!proof.contains("namespace TlxOptimization.GeneratedSymmetry"), "keyed accepted {changed}");
        assert!(proof.contains("namespace TlxOptimization.GeneratedEquivSymmetry"));
    }
    // Overlapping product groups must refuse.
    assert!(certificate_with(
        "ProductSets",
        include_str!("../../../proofs/symmetry/ProductSets.tla"),
        include_str!("../../../proofs/symmetry/ProductSets.cfg"),
        &[vec!["c1".into(), "c2".into()], vec!["c2".into(), "s2".into()]],
    )
    .is_none());
    // Two-key record set is outside KeyedCertificate and falls back to GeneratedEquivSymmetry.
    let two_key_rec = r#"---- MODULE TwoKeyRec ----
CONSTANT P
VARIABLE msgs
Init == msgs = {}
Next == \E p, q \in P : msgs' = msgs \cup {[from |-> p, to |-> q]}
Inv == TRUE
====
"#;
    let cfg = "CONSTANT P = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    let two_key_proof = certificate_with("TwoKeyRec", two_key_rec, cfg, &[vec!["p1".into(), "p2".into(), "p3".into()]])
        .expect("equiv fallback should certify two-key record set");
    assert!(!two_key_proof.contains("namespace TlxOptimization.GeneratedSymmetry"));
    assert!(two_key_proof.contains("namespace TlxOptimization.GeneratedEquivSymmetry"));
    // Unused group in product must refuse.
    assert!(certificate_with(
        "Keyed",
        spec,
        include_str!("../../../proofs/symmetry/Keyed.cfg"),
        &[vec!["p1".into(), "p2".into(), "p3".into()], vec!["x1".into(), "x2".into()]],
    )
    .is_none());
}

#[test]
fn membership_update_with_extra_primed_equalities_is_refused() {
    let cfg = "CONSTANT Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    let base = r#"---- MODULE AmbiguousMembership ----
CONSTANT Proc
VARIABLES x, flag
Pick == CHOOSE q \in Proc : flag \/ q /= (CHOOSE r \in Proc : TRUE)
Init == x \in Proc /\ flag = FALSE
Next == (x' \in Proc /\ x' = x /\ x' = Pick /\ flag' = TRUE) \/ UNCHANGED <<x, flag>>
Inv == ~flag
====
"#;
    assert!(
        certificate_with("AmbiguousMembership", base, cfg, &[vec!["p1".into(), "p2".into(), "p3".into()]]).is_none(),
        "x' \\in Proc /\\ x' = x /\\ x' = Pick must never drop the extra primed equalities"
    );

    let with_unchanged = base.replace("x' = x /\\ x' = Pick", "UNCHANGED x /\\ x' = Pick");
    assert!(
        certificate_with("AmbiguousMembership", &with_unchanged, cfg, &[vec!["p1".into(), "p2".into(), "p3".into()]]).is_none(),
        "x' \\in Proc /\\ UNCHANGED x /\\ x' = Pick must refuse"
    );

    let dup_unchanged = base.replace("x' = x /\\ x' = Pick", "UNCHANGED x /\\ UNCHANGED x");
    if let Some(proof) = certificate_with("AmbiguousMembership", &dup_unchanged, cfg, &[vec!["p1".into(), "p2".into(), "p3".into()]]) {
        assert!(
            !proof.contains("namespace TlxOptimization.GeneratedSymmetry"),
            "keyed certifier must refuse x' \\in Proc /\\ UNCHANGED x /\\ UNCHANGED x"
        );
    }
}

#[test]
fn mixed_map_fixed_entry_nested_except_checks_inner_path() {
    let cfg = "CONSTANT Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    // Homogeneous sequence payload `<<0, 0>>` ensures `m` classifies as `VarShape::MixedMap`
    // and reaches `emit_mixed_map_update`.
    let bad = r#"---- MODULE MixedNestedBad ----
CONSTANT Proc
VARIABLE m
Pick == CHOOSE q \in Proc : TRUE
Init == m = [x \in Proc \cup {"fixed"} |-> <<0, 0>>]
Next == \E p \in Proc :
          \/ m[p][1] = 0 /\ m' = [m EXCEPT ![p] = <<1, 0>>]
          \/ m[p][1] = 1 /\ m' = [m EXCEPT !["fixed"][IF p = Pick THEN 1 ELSE 2] = 1]
Inv == m["fixed"][2] = 0
====
"#;
    assert!(
        certificate_with("MixedNestedBad", bad, cfg, &[vec!["p1".into(), "p2".into(), "p3".into()]]).is_none(),
        "mixed map fixed-entry EXCEPT with key/CHOOSE-dependent inner index must refuse"
    );

    // Key-free nested fixed-entry EXCEPT still certifies via GeneratedSymmetry.
    let good = bad.replace("[IF p = Pick THEN 1 ELSE 2]", "[1]");
    let proof = certificate_with("MixedNestedBad", &good, cfg, &[vec!["p1".into(), "p2".into(), "p3".into()]])
        .expect("key-free nested fixed-entry EXCEPT should certify");
    assert!(proof.contains("namespace TlxOptimization.GeneratedSymmetry"));
}

#[test]
fn mixed_keyset_cardinality_declines_keyed_and_certifies_via_equiv_sym() {
    // R11-#5: `S = Proc \cup {0}` has `Cardinality(S) = 3`; `keyed` must not replace
    // `Cardinality(S)` with moved-key count (`2`), instead delegating cleanly to `equiv_sym`.
    let cfg = "CONSTANT Proc = {p1, p2}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    let spec = r#"---- MODULE MixedCard ----
EXTENDS Naturals, FiniteSets
CONSTANT Proc
VARIABLE S
Init == S = Proc \cup {0}
Next == UNCHANGED S
Inv == Cardinality(S) = 3
====
"#;
    let proof = certificate_with("MixedCard", spec, cfg, &[vec!["p1".into(), "p2".into()]])
        .expect("mixed KeySet cardinality should certify via equiv_sym");
    assert!(
        !proof.contains("namespace TlxOptimization.GeneratedSymmetry"),
        "R11-#5 keyed certifier must decline mixed KeySet Cardinality(S)"
    );
    assert!(proof.contains("namespace TlxOptimization.GeneratedEquivSymmetry"), "equiv_sym should certify mixed KeySet Cardinality(S)");
}
