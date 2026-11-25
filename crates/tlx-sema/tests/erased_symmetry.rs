use tlx_front::cfg::parse_cfg;
use tlx_sema::{
    hir::{Expr, ExprKind, OpRef, RootSymbol, VarId},
    optimize::symmetry_projection_certificate,
    Program,
};
fn certificate(source: &str, kept: &[u32]) -> Option<String> {
    let dir = tlx_testkit::TempDir::new("erased-symmetry");
    let path = dir.write("Erased.tla", source);
    let mut p = Program::load(&path, &[]).unwrap();
    p.resolve_all_root();
    let roots = ["Init", "Next", "Inv"].map(|name| {
        let Some(RootSymbol::Def(id)) = p.lookup_root(name) else { panic!("missing {name}") };
        Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
    });
    let view = Expr::new(
        ExprKind::Tuple(kept.iter().map(|i| Expr::new(ExprKind::Var(VarId(*i)), p.vars[*i as usize].span)).collect()),
        roots[0].span,
    );
    symmetry_projection_certificate(
        &p,
        &parse_cfg(include_str!("../../../proofs/symmetry/Erased.cfg")).unwrap(),
        &roots[0],
        &roots[1],
        &roots[2..],
        &[vec!["p1".into(), "p2".into(), "p3".into()]],
        &view,
    )
}
#[test]
fn erasure_and_symmetry_share_actual_map_and_hidden_transfers() {
    let proof = certificate(include_str!("../../../proofs/symmetry/Erased.tla"), &[2]).unwrap();
    for text in [
        "GeneratedErasedSymmetry",
        "ErasedKeyedRule.Model",
        "def hiddenUpdate",
        "sem.hiddenValue",
        "h ⟨0,",
        "h ⟨1,",
        "theorem erasure_certificate",
        "theorem orbit_key_equivalent",
    ] {
        assert!(proof.contains(text), "missing {text}");
    }
}
#[test]
fn observed_or_partial_hidden_values_and_wrong_views_refuse() {
    let source = include_str!("../../../proofs/symmetry/Erased.tla");
    for source in [
        source.replace("pc[p].n <= Limit", "pc[p].n <= Limit /\\ snapshot = FALSE"),
        source.replace("pc[p].n < Limit", "pc[p].n < Limit /\\ snapshot = FALSE"),
        source.replace("previous' = snapshot", "previous' = snapshot + 1"),
        source.replace("![p].done = TRUE", "![p].done = snapshot"),
    ] {
        assert!(certificate(&source, &[2]).is_none(), "accepted {source}");
    }
    assert!(certificate(source, &[2, 2]).is_none());
    assert!(certificate(source, &[2, 1]).is_none());
    assert!(certificate(source, &[0, 1, 2]).is_none());
}

fn multi_key_certificate(source: &str, kept: &[u32], groups: &[Vec<String>]) -> Option<String> {
    let dir = tlx_testkit::TempDir::new("erased-equiv-symmetry");
    let path = dir.write("ErasedMultiKey.tla", source);
    let mut p = Program::load(&path, &[]).unwrap();
    p.resolve_all_root();
    let roots = ["Init", "Next", "Inv"].map(|name| {
        let Some(RootSymbol::Def(id)) = p.lookup_root(name) else { panic!("missing {name}") };
        Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
    });
    let view = Expr::new(
        ExprKind::Tuple(kept.iter().map(|i| Expr::new(ExprKind::Var(VarId(*i)), p.vars[*i as usize].span)).collect()),
        roots[0].span,
    );
    symmetry_projection_certificate(
        &p,
        &parse_cfg(include_str!("../../../proofs/symmetry/ErasedMultiKey.cfg")).unwrap(),
        &roots[0],
        &roots[1],
        &roots[2..],
        groups,
        &view,
    )
}

#[test]
fn erased_equiv_symmetry_emits_connected_composition_certificate() {
    let source = include_str!("../../../proofs/symmetry/ErasedMultiKey.tla");
    let groups = [vec!["n1".into(), "n2".into(), "n3".into()]];
    // Variables: msgs(0), log(1), audit(2), lastAction(3), stats(4); kept = <<msgs, log>>.
    let proof = multi_key_certificate(source, &[0, 1], &groups).expect("expected GeneratedErasedEquivSymmetry");
    for text in [
        "namespace TlxOptimization.GeneratedErasedEquivSymmetry",
        "ErasedEquivRule.Model",
        "def hiddenUpdate",
        "sem.hiddenUpdate",
        "theorem erasure_certificate",
        "theorem orbit_key_equivalent",
        "theorem counterexample_lifts",
        "theorem deadlock_preserved",
    ] {
        assert!(proof.contains(text), "missing {text}");
    }
    assert!(!proof.contains("sorry"));
}

#[test]
fn erased_equiv_symmetry_refuses_observed_partial_overflow_primed_and_wrong_views() {
    let source = include_str!("../../../proofs/symmetry/ErasedMultiKey.tla");
    let groups = [vec!["n1".into(), "n2".into(), "n3".into()]];
    for mutated in [
        // Observed hidden variable in invariant.
        source.replace("Len(log) <= 2", "Len(log) <= 2 /\\ lastAction.kind # \"bad\""),
        // Observed hidden variable in guard.
        source.replacen("Cardinality(msgs) < 2", "Cardinality(msgs) < 2 /\\ stats[p] = FALSE", 1),
        // Partial hidden update (Head of empty sequence).
        source.replace("lastAction' = [kind |-> \"drop\", actor |-> \"none\"]", "lastAction' = Head(<<>>)"),
        // Overflowing hidden update.
        source.replace("lastAction' = [kind |-> \"drop\", actor |-> \"none\"]", "lastAction' = [kind |-> 2147483647 + 1]"),
        // Primed read in hidden RHS.
        source.replace("lastAction' = [kind |-> \"drop\", actor |-> \"none\"]", "lastAction' = [kind |-> \"drop\", actor |-> log']"),
        // Duplicate binding of hidden variable.
        source.replace("UNCHANGED <<msgs, audit, stats>>", "UNCHANGED <<msgs, audit, stats>> /\\ audit' = {}"),
    ] {
        assert!(multi_key_certificate(&mutated, &[0, 1], &groups).is_none(), "unexpectedly accepted:\n{mutated}");
    }
    // Wrong views: duplicate retained var, wrong order, all vars kept, missing retained var.
    assert!(multi_key_certificate(source, &[0, 0], &groups).is_none());
    assert!(multi_key_certificate(source, &[1, 0], &groups).is_none());
    assert!(multi_key_certificate(source, &[0, 1, 2, 3, 4], &groups).is_none());
    assert!(multi_key_certificate(source, &[0], &groups).is_none());
    // Unused second group must refuse.
    let extra_group = [vec!["n1".into(), "n2".into(), "n3".into()], vec!["x1".into(), "x2".into()]];
    assert!(multi_key_certificate(source, &[0, 1], &extra_group).is_none());
}
