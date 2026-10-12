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
        &["p1".into(), "p2".into(), "p3".into()],
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
