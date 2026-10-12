use tlx_front::cfg::parse_cfg;
use tlx_sema::{
    hir::{Expr, ExprKind, OpRef, RootSymbol},
    optimize::symmetry_certificate,
    Program,
};

fn certificate(spec: &str) -> Option<String> {
    let dir = tlx_testkit::TempDir::new("keyed-sema");
    let path = dir.write("Keyed.tla", spec);
    let mut p = Program::load(&path, &[]).unwrap();
    p.resolve_all_root();
    let roots = ["Init", "Next", "Inv"].map(|name| {
        let Some(RootSymbol::Def(id)) = p.lookup_root(name) else { panic!("missing {name}") };
        Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
    });
    symmetry_certificate(
        &p,
        &parse_cfg(include_str!("../../../proofs/symmetry/Keyed.cfg")).unwrap(),
        &roots[0],
        &roots[1],
        &roots[2..],
        &["p1".into(), "p2".into(), "p3".into()],
    )
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
        "theorem orbit_key_equivalent",
        "theorem counterexample_lifts",
    ] {
        assert!(proof.contains(needle), "{needle}");
    }
}
#[test]
fn unsupported_key_escapes_and_aliasing_are_refused() {
    let spec = include_str!("../../../proofs/symmetry/Keyed.tla");
    for changed in [
        spec.replace("![p].n = @ + 1", "![p].n = p"),
        spec.replace("![p].n = @ + 1", "![p].n = @ + 1, ![CHOOSE q \\in Proc : TRUE].done = TRUE"),
        spec.replace("![p].n = @ + 1", "![p].n = @ + 1, ![p].done = pc'[p].done"),
        spec.replace("pc[p].n <= Limit", "pc[p].n <= Limit /\\ (CHOOSE q \\in Proc : TRUE) = p"),
        spec.replace("audit[p] = audit[q]", "pc' = pc"),
    ] {
        assert!(certificate(&changed).is_none(), "accepted {changed}");
    }
}
