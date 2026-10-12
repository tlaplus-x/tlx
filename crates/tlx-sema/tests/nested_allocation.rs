use tlx_front::cfg::parse_cfg;
use tlx_sema::{
    hir::{Expr, ExprKind, OpRef, RootSymbol},
    optimize::ordered_projection,
    Program,
};
fn certificate(source: &str) -> Option<String> {
    let dir = tlx_testkit::TempDir::new("nested-allocation");
    let path = dir.write("Nested.tla", source);
    let mut p = Program::load(&path, &[]).unwrap();
    p.resolve_all_root();
    let roots = ["Init", "Next", "Inv"].map(|name| {
        let Some(RootSymbol::Def(id)) = p.lookup_root(name) else { panic!("missing {name}") };
        Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
    });
    ordered_projection(&p, &parse_cfg(include_str!("../../../proofs/ordered/Nested.cfg")).unwrap(), &roots[0], &roots[1], &roots[2..])?
        .certificate
}
#[test]
fn nested_fields_arrays_maps_and_independent_families_are_connected() {
    let proof = certificate(include_str!("../../../proofs/ordered/Nested.tla")).expect("connected nested certificate");
    for text in [
        "abbrev Family := Fin 2",
        "Transfer.branch",
        "Token.fresh",
        "sourceLayout",
        "theorem runtime_key_equivalent",
        "theorem counterexample_lifts",
    ] {
        assert!(proof.contains(text), "missing {text}");
    }
}
#[test]
fn unsupported_numeric_uses_and_shape_changes_refuse() {
    let spec = include_str!("../../../proofs/ordered/Nested.tla");
    for source in [
        spec.replace("records[a].items[1].stamp <= frontier", "frontier - records[a].items[1].stamp = 1"),
        spec.replace("frontier + 1,", "frontier + 2,"),
        spec.replace("records[a].items[1].stamp <= frontier", "records[a].items[1].stamp <= serial"),
        spec.replace("records[a].items[1].stamp <= frontier", "records'[a].items[1].stamp <= frontier"),
        spec.replace("![a] = records[b]", "![a] = [items |-> <<[stamp |-> frontier, serial |-> serial]>>]"),
        spec.replace(
            "![a].ready = TRUE",
            "![a].items = <<[stamp |-> frontier, serial |-> serial], [stamp |-> frontier, serial |-> serial]>>",
        ),
    ] {
        assert!(certificate(&source).is_none(), "accepted {source}");
    }
}
