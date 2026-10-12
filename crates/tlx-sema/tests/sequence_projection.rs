use tlx_front::cfg::parse_cfg;
use tlx_sema::{
    hir::{Expr, ExprKind, OpRef, RootSymbol},
    optimize::sequence_length_projection,
    Program,
};

fn certificate(spec: &str) -> Option<String> {
    let dir = tlx_testkit::TempDir::new("length-sema");
    let path = dir.write("Length.tla", spec);
    let mut p = Program::load(&path, &[]).unwrap();
    p.resolve_all_root();
    let roots = ["Init", "Next", "TypeOK"].map(|name| {
        let Some(RootSymbol::Def(id)) = p.lookup_root(name) else { panic!("missing {name}") };
        Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
    });
    sequence_length_projection(&p, &parse_cfg("INIT Init\nNEXT Next\nINVARIANT TypeOK\n").unwrap(), &roots[0], &roots[1], &roots[2..])?
        .certificate
}

#[test]
fn multiple_lengths_and_dependent_transfers_have_a_connected_certificate() {
    let proof = certificate(include_str!("../../../proofs/length/Length.tla")).unwrap();
    assert!(proof.contains("abbrev Key := Fin 2"));
    assert!(proof.contains("Transfer.append"));
    assert!(proof.contains("Transfer.reset"));
    assert!(proof.contains("Length holes"));
    assert!(proof.contains("theorem counterexample_lifts"));
}

#[test]
fn content_and_next_state_length_inputs_remain_uncertified() {
    let spec = include_str!("../../../proofs/length/Length.tla");
    for spec in [
        spec.replace("seen' = Len(log)", "seen' = (Len(log))'"),
        spec.replace("seen' = Len(log)", "seen' = Len(log')"),
        spec.replace("seen' = Len(log)", "seen' = IF Len(log) = 0 THEN 0 ELSE Head(log)"),
    ] {
        // The unaffected audit sequence may still have a certificate. The
        // content/next-state-dependent log must not appear in its projection.
        if let Some(proof) = certificate(&spec) {
            assert!(!proof.contains("abbrev Key := Fin 2"));
        }
    }
}
