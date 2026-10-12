use tlx_front::cfg::parse_cfg;
use tlx_sema::{
    hir::{Expr, ExprKind, OpRef, RootSymbol},
    optimize::ordered_projection,
    Program,
};
fn certificate(source: &str) -> Option<String> {
    let dir = tlx_testkit::TempDir::new("live-versions");
    let path = dir.write("LiveVersions.tla", source);
    let mut p = Program::load(&path, &[]).unwrap();
    p.resolve_all_root();
    let roots = ["Init", "Next", "Inv"].map(|name| {
        let Some(RootSymbol::Def(id)) = p.lookup_root(name) else { panic!("missing {name}") };
        Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
    });
    ordered_projection(
        &p,
        &parse_cfg(include_str!("../../../proofs/ordered/LiveVersions.cfg")).unwrap(),
        &roots[0],
        &roots[1],
        &roots[2..],
    )?
    .certificate
}
#[test]
fn live_versions_have_connected_payload_reads_and_collection() {
    let proof = certificate(include_str!("../../../proofs/ordered/LiveVersions.tla")).expect("connected live-version certificate");
    for text in ["GeneratedLive", "LiveRule.Model", "sem.payload", "Reads V", "payload lookup from reads", "theorem runtime_key_equivalent"]
    {
        assert!(proof.contains(text), "missing {text}");
    }
}
#[test]
fn version_table_escapes_and_primed_reads_are_refused() {
    let source = include_str!("../../../proofs/ordered/LiveVersions.tla");
    for source in [
        source.replace("observed' = versions[held[a]]", "observed' = versions'[held[a]]"),
        source.replace("observed' = versions[held[a]]", "observed' = (versions[held[a]])'"),
        source.replace("observed' = versions[held[a]]", "observed' = versions"),
        source.replace("versions @@ [k \\in {frontier + 1} |-> ~versions[frontier]]", "[versions EXCEPT ![frontier] = TRUE]"),
        source.replace("~versions[frontier]", "frontier"),
        source.replace("versions[frontier] = flag", "versions[frontier - 1] = flag"),
        source.replace("versions[held[a]] \\in BOOLEAN", "DOMAIN versions = {held[a]}"),
    ] {
        assert!(certificate(&source).is_none(), "accepted {source}");
    }
}

#[test]
fn version_collection_keeps_other_allocation_families_separate() {
    let source = include_str!("../../../proofs/ordered/LiveVersions.tla")
        .replace("VARIABLES frontier", "VARIABLES epoch, frontier")
        .replace("Init ==", "Init == /\\ epoch = 10")
        .replace("Publish ==", "Publish == /\\ epoch' = epoch + 2")
        .replace("UNCHANGED <<frontier, versions, flag", "UNCHANGED <<epoch, frontier, versions, flag")
        .replace("Inv ==", "Inv == /\\ epoch >= 10");
    let proof = certificate(&source).unwrap();
    assert!(proof.contains("abbrev Family := Fin 2"));
    assert!(proof.contains("def historyFamily : Family := ⟨1,"));
    let source = source.replace("~versions[frontier]", "epoch");
    assert!(certificate(&source).is_none(), "accepted allocation IDs in a version payload");
}
