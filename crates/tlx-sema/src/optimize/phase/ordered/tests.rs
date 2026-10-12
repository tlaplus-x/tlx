use super::*;

const SPEC: &str = r#"---- MODULE Allocation ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
VARIABLE frontier, stored, versions
Init == /\ frontier = 1 /\ stored = [slots |-> <<[tag |-> 0]>>]
        /\ versions = [t \in {frontier} |-> FALSE]
Next == /\ frontier' = frontier + 1
        /\ stored' = [slots |-> <<[tag |-> frontier]>>]
        /\ versions' = versions @@ [t \in {frontier + 1} |-> TRUE]
Inv == /\ stored.slots[1].tag <= frontier /\ versions[frontier] \in BOOLEAN
====
"#;

fn plan(source: &str) -> Option<FieldProjection> {
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    let dir = tlx_testkit::TempDir::with_spec("ordered-analysis", source, cfg);
    let program = Program::load(&dir.join("Allocation.tla"), &[]).unwrap();
    let expr = |name: &str| {
        let def = program.defs.iter().find(|d| &*d.name == name).unwrap();
        let DefKind::Op(e) = &def.kind else { panic!() };
        e.clone()
    };
    ordered_projection(&program, &tlx_front::cfg::parse_cfg(cfg).unwrap(), &expr("Init"), &expr("Next"), &[expr("Inv")])
}

#[test]
fn follows_structures_without_schema_names() {
    for source in [
        SPEC.to_string(),
        SPEC.replace("frontier", "serial")
            .replace("stored", "objects")
            .replace("versions", "archive")
            .replace("slots", "items")
            .replace("tag", "generation"),
    ] {
        let p = plan(&source).unwrap().ordered.unwrap();
        assert_eq!(p.history.unwrap().variable, 2);
        assert_eq!(p.variables[0].family, Some(0));
        assert!(p.variables[1].fields.values().next().unwrap().value.as_ref().unwrap().fields.values().next().unwrap().family.is_some());
    }
}

#[test]
fn refuses_non_equivariant_reads_and_transfers() {
    for (old, new) in [
        (
            "stored' = [slots |-> <<[tag |-> frontier]>>]",
            "stored' = [slots |-> <<[tag |-> frontier]>>] /\\ stored' = stored /\\ stored' \\in {stored}",
        ),
        ("stored.slots[1].tag <= frontier", "frontier < 10"),
        ("stored.slots[1].tag <= frontier", "ToString(frontier) = \"1\""),
        ("stored.slots[1].tag <= frontier", "Print(frontier, TRUE)"),
        ("stored.slots[1].tag <= frontier", "frontier - stored.slots[1].tag = 1"),
        ("stored.slots[1].tag <= frontier", "Cardinality(DOMAIN versions) = frontier"),
        ("stored.slots[1].tag <= frontier", "versions[frontier - 1] = TRUE"),
        ("stored.slots[1].tag <= frontier", "versions = [t \\in {frontier} |-> TRUE]"),
        ("stored.slots[1].tag <= frontier", "Len([t \\in {frontier} |-> TRUE]) = 1"),
        ("frontier' = frontier + 1", "frontier' = stored.slots[1].tag + 1"),
        ("tag |-> frontier]", "tag |-> frontier + 2]"),
        ("|-> TRUE]", "|-> frontier]"),
    ] {
        assert!(plan(&SPEC.replace(old, new)).is_none(), "accepted {new}");
    }
}

#[test]
fn rank_without_history_still_generalizes() {
    let source = SPEC.replace("versions @@ [t \\in {frontier + 1} |-> TRUE]", "[t \\in {frontier + 1} |-> TRUE]");
    let p = plan(&source).unwrap().ordered.unwrap();
    assert!(p.history.is_none());
}

#[test]
fn mutable_maps_are_ranked_but_not_garbage_collected() {
    let source = SPEC.replace("versions @@ [t \\in {frontier + 1} |-> TRUE]", "[versions EXCEPT ![frontier] = TRUE]");
    assert!(plan(&source).unwrap().ordered.unwrap().history.is_none());
}

#[test]
fn batch_allocations_and_independent_families() {
    let source = r#"---- MODULE Allocation ----
EXTENDS Naturals, FiniteSets
VARIABLE serial, other, tickets
Init == /\ serial = 1 /\ other = 100 /\ tickets = {}
Next == /\ serial' = serial + Cardinality({"a", "b"})
        /\ other' = other + 1
        /\ tickets' = serial..(serial + Cardinality({"a", "b"}))
Inv == (\A t \in tickets : t <= serial) /\ other > 0
====
"#;
    let p = plan(source).unwrap().ordered.unwrap();
    assert_eq!(p.anchors.len(), 2);
    assert!(plan(&source.replace("other > 0", "other > serial")).is_none());
    assert!(plan(&source.replace("other > 0", "other - 100 = serial")).is_none());
}

#[test]
fn universal_frame_requires_a_nonempty_domain() {
    let source = SPEC.replace("Next ==", "Step ==").replace(
        "Inv ==",
        "Next == Step \\/ (\\A member \\in {1} : stored.slots[1].tag = 0 /\\ UNCHANGED <<frontier, stored, versions>>)\nInv ==",
    );
    assert!(plan(&source).is_some());
    assert!(plan(&source.replace("member \\in {1}", "member \\in {}")).is_none());
}

#[test]
fn unknown_container_results_do_not_become_empty_provenance() {
    for replacement in [
        "Head(SubSeq(<<[slots |-> <<[tag |-> 100]>>]>>, 1, 1))",
        "SubSeq(<<[slots |-> <<[tag |-> 100]>>]>>, 1, 1)[1]",
        "[slots |-> SubSeq(<<[tag |-> 100]>>, 1, 1)]",
    ] {
        let source = SPEC.replace("stored = [slots |-> <<[tag |-> 0]>>]", &format!("stored = {replacement}"));
        assert!(plan(&source).is_none(), "accepted opaque result: {replacement}");
    }
    let colored_record = Shape { fields: BTreeMap::from([(Arc::from("id"), Shape::family(0))]), ..Default::default() };
    assert!(Shape::plain().joined(&colored_record).is_none());
}

#[test]
fn negation_keeps_unknown_integer_origins() {
    let source = SPEC
        .replace("EXTENDS Naturals", "EXTENDS Integers")
        .replace("VARIABLE frontier", "VARIABLE raw, frontier")
        .replace("Init ==", "Init == raw = 0 /\\")
        .replace("Next ==", "Next == raw' = raw - 1 /\\")
        .replace("stored.slots[1].tag <= frontier", "-raw < frontier");
    assert!(plan(&source).is_none());
}
