//! CLI end-to-end regressions for `tlc-equality` fixes:
//! - `S-6` (`FairUncovered`, uncovered primed expression),
//! - `E-7` (`SubscriptPanic`, `SubscriptTypeMismatch`),
//! - `Section 4 #3` (`LiveLevel`),
//! - `E-1` (`SeqFilterPanic`),
//! - `C-5` (`StructuralMemberErrorBug`),
//! - `Section 4 #4` (`ComposeInstVar`).

use tlx_testkit::TempDir;

#[test]
fn fair_uncovered_violates_property_in_cli() {
    let dir = TempDir::new("cli-fair-uncovered");
    dir.write(
        "FairUncovered.tla",
        &tlx_testkit::module(
            "FairUncovered",
            "\
VARIABLES x, y
Keep(v) == UNCHANGED v
Init == x = 0 /\\ y = 0
Next == UNCHANGED <<x, y>>
A == x' = 1 /\\ Keep(y)
Spec == Init /\\ [][Next]_<<x, y>>
Prop == WF_<<x, y>>(A)
",
        ),
    );
    dir.write("FairUncovered.cfg", "SPECIFICATION Spec\nPROPERTY Prop\n");
    for extra in [&[][..], &["-tlc"][..]] {
        let mut cmd = tlx_testkit::tlx!();
        cmd.check("FairUncovered.tla").cfg("FairUncovered.cfg").dir(dir.path()).args(extra);
        let out = cmd.run();
        assert_eq!(out.code, 13, "extra={extra:?}\n{}", out.text());
        assert!(out.text().contains("Temporal"), "{}", out.text());
    }
}

#[test]
fn fair_uncovered_primed_expr_violates_property_in_cli() {
    let dir = TempDir::new("cli-fair-uncovered-primed");
    dir.write(
        "FairUncoveredPrimed.tla",
        &tlx_testkit::module(
            "FairUncoveredPrimed",
            "\
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == UNCHANGED x
A == x' = 1 /\\ (x + 1)' = 2
Spec == Init /\\ [][Next]_x
Prop == WF_x(A)
",
        ),
    );
    dir.write("FairUncoveredPrimed.cfg", "SPECIFICATION Spec\nPROPERTY Prop\n");
    let mut cmd = tlx_testkit::tlx!();
    cmd.check("FairUncoveredPrimed.tla").cfg("FairUncoveredPrimed.cfg").dir(dir.path()).arg("-tlc");
    let out = cmd.run();
    assert_eq!(out.code, 13, "{}", out.text());
}

#[test]
fn subscript_lazy_and_type_mismatch_fail_without_panicking() {
    let dir = TempDir::new("cli-subscript");
    dir.write(
        "SubscriptPanic.tla",
        &tlx_testkit::module(
            "SubscriptPanic",
            "\
EXTENDS Naturals
VARIABLE x
Init == x = 1
Next == UNCHANGED x
Spec == Init /\\ [][Next]_x /\\ WF_<<x, [n \\in Nat |-> n]>>(Next)
Prop == <>(x = 2)
",
        ),
    );
    dir.write("SubscriptPanic.cfg", "SPECIFICATION Spec\nPROPERTY Prop\n");
    let mut cmd = tlx_testkit::tlx!();
    cmd.check("SubscriptPanic.tla").cfg("SubscriptPanic.cfg").dir(dir.path()).arg("-tlc");
    let out = cmd.run();
    assert_ne!(out.code, 0, "{}", out.text());
    assert_ne!(out.code, 13, "must fail with evaluation error, not liveness violation:\n{}", out.text());
    assert_ne!(out.code, 101, "must not panic:\n{}", out.text());

    dir.write(
        "SubscriptTypeMismatch.tla",
        &tlx_testkit::module(
            "SubscriptTypeMismatch",
            "\
VARIABLE x
Init == x = 1
Next == IF x = 1 THEN x' = \"a\" ELSE UNCHANGED x
Spec == Init /\\ [][Next]_x /\\ WF_x(Next)
Prop == <>(x = \"a\")
",
        ),
    );
    dir.write("SubscriptTypeMismatch.cfg", "SPECIFICATION Spec\nPROPERTY Prop\n");
    let mut cmd = tlx_testkit::tlx!();
    cmd.check("SubscriptTypeMismatch.tla").cfg("SubscriptTypeMismatch.cfg").dir(dir.path()).arg("-tlc");
    let out = cmd.run();
    assert_eq!(out.code, 255, "{}", out.text());
    assert!(out.text().contains("Attempted to check equality of integer 1 with non-integer"), "{}", out.text());
}

#[test]
fn live_level_threads_bfs_level_through_steps() {
    let dir = TempDir::new("cli-live-level");
    dir.write(
        "LiveLevel.tla",
        &tlx_testkit::module(
            "LiveLevel",
            "\
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == (x = 0 /\\ x' = 1) \\/ (x = 1 /\\ x' = 1)
A == TLCGet(\"level\") = 2 /\\ x' = 2
Spec == Init /\\ [][Next]_x
Prop == WF_x(A)
",
        ),
    );
    dir.write("LiveLevel.cfg", "SPECIFICATION Spec\nPROPERTY Prop\n");
    let mut cmd = tlx_testkit::tlx!();
    cmd.check("LiveLevel.tla").cfg("LiveLevel.cfg").dir(dir.path()).arg("-tlc");
    let out = cmd.run();
    assert_eq!(out.code, 13, "expected liveness violation at BFS level 2:\n{}", out.text());
}

#[test]
fn seq_filter_panic_succeeds_in_cli() {
    let dir = TempDir::new("cli-seqfilter");
    dir.write(
        "SeqFilterPanic.tla",
        &tlx_testkit::module(
            "SeqFilterPanic",
            "\
EXTENDS Naturals
VARIABLE x
Op(f, g) == {s \\in [1..2 -> 1..5] : (IF s[1] = 1 THEN f ELSE g) \\in {}}
Init == x = Op([n \\in Nat |-> n], [n \\in Nat |-> n + 1])
Next == UNCHANGED x
Inv == x = {}
",
        ),
    );
    dir.write("SeqFilterPanic.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\n");
    let mut cmd = tlx_testkit::tlx!();
    cmd.check("SeqFilterPanic.tla").cfg("SeqFilterPanic.cfg").dir(dir.path()).arg("-tlc");
    let out = cmd.run();
    assert_eq!(out.code, 0, "{}", out.text());
}

#[test]
fn structural_member_errors_match_between_interp_and_compile() {
    let dir = TempDir::new("cli-structural-member");
    dir.write(
        "StructuralMemberErrorBug.tla",
        &tlx_testkit::module(
            "StructuralMemberErrorBug",
            "\
EXTENDS Naturals
VARIABLE x
Init == x = <<1>>
Next == UNCHANGED x
Inv == ~(x \\in [a : Nat])
",
        ),
    );
    dir.write("StructuralMemberErrorBug.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\n");
    for (mode, args, envs) in
        [("interp", vec!["-interp"], vec![]), ("compile", vec!["-compile"], vec![("TLX_PRERUN_REUSE", "0"), ("TLX_PARANOID", "1")])]
    {
        let mut cmd = tlx_testkit::tlx!();
        cmd.check("StructuralMemberErrorBug.tla")
            .cfg("StructuralMemberErrorBug.cfg")
            .dir(dir.path())
            .args(&args)
            .envs(envs.iter().copied());
        let out = cmd.run();
        assert_eq!(out.code, 75, "mode={mode}\n{}", out.text());
    }
}

#[test]
fn enabled_compose_with_inst_var_succeeds_in_cli() {
    let dir = TempDir::new("cli-compose-instvar");
    dir.write(
        "Sub.tla",
        &tlx_testkit::module(
            "Sub",
            "\
EXTENDS Naturals
VARIABLES u, v
A == u' = u + 1 /\\ UNCHANGED v
B == v' = 2
Ok == ENABLED (v' = 2 /\\ (A \\cdot B)) /\\ ~ENABLED (v' = 3 /\\ (A \\cdot B))
",
        ),
    );
    dir.write(
        "Main.tla",
        &tlx_testkit::module(
            "Main",
            "\
EXTENDS Naturals
VARIABLE x
I == INSTANCE Sub WITH u <- x + 1, v <- x + 10
Init == x = 0
Next == UNCHANGED x
Inv == I!Ok
",
        ),
    );
    dir.write("Main.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\n");
    let mut cmd = tlx_testkit::tlx!();
    cmd.check("Main.tla").cfg("Main.cfg").dir(dir.path()).arg("-tlc");
    let out = cmd.run();
    assert_eq!(out.code, 0, "{}", out.text());
}

#[test]
fn inline_call_does_not_duplicate_compiled_deferred_thunk() {
    let dir = TempDir::new("cli-inline-deferred-thunk");
    dir.write(
        "DeferredThunkInline.tla",
        &tlx_testkit::module(
            "DeferredThunkInline",
            "\
EXTENDS Integers, TLC
VARIABLE x
Same(a) == a = a
Bump == IF TLCSet(1, TLCGet(1) + 1) THEN TLCGet(1) ELSE 0
Bar(p) == Same(p)
Init == x = 0 /\\ TLCSet(1, 0)
Next == UNCHANGED x
Inv == Bar(<<Bump, 1>>)
",
        ),
    );
    dir.write("DeferredThunkInline.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\n");
    for (mode, args, envs) in
        [("interp", vec!["-interp"], vec![]), ("compile", vec!["-compile"], vec![("TLX_PRERUN_REUSE", "0"), ("TLX_PARANOID", "1")])]
    {
        let mut cmd = tlx_testkit::tlx!();
        cmd.check("DeferredThunkInline.tla").cfg("DeferredThunkInline.cfg").dir(dir.path()).args(&args).envs(envs.iter().copied());
        let out = cmd.run();
        assert_eq!(out.code, 0, "mode={mode}\n{}", out.text());
    }
}

#[test]
fn filtered_powerset_of_powerset_runs_natively_and_matches_interp() {
    let dir = TempDir::new("cli-subset-filter-5nodes");
    dir.write(
        "SubsetEdges.tla",
        &tlx_testkit::module(
            "SubsetEdges",
            "\
EXTENDS Integers, FiniteSets
CONSTANTS Nodes
VARIABLES Edges, seen
Nbrs(n) == {m \\in Nodes : {m, n} \\in Edges}
Init ==
    /\\ Edges \\in {E \\in SUBSET (SUBSET Nodes) : \\A e \\in E : Cardinality(e) = 2}
    /\\ seen = {}
Next ==
    /\\ seen = {}
    /\\ seen' = {n \\in Nodes : Nbrs(n) /= {}}
    /\\ UNCHANGED Edges
Inv == \\A e \\in Edges : (e \\subseteq Nodes) /\\ (Cardinality(e) = 2)
",
        ),
    );
    dir.write("SubsetEdges.cfg", "CONSTANTS\n  Nodes = {n1, n2, n3, n4, n5}\nINIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n");
    for (mode, args, envs) in [
        ("interp", vec!["-interp", "-tlc"], vec![]),
        ("compile", vec!["-compile", "-tlc"], vec![("TLX_PRERUN_REUSE", "0"), ("TLX_PARANOID", "1")]),
    ] {
        let mut cmd = tlx_testkit::tlx!();
        cmd.check("SubsetEdges.tla").cfg("SubsetEdges.cfg").dir(dir.path()).args(&args).envs(envs.iter().copied());
        let out = cmd.run();
        assert_eq!(out.code, 0, "mode={mode}\n{}", out.text());
        assert!(out.text().contains("2047 distinct states found"), "mode={mode}\n{}", out.text());
        if mode == "compile" {
            assert!(out.text().contains("0 boxed, 0 interpreter"), "expected fully native lowering:\n{}", out.text());
        }
    }
}
