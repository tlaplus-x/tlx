//! Coarse replay must preserve the violation and print only a genuine prefix
//! when runtime-dependent generation makes reconstruction impossible (D-30).
use std::time::Duration;

#[test]
fn counter_dependent_next_reports_why_its_trace_is_incomplete() {
    let dir = tlx_testkit::TempDir::new("view-counter-guard");
    std::fs::write(dir.join("ViewCounterGuard.tla"), include_str!("fixtures/view-counter-guard/ViewCounterGuard.tla")).unwrap();
    std::fs::write(dir.join("ViewCounterGuard.cfg"), include_str!("fixtures/view-counter-guard/ViewCounterGuard.cfg")).unwrap();
    let oracle = include_str!("fixtures/view-counter-guard/ViewCounterGuard.tlc.out");
    assert!(oracle.contains("STARTMSG 2123") && oracle.contains("STARTMSG 2128"));
    for mode in [&[][..], &["-tlc"]] {
        for tier in ["-interp", "-compile"] {
            for workers in ["1", "4"] {
                let r = tlx_testkit::tlx_default!()
                    .args(["check", "ViewCounterGuard.tla", tier, "-workers", workers])
                    .args(mode)
                    .envs([("TLX_PARANOID", "1"), ("TLX_PRERUN_REUSE", "0")])
                    .dir(&dir)
                    .timeout(Duration::from_secs(30))
                    .run();
                assert_eq!(r.code, 12, "{}", r.text());
                assert!(r.stdout.contains("Invariant Inv is violated"), "{}", r.text());
                assert!(
                    r.stdout.contains("trace cannot be reconstructed: Next depends on run-time counters (TLCGet/TLCSet/Random) under VIEW"),
                    "{}",
                    r.text()
                );
                assert!(r.stdout.contains("x = 0"), "{}", r.text());
                assert!(!r.stdout.contains("State 2:"), "{}", r.text());
            }
        }
    }
}

#[test]
fn partial_error_trace_does_not_append_an_unconnected_incomplete_successor() {
    let dir = tlx_testkit::TempDir::new("view-counter-incomplete");
    std::fs::write(dir.join("ViewCounterIncomplete.tla"), include_str!("fixtures/view-counter-guard/ViewCounterIncomplete.tla")).unwrap();
    std::fs::write(dir.join("ViewCounterIncomplete.cfg"), include_str!("fixtures/view-counter-guard/ViewCounterIncomplete.cfg")).unwrap();
    assert!(include_str!("fixtures/view-counter-guard/ViewCounterIncomplete.tlc.out").contains("STARTMSG 2128"));
    for tier in ["-interp", "-compile"] {
        let r = tlx_testkit::tlx_default!()
            .args(["check", "ViewCounterIncomplete.tla", "-tlc", tier, "-workers", "1"])
            .envs([("TLX_PARANOID", "1"), ("TLX_PRERUN_REUSE", "0")])
            .dir(&dir)
            .timeout(Duration::from_secs(30))
            .run();
        assert_ne!(r.code, 0, "{}", r.text());
        assert!(r.stdout.contains("not completely specified"), "{}", r.text());
        assert!(r.stdout.contains("trace cannot be reconstructed"), "{}", r.text());
        assert!(r.stdout.contains("x = 0"), "{}", r.text());
        assert!(!r.stdout.contains("State 2:"), "{}", r.text());
        assert!(!r.stdout.contains("x = 2"), "{}", r.text());
    }
}

#[test]
fn counter_dependent_constraint_reports_reconstruction_limit() {
    let dir = tlx_testkit::TempDir::new("view-counter-constraint");
    std::fs::write(dir.join("ViewCounterConstraint.tla"), include_str!("fixtures/view-counter-guard/ViewCounterConstraint.tla")).unwrap();
    std::fs::write(dir.join("ViewCounterConstraint.cfg"), include_str!("fixtures/view-counter-guard/ViewCounterConstraint.cfg")).unwrap();
    assert!(include_str!("fixtures/view-counter-guard/ViewCounterConstraint.tlc.out").contains("STARTMSG 2110"));
    for tier in ["-interp", "-compile"] {
        let r = tlx_testkit::tlx_default!()
            .args(["check", "ViewCounterConstraint.tla", "-tlc", tier, "-workers", "1"])
            .envs([("TLX_PARANOID", "1"), ("TLX_PRERUN_REUSE", "0")])
            .dir(&dir)
            .timeout(Duration::from_secs(30))
            .run();
        assert_eq!(r.code, 12, "{}", r.text());
        assert!(r.stdout.contains("Invariant Inv is violated"), "{}", r.text());
        assert!(r.stdout.contains("a replayed predicate depends on run-time counters"), "{}", r.text());
        assert!(!r.stdout.contains("State 2:"), "{}", r.text());
    }
}

#[test]
fn sym_view_word_least_perm_matches_interpreter_under_paranoid() {
    let dir = tlx_testkit::TempDir::new("sym-view-word-order");
    // Exercises VIEW + SYMMETRY across packed records, bitsets, sequences,
    // variable-domain maps, and non-declaration TLC variable order (z before a),
    // with a VIEW that does not commute with the symmetry group so every orbit's
    // exact TLC-least representative determines the state counts.
    let tla = r#"---- MODULE SymViewWord ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS p1, p2, p3
VARIABLES z_rec, a_set, seq, bag, cnt
Procs == {p1, p2, p3}
Init ==
    /\ z_rec = [owner |-> p1, flag |-> FALSE, n |-> 0]
    /\ a_set = {p2}
    /\ seq = <<p1>>
    /\ bag = [x \in {} |-> 0]
    /\ cnt = 0
Next ==
    \/ \E p \in Procs :
        /\ z_rec' = [owner |-> p, flag |-> ~z_rec.flag, n |-> (z_rec.n + 1) % 2]
        /\ cnt' = (cnt + 1) % 2
        /\ UNCHANGED <<a_set, seq, bag>>
    \/ \E p \in Procs :
        /\ a_set' = IF p \in a_set THEN a_set \ {p} ELSE a_set \cup {p}
        /\ UNCHANGED <<z_rec, seq, bag, cnt>>
    \/ \E p \in Procs :
        /\ Len(seq) < 2
        /\ seq' = Append(seq, p)
        /\ UNCHANGED <<z_rec, a_set, bag, cnt>>
    \/ \E p \in Procs :
        /\ p \notin DOMAIN bag
        /\ Cardinality(DOMAIN bag) < 2
        /\ bag' = bag @@ (p :> z_rec.n)
        /\ UNCHANGED <<z_rec, a_set, seq, cnt>>
View == <<z_rec.owner, a_set, seq, cnt>>
Sym == Permutations(Procs)
===="#;
    let cfg = "CONSTANTS p1 = p1 p2 = p2 p3 = p3\nINIT Init\nNEXT Next\nVIEW View\nSYMMETRY Sym\n";
    std::fs::write(dir.join("SymViewWord.tla"), tla).unwrap();
    std::fs::write(dir.join("SymViewWord.cfg"), cfg).unwrap();

    let interp = tlx_testkit::tlx_default!()
        .args(["check", "SymViewWord.tla", "-tlc", "-interp", "-workers", "1"])
        .dir(&dir)
        .timeout(Duration::from_secs(30))
        .run();
    assert_eq!(interp.code, 0, "{}", interp.text());

    let compiled = tlx_testkit::tlx_default!()
        .args(["check", "SymViewWord.tla", "-tlc", "-compile", "-workers", "1", "-stats"])
        .envs([("TLX_PARANOID", "1"), ("TLX_PRERUN_REUSE", "0")])
        .dir(&dir)
        .timeout(Duration::from_secs(30))
        .run();
    assert_eq!(compiled.code, 0, "{}", compiled.text());
    assert!(
        compiled.stdout.contains("symmetry: least state on encodings, VIEW of its permuted encoding"),
        "expected word-level SymView path:\n{}",
        compiled.text()
    );
    let counts = |out: &str| out.lines().find(|l| l.contains("states generated")).unwrap().to_string();
    assert_eq!(counts(&compiled.stdout), counts(&interp.stdout), "compiled vs interp counts differ");

    // Fallback test: a Dyn variable (Interval witness) and a reversed-order Union
    // ([Bool, Atom(untyped MV)]) under VIEW + SYMMETRY.
    let tla_fb = r#"---- MODULE SymViewFallback ----
EXTENDS Naturals, TLC
CONSTANTS p1, p2
VARIABLES dyn_iv, flag_or_p
Procs == {p1, p2}
Init ==
    /\ dyn_iv = 1..2
    /\ flag_or_p = FALSE
Next ==
    \/ /\ flag_or_p' \in (Procs \cup BOOLEAN)
       /\ UNCHANGED dyn_iv
    \/ /\ dyn_iv' = IF dyn_iv = 1..2 THEN 1..3 ELSE 1..2
       /\ UNCHANGED flag_or_p
View == flag_or_p
Sym == Permutations(Procs)
===="#;
    let cfg_fb = "CONSTANTS p1 = p1 p2 = p2\nINIT Init\nNEXT Next\nVIEW View\nSYMMETRY Sym\n";
    std::fs::write(dir.join("SymViewFallback.tla"), tla_fb).unwrap();
    std::fs::write(dir.join("SymViewFallback.cfg"), cfg_fb).unwrap();

    let interp_fb = tlx_testkit::tlx_default!()
        .args(["check", "SymViewFallback.tla", "-tlc", "-interp", "-workers", "1"])
        .dir(&dir)
        .timeout(Duration::from_secs(30))
        .run();
    assert_eq!(interp_fb.code, 0, "{}", interp_fb.text());

    let compiled_fb = tlx_testkit::tlx_default!()
        .args(["check", "SymViewFallback.tla", "-tlc", "-compile", "-workers", "1"])
        .envs([("TLX_PARANOID", "1"), ("TLX_PRERUN_REUSE", "0")])
        .dir(&dir)
        .timeout(Duration::from_secs(30))
        .run();
    assert_eq!(compiled_fb.code, 0, "{}", compiled_fb.text());
    assert_eq!(counts(&compiled_fb.stdout), counts(&interp_fb.stdout), "fallback compiled vs interp counts differ");
}

#[test]
fn sym_view_mixed_key_map_preserves_tlc_comparison_error() {
    let dir = tlx_testkit::TempDir::new("sym-view-mixed-map");
    let tla = r#"---- MODULE ReviewMap ----
EXTENDS TLC
CONSTANTS p1, p2, t_A
VARIABLE f
Procs == {p1, p2}
Init == \E p \in Procs, b \in BOOLEAN : f = (<<p, IF b THEN t_A ELSE "x">> :> TRUE)
Next == f' = ((<<p1, t_A>> :> TRUE) @@ (<<p2, "x">> :> TRUE))
View == <<f>>
Sym == Permutations(Procs)
===="#;
    let cfg = "CONSTANTS p1 = p1 p2 = p2 t_A = t_A\nINIT Init\nNEXT Next\nVIEW View\nSYMMETRY Sym\nCHECK_DEADLOCK FALSE\n";
    std::fs::write(dir.join("ReviewMap.tla"), tla).unwrap();
    std::fs::write(dir.join("ReviewMap.cfg"), cfg).unwrap();

    let interp = tlx_testkit::tlx_default!()
        .args(["check", "ReviewMap.tla", "-tlc", "-interp", "-workers", "1"])
        .dir(&dir)
        .timeout(Duration::from_secs(30))
        .run();
    assert_eq!(interp.code, 75, "{}", interp.text());

    let compiled = tlx_testkit::tlx_default!()
        .args(["check", "ReviewMap.tla", "-tlc", "-compile", "-workers", "1"])
        .envs([("TLX_PARANOID", "1"), ("TLX_PRERUN_REUSE", "0")])
        .dir(&dir)
        .timeout(Duration::from_secs(30))
        .run();
    assert_eq!(compiled.code, 75, "{}", compiled.text());
    assert!(compiled.text().contains("typed model value"), "{}", compiled.text());
}

#[test]
fn sym_view_losing_perms_do_not_intern_or_fill_value_store() {
    let dir = tlx_testkit::TempDir::new("sym-view-dyn-store");
    let tla = r#"---- MODULE ReviewDyn ----
EXTENDS Naturals, TLC
CONSTANTS p1, p2, p3, p4, p5, p6
VARIABLE msgs
Procs == {p1, p2, p3, p4, p5, p6}
Ids == <<p1, p2, p3, p4, p5, p6>>
Init == \E b \in BOOLEAN : msgs = <<Ids, ([i \in 1..512 |-> Ids[1 + ((i + (IF b THEN 0 ELSE 1)) % 6)]] :> TRUE)>>
Next == UNCHANGED msgs
View == <<msgs>>
Sym == Permutations(Procs)
===="#;
    let cfg = "CONSTANTS p1 = p1 p2 = p2 p3 = p3 p4 = p4 p5 = p5 p6 = p6\nINIT Init\nNEXT Next\nVIEW View\nSYMMETRY Sym\n";
    std::fs::write(dir.join("ReviewDyn.tla"), tla).unwrap();
    std::fs::write(dir.join("ReviewDyn.cfg"), cfg).unwrap();

    let stat_count = |out: &str, label: &str| -> u64 {
        out.lines()
            .find(|l| l.contains(label))
            .and_then(|l| l.split_whitespace().last())
            .and_then(|s| s.replace(',', "").parse::<u64>().ok())
            .unwrap_or_else(|| panic!("missing stat {label:?} in:\n{out}"))
    };

    // Default Dyn path (paranoid off): losing permutations must not intern into dynval.
    let dyn_run = tlx_testkit::tlx_default!()
        .args(["check", "ReviewDyn.tla", "-tlc", "-compile", "-workers", "1", "-stats"])
        .envs([("TLX_PRERUN_REUSE", "0"), ("TLX_VALUE_STORE", "0")])
        .dir(&dir)
        .timeout(Duration::from_secs(30))
        .run();
    assert_eq!(dyn_run.code, 0, "{}", dyn_run.text());
    let dyn_vals = stat_count(&dyn_run.text(), "Dyn interner values");
    assert!(dyn_vals <= 4, "expected losing permutations not to intern Dyn values, got {dyn_vals}:\n{}", dyn_run.text());

    // Value store path under tight -maxmem 2 (paranoid off): must complete cleanly
    // without freezing 719 losing permutations into the store.
    let store_run = tlx_testkit::tlx_default!()
        .args(["check", "ReviewDyn.tla", "-tlc", "-compile", "-workers", "1", "-maxmem", "2", "-stats"])
        .envs([("TLX_PRERUN_REUSE", "0"), ("TLX_VALUE_STORE", "1")])
        .dir(&dir)
        .timeout(Duration::from_secs(30))
        .run();
    assert_eq!(store_run.code, 0, "{}", store_run.text());
    let store_nodes = stat_count(&store_run.text(), "value store nodes");
    assert!(store_nodes <= 16, "expected losing permutations not to fill value store, got {store_nodes} nodes:\n{}", store_run.text());
}
