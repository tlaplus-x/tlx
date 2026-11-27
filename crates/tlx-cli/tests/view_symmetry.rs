//! Certified automatic symmetry over declared user tuple `VIEW`s: an exact
//! (full-retention) view, an unobserved-omission view certified through
//! erasure, and the fail-closed refusals for computed or guard-live views.

use std::time::Duration;

const PROC: &str = "CONSTANT Proc = {p1, p2, p3}\n";

fn spec(name: &str, body: &str, cfg: &str) -> tlx_testkit::TempDir {
    let src = format!("---- MODULE {name} ----\nEXTENDS TLC, Naturals, FiniteSets\nCONSTANT Proc\n{body}\n====\n");
    tlx_testkit::TempDir::with_spec(name, &src, cfg)
}

fn run(dir: &tlx_testkit::TempDir, name: &str, args: &[&str], env: &[(&str, &str)]) -> tlx_testkit::cli::Run {
    tlx_testkit::tlx_default!()
        .check(format!("{name}.tla"))
        .args(args)
        .env("TLX_PROOF_DIR", dir.join("proofs"))
        .envs(env.iter().copied())
        .dir(dir)
        .timeout(Duration::from_secs(60))
        .run()
}

fn distinct(out: &str) -> usize {
    out.lines()
        .find(|l| l.contains("distinct states found"))
        .and_then(|l| l.split_once(" distinct states found"))
        .and_then(|(head, _)| head.rsplit([' ', ',']).find_map(|t| t.replace(',', "").parse().ok()))
        .unwrap_or_else(|| panic!("no distinct-state line:\n{out}"))
}

const EXACT_BODY: &str = "VARIABLES pc, phase\n\
    Init == pc = [p \\in Proc |-> 0] /\\ phase = FALSE\n\
    Next == \\/ \\E p \\in Proc : pc[p] < 2 /\\ pc' = [pc EXCEPT ![p] = @ + 1] /\\ UNCHANGED phase\n\
    \x20       \\/ phase' = ~phase /\\ UNCHANGED pc\n\
    Inv == \\A p \\in Proc : pc[p] <= 2\n\
    View == <<phase, <<pc>>>>";

#[test]
fn an_exact_reordered_tuple_view_composes_with_symmetry() {
    let exact = format!("{PROC}INIT Init\nNEXT Next\nINVARIANT Inv\nVIEW View\nCHECK_DEADLOCK FALSE\n");
    let dir = spec("ExactView", EXACT_BODY, &exact);
    let mut plain = 0;
    for tier in ["-interp", "-compile"] {
        let env = [("TLX_PARANOID", "1"), ("TLX_SYMMETRY_PARANOID", "1")];
        let r = run(&dir, "ExactView", &[tier], &env);
        assert_eq!(r.code, 0, "{tier}: {}", r.text());
        assert!(r.stdout.contains("Optimizations: symmetry Permutations(Proc) (certificate generated"), "{tier}: {}", r.text());
        assert!(r.stdout.contains("(symmetry-reduced)"), "{tier}: {}", r.text());
        assert!(r.stdout.contains("Lean output:"), "{tier}: {}", r.text());
        let reduced = distinct(&r.stdout);
        let full = run(&dir, "ExactView", &[tier, "-noautosymmetry"], &env);
        assert_eq!(full.code, 0, "{tier}: {}", full.text());
        plain = distinct(&full.stdout);
        assert!(reduced < plain, "{tier}: {reduced} not fewer than {plain}\n{}", r.text());
        let parallel = run(&dir, "ExactView", &[tier, "-workers", "2"], &env);
        assert_eq!(parallel.code, 0, "{tier}: {}", parallel.text());
        assert_eq!(distinct(&parallel.stdout), reduced, "{tier}: multi-worker reduced count differs\n{}", parallel.text());
    }
    // `-tlc` applies nothing; it only reports the now-certifiable suggestion.
    let tlc = run(&dir, "ExactView", &["-tlc"], &[]);
    assert_eq!(tlc.code, 0, "{}", tlc.text());
    assert_eq!(distinct(&tlc.stdout), plain, "{}", tlc.text());
    assert!(!tlc.stdout.contains("Optimizations"), "{}", tlc.text());
    assert!(tlc.stdout.contains("Symmetry: Permutations(Proc) is provable for safety checking and not declared"), "{}", tlc.text());
}

const ERASED_BODY: &str = "VARIABLES pc, phase, ghost\n\
    Init == pc = [p \\in Proc |-> 0] /\\ phase = FALSE /\\ ghost = FALSE\n\
    Next == \\E p \\in Proc : pc[p] < 2 /\\ pc' = [pc EXCEPT ![p] = @ + 1] /\\ phase' = ~phase /\\ ghost' = phase\n\
    Inv == \\A p \\in Proc : pc[p] <= 2\n\
    Small == \\A p \\in Proc : pc[p] <= 1\n\
    View == <<phase, <<pc>>>>";

#[test]
fn an_unobserved_omission_tuple_view_composes_with_erasure() {
    let cfg = format!("{PROC}INIT Init\nNEXT Next\nINVARIANT Inv\nVIEW View\nCHECK_DEADLOCK FALSE\n");
    let dir = spec("ErasedView", ERASED_BODY, &cfg);
    let env = [("TLX_PARANOID", "1"), ("TLX_SYMMETRY_PARANOID", "1")];
    for tier in ["-interp", "-compile"] {
        let r = run(&dir, "ErasedView", &[tier], &env);
        assert_eq!(r.code, 0, "{tier}: {}", r.text());
        assert!(r.stdout.contains("Optimizations: symmetry Permutations(Proc) (certificate generated"), "{tier}: {}", r.text());
        assert!(r.stdout.contains("(symmetry-reduced)"), "{tier}: {}", r.text());
        let reduced = distinct(&r.stdout);
        let full = run(&dir, "ErasedView", &[tier, "-noautosymmetry"], &env);
        assert_eq!(full.code, 0, "{tier}: {}", full.text());
        let plain = distinct(&full.stdout);
        assert!(reduced < plain, "{tier}: {reduced} not fewer than {plain}\n{}", r.text());
        let parallel = run(&dir, "ErasedView", &[tier, "-workers", "2"], &env);
        assert_eq!(parallel.code, 0, "{tier}: {}", parallel.text());
        assert_eq!(distinct(&parallel.stdout), reduced, "{tier}: multi-worker reduced count differs\n{}", parallel.text());
    }
    // An omitting view gets no `-tlc` suggestion: declaring the group would use
    // TLC's whole-state least-view path, not the certified erasure composition.
    let tlc = run(&dir, "ErasedView", &["-tlc"], &[]);
    assert_eq!(tlc.code, 0, "{}", tlc.text());
    assert!(!tlc.stdout.contains("Symmetry: "), "{}", tlc.text());
    assert!(!tlc.stdout.contains("Optimizations"), "{}", tlc.text());
    // A concrete counterexample lifts through the composed quotient: the trace
    // keeps the erased `ghost` variable.
    let bad = format!("{PROC}INIT Init\nNEXT Next\nINVARIANT Small\nVIEW View\nCHECK_DEADLOCK FALSE\n");
    let bad_dir = spec("ErasedViewCex", ERASED_BODY, &bad);
    for tier in ["-interp", "-compile"] {
        let r = run(&bad_dir, "ErasedViewCex", &[tier], &env);
        assert_eq!(r.code, 12, "{tier}: {}", r.text());
        assert!(r.stdout.contains("Invariant Small is violated."), "{tier}: {}", r.text());
        assert!(r.stdout.contains("/\\ ghost = "), "{tier}: the trace must keep the erased variable\n{}", r.text());
    }
}

const GUARD_LIVE_BODY: &str = "VARIABLES pc, n\n\
    Init == pc = [p \\in Proc |-> 0] /\\ n = 0\n\
    Next == n < 2 /\\ \\E p \\in Proc : pc[p] < 2 /\\ pc' = [pc EXCEPT ![p] = @ + 1] /\\ n' = n + 1\n\
    Inv == \\A p \\in Proc : pc[p] <= 2\n\
    View == <<pc>>";

#[test]
fn a_guard_live_or_computed_view_keeps_its_search_without_symmetry() {
    let cfg = format!("{PROC}INIT Init\nNEXT Next\nINVARIANT Inv\nVIEW View\nCHECK_DEADLOCK FALSE\n");
    let dir = spec("GuardLiveView", GUARD_LIVE_BODY, &cfg);
    for tier in ["-interp", "-compile"] {
        let r = run(&dir, "GuardLiveView", &[tier, "-stats"], &[("TLX_PARANOID", "1")]);
        assert_eq!(r.code, 0, "{tier}: {}", r.text());
        assert!(r.stdout.contains("Optimizations: none applicable."), "{tier}: {}", r.text());
        assert!(
            r.text().contains("not applied: no connected Lean certificate covers automatic symmetry over the cfg VIEW"),
            "{tier}: {}",
            r.text()
        );
        let plain = run(&dir, "GuardLiveView", &[tier, "-noautosymmetry"], &[("TLX_PARANOID", "1")]);
        assert_eq!(distinct(&r.stdout), distinct(&plain.stdout), "{tier}: the declared VIEW search must be intact");
    }
    // A computed or duplicated variable VIEW is refused before any certificate.
    for view in ["View == <<pc, n + 1>>", "View == <<pc, pc>>"] {
        let body = GUARD_LIVE_BODY.replace("View == <<pc>>", view);
        let dir = spec("ComputedView", &body, &cfg);
        let r = run(&dir, "ComputedView", &["-interp", "-stats"], &[]);
        assert_eq!(r.code, 0, "{view}: {}", r.text());
        assert!(r.stdout.contains("Optimizations: none applicable."), "{view}: {}", r.text());
        assert!(r.text().contains("not applied: the cfg VIEW is not a tuple of distinct state variables"), "{view}: {}", r.text());
    }
}

const EQUIV_BODY: &str = "VARIABLES msgs, phase, ghost\n\
    Init == msgs = {} /\\ phase = FALSE /\\ ghost = FALSE\n\
    Next == \\E p, q \\in Proc : p # q /\\ Cardinality(msgs) < 1\n\
    \x20       /\\ msgs' = msgs \\cup {[src |-> p, dst |-> q]}\n\
    \x20       /\\ phase' = ~phase /\\ ghost' = phase\n\
    Inv == Cardinality(msgs) <= 1\n\
    View == <<phase, msgs>>";

#[test]
fn an_equivariant_omission_view_composes_with_erasure() {
    let cfg = format!("{PROC}INIT Init\nNEXT Next\nINVARIANT Inv\nVIEW View\nCHECK_DEADLOCK FALSE\n");
    let dir = spec("EquivView", EQUIV_BODY, &cfg);
    let env = [("TLX_PARANOID", "1"), ("TLX_SYMMETRY_PARANOID", "1")];
    for tier in ["-interp", "-compile"] {
        let r = run(&dir, "EquivView", &[tier], &env);
        assert_eq!(r.code, 0, "{tier}: {}", r.text());
        assert!(r.stdout.contains("Optimizations: symmetry Permutations(Proc) (certificate generated"), "{tier}: {}", r.text());
        let reduced = distinct(&r.stdout);
        let full = run(&dir, "EquivView", &[tier, "-noautosymmetry"], &env);
        assert_eq!(full.code, 0, "{tier}: {}", full.text());
        let plain = distinct(&full.stdout);
        assert!(reduced < plain, "{tier}: {reduced} not fewer than {plain}\n{}", r.text());
        // A set of two-key records is outside the keyed rule IR, so the
        // emitted composition must be the equivariant one.
        let proof = r
            .stdout
            .lines()
            .find_map(|l| l.strip_prefix("Lean output: "))
            .and_then(|l| l.split_once(" (").map(|(p, _)| p))
            .expect("a Lean output path");
        let cert = std::fs::read_to_string(proof).unwrap();
        assert!(
            cert.contains("namespace TlxOptimization.GeneratedErasedEquivSymmetry"),
            "{tier}: {}",
            cert.lines().find(|l| l.contains("namespace")).unwrap_or("")
        );
    }
}

const SINGLE_BODY: &str = "VARIABLES pc\n\
    Init == pc = [p \\in Proc |-> 0]\n\
    Next == \\E p \\in Proc : pc[p] < 2 /\\ pc' = [pc EXCEPT ![p] = @ + 1]\n\
    Inv == \\A p \\in Proc : pc[p] <= 2\n\
    View == pc";

#[test]
fn a_single_variable_view_is_the_degenerate_full_retention_tuple() {
    let cfg = format!("{PROC}INIT Init\nNEXT Next\nINVARIANT Inv\nVIEW View\nCHECK_DEADLOCK FALSE\n");
    let dir = spec("SingleView", SINGLE_BODY, &cfg);
    for tier in ["-interp", "-compile"] {
        let r = run(&dir, "SingleView", &[tier], &[("TLX_PARANOID", "1"), ("TLX_SYMMETRY_PARANOID", "1")]);
        assert_eq!(r.code, 0, "{tier}: {}", r.text());
        assert!(r.stdout.contains("Optimizations: symmetry Permutations(Proc) (certificate generated"), "{tier}: {}", r.text());
        let reduced = distinct(&r.stdout);
        let full = run(&dir, "SingleView", &[tier, "-noautosymmetry"], &[]);
        assert_eq!(full.code, 0, "{tier}: {}", full.text());
        assert!(reduced < distinct(&full.stdout), "{tier}: {reduced} not fewer than {}\n{}", distinct(&full.stdout), r.text());
    }
}

const GROUP_FULL_BODY: &str = "VARIABLES pc, role, phase\n\
    serverVars == <<pc, role>>\n\
    logVars == <<phase>>\n\
    Init == pc = [p \\in Proc |-> 0] /\\ role = \"follower\" /\\ phase = FALSE\n\
    Next == \\/ \\E p \\in Proc : pc[p] < 2 /\\ pc' = [pc EXCEPT ![p] = @ + 1] /\\ UNCHANGED <<role, phase>>\n\
    \x20       \\/ phase' = ~phase /\\ UNCHANGED <<pc, role>>\n\
    Inv == \\A p \\in Proc : pc[p] <= 2\n\
    View == <<logVars, serverVars>>";

#[test]
fn nested_variable_group_definitions_compose_in_full_retention() {
    let cfg = format!("{PROC}INIT Init\nNEXT Next\nINVARIANT Inv\nVIEW View\nCHECK_DEADLOCK FALSE\n");
    let dir = spec("GroupFullView", GROUP_FULL_BODY, &cfg);
    for tier in ["-interp", "-compile"] {
        let env = [("TLX_PARANOID", "1"), ("TLX_SYMMETRY_PARANOID", "1")];
        let r = run(&dir, "GroupFullView", &[tier], &env);
        assert_eq!(r.code, 0, "{tier}: {}", r.text());
        assert!(r.stdout.contains("Optimizations: symmetry Permutations(Proc) (certificate generated"), "{tier}: {}", r.text());
        let reduced = distinct(&r.stdout);
        let full = run(&dir, "GroupFullView", &[tier, "-noautosymmetry"], &[]);
        assert_eq!(full.code, 0, "{tier}: {}", full.text());
        assert!(reduced < distinct(&full.stdout), "{tier}: {reduced} not fewer than {}\n{}", distinct(&full.stdout), r.text());
    }
}

const GROUP_ERASED_BODY: &str = "VARIABLES pc, phase, ghost\n\
    serverVars == <<pc>>\n\
    logVars == <<phase>>\n\
    Init == pc = [p \\in Proc |-> 0] /\\ phase = FALSE /\\ ghost = FALSE\n\
    Next == \\E p \\in Proc : pc[p] < 2 /\\ pc' = [pc EXCEPT ![p] = @ + 1] /\\ phase' = ~phase /\\ ghost' = phase\n\
    Inv == \\A p \\in Proc : pc[p] <= 2\n\
    View == <<logVars, serverVars>>";

#[test]
fn nested_variable_group_definitions_compose_with_erasure() {
    let cfg = format!("{PROC}INIT Init\nNEXT Next\nINVARIANT Inv\nVIEW View\nCHECK_DEADLOCK FALSE\n");
    let dir = spec("GroupErasedView", GROUP_ERASED_BODY, &cfg);
    for tier in ["-interp", "-compile"] {
        let env = [("TLX_PARANOID", "1"), ("TLX_SYMMETRY_PARANOID", "1")];
        let r = run(&dir, "GroupErasedView", &[tier], &env);
        assert_eq!(r.code, 0, "{tier}: {}", r.text());
        assert!(r.stdout.contains("Optimizations: symmetry Permutations(Proc) (certificate generated"), "{tier}: {}", r.text());
        let reduced = distinct(&r.stdout);
        let full = run(&dir, "GroupErasedView", &[tier, "-noautosymmetry"], &[]);
        assert_eq!(full.code, 0, "{tier}: {}", full.text());
        assert!(reduced < distinct(&full.stdout), "{tier}: {reduced} not fewer than {}\n{}", distinct(&full.stdout), r.text());
    }
}

const GROUP_DUP_BODY: &str = "VARIABLES pc, phase\n\
    serverVars == <<pc, phase>>\n\
    logVars == <<phase>>\n\
    Init == pc = [p \\in Proc |-> 0] /\\ phase = FALSE\n\
    Next == \\E p \\in Proc : pc[p] < 2 /\\ pc' = [pc EXCEPT ![p] = @ + 1] /\\ phase' = ~phase\n\
    Inv == \\A p \\in Proc : pc[p] <= 2\n\
    View == <<serverVars, logVars>>";

#[test]
fn a_variable_repeated_across_groups_refuses_symmetry() {
    let cfg = format!("{PROC}INIT Init\nNEXT Next\nINVARIANT Inv\nVIEW View\nCHECK_DEADLOCK FALSE\n");
    let dir = spec("GroupDupView", GROUP_DUP_BODY, &cfg);
    for tier in ["-interp", "-compile"] {
        let r = run(&dir, "GroupDupView", &[tier, "-stats"], &[("TLX_PARANOID", "1")]);
        assert_eq!(r.code, 0, "{tier}: {}", r.text());
        assert!(r.stdout.contains("Optimizations: none applicable."), "{tier}: {}", r.text());
        assert!(r.text().contains("not applied: the cfg VIEW is not a tuple of distinct state variables"), "{tier}: {}", r.text());
        let full = run(&dir, "GroupDupView", &[tier, "-noautosymmetry"], &[]);
        assert_eq!(distinct(&r.stdout), distinct(&full.stdout), "{tier}: the declared VIEW search must be intact");
    }
    // A group assigned a `.cfg` value is not a group of state variables.
    let value_cfg = format!("{PROC}CONSTANT serverVars = <<1, 2>>\nINIT Init\nNEXT Next\nINVARIANT Inv\nVIEW View\nCHECK_DEADLOCK FALSE\n");
    let value_dir = spec("GroupValueView", GROUP_FULL_BODY, &value_cfg);
    let r = run(&value_dir, "GroupValueView", &["-interp", "-stats"], &[]);
    assert_eq!(r.code, 0, "{}", r.text());
    assert!(r.stdout.contains("Optimizations: none applicable."), "{}", r.text());
    assert!(r.text().contains("not applied: the cfg VIEW is not a tuple of distinct state variables"), "{}", r.text());
    let tlc = run(&value_dir, "GroupValueView", &["-tlc"], &[]);
    assert_eq!(tlc.code, 0, "{}", tlc.text());
    assert!(!tlc.stdout.contains("Symmetry: "), "{}", tlc.text());
}
