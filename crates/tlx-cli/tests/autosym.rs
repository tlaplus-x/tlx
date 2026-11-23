//! Certified keyed symmetry and refusal of unsupported automatic applications.

use std::time::Duration;

/// Write a spec with constant `Proc = {p1, p2, p3}` into a new directory.
fn spec(body: &str, cfg: &str) -> tlx_testkit::TempDir {
    let dir = tlx_testkit::TempDir::new("autosym");
    std::fs::write(
        dir.join("Spec.tla"),
        format!("---- MODULE Spec ----\nEXTENDS TLC, Naturals, FiniteSets\nCONSTANT Proc\n{body}\n====\n"),
    )
    .unwrap();
    std::fs::write(dir.join("Spec.cfg"), format!("CONSTANT Proc = {{p1, p2, p3}}\nINIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n{cfg}\n"))
        .unwrap();
    dir
}

/// Run `tlx check Spec.tla` in the default mode (and tier) on `spec(body,
/// cfg)`; `-tlc` and tier flags come with `args`.
fn run(body: &str, cfg: &str, args: &[&str], env: &[(&str, &str)]) -> tlx_testkit::cli::Run {
    let dir = spec(body, cfg);
    tlx_testkit::tlx_default!()
        .args(["check", "Spec.tla"])
        .args(args)
        .env("TLX_PROOF_DIR", dir.join("proofs"))
        .envs(env.iter().copied())
        .dir(&dir)
        .timeout(Duration::from_secs(60))
        .run()
}

const SYMMETRIC: &str =
    "VARIABLE pc\nInit == pc = [p \\in Proc |-> 0]\nNext == \\E p \\in Proc : pc[p] < 2 /\\ pc' = [pc EXCEPT ![p] = @ + 1]\n\
                         Inv == \\A p \\in Proc : pc[p] <= 2";

/// Symmetric for 15 steps (beyond the bounded check's depth 10); then a
/// CHOOSE picks a process.
const DEEP: &str = "VARIABLES n, pc\nInit == n = 0 /\\ pc = [p \\in Proc |-> 0]\n\
                    Next == \\/ n < 15 /\\ n' = n + 1 /\\ UNCHANGED pc\n\
                    \x20       \\/ n = 15 /\\ \\E q \\in Proc : pc[q] = 0 /\\ pc' = [pc EXCEPT ![CHOOSE p \\in Proc : pc[p] = 0] = 1] /\\ UNCHANGED n";

#[test]
fn a_provable_symmetry_is_suggested_under_tlc() {
    let r = run(SYMMETRIC, "INVARIANT Inv", &["-tlc"], &[]);
    assert_eq!(r.code, 0, "{}", r.text());
    assert!(
        r.stdout.contains("Symmetry: Permutations(Proc) is provable for safety checking and not declared; to use it, run without -tlc, or define Perms == Permutations(Proc) and add \"SYMMETRY Perms\" to the cfg."),
        "{}",
        r.text()
    );
    // Nothing is applied: TLC's counts, no Optimizations line.
    assert!(r.stdout.contains("27 distinct states found, 0 states left on queue."), "{}", r.text());
    assert!(!r.stdout.contains("Optimizations"), "{}", r.text());
}

#[test]
fn the_default_mode_applies_connected_keyed_symmetry() {
    for tier in ["-interp", "-compile"] {
        let r = run(SYMMETRIC, "INVARIANT Inv", &[tier], &[]);
        assert_eq!(r.code, 0, "{}", r.text());
        assert!(r.stdout.contains("certificate generated"), "{}", r.text());
        assert!(r.stdout.contains("10 distinct states found, 0 states left on queue (symmetry-reduced)."), "{}", r.text());
        assert!(r.stdout.contains("Lean output:"), "{}", r.text());
        assert!(!r.stdout.contains("Symmetry: "), "no suggestion in the default mode: {}", r.text());
    }
    let r = run(SYMMETRIC, "INVARIANT Inv", &["-noautosymmetry"], &[]);
    assert_eq!(r.code, 0, "{}", r.text());
    assert!(r.stdout.contains("Optimizations: none applicable."), "{}", r.text());
    assert!(r.stdout.contains("27 distinct states found, 0 states left on queue."), "{}", r.text());
}

#[test]
fn refused_symmetry_keeps_tlc_trace_length() {
    let inv = "INVARIANT Small\n";
    let body = format!("{SYMMETRIC}\nSmall == Cardinality({{p \\in Proc : pc[p] = 2}}) < 2");
    let tlc = run(&body, inv, &["-tlc"], &[]);
    let reduced = run(&body, inv, &[], &[]);
    assert_eq!(tlc.code, 12, "{}", tlc.text());
    assert_eq!(reduced.code, 12, "{}", reduced.text());
    let states = |t: &str| t.lines().filter(|l| l.starts_with("State ")).count();
    assert_eq!(states(&reduced.stdout), states(&tlc.stdout), "{}\n{}", tlc.text(), reduced.text());
    assert!(reduced.stdout.contains("Error: Invariant Small is violated."), "{}", reduced.text());
}

#[test]
fn temporal_properties_and_output_keep_the_full_search() {
    let live = "PROPERTY Live\n";
    let body = format!("{SYMMETRIC}\nLive == <>(\\A p \\in Proc : pc[p] >= 0)");
    let live_dir = spec(&body, live);
    let r = tlx_testkit::tlx_default!().args(["check", "Spec.tla", "-stats"]).dir(&live_dir).timeout(Duration::from_secs(60)).run();
    assert_eq!(r.code, 0, "{}", r.text());
    assert!(r.stdout.contains("Optimizations: none applicable."), "{}", r.text());
    assert!(r.text().contains("not applied: temporal properties are checked"), "{}", r.text());
    assert!(r.stdout.contains("27 distinct states found, 0 states left on queue."), "{}", r.text());
    let printing = SYMMETRIC.replace("Next == ", "Next == PrintT(1) /\\ ");
    let r = run(&printing, "", &["-stats"], &[]);
    assert_eq!(r.code, 0, "{}", r.text());
    assert!(r.stdout.contains("Optimizations: none applicable."), "{}", r.text());
    assert!(r.text().contains("not applied: the output or results depend on the states explored (PrintT at Spec.tla:"), "{}", r.text());
}

#[test]
fn suggest_checks_every_candidate() {
    let r = run(SYMMETRIC, "INVARIANT Inv", &["-checksymmetry", "-suggest"], &[]);
    assert_eq!(r.code, 0, "{}", r.text());
    assert!(r.stdout.contains("Symmetry: Proc = {p1, p2, p3}: proven: Permutations(Proc); bounded check: no violation"), "{}", r.text());
    assert!(r.stdout.contains("define Perms == Permutations(Proc)"), "{}", r.text());
    let r = run(DEEP, "", &["-checksymmetry", "-suggest", "-symmetrydepth", "20"], &[]);
    assert_eq!(r.code, 0, "{}", r.text());
    assert!(r.stdout.contains("not provable (CHOOSE at Spec.tla:"), "{}", r.text());
    assert!(r.stdout.contains("bounded check: violated"), "{}", r.text());
}

#[test]
fn force_cannot_bypass_the_certificate_gate() {
    let r = run(SYMMETRIC, "INVARIANT Inv", &[], &[("TLX_AUTOSYM_FORCE", "Proc"), ("TLX_SYMMETRY_PARANOID", "1")]);
    assert_eq!(r.code, 0, "{}", r.text());
    // Force changes candidate selection only; the connected proof is still required.
    assert!(r.stdout.contains("10 distinct states found, 0 states left on queue (symmetry-reduced)."), "{}", r.text());
    assert!(r.stdout.contains("certificate generated"), "{}", r.text());
}

#[test]
fn certified_symmetry_labels_dumps_and_statistics() {
    let dir = tlx_testkit::TempDir::new("autosym-label");
    std::fs::write(
        dir.join("Spec.tla"),
        format!("---- MODULE Spec ----\nEXTENDS TLC, Naturals, FiniteSets\nCONSTANT Proc\n{SYMMETRIC}\n====\n"),
    )
    .unwrap();
    std::fs::write(dir.join("Spec.cfg"), "CONSTANT Proc = {p1, p2, p3}\nINIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n").unwrap();
    let r = tlx_testkit::tlx_default!()
        .args(["check", "Spec.tla", "-dump", "states", "-stats", "json=stats.json", "-tool"])
        .env("TLX_PROOF_DIR", dir.join("proofs"))
        .dir(&dir)
        .timeout(Duration::from_secs(30))
        .run();
    assert_eq!(r.code, 0, "{}", r.text());
    assert!(r.stdout.contains("@!@!@STARTMSG 9100:0 @!@!@\nOptimizations: symmetry"), "{}", r.text());
    let dump = std::fs::read_to_string(dir.join("states.dump")).unwrap();
    assert!(dump.starts_with("\\* reduced by symmetry; use -tlc for the full graph\n"), "{dump}");
    let stats = std::fs::read_to_string(dir.join("stats.json")).unwrap();
    assert!(stats.contains(r#""proof":"generated-lean""#), "{stats}");
}

#[test]
fn forcing_a_wrong_candidate_keeps_the_full_search() {
    for tier in ["-interp", "-compile"] {
        let reference = run(DEEP, "", &[tier, "-noautosymmetry"], &[]);
        let forced = run(DEEP, "", &[tier, "-stats"], &[("TLX_AUTOSYM_FORCE", "Proc"), ("TLX_SYMMETRY_PARANOID", "1")]);
        assert_eq!(forced.code, reference.code, "{}", forced.text());
        assert_eq!(tlx_testkit::cli::counts(&forced.stdout), tlx_testkit::cli::counts(&reference.stdout));
        assert!(forced.text().contains("no connected Lean certificate for automatic symmetry"), "{}", forced.text());
    }
}

#[test]
fn refused_symmetry_keeps_counts_across_workers() {
    // A proven group is equivariant: the orbits, and the successors of each,
    // do not depend on which representative a worker schedule picks.
    let counts = |args: &[&str]| {
        let r = run(SYMMETRIC, "INVARIANT Inv", args, &[]);
        assert_eq!(r.code, 0, "{}", r.text());
        tlx_testkit::cli::counts(&r.stdout).iter().map(|s| s.to_string()).collect::<Vec<_>>()
    };
    let one = counts(&["-workers", "1", "-interp"]);
    assert_eq!(one.len(), 2, "{one:?}");
    assert_eq!(counts(&["-workers", "4", "-interp"]), one);
    assert_eq!(counts(&["-workers", "1", "-compile"]), one);
    assert_eq!(counts(&["-workers", "4", "-compile"]), one);
}

#[test]
fn unproved_choice_symmetry_is_refused_in_every_tier() {
    for choose in ["(CHOOSE m \\in msgs : TRUE).val", "LET m == CHOOSE m \\in msgs : TRUE IN m.val"] {
        let body = format!(
            "VARIABLES pc, msgs\nInit == pc = [p \\in Proc |-> 0] /\\ msgs = {{[from |-> p, val |-> 7] : p \\in Proc}}\n\
             Next == \\E p \\in Proc : pc[p] < 2 /\\ pc' = [pc EXCEPT ![p] = @ + 1] /\\ UNCHANGED msgs\n\
             Inv == ({choose}) = 7"
        );
        for (tier, env) in [
            ("-interp", vec![]),
            ("-compile", vec![("TLX_PARANOID", "1")]),
            ("-compile", vec![("TLX_NO_NATIVE", "1"), ("TLX_PRERUN_REUSE", "0")]),
            ("-compile", vec![("TLX_JIT", "only"), ("TLX_PRERUN_REUSE", "0")]),
        ] {
            let r = run(&body, "INVARIANT Inv", &[tier], &env);
            assert_eq!(r.code, 0, "{}", r.text());
            assert!(!r.stdout.contains("(runtime guard; safety"), "{}", r.text());
            assert!(r.stdout.contains("27 distinct states found"), "{}", r.text());
        }
    }
}

#[test]
fn unproved_late_choice_keeps_the_original_search() {
    // After the bounded probe, candidate projections first disagree. The
    // chosen field then depends on the order of renamed process identities.
    let body = "VARIABLES pc, n\nInit == pc = [p \\in Proc |-> 0] /\\ n = 0\n\
        Next == (n < 15 /\\ n' = n + 1 /\\ UNCHANGED pc) \\/ (n = 15 /\\ \\E p \\in Proc : pc[p] = 0 /\\ pc' = [pc EXCEPT ![p] = 1] /\\ UNCHANGED n)\n\
        Inv == (CHOOSE m \\in {[from |-> p, val |-> pc[p]] : p \\in Proc} : TRUE).val = 0";
    for tier in ["-interp", "-compile"] {
        let reference = run(body, "INVARIANT Inv", &[tier, "-noautosymmetry"], &[]);
        let guarded = run(body, "INVARIANT Inv", &[tier], &[("TLX_PARANOID", "1"), ("TLX_PRERUN", "1")]);
        assert_eq!(reference.code, 12, "{}", reference.text());
        assert_eq!(guarded.code, reference.code, "{}", guarded.text());
        assert!(!guarded.stdout.contains("restarting without automatic symmetry"), "{}", guarded.text());
        let counts = |s: &str| s.lines().find(|s| s.contains("states generated,")).unwrap().to_string();
        assert_eq!(counts(&guarded.stdout), counts(&reference.stdout));
        assert!(!guarded.stdout.contains("(symmetry-reduced)"), "{}", guarded.text());
    }
}

#[test]
fn unproved_guard_candidates_are_not_evaluated() {
    let body = "VARIABLES n, msgs\n\
        Init == n = 0 /\\ msgs = {[flag |-> f, from |-> p, val |-> 7] : f \\in {0, 1}, p \\in Proc}\n\
        Next == n < 16 /\\ n' = n + 1 /\\ UNCHANGED msgs\n\
        Inv == (CHOOSE m \\in msgs : m.flag = 0 \\/ n < 15 \\/ 1 \\div 0 = 0).val = 7";
    for env in [vec![], vec![("TLX_NO_NATIVE", "1")], vec![("TLX_PARANOID", "1")], vec![("TLX_JIT", "only")]] {
        let mut env = env;
        env.extend([("TLX_PRERUN", "1"), ("TLX_PRERUN_REUSE", "0")]);
        let guarded = run(body, "INVARIANT Inv", &["-compile"], &env);
        assert_eq!(guarded.code, 0, "{}", guarded.text());
        assert!(!guarded.stdout.contains("restarting without automatic symmetry"), "{}", guarded.text());
        assert!(guarded.stdout.contains("17 distinct states found, 0 states left on queue."), "{}", guarded.text());
    }
}

#[test]
fn generated_symmetry_proofs_are_mandatory_and_never_overwritten() {
    let dir = spec(SYMMETRIC, "INVARIANT Inv");
    let proof_dir = dir.join("proofs");
    let run = || tlx_testkit::tlx_default!().args(["check", "Spec.tla", "-interp", "-proofdir"]).arg(&proof_dir).dir(&dir).run();
    let mut printed_paths = Vec::new();
    for _ in 0..2 {
        let r = run();
        assert_eq!(r.code, 0, "{}", r.text());
        assert!(r.stdout.contains("not verified; parametric keyed-symmetry"), "{}", r.text());
        let line = r.stdout.lines().find(|l| l.starts_with("Lean output: ")).unwrap().to_string();
        printed_paths.push(line);
    }
    assert_eq!(printed_paths[0], printed_paths[1], "identical certificates should deduplicate");
    assert!(!dir.join(".tlx-proofs").exists(), "cwd must not be polluted with .tlx-proofs");
    let proofs: Vec<_> = std::fs::read_dir(&proof_dir).unwrap().collect();
    assert_eq!(proofs.len(), 1);
    let text = std::fs::read_to_string(proofs[0].as_ref().unwrap().path().join("Optimization.lean")).unwrap();
    assert!(text.contains("namespace TlxOptimization.GeneratedSymmetry"));
    assert!(text.contains("theorem counterexample_lifts"));

    let blocked = spec(SYMMETRIC, "INVARIANT Inv");
    let blocked_file = blocked.join("blocked-proofs");
    std::fs::write(&blocked_file, "occupied").unwrap();
    let r = tlx_testkit::tlx_default!().args(["check", "Spec.tla", "-interp", "-proofdir"]).arg(&blocked_file).dir(&blocked).run();
    assert_eq!(r.code, 2, "{}", r.text());
    assert!(r.stdout.contains("Cannot write mandatory optimization Lean output"), "{}", r.text());
    assert!(!r.stdout.contains("Computing initial states"), "{}", r.text());
    assert_eq!(std::fs::read_to_string(&blocked_file).unwrap(), "occupied");

    let r = tlx_testkit::tlx_default!().args(["check", "Spec.tla", "-interp"]).env("TLX_PROOF_DIR", &blocked_file).dir(&blocked).run();
    assert_eq!(r.code, 2, "{}", r.text());
    assert!(r.stdout.contains("Cannot write mandatory optimization Lean output"), "{}", r.text());

    let override_dir = blocked.join("override-proofs");
    let r = tlx_testkit::tlx_default!()
        .args(["check", "Spec.tla", "-interp", "-proofdir"])
        .arg(&override_dir)
        .env("TLX_PROOF_DIR", &blocked_file)
        .dir(&blocked)
        .run();
    assert_eq!(r.code, 0, "CLI -proofdir must win over TLX_PROOF_DIR: {}", r.text());
    assert_eq!(std::fs::read_dir(&override_dir).unwrap().count(), 1);
}

#[cfg(unix)]
#[test]
fn read_only_cwd_succeeds_without_polluting_working_directory() {
    use std::os::unix::fs::PermissionsExt;

    let dir = spec(SYMMETRIC, "INVARIANT Inv");
    let cache = tlx_testkit::TempDir::new("autosym-cache");
    std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o555)).unwrap();
    let r = tlx_testkit::tlx_default!().args(["check", "Spec.tla", "-interp"]).env("TLX_CACHE", cache.path()).dir(&dir).run();
    // Always restore permissions before asserting so TempDir cleanup succeeds.
    std::fs::set_permissions(&dir, std::fs::Permissions::from_mode(0o755)).unwrap();

    assert_eq!(r.code, 0, "{}", r.text());
    assert!(r.stdout.contains("10 distinct states found, 0 states left on queue (symmetry-reduced)."), "{}", r.text());
    assert!(!dir.join(".tlx-proofs").exists());
    let entries: Vec<_> = std::fs::read_dir(cache.join("proofs")).unwrap().collect();
    assert_eq!(entries.len(), 1);
    let lean = std::fs::read_to_string(entries[0].as_ref().unwrap().path().join("Optimization.lean")).unwrap();
    assert!(lean.contains("namespace TlxOptimization.GeneratedSymmetry"));

    // Without -proofdir, TLX_PROOF_DIR, or TLX_CACHE, an unwritable HOME cache falls back to $TMPDIR/tlx-proofs.
    let fake_home = tlx_testkit::TempDir::new("autosym-bad-home");
    std::fs::write(fake_home.join(".cache"), "not a directory").unwrap();
    let fake_tmp = tlx_testkit::TempDir::new("autosym-tmp");
    let r = tlx_testkit::tlx_default!()
        .args(["check", "Spec.tla", "-interp"])
        .env("HOME", fake_home.path())
        .env("TMPDIR", fake_tmp.path())
        .dir(&dir)
        .run();
    assert_eq!(r.code, 0, "{}", r.text());
    assert_eq!(std::fs::read_dir(fake_tmp.join("tlx-proofs")).unwrap().count(), 1);
}

#[test]
fn certified_symmetry_preserves_deadlocks_and_concrete_violations() {
    let body = format!("{SYMMETRIC}\nSmall == \\A p \\in Proc : pc[p] < 2");
    for tier in ["-interp", "-compile"] {
        let bad = run(&body, "INVARIANT Small", &[tier], &[("TLX_PARANOID", "1"), ("TLX_SYMMETRY_PARANOID", "1")]);
        assert_eq!(bad.code, 12, "{}", bad.text());
        assert!(bad.stdout.contains("certificate generated"), "{}", bad.text());
        assert_eq!(bad.stdout.lines().filter(|l| l.starts_with("State ")).count(), 3, "{}", bad.text());
        let d = spec(SYMMETRIC, "INVARIANT Inv");
        let cfg = std::fs::read_to_string(d.join("Spec.cfg")).unwrap().replace("CHECK_DEADLOCK FALSE", "CHECK_DEADLOCK TRUE");
        std::fs::write(d.join("Spec.cfg"), cfg).unwrap();
        let dead = tlx_testkit::tlx_default!().args(["check", "Spec.tla", tier]).env("TLX_PROOF_DIR", d.join("proofs")).dir(&d).run();
        assert_eq!(dead.code, 11, "{}", dead.text());
        assert!(dead.stdout.contains("certificate generated"), "{}", dead.text());
        assert!(dead.stdout.contains("Deadlock reached"), "{}", dead.text());
    }
}
