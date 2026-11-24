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
            "VARIABLES pc, msgs\nInit == pc = [p \\in Proc |-> 0] /\\ msgs = {{[from |-> p, val |-> v] : p \\in Proc, v \\in {{7, 8}}}}\n\
             Next == \\E p \\in Proc : pc[p] < 2 /\\ pc' = [pc EXCEPT ![p] = @ + 1] /\\ UNCHANGED msgs\n\
             Inv == ({choose}) \\in {{7, 8}}"
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
            assert!(!r.stdout.contains("(symmetry-reduced)"), "{}", r.text());
            assert!(r.stdout.contains("27 distinct states found"), "{}", r.text());
        }
    }
}

#[test]
fn certified_choice_symmetry_reduces_in_every_tier() {
    for choose in ["(CHOOSE m \\in msgs : TRUE).val", "LET m == CHOOSE m \\in msgs : TRUE IN m.val"] {
        let body = format!(
            "VARIABLES pc, msgs\nInit == pc = [p \\in Proc |-> 0] /\\ msgs = {{[from |-> p, val |-> 7] : p \\in Proc}}\n\
             Next == \\E p \\in Proc : pc[p] < 2 /\\ pc' = [pc EXCEPT ![p] = @ + 1] /\\ UNCHANGED msgs\n\
             Inv == ({choose}) = 7"
        );
        for (tier, env) in [
            ("-interp", vec![("TLX_SYMMETRY_PARANOID", "1")]),
            ("-compile", vec![("TLX_PARANOID", "1"), ("TLX_SYMMETRY_PARANOID", "1")]),
            ("-compile", vec![("TLX_NO_NATIVE", "1"), ("TLX_PRERUN_REUSE", "0")]),
            ("-compile", vec![("TLX_JIT", "only"), ("TLX_PRERUN_REUSE", "0")]),
        ] {
            let r = run(&body, "INVARIANT Inv", &[tier], &env);
            assert_eq!(r.code, 0, "{}", r.text());
            assert!(!r.stdout.contains("(runtime guard; safety"), "{}", r.text());
            assert!(r.stdout.contains("certificate generated"), "{}", r.text());
            assert!(r.stdout.contains("parametric choice-symmetry rule-IR certificate"), "{}", r.text());
            assert!(r.stdout.contains("10 distinct states found, 0 states left on queue (symmetry-reduced)."), "{}", r.text());
        }
    }

    // Showcase ChooseSym specification: concrete vs reduced across -interp and -compile, plus counterexample lifting.
    let tla = include_str!("../../../proofs/symmetry/ChooseSym.tla");
    let cfg = include_str!("../../../proofs/symmetry/ChooseSym.cfg");
    let dir = tlx_testkit::TempDir::with_spec("ChooseSym", tla, cfg);
    let tlc =
        tlx_testkit::tlx_default!().args(["check", "ChooseSym.tla", "-tlc", "-interp"]).dir(&dir).timeout(Duration::from_secs(60)).run();
    assert_eq!(tlc.code, 0, "ChooseSym -tlc: {}", tlc.text());
    assert!(tlc.stdout.contains("to use it, run without -tlc"), "ChooseSym -tlc: {}", tlc.text());
    let distinct_of = |stdout: &str| -> u64 {
        stdout
            .lines()
            .find_map(|l| l.split_once(" distinct states found"))
            .and_then(|(prefix, _)| prefix.split_whitespace().last())
            .unwrap()
            .replace(',', "")
            .parse()
            .unwrap()
    };
    let tlc_distinct = distinct_of(&tlc.stdout);
    assert!(tlc_distinct > 20, "expected nontrivial concrete state space, got {tlc_distinct}");

    for tier in ["-interp", "-compile"] {
        let r = tlx_testkit::tlx_default!()
            .args(["check", "ChooseSym.tla", tier])
            .envs([("TLX_PARANOID", "1"), ("TLX_SYMMETRY_PARANOID", "1")])
            .env("TLX_PROOF_DIR", dir.join("proofs"))
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(r.code, 0, "ChooseSym {tier}: {}", r.text());
        assert!(r.stdout.contains("Optimizations: symmetry Permutations(Proc) (certificate generated"), "{}", r.text());
        assert!(r.stdout.contains("parametric choice-symmetry rule-IR certificate"), "{}", r.text());
        let red_distinct = distinct_of(&r.stdout);
        assert!(red_distinct < tlc_distinct, "expected reduction: {red_distinct} < {tlc_distinct}");
    }

    // Counterexample lifting on ChooseSym when TotalVotes <= 5 is checked:
    let bad_tla = tla.replace("TotalVotes <= 6", "TotalVotes <= 5");
    let bad_dir = tlx_testkit::TempDir::with_spec("ChooseSym", &bad_tla, cfg);
    let bad_tlc = tlx_testkit::tlx_default!().args(["check", "ChooseSym.tla", "-tlc", "-interp"]).dir(&bad_dir).run();
    assert_eq!(bad_tlc.code, 12, "{}", bad_tlc.text());
    let bad_len = bad_tlc.stdout.lines().filter(|l| l.starts_with("State ")).count();
    for tier in ["-interp", "-compile"] {
        let bad_red = tlx_testkit::tlx_default!()
            .args(["check", "ChooseSym.tla", tier])
            .envs([("TLX_PARANOID", "1"), ("TLX_SYMMETRY_PARANOID", "1")])
            .env("TLX_PROOF_DIR", bad_dir.join("proofs"))
            .dir(&bad_dir)
            .run();
        assert_eq!(bad_red.code, 12, "{tier}: {}", bad_red.text());
        assert!(bad_red.stdout.contains("certificate generated"), "{tier}: {}", bad_red.text());
        assert_eq!(bad_red.stdout.lines().filter(|l| l.starts_with("State ")).count(), bad_len, "{tier}: {}", bad_red.text());
    }
}

#[test]
fn unproved_late_choice_keeps_the_original_search() {
    // Projected field value depends on state-dependent process pc values, so
    // ChooseSymCertificate refuses it and the full unreduced search runs.
    let body = "VARIABLES pc, n\nInit == pc = [p \\in Proc |-> 0] /\\ n = 0\n\
        Next == (n < 15 /\\ n' = n + 1 /\\ UNCHANGED pc) \\/ (n = 15 /\\ \\E p \\in Proc : pc[p] = 0 /\\ pc' = [pc EXCEPT ![p] = 1] /\\ UNCHANGED n)\n\
        Inv == (CHOOSE m \\in {[from |-> p, val |-> pc[p]] : p \\in Proc} : TRUE).val = 0";
    for tier in ["-interp", "-compile"] {
        let reference = run(body, "INVARIANT Inv", &[tier, "-noautosymmetry"], &[]);
        let default_run = run(body, "INVARIANT Inv", &[tier], &[("TLX_PARANOID", "1"), ("TLX_PRERUN", "1")]);
        assert_eq!(reference.code, 12, "{}", reference.text());
        assert_eq!(default_run.code, reference.code, "{}", default_run.text());
        let counts = |s: &str| s.lines().find(|s| s.contains("states generated,")).unwrap().to_string();
        assert_eq!(counts(&default_run.stdout), counts(&reference.stdout));
        assert!(!default_run.stdout.contains("(symmetry-reduced)"), "{}", default_run.text());
    }
}

#[test]
fn unproved_choice_does_not_evaluate_extra_candidates() {
    let body = "VARIABLES n, msgs\n\
        Init == n = 0 /\\ msgs = {[flag |-> f, from |-> p, val |-> 7] : f \\in {0, 1}, p \\in Proc}\n\
        Next == n < 16 /\\ n' = n + 1 /\\ UNCHANGED msgs\n\
        Inv == (CHOOSE m \\in msgs : m.flag = 0 \\/ n < 15 \\/ 1 \\div 0 = 0).val = 7";
    for env in [vec![], vec![("TLX_NO_NATIVE", "1")], vec![("TLX_PARANOID", "1")], vec![("TLX_JIT", "only")]] {
        let mut env = env;
        env.extend([("TLX_PRERUN", "1"), ("TLX_PRERUN_REUSE", "0")]);
        let default_run = run(body, "INVARIANT Inv", &["-compile"], &env);
        assert_eq!(default_run.code, 0, "{}", default_run.text());
        assert!(default_run.stdout.contains("17 distinct states found, 0 states left on queue."), "{}", default_run.text());
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

    // Without -proofdir, TLX_PROOF_DIR, or TLX_CACHE, an unwritable HOME cache
    // falls back to a private 0700 per-user directory `$TMPDIR/tlx-proofs-<uid>`.
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
    assert!(!fake_tmp.join("tlx-proofs").exists(), "must not use shared $TMPDIR/tlx-proofs");
    let fallback_dirs: Vec<_> = std::fs::read_dir(fake_tmp.path())
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.file_name().and_then(|n| n.to_str()).is_some_and(|n| n.starts_with("tlx-proofs-")))
        .collect();
    assert_eq!(fallback_dirs.len(), 1, "expected one private tlx-proofs-<uid> dir, got {fallback_dirs:?}");
    let fallback_dir = &fallback_dirs[0];
    let meta = std::fs::symlink_metadata(fallback_dir).unwrap();
    assert!(meta.file_type().is_dir());
    assert_eq!(meta.permissions().mode() & 0o777, 0o700, "fallback dir must be private 0700");
    assert_eq!(std::fs::read_dir(fallback_dir).unwrap().count(), 1);

    // A pre-existing fallback directory with loose permissions (0755) must fail closed.
    std::fs::set_permissions(fallback_dir, std::fs::Permissions::from_mode(0o755)).unwrap();
    let loose = tlx_testkit::tlx_default!()
        .args(["check", "Spec.tla", "-interp"])
        .env("HOME", fake_home.path())
        .env("TMPDIR", fake_tmp.path())
        .dir(&dir)
        .run();
    std::fs::set_permissions(fallback_dir, std::fs::Permissions::from_mode(0o700)).unwrap();
    assert_eq!(loose.code, 2, "loose fallback dir must be refused: {}", loose.text());
    assert!(loose.stdout.contains("Cannot write mandatory optimization Lean output"), "{}", loose.text());

    // A symlink at the fallback path must fail closed.
    std::fs::remove_dir_all(fallback_dir).unwrap();
    let decoy = fake_tmp.join("decoy");
    std::fs::create_dir(&decoy).unwrap();
    std::fs::set_permissions(&decoy, std::fs::Permissions::from_mode(0o700)).unwrap();
    std::os::unix::fs::symlink(&decoy, fallback_dir).unwrap();
    let linked = tlx_testkit::tlx_default!()
        .args(["check", "Spec.tla", "-interp"])
        .env("HOME", fake_home.path())
        .env("TMPDIR", fake_tmp.path())
        .dir(&dir)
        .run();
    assert_eq!(linked.code, 2, "symlink fallback dir must be refused: {}", linked.text());
    assert!(linked.stdout.contains("Cannot write mandatory optimization Lean output"), "{}", linked.text());
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

#[test]
fn certified_scalar_slot_and_product_sets_preserve_verdicts_across_tiers() {
    for (name, tla, cfg, group_label, concrete, reduced) in [
        (
            "ScalarSlot",
            include_str!("../../../proofs/symmetry/ScalarSlot.tla"),
            include_str!("../../../proofs/symmetry/ScalarSlot.cfg"),
            "Permutations(Proc)",
            "108 distinct states found",
            "28 distinct states found",
        ),
        (
            "ProductSets",
            include_str!("../../../proofs/symmetry/ProductSets.tla"),
            include_str!("../../../proofs/symmetry/ProductSets.cfg"),
            "Permutations(Client) x Permutations(Server)",
            "39 distinct states found",
            "17 distinct states found",
        ),
    ] {
        let dir = tlx_testkit::TempDir::with_spec(name, tla, cfg);
        let tlc = tlx_testkit::tlx_default!()
            .args(["check", &format!("{name}.tla"), "-tlc", "-interp"])
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(tlc.code, 0, "{name} -tlc: {}", tlc.text());
        assert!(tlc.stdout.contains(concrete), "{name} -tlc: {}", tlc.text());
        assert!(tlc.stdout.contains("to use it, run without -tlc"), "{name} -tlc: {}", tlc.text());

        for tier in ["-interp", "-compile"] {
            let r = tlx_testkit::tlx_default!()
                .args(["check", &format!("{name}.tla"), tier])
                .envs([("TLX_PARANOID", "1"), ("TLX_SYMMETRY_PARANOID", "1")])
                .env("TLX_PROOF_DIR", dir.join("proofs"))
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            assert_eq!(r.code, 0, "{name} {tier}: {}", r.text());
            assert!(
                r.stdout.contains(&format!("Optimizations: symmetry {group_label} (certificate generated")),
                "{name} {tier}: {}",
                r.text()
            );
            assert!(r.stdout.contains(&format!("{reduced}, 0 states left on queue (symmetry-reduced).")), "{name} {tier}: {}", r.text());
            assert!(r.stdout.contains("Lean output:"), "{name} {tier}: {}", r.text());
        }
    }

    // Product group counterexample lifting: violate Cardinality(acked) < 4.
    let bad_tla = include_str!("../../../proofs/symmetry/ProductSets.tla").replace("Cardinality(acked) <= 4", "Cardinality(acked) < 4");
    let bad_cfg = include_str!("../../../proofs/symmetry/ProductSets.cfg");
    let dir = tlx_testkit::TempDir::with_spec("ProductSets", &bad_tla, bad_cfg);
    let tlc = tlx_testkit::tlx_default!().args(["check", "ProductSets.tla", "-tlc", "-interp"]).dir(&dir).run();
    assert_eq!(tlc.code, 12, "{}", tlc.text());
    let tlc_len = tlc.stdout.lines().filter(|l| l.starts_with("State ")).count();
    for tier in ["-interp", "-compile"] {
        let r = tlx_testkit::tlx_default!()
            .args(["check", "ProductSets.tla", tier])
            .envs([("TLX_PARANOID", "1"), ("TLX_SYMMETRY_PARANOID", "1")])
            .env("TLX_PROOF_DIR", dir.join("proofs"))
            .dir(&dir)
            .run();
        assert_eq!(r.code, 12, "{tier}: {}", r.text());
        assert!(r.stdout.contains("Permutations(Client) x Permutations(Server) (certificate generated"), "{tier}: {}", r.text());
        assert_eq!(r.stdout.lines().filter(|l| l.starts_with("State ")).count(), tlc_len, "{tier}: {}", r.text());
    }
}

#[test]
fn ambiguous_membership_and_mixed_map_nested_except_refuse_autosym_and_find_violations() {
    // 1. ScalarSlot membership combined with extra primed equalities (`x' \in Proc /\ x' = x /\ x' = Pick`)
    //    must refuse automatic symmetry and report the exact same violation as `-noautosymmetry`.
    let membership_body = "VARIABLES x, flag\n\
        Pick == CHOOSE q \\in Proc : flag \\/ q /= (CHOOSE r \\in Proc : TRUE)\n\
        Init == x \\in Proc /\\ flag = FALSE\n\
        Next == (x' \\in Proc /\\ x' = x /\\ x' = Pick /\\ flag' = TRUE) \\/ UNCHANGED <<x, flag>>\n\
        Inv == ~flag";
    let states = |t: &str| t.lines().filter(|l| l.starts_with("State ")).count();
    for tier in ["-interp", "-compile"] {
        let reference = run(membership_body, "INVARIANT Inv", &[tier, "-noautosymmetry"], &[]);
        let default_run = run(membership_body, "INVARIANT Inv", &[tier], &[]);
        assert_eq!(reference.code, 12, "membership {tier} ref: {}", reference.text());
        assert_eq!(default_run.code, 12, "membership {tier} default: {}", default_run.text());
        assert!(!default_run.stdout.contains("(symmetry-reduced)"), "membership {tier} must refuse symmetry: {}", default_run.text());
        assert!(default_run.stdout.contains("Error: Invariant Inv is violated."), "{}", default_run.text());
        assert_eq!(states(&default_run.stdout), states(&reference.stdout));
        assert_eq!(tlx_testkit::cli::counts(&default_run.stdout), tlx_testkit::cli::counts(&reference.stdout));
    }

    // 2. MixedMap fixed-entry nested EXCEPT whose inner index depends on a process vs CHOOSE
    //    must refuse automatic symmetry and report the violation of `m["fixed"][2] = 0`.
    //    (Homogeneous `<<0, 0>>` payload ensures `m` classifies as `VarShape::MixedMap`.)
    let mixed_body = "VARIABLE m\n\
        Pick == CHOOSE q \\in Proc : TRUE\n\
        Init == m = [x \\in Proc \\cup {\"fixed\"} |-> <<0, 0>>]\n\
        Next == \\E p \\in Proc :\n\
                  \\/ m[p][1] = 0 /\\ m' = [m EXCEPT ![p] = <<1, 0>>]\n\
                  \\/ m[p][1] = 1 /\\ m' = [m EXCEPT ![\"fixed\"][IF p = Pick THEN 1 ELSE 2] = 1]\n\
        Inv == m[\"fixed\"][2] = 0";
    for tier in ["-interp", "-compile"] {
        let reference = run(mixed_body, "INVARIANT Inv", &[tier, "-noautosymmetry"], &[]);
        let default_run = run(mixed_body, "INVARIANT Inv", &[tier], &[]);
        assert_eq!(reference.code, 12, "mixed {tier} ref: {}", reference.text());
        assert_eq!(default_run.code, 12, "mixed {tier} default: {}", default_run.text());
        assert!(!default_run.stdout.contains("(symmetry-reduced)"), "mixed {tier} must refuse symmetry: {}", default_run.text());
        assert!(default_run.stdout.contains("Error: Invariant Inv is violated."), "{}", default_run.text());
        assert_eq!(states(&default_run.stdout), states(&reference.stdout));
        assert_eq!(tlx_testkit::cli::counts(&default_run.stdout), tlx_testkit::cli::counts(&reference.stdout));
    }
}

#[test]
fn multi_group_subset_search_picks_largest_order_despite_many_small_sets() {
    // 12 disjoint 2-element sets (whose subsets exceed the 1,024-subset budget if enumerated
    // before sorting) followed by two 4-element sets `Big1` and `Big2` (order 24 * 24 = 576 <= 720).
    let dir = tlx_testkit::TempDir::new("autosym-many-groups");
    let mut const_names = Vec::new();
    let mut cfg_lines = Vec::new();
    let mut init_parts = Vec::new();
    let mut var_names = Vec::new();
    for i in 1..=12 {
        let cname = format!("S{i}");
        let vname = format!("x{i}");
        const_names.push(cname.clone());
        var_names.push(vname.clone());
        cfg_lines.push(format!("CONSTANT {cname} = {{s{i}a, s{i}b}}"));
        init_parts.push(format!("{vname} = [p \\in {cname} |-> 0]"));
    }
    for (j, cname) in [(1, "Big1"), (2, "Big2")] {
        let vname = format!("b{j}");
        const_names.push(cname.into());
        var_names.push(vname.clone());
        cfg_lines.push(format!("CONSTANT {cname} = {{g{j}a, g{j}b, g{j}c, g{j}d}}"));
        init_parts.push(format!("{vname} = [p \\in {cname} |-> 0]"));
    }
    let tla = format!(
        "---- MODULE ManyGroups ----\nEXTENDS Naturals\nCONSTANTS {}\nVARIABLES {}\n\
         Init == {}\n\
         Next == (\\E p \\in Big1 : b1[p] < 1 /\\ b1' = [b1 EXCEPT ![p] = 1] /\\ UNCHANGED <<{}, b2>>)\n\
                 \\/ (\\E q \\in Big2 : b2[q] < 1 /\\ b2' = [b2 EXCEPT ![q] = 1] /\\ UNCHANGED <<{}, b1>>)\n\
         Inv == (\\A p \\in Big1 : b1[p] <= 1) /\\ (\\A q \\in Big2 : b2[q] <= 1)\n====\n",
        const_names.join(", "),
        var_names.join(", "),
        init_parts.join(" /\\ "),
        (1..=12).map(|i| format!("x{i}")).collect::<Vec<_>>().join(", "),
        (1..=12).map(|i| format!("x{i}")).collect::<Vec<_>>().join(", "),
    );
    let cfg = format!("{}\nINIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\nINVARIANT Inv\n", cfg_lines.join("\n"));
    std::fs::write(dir.join("ManyGroups.tla"), tla).unwrap();
    std::fs::write(dir.join("ManyGroups.cfg"), cfg).unwrap();

    let r = tlx_testkit::tlx_default!()
        .args(["check", "ManyGroups.tla", "-interp"])
        .env("TLX_PROOF_DIR", dir.join("proofs"))
        .dir(&dir)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(r.code, 0, "{}", r.text());
    assert!(
        r.stdout.contains("Optimizations: symmetry Permutations(Big1) x Permutations(Big2) (certificate generated"),
        "expected order-576 product Big1 x Big2, got:\n{}",
        r.text()
    );
    assert!(r.stdout.contains("25 distinct states found, 0 states left on queue (symmetry-reduced)."), "{}", r.text());
}

#[test]
fn multi_group_attainable_order_beats_greedy_prefix_truncation() {
    // R10-#6: 20 disjoint 3-element sets (`6!`-bounded prefixes `6^3 = 216`, `C(20,3) = 1,140`)
    // and 4 disjoint 2-element sets (`2^4 = 16`): `6^2 * 2^4 = 576` fits `<= 720` and beats `6^3 * 2 = 432`.
    let dir = tlx_testkit::TempDir::new("autosym-attainable-order");
    let mut const_names = Vec::new();
    let mut cfg_lines = Vec::new();
    let mut init_parts = Vec::new();
    let mut var_names = Vec::new();
    for i in 1..=20 {
        let cname = format!("T{i}");
        let vname = format!("t{i}");
        const_names.push(cname.clone());
        var_names.push(vname.clone());
        cfg_lines.push(format!("CONSTANT {cname} = {{t{i}a, t{i}b, t{i}c}}"));
        init_parts.push(format!("{vname} = [p \\in {cname} |-> 0]"));
    }
    for j in 1..=4 {
        let cname = format!("P{j}");
        let vname = format!("p{j}");
        const_names.push(cname.clone());
        var_names.push(vname.clone());
        cfg_lines.push(format!("CONSTANT {cname} = {{p{j}a, p{j}b}}"));
        init_parts.push(format!("{vname} = [p \\in {cname} |-> 0]"));
    }
    let tla = format!(
        "---- MODULE AttainableOrder ----\nEXTENDS Naturals\nCONSTANTS {}\nVARIABLES {}\n\
         Init == {}\n\
         Next == UNCHANGED <<{}>>\n\
         Inv == TRUE\n====\n",
        const_names.join(", "),
        var_names.join(", "),
        init_parts.join(" /\\ "),
        var_names.join(", "),
    );
    let cfg = format!("{}\nINIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\nINVARIANT Inv\n", cfg_lines.join("\n"));
    std::fs::write(dir.join("AttainableOrder.tla"), tla).unwrap();
    std::fs::write(dir.join("AttainableOrder.cfg"), cfg).unwrap();

    let r = tlx_testkit::tlx_default!()
        .args(["check", "AttainableOrder.tla", "-interp"])
        .env("TLX_PROOF_DIR", dir.join("proofs"))
        .dir(&dir)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(r.code, 0, "{}", r.text());
    assert!(
        r.stdout.contains(
            "Optimizations: symmetry Permutations(T1) x Permutations(T2) x Permutations(P1) x Permutations(P2) x Permutations(P3) x Permutations(P4) (certificate generated"
        ),
        "expected order-576 product T1 x T2 x P1 x P2 x P3 x P4 (not 432), got:\n{}",
        r.text()
    );
}

#[test]
fn choose_record_payload_preserves_integer_field_alongside_key_comparison() {
    // End-to-end R10-#5 verification: `[n |-> 7, same |-> (p = owner)]` must preserve `n = 7`
    // under certified CHOOSE symmetry in both `-interp` and `-compile`.
    let body = "\
        VARIABLE owner, info\n\
        Init == owner \\in Proc /\\ info = [p \\in Proc |-> [n |-> 7, same |-> FALSE]]\n\
        Next == owner' = (CHOOSE x \\in Proc : x = owner) /\\ info' = [p \\in Proc |-> [n |-> 7, same |-> (p = owner)]]\n\
        Inv == \\A p \\in Proc : info[p].n = 7 /\\ (info[p].same => (p = owner))";
    for tier in ["-interp", "-compile"] {
        let r = run(body, "INVARIANT Inv", &[tier], &[]);
        assert_eq!(r.code, 0, "{tier}: {}", r.text());
        assert!(r.stdout.contains("(symmetry-reduced)"), "{tier} should certify CHOOSE symmetry: {}", r.text());
    }
}

#[test]
fn budget_fallback_recovers_certifiable_product_behind_uncertifiable_proven_sets() {
    // R12-#4 & R12-#5: 15 disjoint order-2 proven candidate sets (`S1..S15`, `C(15, 9) = 5,005 > 1,024`
    // order-512 products). `S1..S13` occur in state through symmetric tuple-set constants
    // `T{i} = {<<u{i}a, u{i}b>>, <<u{i}b, u{i}a>>}` so `autosym::analyze` proves all 15 full order-2
    // groups, while every product containing any `S1..S13` fails certificate lowering. After the 1,024
    // primary attempts expire on order-512 products, the fallback must still recover the full
    // order-4 product `Permutations(S14) x Permutations(S15)` (not `None` and not order-2 `S14` alone).
    let dir = tlx_testkit::TempDir::new("autosym-budget-product-fallback");
    let mut const_names = Vec::new();
    let mut cfg_lines = Vec::new();
    let mut tuple_refs = Vec::new();
    for i in 1..=13 {
        let sname = format!("S{i}");
        let tname = format!("T{i}");
        const_names.push(sname.clone());
        const_names.push(tname.clone());
        cfg_lines.push(format!("CONSTANT {sname} = {{u{i}a, u{i}b}}"));
        cfg_lines.push(format!("CONSTANT {tname} = {{<<u{i}a, u{i}b>>, <<u{i}b, u{i}a>>}}"));
        tuple_refs.push(tname);
    }
    for i in 14..=15 {
        let sname = format!("S{i}");
        const_names.push(sname.clone());
        cfg_lines.push(format!("CONSTANT {sname} = {{u{i}a, u{i}b}}"));
    }
    let tla = format!(
        "---- MODULE BudgetProductFallback ----\nEXTENDS Naturals\nCONSTANTS {}\nVARIABLES aux, m14, m15\n\
         Init == aux = <<{}>> /\\ m14 = [p \\in S14 |-> 0] /\\ m15 = [q \\in S15 |-> 0]\n\
         Next ==\n\
           \\/ \\E p \\in S14 : m14[p] = 0 /\\ m14' = [m14 EXCEPT ![p] = 1] /\\ UNCHANGED <<aux, m15>>\n\
           \\/ \\E q \\in S15 : m15[q] = 0 /\\ m15' = [m15 EXCEPT ![q] = 1] /\\ UNCHANGED <<aux, m14>>\n\
         Inv == (\\A p \\in S14 : m14[p] <= 1) /\\ (\\A q \\in S15 : m15[q] <= 1)\n====\n",
        const_names.join(", "),
        tuple_refs.join(", "),
    );
    let cfg = format!("{}\nINIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\nINVARIANT Inv\n", cfg_lines.join("\n"));
    std::fs::write(dir.join("BudgetProductFallback.tla"), tla).unwrap();
    std::fs::write(dir.join("BudgetProductFallback.cfg"), cfg).unwrap();

    let r = tlx_testkit::tlx_default!()
        .args(["check", "BudgetProductFallback.tla", "-interp", "-stats"])
        .env("TLX_PROOF_DIR", dir.join("proofs"))
        .dir(&dir)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(r.code, 0, "{}", r.text());
    for i in 1..=15 {
        assert!(r.text().contains(&format!("S{i}: proven Permutations(S{i})")), "S{i} must be proven eligible:\n{}", r.text());
    }
    assert!(
        r.stdout.contains("Optimizations: symmetry Permutations(S14) x Permutations(S15) (certificate generated"),
        "expected order-4 fallback product Permutations(S14) x Permutations(S15), got:\n{}",
        r.text()
    );
    assert!(r.stdout.contains("9 distinct states found, 0 states left on queue (symmetry-reduced)."), "{}", r.text());
}

#[test]
fn tlc_advice_finds_certifiable_group_behind_pinned_order_720_candidate() {
    // R12-#3: `Big` has 6 movable elements (`6! = 720`) plus 1 pinned element (`b7`), so `!Big.full()`
    // even though `an.select(720)` greedily consumes the entire 720 budget on `Big` alone.
    // Both `-tlc` advice and default-mode `apply` must still find and certify `Permutations(Small)`.
    let dir = tlx_testkit::TempDir::new("autosym-tlc-advice-pinned-big");
    let tla = "\
---- MODULE PinnedBigAdvice ----
EXTENDS Naturals
CONSTANTS Big, Pin, Small
VARIABLES bset, smap
Init == bset = Big \\ {Pin} /\\ smap = [p \\in Small |-> 0]
Next == \\E p \\in Small : smap[p] = 0 /\\ smap' = [smap EXCEPT ![p] = 1] /\\ UNCHANGED bset
Inv == \\A p \\in Small : smap[p] <= 1
====
";
    let cfg = "\
CONSTANT Big = {b1, b2, b3, b4, b5, b6, b7}
CONSTANT Pin = b7
CONSTANT Small = {s1, s2}
INIT Init
NEXT Next
CHECK_DEADLOCK FALSE
INVARIANT Inv
";
    std::fs::write(dir.join("PinnedBigAdvice.tla"), tla).unwrap();
    std::fs::write(dir.join("PinnedBigAdvice.cfg"), cfg).unwrap();

    let tlc = tlx_testkit::tlx_default!()
        .args(["check", "PinnedBigAdvice.tla", "-tlc", "-interp"])
        .dir(&dir)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(tlc.code, 0, "{}", tlc.text());
    assert!(
        tlc.stdout.contains("run without -tlc to use Permutations(Small)."),
        "expected -tlc advice to name certified subset Permutations(Small):\n{}",
        tlc.text()
    );

    let def = tlx_testkit::tlx_default!()
        .args(["check", "PinnedBigAdvice.tla", "-interp"])
        .env("TLX_PROOF_DIR", dir.join("proofs"))
        .dir(&dir)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(def.code, 0, "{}", def.text());
    assert!(
        def.stdout.contains("Optimizations: symmetry Permutations(Small) (certificate generated"),
        "expected default mode to apply Permutations(Small):\n{}",
        def.text()
    );
}

#[test]
fn absent_non_model_except_key_on_untyped_model_map_reduces_in_both_tiers() {
    // R13-#2 end-to-end verification: `[m EXCEPT ![0] = 0]` on `m = [p \in Proc |-> p]` leaves `m`
    // unchanged at runtime without error and certifies automatic symmetry in `-interp` and `-compile`.
    let body = "\
        VARIABLES m, c\n\
        Init == m = [p \\in Proc |-> p] /\\ c \\in Proc\n\
        Next == m' = [m EXCEPT ![0] = 0] /\\ \\E p \\in Proc : c' = p\n\
        Inv == \\A p \\in Proc : m[p] = p";
    for (tier, env) in [("-interp", vec![]), ("-compile", vec![("TLX_PARANOID", "1")])] {
        let r = run(body, "INVARIANT Inv", &[tier], &env);
        assert_eq!(r.code, 0, "{tier}: {}", r.text());
        assert!(r.stdout.contains("1 distinct states found, 0 states left on queue (symmetry-reduced)."), "{tier}: {}", r.text());
    }
}

#[test]
fn subseteq_assign_and_empty_map_except_guard_behave_soundly_in_both_tiers() {
    // R16-#1 & R16-#2 end-to-end verification:
    // 1. `s \subseteq Proc /\ m = [p \in s |-> p]` with unguarded `\E p \in Proc : m' = [m EXCEPT ![p] = p]`
    //    must refuse automatic symmetry in both tiers and match `-noautosymmetry`.
    let unsafe_body = "\
        VARIABLES s, m\n\
        Init == s \\subseteq Proc /\\ m = [p \\in s |-> p]\n\
        Next == \\E p \\in Proc : s' = s /\\ m' = [m EXCEPT ![p] = p]\n\
        Inv == m = [p \\in s |-> p]";
    for tier in ["-interp", "-compile"] {
        let r = run(unsafe_body, "INVARIANT Inv", &[tier], &[]);
        let base = run(unsafe_body, "INVARIANT Inv", &[tier, "-noautosymmetry"], &[]);
        assert!(!r.stdout.contains("(symmetry-reduced)"), "{tier} must refuse symmetry: {}", r.text());
        assert!(r.stdout.contains("Optimizations: none applicable."), "{tier}: {}", r.text());
        assert_eq!(r.code, base.code, "{tier} exit code mismatch vs -noautosymmetry");
    }

    // 2. Guarding `EXCEPT` with `\E p \in DOMAIN m` proves `m` non-empty and `s' \subseteq Proc`
    //    certifies and reduces cleanly across `-interp` and `-compile` (`TLX_PARANOID=1`).
    let safe_body = "\
        VARIABLES s, m\n\
        Init == s \\subseteq Proc /\\ m = [p \\in s |-> p]\n\
        Next == (\\E p \\in DOMAIN m : s' = s /\\ m' = [m EXCEPT ![p] = p]) \\/ (s' \\subseteq Proc /\\ m' = [p \\in s' |-> p])\n\
        Inv == m = [p \\in s |-> p]";
    for (tier, env) in [("-interp", vec![]), ("-compile", vec![("TLX_PARANOID", "1"), ("TLX_SYMMETRY_PARANOID", "1")])] {
        let r = run(safe_body, "INVARIANT Inv", &[tier], &env);
        assert_eq!(r.code, 0, "{tier}: {}", r.text());
        assert!(r.stdout.contains("4 distinct states found, 0 states left on queue (symmetry-reduced)."), "{tier}: {}", r.text());
    }
}
