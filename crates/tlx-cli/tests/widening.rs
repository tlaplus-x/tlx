//! Layout misses of the compiled tier converge: a string variable
//! that keeps taking new values (computed with `ToString`) widens to a
//! dynamic value after at most two misses, counters grow geometrically, and
//! a miss after the last allowed restart continues the run with dynamic
//! values instead of failing. The results are the interpreter's.

use std::path::Path;

const SPEC: &str = r#"---- MODULE Widen ----
EXTENDS Naturals, Sequences, TLC
VARIABLES x, y, s
Init == x = 0 /\ y = 0 /\ s = "n0"
Next == \/ x < 79 /\ x' = x + 1 /\ y' = y /\ s' = "n" \o ToString(x' * 1000 + y')
        \/ y < 79 /\ y' = y + 1 /\ x' = x /\ s' = "n" \o ToString(x' * 1000 + y')
====
"#;

const CFG: &str = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";

/// A counter (simulations do not pre-run specs that make strings).
const COUNTER: &str = "---- MODULE Widen ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\n====\n";

/// A directory holding spec `spec` as Widen.tla (one per test).
fn spec_dir(_test: &str, spec: &str) -> tlx_testkit::TempDir {
    tlx_testkit::TempDir::with_spec("widening", spec, CFG)
}

/// `tlx check` with `extra` arguments and environment `env`: exit code and
/// output (stdout and stderr).
fn run(dir: &Path, extra: &[&str], env: &[(&str, &str)]) -> (i32, String) {
    let mut cmd = tlx_testkit::tlx!();
    cmd.args(["check", "Widen.tla", "-config", "Widen.cfg", "-workers", "1"]).args(extra).dir(dir);
    let out = cmd.envs(env.iter().copied()).run();
    (out.code, out.text())
}

use tlx_testkit::cli::counts;

fn misses(out: &str) -> usize {
    out.lines().filter(|l| l.starts_with("compile: layout miss")).count()
}

#[test]
fn growing_strings_converge() {
    let dir = spec_dir("converge", SPEC);
    let (code, plain) = run(&dir, &[], &[]);
    assert_eq!(code, 0, "{plain}");
    assert_eq!(
        counts(&plain),
        [
            "12641 states generated, 6400 distinct states found, 0 states left on queue.",
            "The depth of the complete state graph search is 159."
        ]
    );
    // A small pre-run: s, x and y miss (s at most twice), in the default
    // number of restarts; resumed or started over.
    for env in [&[("TLX_PRERUN", "50")][..], &[("TLX_PRERUN", "50"), ("TLX_RETAIN_MB", "0")]] {
        let (code, out) = run(&dir, &["-compile"], env);
        assert_eq!((code, counts(&out)), (0, counts(&plain)), "{env:?}:\n{out}");
        assert!((1..=6).contains(&misses(&out)), "{env:?}: too many layout misses:\n{out}");
        assert!(!out.contains("continuing with dynamic values"), "{out}");
    }
}

#[test]
fn stats_report_scratch_restarts_and_budget_derived_archive_limit() {
    let dir = spec_dir("stats-archive", SPEC);
    let (code, out) = run(&dir, &["-compile", "-stats", "json", "-maxmem", "256"], &[("TLX_PRERUN", "50")]);
    assert_eq!(code, 0, "{out}");
    assert!(out.contains("archive memory limit (-maxmem / 4)"), "{out}");
    assert!(out.contains("67108864"), "{out}");
    let (code, out) = run(&dir, &["-compile", "-stats", "json"], &[("TLX_PRERUN", "50"), ("TLX_RETAIN_MB", "0")]);
    assert_eq!(code, 0, "{out}");
    assert!(out.contains("states repeated from scratch"), "{out}");
    assert!(out.contains("restarts from scratch"), "{out}");
    assert!(!out.contains("resume archive dropped"), "an explicitly disabled archive was never dropped: {out}");
}

#[test]
fn late_layout_miss_reports_work_repeated_after_archive_loss() {
    let spec = r#"---- MODULE Widen ----
EXTENDS Naturals
VARIABLES x, y, z
Init == x = 0 /\ y = 0 /\ z = 0
Next == /\ \/ x < 500 /\ x' = x + 1 /\ y' = y
           \/ y < 500 /\ y' = y + 1 /\ x' = x
        /\ z' = IF x + y = 900 THEN <<0>> ELSE z
====
"#;
    let dir = spec_dir("archive-loss", spec);
    let (code, out) = run(&dir, &["-compile", "-spill", "off", "-stats", "json"], &[("TLX_PRERUN", "50"), ("TLX_RETAIN_MB", "1")]);
    assert_eq!(code, 0, "{out}");
    assert_eq!(
        counts(&out),
        [
            "501001 states generated, 251001 distinct states found, 0 states left on queue.",
            "The depth of the complete state graph search is 1001."
        ]
    );
    assert!(out.contains("resume archive dropped: restarting from scratch,"), "{out}");
    assert!(out.contains("restarts after archive dropped"), "{out}");
}

#[test]
fn miss_after_last_restart_continues_with_dynamic_values() {
    let dir = spec_dir("fallback", SPEC);
    let (_, plain) = run(&dir, &[], &[]);
    for n in ["0", "1"] {
        for retain in ["1024", "0"] {
            let env = [("TLX_PRERUN", "50"), ("TLX_MAX_RESTARTS", n), ("TLX_RETAIN_MB", retain)];
            let (code, out) = run(&dir, &["-compile"], &env);
            assert_eq!((code, counts(&out)), (0, counts(&plain)), "{env:?}:\n{out}");
            assert!(out.contains(&format!("after {n} restarts; continuing with dynamic values")), "{env:?}:\n{out}");
        }
    }
}

#[test]
fn simulation_miss_after_last_restart_continues_with_dynamic_values() {
    let dir = spec_dir("simulate", COUNTER);
    // Synchronous native build: the miss must be detected by the compiled
    // code, not depend on whether a background build finishes in time.
    //
    // A simulation pre-run also makes random walks (of `-depth` steps) whose
    // observations size the layout; with a wall-clock budget of 1ms how far
    // they get is machine-load dependent, and often the resulting integer
    // range already covers the whole 5000-step simulation (no miss).
    // A 0ms budget observes only the initial states: x=0 gives the range
    // 0..2, so the compiled code must miss at x=3 and fall back.
    let env = [("TLX_PRERUN", "1"), ("TLX_PRERUN_MS", "0"), ("TLX_MAX_RESTARTS", "0"), ("TLX_NATIVE_SYNC", "1")];
    let (code, out) = run(&dir, &["-compile", "-simulate", "num=3", "-depth", "5000", "-seed", "1"], &env);
    assert_eq!(code, 0, "{out}");
    assert!(out.contains("layout miss on x"), "{out}");
    assert!(out.contains("after 0 restarts; continuing with dynamic values"), "{out}");
    assert!(out.contains("The number of states generated: 15001"), "{out}");
}

#[test]
fn packed_zero_width_field_reports_layout_miss_and_invariant_in_c() {
    let spec = r#"---- MODULE Widen ----
EXTENDS Naturals
VARIABLES r, n
Init == r = <<FALSE, {}>> /\ n \in {0, 100}
Next == /\ r' = <<TRUE, IF n = 99 THEN {1} ELSE {}>>
        /\ n' = IF n < 100 THEN n + 1 ELSE n
Inv == r[2] = {}
====
"#;
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    let dir = tlx_testkit::TempDir::with_spec("widening-packed-zero", spec, cfg);
    let (interp_code, interp_out) = run(&dir, &["-interp"], &[]);
    assert_eq!(interp_code, 12, "{interp_out}");
    assert!(interp_out.contains("Invariant Inv is violated"), "{interp_out}");

    for (label, env) in [
        ("C", &[("TLX_PRERUN", "10"), ("TLX_JIT", "0"), ("TLX_NATIVE_SYNC", "1")][..]),
        ("JIT", &[("TLX_PRERUN", "10"), ("TLX_JIT", "1"), ("TLX_NATIVE_SYNC", "1")][..]),
    ] {
        let (code, out) = run(&dir, &["-compile"], env);
        assert_eq!(code, 12, "{label}:\n{out}");
        assert!(out.contains("Invariant Inv is violated"), "{label}:\n{out}");
        assert!(misses(&out) >= 1, "{label}: expected layout miss on zero-width set field:\n{out}");
        assert_eq!(counts(&out), counts(&interp_out), "{label}:\n{out}");
    }
}
