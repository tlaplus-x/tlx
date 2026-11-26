//! `TLX_PARANOID` reports a wrong compiled result at once, with a clear
//! message and a failing exit code, also with several workers: wrong
//! results are injected with `TLX_INJECT_MISMATCH`.

use std::path::Path;
use std::time::{Duration, Instant};

const SPEC: &str = r#"---- MODULE Paranoid ----
EXTENDS Naturals
VARIABLES x, y, z
Init == x = 0 /\ y \in 0..2 /\ z = 0
IncX == x' = (x + 1) % 30 /\ UNCHANGED <<y, z>>
IncY == y' = (y + 1) % 30 /\ UNCHANGED <<x, z>>
IncZ == z' \in {(z + 1) % 30, (z + 2) % 30} /\ UNCHANGED <<x, y>>
Next == IncX \/ IncY \/ IncZ
Inv == x + y + z < 100
====
"#;

const CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\n";

/// A directory holding the spec (one per test: tests run in parallel).
fn spec_dir(_name: &str) -> tlx_testkit::TempDir {
    tlx_testkit::TempDir::with_spec("paranoid", SPEC, CFG)
}

/// Run `tlx check -compile` on the spec with `env` and `args`: exit code and
/// output (stdout and stderr). Fails if it does not end within a minute.
fn run(dir: &Path, env: &[(&str, &str)], args: &[&str]) -> (i32, String) {
    let mut cmd = tlx_testkit::tlx!();
    cmd.args(["check", "Paranoid.tla", "-config", "Paranoid.cfg", "-compile"]).args(args).dir(dir);
    cmd.command().env_remove("RUST_BACKTRACE");
    let run = cmd.envs(env.iter().copied()).timeout(Duration::from_secs(60)).run();
    (run.code, run.text())
}

const MISMATCH: &str = "TLX_PARANOID: compiled code differs from the interpreter";

#[test]
fn paranoid_passes_correct_code() {
    let dir = spec_dir("ok");
    for workers in ["1", "4"] {
        let (code, out) = run(&dir, &[("TLX_PARANOID", "1")], &["-workers", workers]);
        assert_eq!(code, 0, "{out}");
        assert!(out.contains("27000 distinct states found"), "{out}");
        assert!(!out.contains(MISMATCH), "{out}");
    }
}

/// Without TLX_PARANOID an injected wrong result goes unnoticed (the counts
/// are wrong): the injection works.
#[test]
fn injected_mismatch_changes_counts() {
    let dir = spec_dir("unchecked");
    let (code, out) = run(&dir, &[("TLX_INJECT_MISMATCH", "dup:10")], &[]);
    assert_eq!(code, 0, "{out}");
    assert!(out.contains("27000 distinct states found"), "{out}");
    let (_, want) = run(&dir, &[], &[]);
    let generated = |o: &str| o.lines().find(|l| l.contains("states generated,")).map(str::to_string);
    assert_ne!(generated(&out), generated(&want), "{out}");
}

#[test]
fn paranoid_reports_wrong_successors() {
    let dir = spec_dir("succ");
    // Early (in a narrow level) and late (in a wide one), with one worker
    // and with several (whose search is level-synchronous).
    for inject in ["drop:0", "drop:20000", "dup:5000", "stale:15000"] {
        for workers in ["1", "4", "8"] {
            let t0 = Instant::now();
            let (code, out) = run(&dir, &[("TLX_PARANOID", "1"), ("TLX_INJECT_MISMATCH", inject)], &["-workers", workers]);
            let what = format!("{inject}, {workers} workers:\n{out}");
            assert_eq!(code, 101, "{what}");
            assert!(out.contains(&format!("{MISMATCH}: action Inc")), "{what}");
            assert!(out.contains("interpreter (") && out.contains("compiled (") && out.contains("missing in compiled ("), "{what}");
            assert!(!out.contains("Model checking completed"), "{what}");
            assert!(t0.elapsed() < Duration::from_secs(30), "{what}");
        }
    }
}

#[test]
fn paranoid_reports_wrong_init_and_invariant() {
    let dir = spec_dir("init");
    for workers in ["1", "4"] {
        let (code, out) = run(&dir, &[("TLX_PARANOID", "1"), ("TLX_INJECT_MISMATCH", "init")], &["-workers", workers]);
        assert_eq!(code, 101, "{out}");
        assert!(out.contains(&format!("{MISMATCH}: Init")), "{out}");
        let (code, out) = run(&dir, &[("TLX_PARANOID", "1"), ("TLX_INJECT_MISMATCH", "inv:5000")], &["-workers", workers]);
        assert_eq!(code, 101, "{out}");
        assert!(out.contains(&format!("{MISMATCH}: invariant Inv on state")), "{out}");
    }
}

#[test]
fn paranoid_reports_wrong_successors_in_simulation() {
    let dir = spec_dir("sim");
    for workers in ["1", "4"] {
        let (code, out) =
            run(&dir, &[("TLX_PARANOID", "1"), ("TLX_INJECT_MISMATCH", "drop:500")], &["-workers", workers, "-simulate", "-depth", "50"]);
        assert_eq!(code, 101, "{out}");
        assert!(out.contains(&format!("{MISMATCH}: action Inc")), "{out}");
    }
}

/// The IR executor's results are cross-checked as well (no native code).
#[test]
fn paranoid_reports_wrong_ir_successors() {
    let dir = spec_dir("ir");
    let (code, out) = run(&dir, &[("TLX_PARANOID", "1"), ("TLX_NO_NATIVE", "1"), ("TLX_INJECT_MISMATCH", "drop:3000")], &["-workers", "4"]);
    assert_eq!(code, 101, "{out}");
    assert!(out.contains(&format!("{MISMATCH}: action Inc")), "{out}");
}

/// A panic is reported as one clean line: no Rust panic-location header and
/// no "run with RUST_BACKTRACE=1" hint (an internal error is a tlx bug).
#[test]
fn internal_error_message_is_clean() {
    let dir = spec_dir("panicmsg");
    let (code, out) = run(&dir, &[("TLX_PARANOID", "1"), ("TLX_INJECT_MISMATCH", "drop:0")], &["-workers", "2"]);
    assert_eq!(code, 101, "{out}");
    assert!(out.contains(&format!("tlx: internal error: {MISMATCH}")), "{out}");
    assert!(!out.contains("RUST_BACKTRACE"), "{out}");
    assert!(!out.contains("panicked at"), "{out}");
    assert!(!out.contains("note: run with"), "{out}");
    assert!(!out.contains("Model checking completed"), "{out}");
    // A developer can still ask for the backtrace.
    let (code, out) = run(&dir, &[("TLX_PARANOID", "1"), ("TLX_INJECT_MISMATCH", "drop:0"), ("RUST_BACKTRACE", "1")], &["-workers", "2"]);
    assert_eq!(code, 101, "{out}");
    assert!(out.contains(&format!("tlx: internal error: {MISMATCH}")), "{out}");
}

/// A tied minimum under VIEW + SYMMETRY: two permutations of the declared
/// (overlapping-union) group map `x = b` to the same least state, so the
/// interpreter and the compiled word-level walk can select different
/// permutation indices. The cross-check compares the selected states, not the
/// indices, and both tiers still report the same counts.
#[test]
fn paranoid_accepts_tied_symmetry_representatives() {
    const TIE: &str = r#"---- MODULE TiedMinimum ----
EXTENDS TLC
CONSTANTS a,b,c
VARIABLE x
Sym == Permutations({a,c}) \cup Permutations({b,c})
V == x
Init == x \in {a,b,c}
Next == UNCHANGED x
====
"#;
    const TIE_CFG: &str = "CONSTANTS a = a b = b c = c\nINIT Init\nNEXT Next\nSYMMETRY Sym\nVIEW V\n";
    let dir = tlx_testkit::TempDir::with_spec("paranoid-tied-symmetry", TIE, TIE_CFG);
    let run = |args: &[&str], paranoid: bool| {
        let mut cmd = tlx_testkit::tlx!();
        cmd.check("TiedMinimum.tla").cfg("TiedMinimum.cfg").args(["-tlc", "-workers", "1"]).args(args).dir(dir.path());
        if paranoid {
            cmd.env("TLX_PARANOID", "1");
        }
        cmd.run()
    };
    let interp = run(&["-interp"], false);
    assert_eq!(interp.code, 0, "interp:\n{}", interp.text());
    let compiled = run(&["-compile"], true);
    assert_eq!(compiled.code, 0, "paranoid -compile:\n{}", compiled.text());
    assert!(!compiled.text().contains(MISMATCH), "{}", compiled.text());
    assert_eq!(
        tlx_testkit::cli::result_lines(&compiled.text()),
        tlx_testkit::cli::result_lines(&interp.text()),
        "paranoid -compile:\n{}\ninterp:\n{}",
        compiled.text(),
        interp.text()
    );
}

/// After layout misses (a tiny pre-run), in a search resumed in a widened
/// layout.
#[test]
fn paranoid_reports_wrong_successors_after_resume() {
    let dir = spec_dir("resume");
    for workers in ["1", "4"] {
        let env = [("TLX_PARANOID", "1"), ("TLX_PRERUN", "3"), ("TLX_INJECT_MISMATCH", "drop:2000")];
        let (code, out) = run(&dir, &env, &["-workers", workers]);
        assert_eq!(code, 101, "{out}");
        assert!(out.contains("compile: resuming the search"), "{out}");
        assert!(out.contains(&format!("{MISMATCH}: action Inc")), "{out}");
    }
}
