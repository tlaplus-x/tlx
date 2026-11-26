//! The layout-miss archive is elided only when every compiled layout slot is
//! provably closed against misses (scale.md §6): a spec whose `Init` and
//! `Next` stay inside the speculated shapes reports no archive, while a spec
//! that can widen a slot (an out-of-shape counter, a function-witness flip)
//! keeps it and resumes.

use std::path::Path;

use tlx_testkit::cli::counts;

const CLOSED: &str = r#"---- MODULE Archive ----
EXTENDS Naturals
VARIABLES b, n, r, f, s, st
Init == b = FALSE /\ n = 0 /\ r = [a |-> 0, c |-> 0] /\ f = [i \in {1, 2} |-> 0]
     /\ s = "a" /\ st = {}
Next == /\ b' = ~b
        /\ n' = IF n < 5 THEN n + 1 ELSE 0
        /\ r' = [r EXCEPT !.a = 1]
        /\ f' = [f EXCEPT ![1] = 0]
        /\ s' = IF s = "a" THEN "b" ELSE "a"
        /\ st' = IF st = {} THEN {1} ELSE {1, 2}
====
"#;

const WITNESS_FLIP: &str = r#"---- MODULE Archive ----
EXTENDS Naturals
VARIABLES n, f
Init == n = 0 /\ f = [i \in {1, 2} |-> 0]
Next == /\ n' = IF n < 40 THEN n + 1 ELSE n
        /\ f' = IF n < 20 THEN [i \in {1, 2} |-> 0] ELSE <<1, 2>>
====
"#;

const GROWING: &str = r#"---- MODULE Archive ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = IF x < 50 THEN x + 1 ELSE x
====
"#;

const CFG: &str = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";

fn spec_dir(tag: &str, src: &str) -> tlx_testkit::TempDir {
    tlx_testkit::TempDir::with_spec(tag, src, CFG)
}

fn run(dir: &Path, tier: &[&str], env: &[(&str, &str)]) -> (i32, String) {
    let mut cmd = tlx_testkit::tlx_default!();
    cmd.check("Archive.tla").args(["-config", "Archive.cfg", "-workers", "1"]).args(tier).dir(dir);
    let out = cmd.envs(env.iter().copied()).run();
    (out.code, out.text())
}

/// The compiled run with the pre-run prevented from standing in for the
/// search (otherwise a small spec never compiles anything).
fn compiled(dir: &Path, env: &[(&str, &str)]) -> (i32, String) {
    let mut env = env.to_vec();
    env.push(("TLX_PRERUN_REUSE", "0"));
    run(dir, &["-compile", "-stats"], &env)
}

fn interpreter(dir: &Path) -> (i32, String) {
    run(dir, &["-interp", "-stats"], &[])
}

#[test]
fn a_closed_layout_reports_zero_archive_retention() {
    let dir = spec_dir("elided", CLOSED);
    let (code, out) = compiled(&dir, &[]);
    let (interp_code, interp) = interpreter(&dir);
    assert_eq!((code, counts(&out)), (interp_code, counts(&interp)), "{out}");
    assert!(out.contains("archive retention elided"), "{out}");
    assert!(out.contains("archive memory limit (elided: closed layout)"), "{out}");
    assert!(out.contains("0.0 KiB"), "an elided archive reports 0 B: {out}");
    // Nothing is allocated, spilled or dropped: the stats carry no archive
    // segment or peak lines at all.
    for line in ["archive peak (for resuming)", "archived states (for resuming)", "archive segments spilled"] {
        assert!(!out.contains(line), "an elided archive must not report {line}: {out}");
    }
    assert!(!out.contains("layout miss on"), "{out}");
    assert!(!out.contains("restarts (layout miss)"), "{out}");
}

#[test]
fn a_function_witness_flip_keeps_the_archive_and_resumes() {
    let dir = spec_dir("witness-flip", WITNESS_FLIP);
    // A small pre-run sees only the enumerated construction; the tuple the
    // other branch builds later can miss the fixed layout.
    let (code, out) = compiled(&dir, &[("TLX_PRERUN", "4"), ("TLX_RETAIN_MB", "64")]);
    let (interp_code, interp) = interpreter(&dir);
    assert_eq!((code, counts(&out)), (interp_code, counts(&interp)), "{out}");
    assert!(out.contains("layout miss on f (value <<1, 2>>)"), "{out}");
    // The miss resumed from the archive instead of restarting from scratch.
    assert!(!out.contains("restarts from scratch"), "{out}");
    assert!(!out.contains("resume archive dropped"), "{out}");
    // The first attempts kept the archive (the stat is the -stats line).
    assert!(out.contains("archive memory limit (TLX_RETAIN_MB)"), "{out}");
}

#[test]
fn an_out_of_shape_counter_keeps_the_archive_and_resumes() {
    let dir = spec_dir("growing", GROWING);
    // The pre-run stops far below the state space, so the counter leaves the
    // speculated integer range; the archive must carry the resumed states.
    let (code, out) = compiled(&dir, &[("TLX_PRERUN", "5"), ("TLX_RETAIN_MB", "64")]);
    let (interp_code, interp) = interpreter(&dir);
    assert_eq!((code, counts(&out)), (interp_code, counts(&interp)), "{out}");
    assert!(out.contains("layout miss on x"), "{out}");
    assert!(!out.contains("restarts from scratch"), "{out}");
    assert!(out.contains("archive memory limit (TLX_RETAIN_MB)"), "{out}");
}

#[test]
fn all_ref_slots_elide_the_archive_even_with_multi_arg_function_actions() {
    let src = r#"---- MODULE Archive ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
F[i \in {0}, j \in {1}] == x' = j
Next == F[0, 1]
====
"#;
    let dir = spec_dir("all-ref", src);
    let (code, out) = compiled(&dir, &[("TLX_VALUE_STORE", "all"), ("TLX_PRERUN", "1")]);
    let (interp_code, interp) = interpreter(&dir);
    assert_eq!((code, counts(&out)), (interp_code, counts(&interp)), "{out}");
    assert!(out.contains("archive retention elided"), "{out}");
    for line in ["archive peak (for resuming)", "archived states (for resuming)", "archive segments spilled"] {
        assert!(!out.contains(line), "an all-Ref elided archive must not report {line}: {out}");
    }
}

#[test]
fn soundness_regressions_keep_archive_under_paranoid_mode() {
    let cases = [
        (
            "quant",
            "1",
            r#"---- MODULE Archive ----
EXTENDS Integers, TLC, FiniteSets
VARIABLES a, b, c, x
Init == /\ a = FALSE /\ b = FALSE /\ c = FALSE /\ x = 0
Next == /\ a' = TRUE /\ b' = a /\ c' = b
        /\ \E i \in (IF a THEN 0..1 ELSE {0}) : x' = IF c THEN 100 ELSE 0
====
"#,
        ),
        (
            "scope2",
            "3",
            r#"---- MODULE Archive ----
EXTENDS Naturals
VARIABLES a, b, c, n, y
Init == /\ a = FALSE /\ b = FALSE /\ c = FALSE /\ n \in 0..2 /\ y = "ok"
Next == /\ a' = TRUE /\ b' = a /\ c' = b
        /\ n >= 0
        /\ n' = IF n < 1 THEN n ELSE n
        /\ y' = IF c THEN n ELSE "ok"
====
"#,
        ),
        (
            "member",
            "3",
            r#"---- MODULE Archive ----
EXTENDS Integers
VARIABLES a, b, c, x, y, number
Init == /\ a = FALSE /\ b = FALSE /\ c = FALSE /\ ((x = "hi" /\ number = FALSE) \/ (x = 0 /\ number = TRUE)) /\ y = "ok"
Next == /\ a' = TRUE /\ b' = a /\ c' = b /\ x' = x /\ number' = number
        /\ y' = IF number /\ c /\ x \in 0..1 THEN x ELSE "ok"
====
"#,
        ),
        (
            "cart",
            "1",
            r#"---- MODULE Archive ----
EXTENDS Integers, TLC, FiniteSets
VARIABLES a, b, c, x
Init == /\ a = FALSE /\ b = FALSE /\ c = FALSE /\ x \in 0..3
Next == /\ a' = TRUE /\ b' = a /\ c' = b
        /\ x' = IF c THEN Cardinality({<<i, j>> : i, j \in {0, 1, 2}}) ELSE 0
====
"#,
        ),
        (
            "fset",
            "1",
            r#"---- MODULE Archive ----
EXTENDS Integers, TLC, FiniteSets
VARIABLES a, b, c, x
Init == /\ a = FALSE /\ b = FALSE /\ c = FALSE /\ x = [i \in {1} |-> {0}]
Next == /\ a' = TRUE /\ b' = a /\ c' = b
        /\ IF c THEN x' \in [{1} -> {0}] ELSE x' = x
====
"#,
        ),
        (
            "tuplebind",
            "1",
            r#"---- MODULE Archive ----
EXTENDS Integers, TLC, FiniteSets
VARIABLES a, b, c, x
Init == /\ a = FALSE /\ b = FALSE /\ c = FALSE /\ x = [t \in {<<1>>} |-> t]
Next == /\ a' = TRUE /\ b' = a /\ c' = b
        /\ IF c THEN x' = [<<i>> \in {<<1>>} |-> i] ELSE x' = x
====
"#,
        ),
        (
            "assert",
            "1",
            r#"---- MODULE Archive ----
EXTENDS Integers, TLC, FiniteSets
VARIABLES a, b, c, x
Init == /\ a = FALSE /\ b = FALSE /\ c = FALSE /\ x = "ok"
Next == /\ a' = TRUE /\ b' = a /\ c' = b
        /\ x' = IF c THEN Assert(a, "ok") ELSE "ok"
====
"#,
        ),
    ];
    for (name, prerun, src) in cases {
        let dir = spec_dir(name, src);
        let (code, out) = compiled(&dir, &[("TLX_PARANOID", "1"), ("TLX_PRERUN", prerun), ("TLX_RETAIN_MB", "64")]);
        let (interp_code, interp) = interpreter(&dir);
        assert_eq!((code, counts(&out)), (interp_code, counts(&interp)), "{name}: {out}");
        assert!(!out.contains("proved closed against"), "{name} hit paranoid mismatch: {out}");
        assert!(!out.contains("resume archive dropped"), "{name} dropped resume archive: {out}");
        assert!(out.contains("resumed searches                     1"), "{name} did not resume from archive: {out}");
        assert!(out.contains("archive memory limit (TLX_RETAIN_MB)"), "{name} did not retain archive: {out}");
    }
}

#[test]
fn cfg_overrides_and_const_substitutions_keep_archive_under_paranoid_mode() {
    let cases = [
        (
            "guard-override",
            r#"---- MODULE Archive ----
EXTENDS Naturals
VARIABLES a, b, c, x, y
AlwaysLT(u, v) == TRUE
Init == /\ a = FALSE /\ b = FALSE /\ c = FALSE /\ x = 12 /\ y = 0
Next == /\ a' = TRUE /\ b' = a /\ c' = b /\ x' = x
        /\ y' = IF c /\ x < 1 THEN x ELSE 0
====
"#,
            "INIT Init\nNEXT Next\nCONSTANT < <- AlwaysLT\nCHECK_DEADLOCK FALSE\n",
        ),
        (
            "cmp-override-str",
            r#"---- MODULE Archive ----
EXTENDS Integers
VARIABLES a, b, c, n, x
Yes(l, r) == TRUE
Init == /\ a = FALSE /\ b = FALSE /\ c = FALSE /\ n = 1 /\ x = "ok"
Next == /\ a' = TRUE /\ b' = a /\ c' = b /\ UNCHANGED n
        /\ x' = IF c /\ n < 0 THEN n ELSE "ok"
====
"#,
            "INIT Init\nNEXT Next\nCONSTANT < <- Yes\nCHECK_DEADLOCK FALSE\n",
        ),
        (
            "const-def-value",
            r#"---- MODULE Archive ----
EXTENDS Integers
VARIABLES a, b, c, n, x
CONSTANT K
F == "ok"
Init == /\ a = FALSE /\ b = FALSE /\ c = FALSE /\ n = 1 /\ x = "ok"
Next == /\ a' = TRUE /\ b' = a /\ c' = b /\ UNCHANGED n
        /\ x' = IF c THEN K ELSE "ok"
====
"#,
            "INIT Init\nNEXT Next\nCONSTANT K <- F\nCONSTANT F = 100\nCHECK_DEADLOCK FALSE\n",
        ),
    ];
    for (name, src, cfg) in cases {
        let dir = tlx_testkit::TempDir::with_spec(name, src, cfg);
        let (code, out) = compiled(&dir, &[("TLX_PARANOID", "1"), ("TLX_PRERUN", "1"), ("TLX_RETAIN_MB", "64")]);
        let (interp_code, interp) = interpreter(&dir);
        assert_eq!((code, counts(&out)), (interp_code, counts(&interp)), "{name}: {out}");
        assert!(!out.contains("proved closed against"), "{name} hit paranoid mismatch: {out}");
        assert!(!out.contains("resume archive dropped"), "{name} dropped resume archive: {out}");
        assert!(out.contains("resumed searches                     1"), "{name} did not resume from archive: {out}");
        assert!(out.contains("archive memory limit (TLX_RETAIN_MB)"), "{name} did not retain archive: {out}");
    }
}

#[test]
fn untaken_huge_lazy_domain_does_not_exhaust_analysis_budget() {
    for (tag, def) in [
        ("huge-powerset", "Huge == SUBSET (1..19)"),
        ("wide-singleton-fcnset", "Huge == [1..250000 -> {0}]"),
        ("nested-lazy-recordset", "Huge == [pool: {SUBSET (1..19)}]"),
    ] {
        let src = format!(
            "---- MODULE Archive ----\nEXTENDS Naturals\n{def}\nVARIABLES b, x\n\
             Init == b = FALSE /\\ x = 0\n\
             Next == b' = b /\\ x' = IF b THEN [i \\in Huge |-> b] ELSE x\n====\n"
        );
        let dir = spec_dir(tag, &src);
        let (code, out) = compiled(&dir, &[("TLX_PARANOID", "1"), ("TLX_RETAIN_MB", "8")]);
        let (interp_code, interp) = interpreter(&dir);
        assert_eq!((code, counts(&out)), (interp_code, counts(&interp)), "{tag}: {out}");
        assert!(!out.contains("budget is exhausted"), "{tag}: {out}");
        assert!(out.contains("archive memory limit (TLX_RETAIN_MB)"), "{tag}: {out}");
    }
}

#[test]
fn value_store_exhaustion_does_not_trigger_false_closure_refutation() {
    let src = r#"---- MODULE Archive ----
EXTENDS Naturals, Sequences, TLC
VARIABLES bag, n
K(i) == [id |-> i, log |-> <<i>>]
Init == bag = (K(0) :> 0) /\ n = 0
Next == n < 1000 /\ bag' = bag @@ (K(n + 1) :> n) /\ n' = n + 1
====
"#;
    let dir = spec_dir("store-budget", src);
    for paranoid in ["0", "1"] {
        let mut cmd = tlx_testkit::tlx_default!();
        cmd.check("Archive.tla").args(["-config", "Archive.cfg", "-workers", "1", "-compile", "-stats", "-maxmem", "4M"]).dir(&dir).envs([
            ("TLX_VALUE_STORE", "all"),
            ("TLX_PRERUN", "1"),
            ("TLX_PRERUN_REUSE", "0"),
            ("TLX_PARANOID", paranoid),
        ]);
        let out = cmd.run();
        let text = out.text();
        assert_ne!(out.code, 0, "paranoid={paranoid}: expected budget stop: {text}");
        assert_ne!(out.code, 101, "paranoid={paranoid}: panicked instead of reporting budget error: {text}");
        assert!(text.contains("value store (TLX_VALUE_STORE) exceeded its budget"), "paranoid={paranoid}: {text}");
        assert!(!text.contains("proved closed against"), "paranoid={paranoid}: {text}");
        assert!(!text.contains("closed-layout proof refuted"), "paranoid={paranoid}: {text}");
    }
}
