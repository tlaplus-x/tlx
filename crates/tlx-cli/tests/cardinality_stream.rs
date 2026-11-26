//! A quantifier over a set whose `size()` overflows TLC's int: the interpreter
//! used to materialize the domain of a bound variable and fail with the
//! overflow, while the compiled tier streamed its quantifiers, so
//! `TLX_PARANOID` reported the divergence.
//! `SpanningTree/SpanTreeTest5Nodes` and
//! `CarTalkPuzzle/CarTalkPuzzle.toolbox/Model_3/MC` failed the same way
//! through `x' \in S` and through printing a set filter, which TLC streams too
//! (the default order of `Enumerable.elements()`).
//!
//! For a *bound*, TLC asks for the normalized order: it streams a `SUBSET S`
//! domain and materializes every other kind, so `\E s \in SUBSET (1..31)` is a
//! claim of agreement with TLC, and `\E f \in [1..5 -> 1..121]` is TLC's
//! "too many elements" error (`ValueVec.ensureCapacity` at `-maxSetSize`,
//! which a growing `[S -> T]` reaches long before its size could overflow):
//! both tiers must report it (`docs/compat.md` section 5).

use std::path::Path;
use std::time::Duration;

use tlx_testkit::cli::counts;

/// `SUBSET (1..31)` (2^31 elements) starts with `{}`, so a streamed
/// enumeration answers at the first element; a materializing one would not
/// finish.
const SUBSET_SPEC: &str = r#"---- MODULE CardStream ----
EXTENDS Naturals, FiniteSets

VARIABLE x

Init == x = 0

Next == x' = x

BigSubset == \E s \in SUBSET (1..31) : s = {}

Inv == x = 0 /\ BigSubset
====
"#;

/// `[1..5 -> 1..121]` (121^5 elements): the third function of the normalized
/// order satisfies the body, but TLC materializes the domain and stops at its
/// set bound first.
const FUNCTION_SET_SPEC: &str = r#"---- MODULE CardStreamFcn ----
EXTENDS Naturals, FiniteSets

VARIABLE x

Init == x = 0

Next == x' = x

BigFcn == \E f \in [1..5 -> 1..121] : f[1] = 1 /\ f[5] = 3

Inv == x = 0 /\ BigFcn
====
"#;

const CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";

/// Whether to run the default tier (else the `-tlc -interp` parity tier of
/// `tlx!`). The timeout turns a materializing enumeration into a failure
/// instead of a hang.
fn run(dir: &Path, spec: &str, default_tier: bool, args: &[&str], env: &[(&str, &str)]) -> (i32, String) {
    let mut cmd = if default_tier { tlx_testkit::tlx_default!() } else { tlx_testkit::tlx!() };
    cmd.args(["check", spec]).args(args).dir(dir).timeout(Duration::from_secs(120));
    let out = cmd.envs(env.iter().copied()).run();
    (out.code, out.text())
}

/// Paranoid runs with forced misses (a one-state pre-run), on the IR executor
/// and on native code.
const PARANOID_MODES: [&[(&str, &str)]; 2] = [
    &[("TLX_PARANOID", "1"), ("TLX_PRERUN", "1"), ("TLX_NO_NATIVE", "1")],
    &[("TLX_PARANOID", "1"), ("TLX_PRERUN", "1"), ("TLX_NATIVE_SYNC", "1")],
];

#[test]
fn overflowing_subset_bound_is_streamed() {
    let dir = tlx_testkit::TempDir::with_spec("card_stream", SUBSET_SPEC, CFG);
    let (code, plain) = run(&dir, "CardStream.tla", true, &[], &[]);
    assert_eq!(code, 0, "{plain}");
    assert!(!plain.contains("Overflow"), "{plain}");
    assert_eq!(
        counts(&plain),
        ["2 states generated, 1 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 1."]
    );
    // The interpreter (the parity tier) and the compiled tier agree.
    for (default_tier, args) in [(false, &[][..]), (true, &["-interp"][..]), (true, &["-compile"][..])] {
        let (code, out) = run(&dir, "CardStream.tla", default_tier, args, &[]);
        assert_eq!((code, counts(&out)), (0, counts(&plain)), "default_tier={default_tier} {args:?}:\n{out}");
    }
    for env in PARANOID_MODES {
        let (code, out) = run(&dir, "CardStream.tla", true, &["-compile"], env);
        assert_eq!((code, counts(&out)), (0, counts(&plain)), "{env:?}:\n{out}");
    }
}

#[test]
fn overflowing_function_set_bound_is_tlcs_error() {
    let dir = tlx_testkit::TempDir::with_spec("card_stream_fcn", FUNCTION_SET_SPEC, CFG);
    for args in [&[][..], &["-interp"][..], &["-compile"][..]] {
        let (code, out) = run(&dir, "CardStreamFcn.tla", true, args, &[]);
        assert_eq!(code, 75, "{args:?}:\n{out}");
        assert!(out.contains("Attempted to construct a set with too many elements (>1000000)"), "{args:?}:\n{out}");
    }
    for env in PARANOID_MODES {
        let (code, out) = run(&dir, "CardStreamFcn.tla", true, &["-compile"], env);
        assert_eq!(code, 75, "{env:?}:\n{out}");
        assert!(out.contains("too many elements (>1000000)"), "{env:?}:\n{out}");
    }
}
