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

/// `ENABLED (x' \subseteq (1..31) /\ ...)` streams `SUBSET (1..31)` in TLC's
/// normalized order (`{}`, `{1}`, ...) and stops at the witness without
/// materializing `2^31` subsets. Two distinct states ensure `TLX_PRERUN=1`
/// enters compiled execution.
const SUBSETEQ_ENABLED_SPEC: &str = r#"---- MODULE CardStreamSubsetEqEnabled ----
EXTENDS Naturals

VARIABLE x

Init == x = {}

Next == IF x = {} THEN x' = {1} ELSE x' = x

Inv ==
    /\ ENABLED (x' \subseteq (1..31) /\ x' = {})
    /\ ENABLED (x' \subseteq (1..31) /\ x' = {1})
====
"#;

/// Below-overflow base (`|1..25| = 25 < 31`, `2^25 = 33,554,432` subsets):
/// native mixed mode must route `x' \subseteq (1..25)` to the streaming
/// executor instead of materializing all `2^25` subsets via `HostFn::Elems`.
const SUBSETEQ_BELOW_OVERFLOW_SPEC: &str = r#"---- MODULE CardStreamSubsetEqBelowOverflow ----
EXTENDS Naturals

VARIABLE x

Init == x = {}

Next == IF x = {} THEN x' = {1} ELSE x' = x

Inv ==
    /\ ENABLED (x' \subseteq (1..25) /\ x' = {})
    /\ ENABLED (x' \subseteq (1..25) /\ x' = {1})
====
"#;

/// Exhaustive `Init` (`x \subseteq (1..3)`) and `Next` (`x' \subseteq x`)
/// enumeration: 8 initial states, sum_{k=0}^3 C(3,k)*2^k = 27 transitions,
/// 16 distinct states total, depth 2.
const SUBSETEQ_ENUM_SPEC: &str = r#"---- MODULE CardStreamSubsetEqEnum ----
EXTENDS Naturals

VARIABLES step, x

Init == step = 0 /\ x \subseteq (1..3)

Next == step = 0 /\ step' = 1 /\ x' \subseteq x

Inv == x \subseteq (1..3)
====
"#;

/// Normalized order of `x' \subseteq (1..3)`: `{}`, `{1}`, `{2}`, `{3}`,
/// `{1, 2}`, ... — the first subset with cardinality >= 2 is `{1, 2}`.
const SUBSETEQ_ORDER_SPEC: &str = r#"---- MODULE CardStreamSubsetEqOrder ----
EXTENDS Naturals, FiniteSets

VARIABLE x

Init == x = {}

Next == x' \subseteq (1..3)

Inv == Cardinality(x) < 2
====
"#;

/// Non-enumerable base in `x' \subseteq Nat` must report the same error across
/// interpreter and compiled tiers.
const SUBSETEQ_NON_ENUM_SPEC: &str = r#"---- MODULE CardStreamSubsetEqNonEnum ----
EXTENDS Naturals

VARIABLE x

Init == x = {}

Next == x' = x

Inv == ENABLED (x' \subseteq Nat)
====
"#;

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

#[test]
fn overflowing_subseteq_enabled_is_streamed() {
    let dir = tlx_testkit::TempDir::with_spec("card_stream_subseteq_enabled", SUBSETEQ_ENABLED_SPEC, CFG);
    let (code, plain) = run(&dir, "CardStreamSubsetEqEnabled.tla", true, &[], &[]);
    assert_eq!(code, 0, "{plain}");
    assert!(!plain.contains("Overflow"), "{plain}");
    assert_eq!(
        counts(&plain),
        ["3 states generated, 2 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 2."]
    );
    for (default_tier, args) in [(false, &[][..]), (true, &["-interp"][..]), (true, &["-compile"][..])] {
        let (code, out) = run(&dir, "CardStreamSubsetEqEnabled.tla", default_tier, args, &[]);
        assert_eq!((code, counts(&out)), (0, counts(&plain)), "default_tier={default_tier} {args:?}:\n{out}");
    }
    for env in PARANOID_MODES {
        let (code, out) = run(&dir, "CardStreamSubsetEqEnabled.tla", true, &["-compile"], env);
        assert_eq!((code, counts(&out)), (0, counts(&plain)), "{env:?}:\n{out}");
    }
}

#[test]
fn below_overflow_subseteq_enabled_streams_in_native_mode() {
    let dir = tlx_testkit::TempDir::with_spec("card_stream_subseteq_below_overflow", SUBSETEQ_BELOW_OVERFLOW_SPEC, CFG);
    let (code, plain) = run(&dir, "CardStreamSubsetEqBelowOverflow.tla", true, &[], &[]);
    assert_eq!(code, 0, "{plain}");
    assert_eq!(
        counts(&plain),
        ["3 states generated, 2 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 2."]
    );
    for (default_tier, args) in [(false, &[][..]), (true, &["-interp"][..]), (true, &["-compile"][..])] {
        let (code, out) = run(&dir, "CardStreamSubsetEqBelowOverflow.tla", default_tier, args, &[]);
        assert_eq!((code, counts(&out)), (0, counts(&plain)), "default_tier={default_tier} {args:?}:\n{out}");
    }
    for env in PARANOID_MODES {
        let (code, out) = run(&dir, "CardStreamSubsetEqBelowOverflow.tla", true, &["-compile"], env);
        assert_eq!((code, counts(&out)), (0, counts(&plain)), "{env:?}:\n{out}");
    }
}

#[test]
fn subseteq_action_enumeration_and_normalized_order() {
    let dir = tlx_testkit::TempDir::with_spec("card_stream_subseteq_enum", SUBSETEQ_ENUM_SPEC, CFG);
    let (code, tlc) = run(&dir, "CardStreamSubsetEqEnum.tla", false, &[], &[]);
    assert_eq!(code, 0, "{tlc}");
    assert_eq!(
        counts(&tlc),
        ["35 states generated, 16 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 2."]
    );
    for (default_tier, args) in [(true, &[][..]), (true, &["-interp"][..]), (true, &["-compile"][..])] {
        let (code, out) = run(&dir, "CardStreamSubsetEqEnum.tla", default_tier, args, &[]);
        assert_eq!((code, counts(&out)), (0, counts(&tlc)), "default_tier={default_tier} {args:?}:\n{out}");
    }
    for env in PARANOID_MODES {
        let (code, out) = run(&dir, "CardStreamSubsetEqEnum.tla", true, &["-compile"], env);
        assert_eq!((code, counts(&out)), (0, counts(&tlc)), "{env:?}:\n{out}");
    }

    let dir = tlx_testkit::TempDir::with_spec("card_stream_subseteq_order", SUBSETEQ_ORDER_SPEC, CFG);
    let (code, tlc) = run(&dir, "CardStreamSubsetEqOrder.tla", false, &[], &[]);
    assert_eq!(code, 12, "{tlc}");
    assert!(tlc.contains("Invariant Inv is violated"), "{tlc}");
    assert!(tlc.contains("x = {1, 2}"), "{tlc}");
    assert_eq!(
        counts(&tlc),
        ["6 states generated, 5 distinct states found, 3 states left on queue.", "The depth of the complete state graph search is 2."]
    );
    for (default_tier, args) in [(true, &[][..]), (true, &["-interp"][..]), (true, &["-compile"][..])] {
        let (code, out) = run(&dir, "CardStreamSubsetEqOrder.tla", default_tier, args, &[]);
        assert_eq!((code, counts(&out)), (12, counts(&tlc)), "default_tier={default_tier} {args:?}:\n{out}");
        assert!(out.contains("x = {1, 2}"), "default_tier={default_tier} {args:?}:\n{out}");
    }
    for env in PARANOID_MODES {
        let (code, out) = run(&dir, "CardStreamSubsetEqOrder.tla", true, &["-compile"], env);
        assert_eq!((code, counts(&out)), (12, counts(&tlc)), "{env:?}:\n{out}");
        assert!(out.contains("x = {1, 2}"), "{env:?}:\n{out}");
    }
}

#[test]
fn non_enumerable_subseteq_errors() {
    let dir = tlx_testkit::TempDir::with_spec("card_stream_subseteq_non_enum", SUBSETEQ_NON_ENUM_SPEC, CFG);
    for (default_tier, args) in [(false, &[][..]), (true, &[][..]), (true, &["-interp"][..]), (true, &["-compile"][..])] {
        let (code, out) = run(&dir, "CardStreamSubsetEqNonEnum.tla", default_tier, args, &[]);
        assert_eq!(code, 75, "default_tier={default_tier} {args:?}:\n{out}");
        assert!(out.contains("non-enumerable"), "default_tier={default_tier} {args:?}:\n{out}");
    }
    for env in PARANOID_MODES {
        let (code, out) = run(&dir, "CardStreamSubsetEqNonEnum.tla", true, &["-compile"], env);
        assert_eq!(code, 75, "{env:?}:\n{out}");
        assert!(out.contains("non-enumerable"), "{env:?}:\n{out}");
    }
}
