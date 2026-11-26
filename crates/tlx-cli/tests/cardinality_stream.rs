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

/// `CHOOSE` over overflowing `SUBSET (1..31)` and over-`-maxSetSize`
/// `kSubset(10, 1..30)` (30,045,015 subsets) streams in TLC's normalized order
/// for both constant hoisted and state-dependent predicates. Two distinct
/// states ensure `TLX_PRERUN=1` enters compiled execution.
const CHOOSE_STREAM_SPEC: &str = r#"---- MODULE CardStreamChoose ----
EXTENDS Naturals, FiniteSets, FiniteSetsExt

VARIABLE x

Init == x = 1

Next == IF x = 1 THEN x' = 2 ELSE x' = x

Inv ==
    /\ (CHOOSE s \in SUBSET (1..31) : s = {}) = {}
    /\ (CHOOSE s \in SUBSET (1..31) : TRUE) = {}
    /\ (CHOOSE s \in SUBSET (1..31) : x \in s) = {x}
    /\ (CHOOSE s \in kSubset(10, 1..30) : x \in s) = (1..10)
    /\ (CHOOSE s \in kSubset(10, 1..30) : (x + 10) \in s) = ((1..9) \cup {x + 10})
====
"#;

/// Empty `kSubset(2, {1})` in `CHOOSE` must report the standard no-witness
/// error across every tier.
const CHOOSE_EMPTY_KSUBSET_SPEC: &str = r#"---- MODULE CardStreamChooseEmptyKSub ----
EXTENDS Naturals, FiniteSetsExt

VARIABLE x

Init == x = 1

Next == IF x = 1 THEN x' = 2 ELSE x' = x

Inv == (CHOOSE s \in kSubset(2, {x}) : TRUE) = {}
====
"#;

/// Non-enumerable base in `CHOOSE s \in SUBSET Nat : TRUE` must validate the
/// base even on the `TRUE` fast path across every tier.
const CHOOSE_SUBSET_NAT_SPEC: &str = r#"---- MODULE CardStreamChooseSubsetNat ----
EXTENDS Naturals

VARIABLE x

Init == x = 1

Next == IF x = 1 THEN x' = 2 ELSE x' = x

Inv == (CHOOSE s \in SUBSET Nat : TRUE) = {x}
====
"#;

/// Tuple binder over `SUBSET (1..31)` with `TRUE` body must still fail tuple
/// destructuring rather than taking the single-variable `TRUE` fast path.
const CHOOSE_TUPLE_BINDER_SPEC: &str = r#"---- MODULE CardStreamChooseTuple ----
EXTENDS Naturals

VARIABLE x

Init == x = 1

Next == IF x = 1 THEN x' = 2 ELSE x' = x

Inv == (CHOOSE <<a, b>> \in SUBSET (1..31) : TRUE) = <<x, x>>
====
"#;

/// Non-`streams_normalized` lazy set (`[1..5 -> 1..121]`) in `CHOOSE` keeps
/// TLC's `-maxSetSize` materialization error across every tier.
const CHOOSE_FUNCTION_SET_SPEC: &str = r#"---- MODULE CardStreamChooseFcn ----
EXTENDS Naturals

VARIABLE x

Init == x = 1

Next == IF x = 1 THEN x' = 2 ELSE x' = x

Inv == (CHOOSE f \in [1..5 -> 1..121] : f[1] = x)[1] = x
====
"#;

/// Dynamic bitset state variable (`|x| = 24`) in `CHOOSE s \in SUBSET x : ...`:
/// lowering emits `ExprKind::Subsets(x)`, so the closure executor's
/// `Src::Subsets` must stream without allocating `2^24` subsets upfront.
const CHOOSE_DYNAMIC_BITSET_SPEC: &str = r#"---- MODULE CardStreamChooseDynBitset ----
EXTENDS Naturals

VARIABLE x

Init == x = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24}

Next == IF 24 \in x THEN x' = x \ {24} ELSE x' = x

Inv ==
    /\ (CHOOSE s \in SUBSET x : TRUE) = {}
    /\ (CHOOSE s \in SUBSET x : 2 \in s) = {2}
====
"#;

/// Dynamic bitset state variable (`|x| = 32 -> 31`) in both `CHOOSE` and
/// multi-variable `\E a, b \in SUBSET x`: bases beyond 24 elements fall back
/// from `Src::Subsets` to the streaming interpreter and succeed across every
/// tier and `TLX_PARANOID=1`.
const CHOOSE_DYNAMIC_BITSET_31_SPEC: &str = r#"---- MODULE CardStreamChooseDynBitset31 ----
EXTENDS Naturals

VARIABLE x

Init == x = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32}

Next == IF 32 \in x THEN x' = x \ {32} ELSE x' = x

Inv ==
    32 \in x \/ (
        /\ (CHOOSE s \in SUBSET x : TRUE) = {}
        /\ (CHOOSE s \in SUBSET x : 2 \in s) = {2}
    )
====
"#;

const MULTI_VAR_DYNAMIC_BITSET_31_SPEC: &str = r#"---- MODULE CardStreamMultiDynBitset31 ----
EXTENDS Naturals

VARIABLE x

Init == x = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32}

Next == IF 32 \in x THEN x' = x \ {32} ELSE x' = x

Inv == 32 \in x \/ (\E a, b \in SUBSET x : a = {1} /\ b = {})
====
"#;

/// Multi-variable, tuple-binder, empty-sibling, and action-level `ENABLED`
/// streaming over `SUBSET (1..31)` and `kSubset(10, 1..30)`. Two distinct
/// states ensure `TLX_PRERUN=1` enters compiled execution.
const MULTI_VAR_STREAM_SPEC: &str = r#"---- MODULE CardStreamMultiVar ----
EXTENDS Naturals, FiniteSets, FiniteSetsExt

VARIABLE x

Init == x = {}

Next == IF x = {} THEN x' = {1} ELSE x' = x

Inv ==
    /\ (\E a, b \in SUBSET (1..31) : a = {1} /\ b = {})
    /\ (\E a, b \in kSubset(10, 1..30) : a = (1..10) /\ b = (1..10))
    /\ (\E s \in SUBSET (1..31), <<a, b>> \in {<<1, 2>>} : s = x /\ a = 1 /\ b = 2)
    /\ ~(\E a \in SUBSET (1..31), b \in {} : TRUE)
    /\ ~(\E a \in {}, b \in SUBSET (1..31) : TRUE)
    /\ ~(\E a \in SUBSET (1..31), b \in kSubset(2, {1}) : TRUE)
    /\ ~ENABLED (\A a, b \in SUBSET (1..31) : a = b)
    /\ ENABLED (\E a, b \in SUBSET (1..31) : a = {1} /\ b = {} /\ x' = a)
    /\ (x = {} => ~ENABLED (\E a \in x, b \in SUBSET (1..31) : x' = b))
====
"#;

/// Tuple binder over `SUBSET (1..31)` in `\E` must fail tuple destructuring
/// consistently across every tier.
const MULTI_VAR_TUPLE_ERROR_SPEC: &str = r#"---- MODULE CardStreamMultiTupleErr ----
EXTENDS Naturals

VARIABLE x

Init == x = 1

Next == IF x = 1 THEN x' = 2 ELSE x' = x

Inv == \E <<a, b>> \in SUBSET (1..31) : a = x
====
"#;

/// Empty first bound followed by an invalid second bound (`SUBSET Nat`) must
/// still report the non-enumerable bound error in source order across tiers.
const MULTI_VAR_EMPTY_THEN_INVALID_SPEC: &str = r#"---- MODULE CardStreamMultiEmptyInvalid ----
EXTENDS Naturals

VARIABLE x

Init == x = 1

Next == IF x = 1 THEN x' = 2 ELSE x' = x

Inv == \E a \in {}, b \in SUBSET Nat : x = 1
====
"#;

/// Multi-variable set comprehension `{a \cup b : a, b \in SUBSET (1..20)}`
/// streams bindings and stops at `-maxSetSize` via `limits::push`.
const MULTI_VAR_SETMAP_LIMIT_SPEC: &str = r#"---- MODULE CardStreamMultiSetMapLimit ----
EXTENDS Naturals

VARIABLE x

Init == x = 1

Next == IF x = 1 THEN x' = 2 ELSE x' = x

Inv == x \in {a \cup b : a, b \in SUBSET (1..20)}
====
"#;

/// Action splitting must keep `\E a, b \in SUBSET (1..31) : ...` unsplit so
/// initial-state invariant violations are reported without materializing
/// `2^62` action instances at startup.
const ACTION_SPLIT_STREAM_SPEC: &str = r#"---- MODULE CardStreamActionSplit ----
EXTENDS Naturals

VARIABLE n

Init == n = 0

Next == \E a, b \in SUBSET (1..31) : n' = n

Inv == n = 1
====
"#;

/// Dynamically empty inner domain paired with a large streamed outer domain
/// (`kSubset(15, 1..30)`, `SUBSET (1..25)`) in compiled expression quantifiers
/// must short-circuit without walking the outer combinations.
const DYN_EMPTY_INNER_STREAM_SPEC: &str = r#"---- MODULE CardStreamDynEmptyInner ----
EXTENDS Naturals, FiniteSetsExt

VARIABLE n

Init == n = 0

Next == n' = IF n = 0 THEN 1 ELSE n

Inv ==
    n = 0 \/ (
        /\ ~(\E a \in 1..(1 - n), b \in kSubset(15, 1..30) : a \in b)
        /\ (\A a \in 1..(1 - n), b \in SUBSET (1..25) : a \in b)
    )
====
"#;

/// Dynamically empty inner domain followed by a dynamically invalid outer
/// domain must still report the invalid outer domain in source order across
/// every tier.
const DYN_EMPTY_INNER_INVALID_OUTER_SPEC: &str = r#"---- MODULE CardStreamDynEmptyInvalidOuter ----
EXTENDS Naturals

VARIABLE n

Init == n = 0

Next == n' = IF n = 0 THEN 1 ELSE n

Inv == n = 0 \/ ~(\E a \in 1..(1 - n), b \in (IF n = 1 THEN SUBSET Nat ELSE SUBSET (1..2)) : a \in b)
====
"#;

/// Ordinary tuple/function lookup (`flags[...]`) inside an action universal
/// over `SUBSET (1..31)` short-circuits via `self.test`, while an action-valued
/// function definition (`Act[i]`) retains its action-enumeration semantics.
const ACTION_FORALL_LOOKUP_SPEC: &str = r#"---- MODULE CardStreamForallLookup ----
EXTENDS Naturals

VARIABLES flags, x

Act[i \in {1}] == x' = i

Init == flags = <<FALSE, TRUE>> /\ x = 0

Next == flags' = flags /\ \A i \in {1} : Act[i]

Inv == ~ENABLED (\A a, b \in SUBSET (1..31) : flags[IF a = b THEN 1 ELSE 2])
====
"#;

/// Quantified safety property (`PROPERTY P == \A a, b \in 1..4 : [](...)`)
/// must stay classified as an invariant even when `-maxSetSize 10` is smaller
/// than the 16-element binding product.
const PROP_FORALL_SMALL_SPEC: &str = r#"---- MODULE CardStreamPropForallSmall ----
EXTENDS Naturals

VARIABLE n

Init == n = 0

Next == n' = n

P == \A a, b \in 1..4 : [](n # a - b)
====
"#;

/// Quantified safety property over `SUBSET (1..31)` must stay classified as an
/// invariant (probing at most one binding at classification time) and report
/// the initial-state violation immediately without expanding `2^62` temporal
/// branches.
const PROP_FORALL_STREAM_SPEC: &str = r#"---- MODULE CardStreamPropForallStream ----
EXTENDS Naturals

VARIABLE n

Init == n = 0

Next == n' = n

P == \A a, b \in SUBSET (1..31) : [](n # 0 \/ a # b)
====
"#;

/// A malformed tuple element in a quantified property whose body is a constant
/// `TRUE` definition must still be rejected across every tier rather than
/// folded away during property classification.
const PROP_FORALL_MALFORMED_TUPLE_SPEC: &str = r#"---- MODULE CardStreamPropMalformedTuple ----
EXTENDS Naturals

VARIABLE n

Init == n = 0

Next == n' = n

T == TRUE

P == \A <<a, b>> \in {<<1, 2>>, <<1, 2, 3>>} : T
====
"#;

const PROP_CFG: &str = "INIT Init\nNEXT Next\nPROPERTY P\nCHECK_DEADLOCK FALSE\n";

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

#[test]
fn choose_streams_normalized_subset_and_ksubset() {
    let dir = tlx_testkit::TempDir::with_spec("card_stream_choose", CHOOSE_STREAM_SPEC, CFG);
    let (code, plain) = run(&dir, "CardStreamChoose.tla", true, &[], &[]);
    assert_eq!(code, 0, "{plain}");
    assert!(!plain.contains("Overflow"), "{plain}");
    assert_eq!(
        counts(&plain),
        ["3 states generated, 2 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 2."]
    );
    for (default_tier, args) in [(false, &[][..]), (true, &["-interp"][..]), (true, &["-compile"][..])] {
        let (code, out) = run(&dir, "CardStreamChoose.tla", default_tier, args, &[]);
        assert_eq!((code, counts(&out)), (0, counts(&plain)), "default_tier={default_tier} {args:?}:\n{out}");
    }
    for env in PARANOID_MODES {
        let (code, out) = run(&dir, "CardStreamChoose.tla", true, &["-compile"], env);
        assert_eq!((code, counts(&out)), (0, counts(&plain)), "{env:?}:\n{out}");
    }
}

#[test]
fn choose_streams_dynamic_bitset_subsets() {
    let dir = tlx_testkit::TempDir::with_spec("card_stream_choose_dyn_bitset", CHOOSE_DYNAMIC_BITSET_SPEC, CFG);
    let (code, plain) = run(&dir, "CardStreamChooseDynBitset.tla", true, &[], &[]);
    assert_eq!(code, 0, "{plain}");
    assert_eq!(
        counts(&plain),
        ["3 states generated, 2 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 2."]
    );
    for (default_tier, args) in [(false, &[][..]), (true, &["-interp"][..]), (true, &["-compile"][..])] {
        let (code, out) = run(&dir, "CardStreamChooseDynBitset.tla", default_tier, args, &[]);
        assert_eq!((code, counts(&out)), (0, counts(&plain)), "default_tier={default_tier} {args:?}:\n{out}");
    }
    for env in PARANOID_MODES {
        let (code, out) = run(&dir, "CardStreamChooseDynBitset.tla", true, &["-compile"], env);
        assert_eq!((code, counts(&out)), (0, counts(&plain)), "{env:?}:\n{out}");
    }

    let dir = tlx_testkit::TempDir::with_spec("card_stream_choose_dyn_bitset_31", CHOOSE_DYNAMIC_BITSET_31_SPEC, CFG);
    let (code, plain) = run(&dir, "CardStreamChooseDynBitset31.tla", true, &[], &[]);
    assert_eq!(code, 0, "{plain}");
    assert_eq!(
        counts(&plain),
        ["3 states generated, 2 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 2."]
    );
    for (default_tier, args) in [(false, &[][..]), (true, &["-interp"][..]), (true, &["-compile"][..])] {
        let (code, out) = run(&dir, "CardStreamChooseDynBitset31.tla", default_tier, args, &[]);
        assert_eq!((code, counts(&out)), (0, counts(&plain)), "default_tier={default_tier} {args:?}:\n{out}");
    }
    for env in PARANOID_MODES {
        let (code, out) = run(&dir, "CardStreamChooseDynBitset31.tla", true, &["-compile"], env);
        assert_eq!((code, counts(&out)), (0, counts(&plain)), "{env:?}:\n{out}");
    }
}

#[test]
fn multi_var_dynamic_bitset_streams_across_tiers() {
    let dir = tlx_testkit::TempDir::with_spec("card_stream_multi_dyn_bitset_31", MULTI_VAR_DYNAMIC_BITSET_31_SPEC, CFG);
    let (code, plain) = run(&dir, "CardStreamMultiDynBitset31.tla", true, &[], &[]);
    assert_eq!(code, 0, "{plain}");
    assert!(!plain.contains("Overflow"), "{plain}");
    assert_eq!(
        counts(&plain),
        ["3 states generated, 2 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 2."]
    );
    for (default_tier, args) in [(false, &[][..]), (true, &["-interp"][..]), (true, &["-compile"][..])] {
        let (c, out) = run(&dir, "CardStreamMultiDynBitset31.tla", default_tier, args, &[]);
        assert_eq!((c, counts(&out)), (0, counts(&plain)), "default_tier={default_tier} {args:?}:\n{out}");
    }
    for env in PARANOID_MODES {
        let (c, out) = run(&dir, "CardStreamMultiDynBitset31.tla", true, &["-compile"], env);
        assert_eq!((c, counts(&out)), (0, counts(&plain)), "{env:?}:\n{out}");
    }
}

#[test]
fn multi_var_and_tuple_bounds_stream_across_tiers() {
    let dir = tlx_testkit::TempDir::with_spec("card_stream_multi_var", MULTI_VAR_STREAM_SPEC, CFG);
    let (code, plain) = run(&dir, "CardStreamMultiVar.tla", true, &[], &[]);
    assert_eq!(code, 0, "{plain}");
    assert!(!plain.contains("Overflow"), "{plain}");
    assert_eq!(
        counts(&plain),
        ["3 states generated, 2 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 2."]
    );
    for (default_tier, args) in [(false, &[][..]), (true, &["-interp"][..]), (true, &["-compile"][..])] {
        let (c, out) = run(&dir, "CardStreamMultiVar.tla", default_tier, args, &[]);
        assert_eq!((c, counts(&out)), (0, counts(&plain)), "default_tier={default_tier} {args:?}:\n{out}");
    }
    for env in PARANOID_MODES {
        let (c, out) = run(&dir, "CardStreamMultiVar.tla", true, &["-compile"], env);
        assert_eq!((c, counts(&out)), (0, counts(&plain)), "{env:?}:\n{out}");
    }
}

#[test]
fn multi_var_stream_errors_match_across_tiers() {
    let cases = [
        ("card_stream_multi_tuple_err", "CardStreamMultiTupleErr.tla", MULTI_VAR_TUPLE_ERROR_SPEC, "non-tuple"),
        ("card_stream_multi_empty_invalid", "CardStreamMultiEmptyInvalid.tla", MULTI_VAR_EMPTY_THEN_INVALID_SPEC, "non-enumerable"),
        (
            "card_stream_multi_setmap_limit",
            "CardStreamMultiSetMapLimit.tla",
            MULTI_VAR_SETMAP_LIMIT_SPEC,
            "Attempted to construct a set with too many elements (>1000000)",
        ),
    ];
    for (tag, file, spec, needle) in cases {
        let dir = tlx_testkit::TempDir::with_spec(tag, spec, CFG);
        for (default_tier, args) in [(false, &[][..]), (true, &[][..]), (true, &["-interp"][..]), (true, &["-compile"][..])] {
            let (code, out) = run(&dir, file, default_tier, args, &[]);
            assert_eq!(code, 75, "{file} default_tier={default_tier} {args:?}:\n{out}");
            assert!(out.contains(needle), "{file} default_tier={default_tier} {args:?}:\n{out}");
        }
        for env in PARANOID_MODES {
            let (code, out) = run(&dir, file, true, &["-compile"], env);
            assert_eq!(code, 75, "{file} {env:?}:\n{out}");
            assert!(out.contains(needle), "{file} {env:?}:\n{out}");
        }
    }
}

#[test]
fn action_split_keeps_huge_streamed_product_unsplit() {
    let dir = tlx_testkit::TempDir::with_spec("card_stream_action_split", ACTION_SPLIT_STREAM_SPEC, CFG);
    for (default_tier, args) in [(false, &[][..]), (true, &[][..]), (true, &["-interp"][..]), (true, &["-compile"][..])] {
        let (code, out) = run(&dir, "CardStreamActionSplit.tla", default_tier, args, &[]);
        assert_eq!(code, 12, "default_tier={default_tier} {args:?}:\n{out}");
        assert!(out.contains("Invariant Inv is violated"), "default_tier={default_tier} {args:?}:\n{out}");
    }
    for env in PARANOID_MODES {
        let (code, out) = run(&dir, "CardStreamActionSplit.tla", true, &["-compile"], env);
        assert_eq!(code, 12, "{env:?}:\n{out}");
        assert!(out.contains("Invariant Inv is violated"), "{env:?}:\n{out}");
    }
}

#[test]
fn dynamic_empty_inner_bound_and_forall_lookup_stream_across_tiers() {
    let dir = tlx_testkit::TempDir::with_spec("card_stream_dyn_empty_inner", DYN_EMPTY_INNER_STREAM_SPEC, CFG);
    let (code, plain) = run(&dir, "CardStreamDynEmptyInner.tla", true, &[], &[]);
    assert_eq!(code, 0, "{plain}");
    assert_eq!(
        counts(&plain),
        ["3 states generated, 2 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 2."]
    );
    for (default_tier, args) in [(false, &[][..]), (true, &["-interp"][..]), (true, &["-compile"][..])] {
        let (c, out) = run(&dir, "CardStreamDynEmptyInner.tla", default_tier, args, &[]);
        assert_eq!((c, counts(&out)), (0, counts(&plain)), "default_tier={default_tier} {args:?}:\n{out}");
    }
    for env in PARANOID_MODES {
        let (c, out) = run(&dir, "CardStreamDynEmptyInner.tla", true, &["-compile"], env);
        assert_eq!((c, counts(&out)), (0, counts(&plain)), "{env:?}:\n{out}");
    }

    let dir = tlx_testkit::TempDir::with_spec("card_stream_dyn_empty_invalid", DYN_EMPTY_INNER_INVALID_OUTER_SPEC, CFG);
    for (default_tier, args) in [(false, &[][..]), (true, &[][..]), (true, &["-interp"][..]), (true, &["-compile"][..])] {
        let (code, out) = run(&dir, "CardStreamDynEmptyInvalidOuter.tla", default_tier, args, &[]);
        assert_eq!(code, 76, "default_tier={default_tier} {args:?}:\n{out}");
        assert!(out.contains("non-enumerable"), "default_tier={default_tier} {args:?}:\n{out}");
    }
    for env in PARANOID_MODES {
        let (code, out) = run(&dir, "CardStreamDynEmptyInvalidOuter.tla", true, &["-compile"], env);
        assert_eq!(code, 76, "{env:?}:\n{out}");
        assert!(out.contains("non-enumerable"), "{env:?}:\n{out}");
    }

    let dir = tlx_testkit::TempDir::with_spec("card_stream_forall_lookup", ACTION_FORALL_LOOKUP_SPEC, CFG);
    let (code, plain) = run(&dir, "CardStreamForallLookup.tla", true, &[], &[]);
    assert_eq!(code, 0, "{plain}");
    assert_eq!(
        counts(&plain),
        ["3 states generated, 2 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 2."]
    );
    for (default_tier, args) in [(false, &[][..]), (true, &["-interp"][..]), (true, &["-compile"][..])] {
        let (c, out) = run(&dir, "CardStreamForallLookup.tla", default_tier, args, &[]);
        assert_eq!((c, counts(&out)), (0, counts(&plain)), "default_tier={default_tier} {args:?}:\n{out}");
    }
    for env in PARANOID_MODES {
        let (c, out) = run(&dir, "CardStreamForallLookup.tla", true, &["-compile"], env);
        assert_eq!((c, counts(&out)), (0, counts(&plain)), "{env:?}:\n{out}");
    }
}

#[test]
fn quantified_safety_property_classifies_as_invariant_for_small_limit_and_stream() {
    let dir = tlx_testkit::TempDir::with_spec("card_stream_prop_small", PROP_FORALL_SMALL_SPEC, PROP_CFG);
    for (default_tier, args) in [
        (false, &["-maxSetSize", "10"][..]),
        (true, &["-maxSetSize", "10"][..]),
        (true, &["-interp", "-maxSetSize", "10"][..]),
        (true, &["-compile", "-maxSetSize", "10"][..]),
    ] {
        let (code, out) = run(&dir, "CardStreamPropForallSmall.tla", default_tier, args, &[]);
        assert_eq!(code, 12, "default_tier={default_tier} {args:?}:\n{out}");
        assert!(out.contains("Invariant") && out.contains("is violated"), "default_tier={default_tier} {args:?}:\n{out}");
        assert!(!out.contains("Temporal properties were violated"), "default_tier={default_tier} {args:?}:\n{out}");
    }
    for env in PARANOID_MODES {
        let (code, out) = run(&dir, "CardStreamPropForallSmall.tla", true, &["-compile", "-maxSetSize", "10"], env);
        assert_eq!(code, 12, "{env:?}:\n{out}");
        assert!(out.contains("Invariant") && out.contains("is violated"), "{env:?}:\n{out}");
        assert!(!out.contains("Temporal properties were violated"), "{env:?}:\n{out}");
    }

    let dir = tlx_testkit::TempDir::with_spec("card_stream_prop_stream", PROP_FORALL_STREAM_SPEC, PROP_CFG);
    for (default_tier, args) in [(false, &[][..]), (true, &[][..]), (true, &["-interp"][..]), (true, &["-compile"][..])] {
        let (code, out) = run(&dir, "CardStreamPropForallStream.tla", default_tier, args, &[]);
        assert_eq!(code, 12, "default_tier={default_tier} {args:?}:\n{out}");
        assert!(out.contains("Invariant") && out.contains("is violated"), "default_tier={default_tier} {args:?}:\n{out}");
        assert!(!out.contains("Temporal properties were violated"), "default_tier={default_tier} {args:?}:\n{out}");
    }
    for env in PARANOID_MODES {
        let (code, out) = run(&dir, "CardStreamPropForallStream.tla", true, &["-compile"], env);
        assert_eq!(code, 12, "{env:?}:\n{out}");
        assert!(out.contains("Invariant") && out.contains("is violated"), "{env:?}:\n{out}");
        assert!(!out.contains("Temporal properties were violated"), "{env:?}:\n{out}");
    }

    let dir = tlx_testkit::TempDir::with_spec("card_stream_prop_malformed_tuple", PROP_FORALL_MALFORMED_TUPLE_SPEC, PROP_CFG);
    for (default_tier, args) in [(false, &[][..]), (true, &[][..]), (true, &["-interp"][..]), (true, &["-compile"][..])] {
        let (code, out) = run(&dir, "CardStreamPropMalformedTuple.tla", default_tier, args, &[]);
        assert_eq!(code, 75, "default_tier={default_tier} {args:?}:\n{out}");
        assert!(out.contains("tuple binder of length 2"), "default_tier={default_tier} {args:?}:\n{out}");
    }
    for env in PARANOID_MODES {
        let (code, out) = run(&dir, "CardStreamPropMalformedTuple.tla", true, &["-compile"], env);
        assert_eq!(code, 75, "{env:?}:\n{out}");
        assert!(out.contains("tuple binder of length 2"), "{env:?}:\n{out}");
    }
}

#[test]
fn choose_stream_errors_match_across_tiers() {
    let cases = [
        ("card_stream_choose_empty_ksub", "CardStreamChooseEmptyKSub.tla", CHOOSE_EMPTY_KSUBSET_SPEC, "no element of S satisfied P"),
        ("card_stream_choose_subset_nat", "CardStreamChooseSubsetNat.tla", CHOOSE_SUBSET_NAT_SPEC, "non-enumerable"),
        ("card_stream_choose_tuple", "CardStreamChooseTuple.tla", CHOOSE_TUPLE_BINDER_SPEC, "non-tuple"),
        (
            "card_stream_choose_fcn",
            "CardStreamChooseFcn.tla",
            CHOOSE_FUNCTION_SET_SPEC,
            "Attempted to construct a set with too many elements (>1000000)",
        ),
    ];
    for (tag, file, spec, needle) in cases {
        let dir = tlx_testkit::TempDir::with_spec(tag, spec, CFG);
        for (default_tier, args) in [(false, &[][..]), (true, &[][..]), (true, &["-interp"][..]), (true, &["-compile"][..])] {
            let (code, out) = run(&dir, file, default_tier, args, &[]);
            assert_eq!(code, 75, "{file} default_tier={default_tier} {args:?}:\n{out}");
            assert!(out.contains(needle), "{file} default_tier={default_tier} {args:?}:\n{out}");
        }
        for env in PARANOID_MODES {
            let (code, out) = run(&dir, file, true, &["-compile"], env);
            assert_eq!(code, 75, "{file} {env:?}:\n{out}");
            assert!(out.contains(needle), "{file} {env:?}:\n{out}");
        }
    }
}
