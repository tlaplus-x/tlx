//! `-maxSetSize N`: TLC's upper bound on the elements of a set that is
//! *materialized* (`TLCGlobals.setBound`, docs/compat.md section 5).
//!
//! TLC builds `[S -> T]`, `S \X T`, a record set, a set former or a set
//! filter over an enumerable set in a `ValueVec` that may grow only up to the
//! bound, so a domain of a quantifier over one of them with more elements is
//! an error, while `x' \in S`, `{x \in S : P}`, a `SUBSET S` bound and an
//! interval stream. `tlx` accepts the option and agrees in every tier.
//!
//! `TraceWithLargeSetOfInitialStatesTest` (tlcsuite) is the same distinction
//! from TLC's own suite: with `-maxSetSize 10`, 11 initial states of `x \in
//! 1..11` stream and the run reports the safety violation.

use std::path::Path;
use std::time::Duration;

use tlx_testkit::cli::counts;

/// A quantifier over a materialized domain (`[1..3 -> 1..5]`, 125 elements).
const MATERIALIZED: &str = r#"---- MODULE MatBound ----
EXTENDS Integers

VARIABLE x

Init == x = 0

Next == x' = x

Inv == x = 0 /\ \E f \in [1..3 -> 1..5] : f[1] = 1
====
"#;

/// The paths TLC streams: an interval bound, a `SUBSET` bound, and the
/// elements of a function set assigned to a variable.
const STREAMED: &str = r#"---- MODULE StreamBound ----
EXTENDS Integers, FiniteSets

VARIABLE x

Init == x = 0

Next == x' \in [1..3 -> 1..5]

Inv == x = x /\ (\E i \in 1..2000000 : i = 5) /\ (\E s \in SUBSET (1..5) : s = {})
====
"#;

/// TLC's `TraceWithLargeSetOfInitialStatesTest` spec, with TLC's own config.
const LARGE_INIT: &str = r#"---- MODULE LargeInit ----
EXTENDS Integers

VARIABLES x,y

Spec == (x \in 1..11 /\ y = FALSE) /\ [][x' = x /\ y' = TRUE]_<<x,y>>

Inv == y = FALSE
====
"#;

const LARGE_INIT_CFG: &str = "SPECIFICATION Spec\nINVARIANT Inv\n";

const CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";

/// The tiers: the default one, the interpreter and the compiled tier.
const TIERS: [(&[&str], &str); 3] = [(&[], "default"), (&["-interp"], "-interp"), (&["-compile"], "-compile")];

/// `TLX_PARANOID=1` with forced layout misses on the IR executor and on
/// native code: the compiled tier must give the interpreter's answer.
const PARANOID_MODES: [&[(&str, &str)]; 2] = [
    &[("TLX_PARANOID", "1"), ("TLX_PRERUN", "1"), ("TLX_NO_NATIVE", "1")],
    &[("TLX_PARANOID", "1"), ("TLX_PRERUN", "1"), ("TLX_NATIVE_SYNC", "1")],
];

fn run(dir: &Path, args: &[&str], env: &[(&str, &str)]) -> (i32, String) {
    let mut cmd = tlx_testkit::tlx_default!();
    cmd.args(["check"]).args(args).dir(dir).timeout(Duration::from_secs(120));
    let out = cmd.envs(env.iter().copied()).run();
    (out.code, out.text())
}

#[test]
fn the_default_bound_admits_the_spec() {
    let dir = tlx_testkit::TempDir::with_spec("mat_bound_default", MATERIALIZED, CFG);
    for (args, what) in TIERS {
        let (code, out) = run(&dir, &[args, &["MatBound.tla"]].concat(), &[]);
        assert_eq!(code, 0, "{what}:\n{out}");
        assert_eq!(
            counts(&out),
            ["2 states generated, 1 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 1."],
            "{what}:\n{out}"
        );
    }
}

#[test]
fn a_materialized_domain_over_the_bound_is_an_error_in_every_tier() {
    let dir = tlx_testkit::TempDir::with_spec("mat_bound_small", MATERIALIZED, CFG);
    for (args, what) in TIERS {
        let (code, out) = run(&dir, &[args, &["MatBound.tla", "-maxSetSize", "10"]].concat(), &[]);
        assert_eq!(code, 75, "{what}:\n{out}");
        assert!(out.contains("Attempted to construct a set with too many elements (>10)"), "{what}:\n{out}");
    }
    // Exactly the domain's size is the bound TLC allows.
    for (args, what) in TIERS {
        let (code, out) = run(&dir, &[args, &["MatBound.tla", "-maxSetSize", "125"]].concat(), &[]);
        assert_eq!(code, 0, "{what}:\n{out}");
    }
    // The compiled tier agrees with the interpreter (`TLX_PARANOID`).
    for env in PARANOID_MODES {
        let (code, out) = run(&dir, &["-compile", "MatBound.tla", "-maxSetSize", "10"], env);
        assert_eq!(code, 75, "{env:?}:\n{out}");
        assert!(out.contains("too many elements (>10)"), "{env:?}:\n{out}");
    }
}

#[test]
fn streaming_paths_are_not_limited() {
    let dir = tlx_testkit::TempDir::with_spec("stream_bound", STREAMED, CFG);
    for (args, what) in TIERS {
        let (code, out) = run(&dir, &[args, &["StreamBound.tla", "-maxSetSize", "10"]].concat(), &[]);
        assert_eq!(code, 0, "{what}:\n{out}");
        assert!(!out.contains("too many elements"), "{what}:\n{out}");
        assert_eq!(
            counts(&out),
            [
                "15751 states generated, 126 distinct states found, 0 states left on queue.",
                "The depth of the complete state graph search is 2."
            ],
            "{what}:\n{out}"
        );
    }
    for env in PARANOID_MODES {
        let (code, out) = run(&dir, &["-compile", "StreamBound.tla", "-maxSetSize", "10"], env);
        assert_eq!(code, 0, "{env:?}:\n{out}");
        assert!(!out.contains("too many elements"), "{env:?}:\n{out}");
    }
}

#[test]
fn large_set_of_initial_states_still_reports_the_violation() {
    // TLC's `TraceWithLargeSetOfInitialStatesTest`: `-maxSetSize 10` with 11
    // initial states is a safety violation, not an error.
    let dir = tlx_testkit::TempDir::with_spec("large_init", LARGE_INIT, LARGE_INIT_CFG);
    for (args, what) in TIERS {
        let (code, out) = run(&dir, &[args, &["LargeInit.tla", "-maxSetSize", "10", "-deadlock"]].concat(), &[]);
        assert_eq!(code, 12, "{what}:\n{out}");
        assert!(out.contains("Error: Invariant Inv is violated."), "{what}:\n{out}");
        assert!(out.contains("/\\ x = 1\n/\\ y = FALSE"), "{what}:\n{out}");
        assert!(out.contains("/\\ x = 1\n/\\ y = TRUE"), "{what}:\n{out}");
        assert!(!out.contains("too many elements"), "{what}:\n{out}");
    }
    for env in PARANOID_MODES {
        let (code, out) = run(&dir, &["-compile", "LargeInit.tla", "-maxSetSize", "10", "-deadlock"], env);
        assert_eq!(code, 12, "{env:?}:\n{out}");
        assert!(!out.contains("too many elements"), "{env:?}:\n{out}");
    }
}

#[test]
fn invalid_values_are_bad_arguments() {
    for bad in ["0", "-1", "abc", "2147483648"] {
        let (code, out) = run(Path::new("."), &["X.tla", "-maxSetSize", bad], &[]);
        assert_eq!(code, 2, "-maxSetSize {bad}:\n{out}");
        assert!(out.contains("invalid value of -maxSetSize"), "-maxSetSize {bad}:\n{out}");
    }
    let (code, out) = run(Path::new("."), &["X.tla", "-maxSetSize"], &[]);
    assert_eq!(code, 2, "{out}");
    assert!(out.contains("-maxSetSize needs a value"), "{out}");
}

#[test]
fn the_option_is_in_the_help_text() {
    let mut cmd = tlx_testkit::tlx_default!();
    let out = cmd.args(["check", "-h"]).run();
    assert!(out.text().contains("-maxSetSize"), "{}", out.text());
}

/// TLC's `-maxSetSize` is an implementation detail of its `ValueVec`, and the
/// observable behavior has corners: a growing set starts with ten slots, an
/// eager `UNION` counts distinct elements, a set literal and an interval are
/// preallocated, and a streamed product or `SUBSET S` domain is not
/// materialized. These models pin one corner each, compared with TLC's result
/// (run next to the pinned TLC jar):
///
/// | model | bound | TLC |
/// |---|---|---|
/// | `Overflow`: `\E f \in [1..32 -> 1..(2+x)]` in an invariant | 10 | 75 |
/// | `Nested`: `Init == x \in ([1..2 -> 1..4] \X {1})` | 10 | 0, 16 distinct |
/// | `Grow`: the set grows by singleton union | 10 | 75 |
/// | `LiteralMember`: 11-tuple literal membership | 10 | 0 |
/// | `Small`: `{i : i \in 1..5}` | 4 | 0 |
/// | `Overlap`: `UNION {{1..6}, {3..8}}` | 10 | 0 |
/// | `Filter`: 11 filtered functions, then a division by zero | 10 | 75 |
/// | `FiniteSubset`: `\E s \in SUBSET (1..18) : s = {}` | 10 | 0 |
/// | `IntervalCup`: `(1..4000000) \cup {}` | 10 | 75 |
const PROBES: &[(&str, &str, &str, i64, i32, bool)] = &[
    (
        "overflow",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets, TLC, Randomization
VARIABLE x
Init == x = 0
Next == x' = x
Inv == x = x /\ (\E f \in [1..32 -> 1..(2+x)] : f[1]=1)
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "nested",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets, TLC, Randomization
VARIABLE x
Init == x \in ([1..2 -> 1..4] \X {1})
Next == x' = x
Inv == x = x /\ (TRUE)
====
"#,
        CFG,
        10,
        0,
        false,
    ),
    (
        "grow",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x = {}
Next == IF Cardinality(x) < 12 THEN x' = x \cup {Cardinality(x)+1} ELSE x' = x
Inv == TRUE
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "literal_member",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=1
Next == x'=x
Inv == <<x>> \in {<<x>>,<<2>>,<<3>>,<<4>>,<<5>>,<<6>>,<<7>>,<<8>>,<<9>>,<<10>>,<<11>>}
====
"#,
        CFG,
        10,
        0,
        false,
    ),
    (
        "small",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets, TLC, Randomization
VARIABLE x
Init == x = 0
Next == x' = x
Inv == x = x /\ (Cardinality({i : i \in 1..5}) = 5)
====
"#,
        CFG,
        4,
        0,
        false,
    ),
    (
        "overlap",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets, TLC, Randomization
VARIABLE x
Init == x = 0
Next == x' = x
Inv == x = x /\ (Cardinality(UNION {{1,2,3,4,5,6}, {3,4,5,6,7,8}}) = 8)
====
"#,
        CFG,
        10,
        0,
        false,
    ),
    (
        "filter",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets, TLC, Randomization
VARIABLE x
Init == x = 0
Next == x' = x
Inv == x = x /\ (\E f \in {g \in [1..2 -> 1..5] : IF g[1] = 5 THEN 1 \div 0 = 0 ELSE TRUE} : TRUE)
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "finite_subset",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=0
Next == x'=x
Inv == \E s \in SUBSET (1..(18+x)) : s = {}
====
"#,
        CFG,
        10,
        0,
        false,
    ),
    (
        "interval_cup",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=0
Next == x'=x
Inv == Cardinality((1..(4000000+x)) \cup {}) > 0
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "existing_element",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x = {1,2,3,4,5,6,7,8,9,10,11,12}
Next == x' = x \cup {1}
Inv == TRUE
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "remove_one",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x = {1,2,3,4,5,6,7,8,9,10,11,12}
Next == x' = x \ {12}
Inv == TRUE
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "intersect",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x = {1,2,3,4,5,6,7,8,9,10,11,12}
Next == x' = x \cap (1..11)
Inv == TRUE
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "project_map",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x = {1,2,3,4,5,6,7,8,9,10,11,12}
Next == x'=x
Inv == Cardinality({(i % 2) : i \in x})=2
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "cup_present",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLES n,s
Init == n=0 /\ s={1,2,3,4,5,6,7,8,9,10,11,12}
Next == /\ n' = IF n < 3 THEN n+1 ELSE n
        /\ s' = IF n < 2 THEN s ELSE s \cup {1}
====
"#,
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n",
        10,
        75,
        true,
    ),
    (
        "minus_absent",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLES n,s
Init == n=0 /\ s={1,2,3,4,5,6,7,8,9,10,11,12}
Next == /\ n' = IF n < 3 THEN n+1 ELSE n
        /\ s' = IF n < 2 THEN s ELSE s \ {99}
====
"#,
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n",
        10,
        75,
        true,
    ),
    (
        "set_former_state",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLES n,s
Init == n=11 /\ s={0,1}
Next == n'=n /\ s'={i % 2 : i \in 1..n}
====
"#,
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n",
        10,
        75,
        true,
    ),
    (
        "constant_union_twelve",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE n
Init == n=1
Next == n'=n
Inv == Cardinality(({n,100000,200000,300000,400000,500000} \cup {600000,700000,800000,900000,1000000,1100000})) = 12
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "cartesian_large",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=0
Next == x'=x
Inv == \E p \in (1..(4000000+x)) \X {1} : TRUE
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "fcn_range_large",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=0
Next == x'=x
Inv == \E p \in [1..1 -> 1..(4000000+x)] : TRUE
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "record_set_large",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=0
Next == x'=x
Inv == \E p \in [a: 1..(4000000+x)] : TRUE
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "product_growth",
        r#"---- MODULE Probe ----
EXTENDS Naturals
VARIABLE n
Init == n=1000000
Next == n'=n
Inv == \E t \in ((1..n) \X {0}) : TRUE
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "witness_except",
        r#"---- MODULE Probe ----
EXTENDS Integers
CONSTANT Missing
VARIABLE n
Init == n = 3
Next == n' = n
F == [i \in ((1..n) \cup {}) |-> i]
Inv == [F EXCEPT ![Missing] = 0] = F
====
"#,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\nCONSTANT Missing = Missing\n",
        10,
        0,
        false,
    ),
    (
        "existential_init",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == \E f \in [1..2 -> 1..4] : x = f[1]
Next == x'=x
Inv == x=x
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "big_union_distinct",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x={{1,2,3,4,5,6},{7,8,9,10,11,12}}
Next == x'=x
Inv == Cardinality(UNION x) = 12
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "flatten_former",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x={1,2,3,4,5,6,7,8,9,10,11,12}
Next == x'=x
Inv == Cardinality(UNION {{i % 2} : i \in x}) = 2
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "fused_filter_member",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x={1,2,3,4,5,6,7,8,9,10,11,12}
Next == x'=x
Inv == 1 \in {i \in x: i>0}
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "mapped_member",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x={1,2,3,4,5,6,7,8,9,10,11,12}
Next == x'=x
Inv == 1 \in {i % 2 : i \in x}
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "sorted_union_present",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE s
Init == s={100000,200000,300000,400000,500000,600000,700000,800000,900000,1000000,1100000,1200000}
Next == s'=s
Inv == Cardinality(s \cup {100000}) = 12
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "sorted_self_union",
        r#"---- MODULE Probe ----
EXTENDS Naturals, FiniteSets
VARIABLE s
Init == s={100000,200000,300000,400000,500000,600000,700000,800000,900000,1000000,1100000,1200000}
Next == s'=s
Inv == Cardinality(s \cup s)=12
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "wide_literal",
        r#"---- MODULE Probe ----
EXTENDS Naturals, FiniteSets
VARIABLES s,n
Init == n=12 /\ s={1,2,3,4,5,6,7,8,9,10,11,12}
Next == n'=n /\ s'={1,2,3,4,5,6,7,8,9,10,11,n}
Inv == TRUE
====
"#,
        CFG,
        10,
        0,
        false,
    ),
    (
        "nested_record_filter",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=0
Next == x'=x
Inv == \E p \in ([a : 1..(4000000+x), b : {f \in [1..2 -> 1..4] : TRUE}]) : TRUE
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "nested_filter_passes",
        r#"---- MODULE Probe ----
EXTENDS Naturals, TLC
VARIABLE n
Init == n=2
Next == n'=n
Inv == \E t \in ({r \in [a: 1..n] : Print("visited", TRUE)} \X {0}) : TRUE
====
"#,
        CFG,
        10,
        0,
        false,
    ),
    (
        "empty_subset",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=0
Next == (x=0 /\ (\E p \in ([a: SUBSET (1..x), b: {0}]): x'  = 1)) \/ x'=x
Inv == x=0
====
"#,
        CFG,
        1000000,
        12,
        false,
    ),
    (
        "empty_function",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=0
Next == (x=0 /\ (\E p \in (([1..x -> {1}]) \X {1}): x'  = 1)) \/ x'=x
Inv == x=0
====
"#,
        CFG,
        1000000,
        12,
        false,
    ),
    (
        "empty_power",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=0
Next == x'=1 /\ (\E p \in ((SUBSET {}) \X {x}): TRUE)
Inv == x=0
====
"#,
        CFG,
        1000000,
        12,
        false,
    ),
    (
        "empty_domain",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=0
Next == x'=1 /\ (\E p \in [a:[{} -> {x}]]: TRUE)
Inv == x=0
====
"#,
        CFG,
        1000000,
        12,
        false,
    ),
    (
        "cup_member",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x={1,2,3,4,5,6,7,8,9,10,11,12}
Next == x'=x
Inv == 1 \in (x \cup {1})
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "cup_nonoverlap",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x={1,2,3,4,5,6}
Next == x'=x
Inv == 1 \in (x \cup {7,8,9,10,11,12})
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "filtered_component",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=0
Next == x'=x
Inv == \E p \in ([a: {f \in [1..2 -> 1..(10+x)] : f[1] < 5 \/ 1 \div (f[1]-5) = 1}, b: {0}]): TRUE
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "small_filter",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=0
Next == x'=x
Inv == \E p \in ([a: {f \in [1..2 -> 1..(5+x)] : TRUE}, b: {0}]): TRUE
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "large_filter",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=0
Next == x'=x
Inv == \E p \in ([a: {f \in [1..2 -> 1..(450+x)] : TRUE}, b: {0}]): TRUE
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "choose_overflow_product",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=0
Next == x'=x
Inv == (CHOOSE p \in ((1..(50000+x)) \X (1..50000)): TRUE) = <<1,1>>
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "choose_overflow_fcn",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=0
Next == x'=x
Inv == (CHOOSE f \in [1..32 -> 1..(2+x)]: TRUE)[1] = 1
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "nested_stop",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=0
Next == x'=x
Inv == \E p \in ({r \in [a: 1..(20+x)] : IF r.a=15 THEN (1 \div 0)=0 ELSE TRUE} \X {0}) : TRUE
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "empty_pending",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=0
Next == x'=x
Inv == \A p \in (Nat \X {r \in [id:1..2]: r.id < x}): FALSE
====
"#,
        CFG,
        10,
        0,
        false,
    ),
    (
        "empty_both",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=0
Next == x'=x
Inv == \A p \in ({r \in [i:1..4]: r.i=1 \/ 1 \div (2-r.i)=x} \X {r \in [id:1..2]: r.id < x}): FALSE
====
"#,
        CFG,
        10,
        0,
        false,
    ),
    (
        "empty_field",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=0
Next == x'=x
Inv == \A f \in [a: Nat, b: {r \in [id:1..2]: r.id < x}]: FALSE
====
"#,
        CFG,
        10,
        0,
        false,
    ),
    (
        "empty_range",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=0
Next == x'=x
Inv == \A f \in [Nat -> {r \in [id:1..2]: r.id < x}]: FALSE
====
"#,
        CFG,
        10,
        0,
        false,
    ),
    (
        "empty_right",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x=0
Next == x'=x
Inv == \A p \in ({r \in [a:1..(x+4)] : IF r.a=3 THEN (1 \div 0)=0 ELSE TRUE} \X {r \in [a:1..(x+4)] : r.a=0}) : FALSE
====
"#,
        CFG,
        10,
        0,
        false,
    ),
    (
        "lazy_empty_nat",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x=0
Next == x'=x
Inv == \A p \in ({r \in [a:1..(x+4)] : r.a=0} \X Nat) : FALSE
====
"#,
        CFG,
        10,
        0,
        false,
    ),
    (
        "empty_visits",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets, TLC
VARIABLE x
Init == x=0
Next == x'=x
Inv == \A p \in ((1..(x+40)) \X {r \in [a:1..(x+4)] : Print("empty-probe",FALSE)}) : FALSE
====
"#,
        CFG,
        10,
        0,
        false,
    ),
    (
        "non_empty_10",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=4
Next == x'=x
Inv == [1..2 -> 1..x] # {}
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "non_empty_16",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=4
Next == x'=x
Inv == [1..2 -> 1..x] # {}
====
"#,
        CFG,
        16,
        0,
        false,
    ),
    (
        "candidate_pairs_10",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=4
Next == x'=x
Inv == ((1..x) \X (1..x)) # {<<1,1>>}
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "candidate_pairs_16",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=4
Next == x'=x
Inv == ((1..x) \X (1..x)) # {<<1,1>>}
====
"#,
        CFG,
        16,
        0,
        false,
    ),
    (
        "sorted_family_10",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=4
Next == x'=x
Inv == Cardinality({[1..2 -> 1..x], {}})=2
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "sorted_family_16",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=4
Next == x'=x
Inv == Cardinality({[1..2 -> 1..x], {}})=2
====
"#,
        CFG,
        16,
        0,
        false,
    ),
    (
        "structural_control_10",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=4
Next == x'=x
Inv == [1..2 -> 1..x] = [1..2 -> 1..x]
====
"#,
        CFG,
        10,
        0,
        false,
    ),
    (
        "structural_control_16",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=4
Next == x'=x
Inv == [1..2 -> 1..x] = [1..2 -> 1..x]
====
"#,
        CFG,
        16,
        0,
        false,
    ),
    (
        "sorted_functions_10",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=4
Next == x'=x
Inv == Cardinality({[1..2 -> 1..x], [1..2 -> 1..(x-1)]}) = 2
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "sorted_functions_16",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=4
Next == x'=x
Inv == Cardinality({[1..2 -> 1..x], [1..2 -> 1..(x-1)]}) = 2
====
"#,
        CFG,
        16,
        0,
        false,
    ),
    (
        "sorted_products_10",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=4
Next == x'=x
Inv == Cardinality({((1..x) \X (1..x)), ((1..x) \X {1})}) = 2
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "sorted_products_16",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=4
Next == x'=x
Inv == Cardinality({((1..x) \X (1..x)), ((1..x) \X {1})}) = 2
====
"#,
        CFG,
        16,
        0,
        false,
    ),
    (
        "subset_non_empty_10",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=4
Next == x'=x
Inv == (SUBSET (1..x)) # {}
====
"#,
        CFG,
        10,
        0,
        false,
    ),
    (
        "subset_non_empty_16",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x=4
Next == x'=x
Inv == (SUBSET (1..x)) # {}
====
"#,
        CFG,
        16,
        0,
        false,
    ),
    (
        "bounded_sequences_10",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x \in UNION {[1..n -> {0,1}] : n \in 1..4}
Next == x'=x
Inv == TRUE
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "bounded_sequences_16",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x \in UNION {[1..n -> {0,1}] : n \in 1..4}
Next == x'=x
Inv == TRUE
====
"#,
        CFG,
        16,
        0,
        false,
    ),
    (
        "edge_functions_10",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x = 4
Next == x' = x
Inv == [((1..x) \X (1..x)) -> {0}] # {}
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "edge_functions_16",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x = 4
Next == x' = x
Inv == [((1..x) \X (1..x)) -> {0}] # {}
====
"#,
        CFG,
        16,
        0,
        false,
    ),
    (
        "edge_subsets_10",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x = 4
Next == x' = x
Inv == (SUBSET ((1..x) \X (1..x))) # {}
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "edge_subsets_16",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x = 4
Next == x' = x
Inv == (SUBSET ((1..x) \X (1..x))) # {}
====
"#,
        CFG,
        16,
        0,
        false,
    ),
    (
        "link_maps_10",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Links == (1..3) \X (1..x)
Init == x = 4
Next == x' = x
Inv == Cardinality({[Links -> {FALSE}], {}}) = 2
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "link_maps_16",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Links == (1..3) \X (1..x)
Init == x = 4
Next == x' = x
Inv == Cardinality({[Links -> {FALSE}], {}}) = 2
====
"#,
        CFG,
        16,
        0,
        false,
    ),
    (
        "relation_domain_10",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x = 4
Next == x' = x
Inv == (SUBSET ((1..3) \X (1..x))) # {}
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "relation_domain_16",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x = 4
Next == x' = x
Inv == (SUBSET ((1..3) \X (1..x))) # {}
====
"#,
        CFG,
        16,
        0,
        false,
    ),
    (
        "mixed_ids_10",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x = 11
Next == x' = x
Inv == Cardinality((1..x) \cup {"unknown"}) > 0
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "union_overlap_10",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x = 11
Next == x' = x
Inv == Cardinality((1..x) \cup ((x \div 2)..(x+1))) = x+1
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "union_overlap_16",
        r#"---- MODULE Probe ----
EXTENDS Integers, FiniteSets
VARIABLE x
Init == x = 11
Next == x' = x
Inv == Cardinality((1..x) \cup ((x \div 2)..(x+1))) = x+1
====
"#,
        CFG,
        16,
        0,
        false,
    ),
    (
        "configured_workers_10",
        r#"---- MODULE Probe ----
EXTENDS Naturals
CONSTANT Workers
VARIABLE x
Init == x = 1
Next == x' = x
Inv == x \in Workers
====
"#,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nCONSTANT Workers = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}\n",
        10,
        150,
        true,
    ),
    (
        "configured_workers_11",
        r#"---- MODULE Probe ----
EXTENDS Naturals
CONSTANT Workers
VARIABLE x
Init == x = 1
Next == x' = x
Inv == x \in Workers
====
"#,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nCONSTANT Workers = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11}\n",
        11,
        0,
        false,
    ),
    (
        "repeated_worker_10",
        r#"---- MODULE Probe ----
EXTENDS Naturals
CONSTANT Workers
VARIABLE x
Init == x = 1
Next == x' = x
Inv == x \in Workers
====
"#,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nCONSTANT Workers = {1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}\n",
        10,
        150,
        true,
    ),
    (
        "repeated_worker_11",
        r#"---- MODULE Probe ----
EXTENDS Naturals
CONSTANT Workers
VARIABLE x
Init == x = 1
Next == x' = x
Inv == x \in Workers
====
"#,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nCONSTANT Workers = {1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10}\n",
        11,
        0,
        false,
    ),
    (
        "configured_ten_at_4",
        r#"---- MODULE Probe ----
EXTENDS Naturals
CONSTANT Workers
VARIABLE x
Init == x = 1
Next == x' = x
Inv == x \in Workers
====
"#,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nCONSTANT Workers = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}\n",
        4,
        0,
        false,
    ),
    (
        "mixed_keep_10",
        r#"---- MODULE Probe ----
EXTENDS Naturals, FiniteSets
VARIABLE x
Init == x = 1
Next == x' = x
Mixed == {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, "sentinel"}
Inv == Cardinality(Mixed \cap (1..11)) > 0
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "mixed_keep_11",
        r#"---- MODULE Probe ----
EXTENDS Naturals, FiniteSets
VARIABLE x
Init == x = 1
Next == x' = x
Mixed == {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, "sentinel"}
Inv == Cardinality(Mixed \cap (1..11)) > 0
====
"#,
        CFG,
        11,
        75,
        false,
    ),
    (
        "kept_candidates_10",
        r#"---- MODULE Probe ----
EXTENDS Naturals, FiniteSets
VARIABLE id
Init == id = 1
Next == id' = id
Inv == Cardinality({id, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10} \cap (1..10)) = 10
====
"#,
        CFG,
        10,
        0,
        false,
    ),
    (
        "minus_empty_10",
        r#"---- MODULE Probe ----
EXTENDS Naturals, FiniteSets
VARIABLE id
Init == id = 1
Next == id' = id
Inv == Cardinality({id, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10} \ {}) = 10
====
"#,
        CFG,
        10,
        0,
        false,
    ),
    (
        "candidate_coverage_default",
        r#"---- MODULE Probe ----
EXTENDS Integers
VARIABLE epoch
Init == epoch = 0
Next == epoch' = IF epoch < 1 THEN epoch + 1 ELSE epoch
Inv == epoch = 0 \/ ((SUBSET (1..31)) \X {epoch} \subseteq {<<{}, 0>>})
====
"#,
        CFG,
        1000000,
        12,
        false,
    ),
    (
        "candidate_coverage_10",
        r#"---- MODULE Probe ----
EXTENDS Integers
VARIABLE epoch
Init == epoch = 0
Next == epoch' = IF epoch < 1 THEN epoch + 1 ELSE epoch
Inv == epoch = 0 \/ ((SUBSET (1..31)) \X {epoch} \subseteq {<<{}, 0>>})
====
"#,
        CFG,
        10,
        12,
        false,
    ),
    (
        "record_coverage_default",
        r#"---- MODULE Probe ----
EXTENDS Integers
VARIABLE epoch
Init == epoch = 0
Next == epoch' = IF epoch < 1 THEN epoch + 1 ELSE epoch
Inv == epoch = 0 \/ ([a : SUBSET (1..31), b : {epoch}] \subseteq {[a |-> {}, b |-> 0]})
====
"#,
        CFG,
        1000000,
        12,
        false,
    ),
    (
        "record_coverage_10",
        r#"---- MODULE Probe ----
EXTENDS Integers
VARIABLE epoch
Init == epoch = 0
Next == epoch' = IF epoch < 1 THEN epoch + 1 ELSE epoch
Inv == epoch = 0 \/ ([a : SUBSET (1..31), b : {epoch}] \subseteq {[a |-> {}, b |-> 0]})
====
"#,
        CFG,
        10,
        12,
        false,
    ),
    (
        "product_overflow_existential_10",
        r#"---- MODULE Probe ----
EXTENDS Integers
VARIABLE epoch
Init == epoch = 0
Next == epoch' = epoch
Inv == \E p \in (SUBSET (1..31)) \X {epoch} : p[2] = epoch
====
"#,
        CFG,
        10,
        75,
        true,
    ),
    (
        "quorum_families_20",
        r#"---- MODULE Probe ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x
Eligible == {i \in 1..20 : i > x}
Quorums == SUBSET Eligible
Inv == (SUBSET Quorums) # {}
====
"#,
        CFG,
        1000000,
        75,
        false,
    ),
    (
        "policy_8_at_10",
        r#"---- MODULE Probe ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == x' = x
Choices == {i \in 1..2 : i > x}
Policies == [1..5 -> Choices]
Inv == (SUBSET Policies) # {}
====
"#,
        CFG,
        10,
        75,
        false,
    ),
];

/// Assertions beyond each model's verdict: a required substring (the
/// reachable states of a violation, or the first error) and substrings that
/// must not appear (a later predicate or a cardinality overflow reported
/// instead of the bound).
const PROBE_DETAILS: &[(&str, &[&str], &[&str])] = &[
    ("edge_functions_10", &["too many elements"], &[]),
    ("edge_subsets_10", &["too many elements"], &[]),
    ("link_maps_10", &["too many elements"], &[]),
    ("relation_domain_10", &["too many elements"], &[]),
    ("mixed_ids_10", &["too many elements"], &["compare string"]),
    ("union_overlap_10", &["too many elements"], &[]),
    ("edge_functions_16", &["2 states generated, 1 distinct states found"], &["too many elements"]),
    ("edge_subsets_16", &["2 states generated, 1 distinct states found"], &["too many elements"]),
    ("link_maps_16", &["2 states generated, 1 distinct states found"], &["too many elements"]),
    ("relation_domain_16", &["2 states generated, 1 distinct states found"], &["too many elements"]),
    ("union_overlap_16", &["2 states generated, 1 distinct states found"], &["too many elements"]),
    ("sorted_functions_10", &["too many elements"], &[]),
    ("sorted_products_10", &["too many elements"], &[]),
    ("bounded_sequences_10", &["too many elements"], &[]),
    ("sorted_functions_16", &["2 states generated, 1 distinct states found"], &["too many elements"]),
    ("sorted_products_16", &["2 states generated, 1 distinct states found"], &["too many elements"]),
    ("subset_non_empty_10", &["2 states generated, 1 distinct states found"], &["too many elements"]),
    ("subset_non_empty_16", &["2 states generated, 1 distinct states found"], &["too many elements"]),
    ("bounded_sequences_16", &["60 states generated, 30 distinct states found"], &["too many elements"]),
    ("non_empty_10", &["too many elements"], &[]),
    ("candidate_pairs_10", &["too many elements"], &[]),
    ("sorted_family_10", &["too many elements"], &[]),
    ("non_empty_16", &["2 states generated, 1 distinct states found"], &["too many elements"]),
    ("candidate_pairs_16", &["2 states generated, 1 distinct states found"], &["too many elements"]),
    ("sorted_family_16", &["2 states generated, 1 distinct states found"], &["too many elements"]),
    ("structural_control_10", &["2 states generated, 1 distinct states found"], &["too many elements"]),
    ("structural_control_16", &["2 states generated, 1 distinct states found"], &["too many elements"]),
    ("empty_subset", &["2 distinct states found", "Invariant Inv is violated"], &["too many elements"]),
    ("empty_function", &["2 distinct states found", "Invariant Inv is violated"], &["too many elements"]),
    ("empty_power", &["2 distinct states found", "Invariant Inv is violated"], &["too many elements"]),
    ("empty_domain", &["2 distinct states found", "Invariant Inv is violated"], &["too many elements"]),
    ("cup_member", &["too many elements"], &["second argument"]),
    ("cup_nonoverlap", &["too many elements"], &["second argument"]),
    ("filtered_component", &["too many elements"], &["second argument"]),
    ("nested_stop", &["too many elements"], &["second argument"]),
    ("empty_pending", &["2 states generated, 1 distinct states found"], &["cannot be enumerated", "too many elements"]),
    ("empty_both", &["2 states generated, 1 distinct states found"], &["second argument", "cannot be enumerated", "too many elements"]),
    ("empty_field", &["2 states generated, 1 distinct states found"], &["cannot be enumerated", "too many elements"]),
    ("empty_range", &["2 states generated, 1 distinct states found"], &["cannot be enumerated", "too many elements"]),
    ("empty_right", &["2 states generated, 1 distinct states found"], &["second argument", "cannot be enumerated", "too many elements"]),
    ("lazy_empty_nat", &["2 states generated, 1 distinct states found"], &["cannot be enumerated", "too many elements"]),
    ("empty_visits", &["2 states generated, 1 distinct states found"], &["second argument", "cannot be enumerated", "too many elements"]),
    ("choose_overflow_product", &["too many elements"], &["Overflow when computing"]),
    ("choose_overflow_fcn", &["too many elements"], &["Overflow when computing"]),
    ("configured_workers_10", &["too many elements"], &[]),
    ("configured_workers_11", &["2 states generated, 1 distinct states found"], &["too many elements"]),
    ("repeated_worker_10", &["too many elements"], &[]),
    ("repeated_worker_11", &["2 states generated, 1 distinct states found"], &["too many elements"]),
    ("configured_ten_at_4", &["2 states generated, 1 distinct states found"], &["too many elements"]),
    ("mixed_keep_10", &["too many elements"], &["compare string"]),
    ("mixed_keep_11", &[], &["too many elements"]),
    ("kept_candidates_10", &["2 states generated, 1 distinct states found"], &["too many elements"]),
    ("minus_empty_10", &["2 states generated, 1 distinct states found"], &["too many elements"]),
    ("candidate_coverage_default", &["Invariant Inv is violated", "2 distinct states found"], &["Overflow", "too many elements"]),
    ("candidate_coverage_10", &["Invariant Inv is violated", "2 distinct states found"], &["Overflow", "too many elements"]),
    ("record_coverage_default", &["Invariant Inv is violated", "2 distinct states found"], &["Overflow", "too many elements"]),
    ("record_coverage_10", &["Invariant Inv is violated", "2 distinct states found"], &["Overflow", "too many elements"]),
    ("product_overflow_existential_10", &["too many elements"], &["Overflow"]),
    ("quorum_families_20", &["Overflow when computing"], &["too many elements"]),
    ("policy_8_at_10", &["Overflow when computing"], &["too many elements"]),
];

fn probe_details(name: &str) -> Option<(&'static [&'static str], &'static [&'static str])> {
    PROBE_DETAILS.iter().find(|(n, _, _)| *n == name).map(|(_, required, forbidden)| (*required, *forbidden))
}

#[test]
fn the_tlc_corners_of_the_bound_match_in_every_tier() {
    for (name, src, cfg, mss, want_code, bound_error) in PROBES {
        let dir = tlx_testkit::TempDir::with_spec(name, src, cfg);
        let mss = mss.to_string();
        for (args, what) in TIERS {
            let mut argv: Vec<&str> = args.to_vec();
            argv.extend(["Probe.tla", "-maxSetSize", &mss]);
            let (code, out) = run(&dir, &argv, &[]);
            assert_eq!(code, *want_code, "{name} {what}:\n{out}");
            assert_eq!(out.contains("too many elements"), *bound_error, "{name} {what} (bound error expected: {bound_error}):\n{out}");
            if let Some((required, forbidden)) = probe_details(name) {
                for text in required {
                    assert!(out.contains(text), "{name} {what}: missing {text:?}:\n{out}");
                }
                for text in forbidden {
                    assert!(!out.contains(text), "{name} {what}: unexpected {text:?} (the bound must be the first failure):\n{out}");
                }
            }
            if *name == "nested" && code == 0 {
                assert_eq!(
                    counts(&out),
                    [
                        "32 states generated, 16 distinct states found, 0 states left on queue.",
                        "The depth of the complete state graph search is 1."
                    ],
                    "{name} {what}:\n{out}"
                );
            }
        }
        for env in PARANOID_MODES {
            let (code, out) = run(&dir, &["-compile", "Probe.tla", "-maxSetSize", &mss], env);
            assert_eq!(code, *want_code, "{name} {env:?}:\n{out}");
            assert_eq!(out.contains("too many elements"), *bound_error, "{name} {env:?}:\n{out}");
        }
    }
}
