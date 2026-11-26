//! Mixed mode, code generation side (docs/mixed-mode.md §10):
//! the C generator turns what it cannot compile into host region calls.
//!
//! - `region_calls_in_generated_code`: actions and predicates with boxed
//!   parts become native with regions (statement loops over boxed sets
//!   through `host->elems`, regions in `ENABLED`), the library reports its
//!   region table and is only loaded against it;
//! - `volatile_functions_are_not_mixed`: an action evaluating a
//!   nondeterministic builtin keeps falling back as a whole (R4);
//! - `*_matches_the_interpreter`: whole searches of `EncModel`s in mixed
//!   mode, also with `TLX_MIXED_FORCE`-style forced regions, under
//!   `TLX_PARANOID` (every compiled result is checked against the
//!   interpreter), with the interpreter's counts.

use std::sync::Arc;

use tlx_compile::cgen::{CGen, Library};
use tlx_compile::enc::mixed::{FastRegions, HostRegions};
use tlx_compile::enc::EncModel;
use tlx_compile::lower::Lowerer;
use tlx_compile::native_plan::Mixed;
use tlx_compile::settings::Settings;
use tlx_compile::types::Typing;
use tlx_native::build::{build, BuildOptions};
use tlx_native::mixed::MixedCx;
use tlx_native::native::{Mixed as MixedCall, NativeLib};
use tlx_runtime::{explore, Model, Options, Outcome};
use tlx_testkit::diff::Harness;
use tlx_testkit::module;

const CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv Live\nPROPERTY Mono\n";

/// Boxed parts: `SUBSET` (a statement loop over a boxed set in `Pick`),
/// `Cardinality` of boxed sets, an interpreter fallback (`Inv`), `ENABLED`
/// of an action with boxed parts (`Live`).
const SETS: &str = r#"EXTENDS Naturals, FiniteSets
VARIABLES x, s, f
Init == x = 0 /\ s = {} /\ f = [i \in 1..2 |-> {}]
Grow == x < 3 /\ x' = x + 1 /\ s' = s \cup {x} /\ UNCHANGED f
Pick == \E t \in SUBSET s : Cardinality(t) = 2 /\ s' = t /\ UNCHANGED <<x, f>>
Fold == \E g \in [s -> s] : s' = {g[i] : i \in s} /\ UNCHANGED <<x, f>>
Put == \E i \in 1..2 : f' = [f EXCEPT ![i] = SUBSET s] /\ UNCHANGED <<x, s>>
Inv == Cardinality({t \in SUBSET s : x \in t}) < 10
Live == x < 3 \/ ENABLED Fold \/ Cardinality(s) < 2
Mono == [][Cardinality(s') <= Cardinality(s) + 1]_<<x, s, f>>
Next == Grow \/ Pick \/ Put \/ Fold"#;

/// Boxed values bound by LETs and used in loop bodies (handles released
/// per iteration), records, sequences, CHOOSE, IF on boxed values.
const LOOPS: &str = r#"EXTENDS Naturals, FiniteSets, Sequences
VARIABLES n, r, q
Init == n = 0 /\ r = [a |-> {}, b |-> 0] /\ q = <<>>
Step == n < 3 /\ Len(q) < 3 /\ n' = n + 1 /\ r' = [r EXCEPT !.a = @ \cup {n}] /\ q' = Append(q, n)
Shuffle == \E g \in [r.a -> r.a] :
             LET u == {g[i] : i \in r.a} \cup {n}
                 v == IF Cardinality(u) > 2 THEN u \ {n} ELSE u
             IN /\ Cardinality(v) > 1
                /\ r' = [r EXCEPT !.b = Cardinality(v)]
                /\ UNCHANGED <<n, q>>
Pop == q # <<>> /\ q' = Tail(q) /\ UNCHANGED r
       /\ n' = IF r.a = {} THEN 0 ELSE CHOOSE z \in r.a : \A w \in r.a : z <= w
Next == Step \/ Shuffle \/ Pop
Inv == \A t \in SUBSET r.a : Cardinality(t) <= 4 /\ LET c == {Len(q) - 10} \cup t IN c # {}
Live == ENABLED Shuffle \/ Cardinality(r.a) < 3 \/ r.b > 0
Mono == [][Len(q') <= Len(q) + 1 /\ \A z \in r'.a : z \in r.a \/ z = n]_<<n, r, q>>"#;

/// Generate the library of `src` against the layout the harness
/// speculates, in mixed mode if `mixed` (with `force`; also mixing
/// functions with element-dependent regions in statement loops).
fn generate(src: &str, cfg: &str, mixed: bool, force: u32) -> (Harness, Typing, Library) {
    generate_with(src, cfg, mixed, force, true)
}

fn generate_with(src: &str, cfg: &str, mixed: bool, force: u32, loops: bool) -> (Harness, Typing, Library) {
    let h = Harness::new(src, cfg);
    let ip = h.base.ip.clone();
    let mut lw = Lowerer::with_typing(&ip, Typing::new(h.layout.clone()));
    let init = lw.lower_init(h.base.init_expr()).ok();
    let actions: Vec<_> = h.base.actions().iter().map(|a| lw.lower_action(a).ok()).collect();
    let invariants: Vec<_> = h.base.invariant_exprs().iter().zip(h.base.invariant_names()).map(|(e, n)| lw.lower_pred(n, e)).collect();
    let aprops: Vec<_> =
        h.base.action_property_exprs().iter().zip(h.base.action_property_names()).map(|(e, n)| lw.lower_trans_pred(n, e)).collect();
    let typing = &lw.typing;
    let verified = tlx_compile::verify::Program::new(typing, init.as_ref(), &actions, &invariants, &aprops).expect("valid IR");
    let mut gen = CGen::new(&verified);
    if mixed {
        gen = gen.with_mixed(Mixed { oracle: &lw, force, loops });
    }
    let lib = gen.library(h.base.action_names(), h.base.invariant_names());
    (h, lw.into_typing(), lib)
}

fn all(v: &[bool]) -> bool {
    v.iter().all(|x| *x)
}

#[test]
fn region_calls_in_generated_code() {
    let src = module("MixedCGenSets", SETS);
    let (_, _, plain) = generate(&src, CFG, false, 0);
    assert!(
        !all(&plain.plan.native.actions) && !all(&plain.plan.native.invariants),
        "the spec should have functions C cannot compile alone"
    );
    assert!(plain.plan.regions.is_empty() && !plain.src.contains("h->eval"));

    let (h, typing, lib) = generate(&src, CFG, true, 0);
    let n = &lib.plan.native;
    assert!(n.init && all(&n.actions) && all(&n.invariants) && all(&n.action_properties), "all native with regions: {n:?}");
    assert!(n.mixed > 0 && !lib.plan.regions.is_empty());
    // A statement loop over a boxed set, regions in ENABLED (over its
    // local next state) and the region table in the source.
    assert!(lib.src.contains("h->elems(cx, "), "no loop over a boxed set");
    assert!(lib.plan.regions.regions().iter().any(|r| r.info.enabled), "no region inside ENABLED");
    assert!(lib.src.starts_with(&format!("/* host regions: {}, digest {} */", lib.plan.regions.len(), lib.plan.regions.digest())));
    assert!(
        lib.src.contains(&format!(", {}, {}ULL, 0, 0ULL}};", lib.plan.regions.len(), lib.plan.regions.hash())),
        "regions in tlx_spec_info"
    );

    let dir = std::env::temp_dir().join(format!("tlx-mixed-cgen-{}", std::process::id()));
    let path = build(&lib.src, &BuildOptions { cache_dir: dir.clone(), ..Default::default() }).expect("generated C builds");
    // SAFETY: CGen emitted this library from verified IR with lib.plan.regions;
    // the host uses that same table. The test compiler/cache are trusted.
    assert!(unsafe { NativeLib::load(&path) }.is_err(), "a library with regions needs its region table");
    let prog = tlx_compile::exec::fast::Program::new(&typing);
    let slots = FastRegions::slots(&lib.plan.regions);
    let regions = HostRegions {
        ip: &h.base.ip,
        typing: &typing,
        table: &lib.plan.regions,
        memo: 0,
        fast: Some(FastRegions { prog: &prog, progs: &slots }),
    };
    // SAFETY: CGen emitted this library from verified IR with lib.plan.regions;
    // the host uses that same table. The test compiler/cache are trusted.
    let native = unsafe { NativeLib::load_with(&path, Some(&regions), None) }.expect("load against the region table");
    assert_eq!((native.n_regions() as usize, native.regions_hash()), (lib.plan.regions.len(), lib.plan.regions.hash()));
    // The invariants on the reachable states, as the interpreter has them.
    let (states, _) = h.reachable(1000);
    let mut cx = MixedCx::new();
    for vals in &states {
        let w = h.encode(vals).expect("state fits the layout");
        let st = tlx_eval::model::State::new(vals.clone(), 1, 0);
        for i in 0..h.base.invariant_names().len() {
            let want = h.base.check_invariant(&st, i).expect("invariant evaluates").is_none();
            let got = native.invariant_mixed(MixedCall { cx: &mut cx, regions: &regions, level: 1 }, &w, i as u32);
            assert_eq!(got, want as i32, "invariant {i} on {vals:?}");
            assert_eq!(cx.live_values(), 0, "handles freed after the call");
        }
    }
    assert!(cx.evals > 0 && cx.errors == 0);
    let _ = std::fs::remove_dir_all(dir);

    // Loops whose bodies make handles release them per iteration.
    let (_, _, lib) = generate(&module("MixedCGenLoops", LOOPS), CFG, true, 0);
    assert!(
        lib.plan.native.mixed > 0 && lib.src.contains("= h->mark(cx);") && lib.src.contains("h->release(cx, mk"),
        "no handle release in loops"
    );
}

/// A statement loop calling a region that depends on the element (a loop
/// over a boxed set through `host->elems`, whose body passes the element
/// to regions) makes a function that is not mixed, unless `Mixed::loops`;
/// the other functions stay mixed.
#[test]
fn element_dependent_loop_regions_are_not_mixed() {
    let src = module("MixedCGenSets", SETS);
    let (h, _, loops) = generate_with(&src, CFG, true, 0, true);
    let (_, _, lib) = generate_with(&src, CFG, true, 0, false);
    assert!(loops.src.contains("h->elems(cx, ") && !lib.src.contains("h->elems(cx, "));
    let names = h.base.action_names();
    let dropped: Vec<usize> = (0..names.len()).filter(|&i| loops.plan.native.mixed_actions[i] && !lib.plan.native.actions[i]).collect();
    assert!(!dropped.is_empty(), "{:?} vs {:?}", loops.plan.native, lib.plan.native);
    for i in dropped {
        assert!(lib.plan.regions.regions().iter().all(|r| *r.info.func != *names[i]), "regions of {}", names[i]);
    }
    assert!(
        lib.plan.native.mixed > 0 && lib.plan.native.mixed < loops.plan.native.mixed,
        "{:?} vs {:?}",
        lib.plan.native,
        loops.plan.native
    );
    // The flags agree with the counts.
    for n in [&loops.plan.native, &lib.plan.native] {
        let flagged = [&n.mixed_actions, &n.mixed_invariants, &n.mixed_action_properties]
            .iter()
            .map(|v| v.iter().filter(|x| **x).count())
            .sum::<usize>();
        assert_eq!(flagged + n.mixed_init as usize, n.mixed);
    }
}

#[test]
fn volatile_functions_are_not_mixed() {
    let src = module(
        "MixedCGenVolatile",
        r#"EXTENDS Naturals, FiniteSets, TLC
VARIABLES x, s
Init == x = 0 /\ s = {}
Grow == x < 3 /\ x' = x + 1 /\ s' = s \cup {x}
Rand == s # {} /\ x' = RandomElement(s) + Cardinality(SUBSET s) /\ UNCHANGED s
Same == s # {} /\ x' = Cardinality(SUBSET s) /\ UNCHANGED s
Next == Grow \/ Rand \/ Same"#,
    );
    let (h, _, lib) = generate(&src, "INIT Init\nNEXT Next\n", true, 0);
    let names = h.base.action_names();
    let native = |name: &str| lib.plan.native.actions[names.iter().position(|n| n == name).expect("action")];
    assert!(native("Grow") && native("Same"), "{:?}", lib.plan.native);
    assert!(!native("Rand"), "an action with a nondeterministic builtin must not be mixed");
    assert!(lib.plan.regions.regions().iter().all(|r| &*r.info.func != "Rand"));
}

/// Search `body` with an `EncModel` under `TLX_PARANOID` with the given
/// mixed-mode settings, and compare the result with the interpreter's.
/// Returns the model's notes.
fn search(name: &str, body: &str, cfg: &str, env: &[(&str, &str)]) -> Vec<String> {
    let src = module(name, body);
    let h = Harness::new(&src, cfg);
    let opts = Options::default();
    let want = explore(&h.base, &opts);
    let mut vars = vec![("TLX_PARANOID", "1")];
    vars.extend_from_slice(env);
    let settings = Settings::from_lookup(|n| vars.iter().find(|(k, _)| *k == n).map(|(_, v)| v.to_string())).expect("settings");
    let base = Arc::new(tlx_testkit::spec::load(&src, cfg));
    let m = EncModel::new(base, h.layout.clone(), Vec::new(), &settings);
    let got = explore(&m, &opts);
    let key = |s: &tlx_runtime::Stats| (s.distinct, s.generated, s.depth);
    assert_eq!(key(&got.stats), key(&want.stats), "{name} {env:?}: counts");
    assert_eq!(format!("{:?}", got.outcome), format!("{:?}", want.outcome), "{name} {env:?}: outcome");
    assert!(matches!(want.outcome, Outcome::Ok), "{name}: {:?}", want.outcome);
    m.notes.clone()
}

/// The number of mixed functions in the notes of a model.
fn mixed_functions(notes: &[String]) -> usize {
    notes.iter().find_map(|n| n.split("mixed: ").nth(1)?.split(' ').next()?.parse().ok()).unwrap_or(0)
}

#[test]
fn mixed_search_matches_the_interpreter() {
    for (name, body) in [("MixedCGenSets", SETS), ("MixedCGenLoops", LOOPS)] {
        let notes = search(name, body, CFG, &[("TLX_MIXED", "1")]);
        assert!(mixed_functions(&notes) > 0, "{name}: no mixed function: {notes:?}");
    }
}

/// The same without adaptive tiering (mixed functions always native),
/// and with element-dependent loop regions (loops over boxed sets through
/// `host->elems`).
#[test]
fn mixed_search_without_adaptation_matches_the_interpreter() {
    for (name, body) in [("MixedCGenSets", SETS), ("MixedCGenLoops", LOOPS)] {
        let notes = search(name, body, CFG, &[("TLX_MIXED", "1"), ("TLX_MIXED_ADAPT", "0")]);
        assert!(mixed_functions(&notes) > 0, "{name}: no mixed function: {notes:?}");
    }
}

#[test]
fn forced_regions_match_the_interpreter() {
    for force in ["1", "2", "3", "5"] {
        for (name, body) in [("MixedCGenSets", SETS), ("MixedCGenLoops", LOOPS)] {
            let notes = search(name, body, CFG, &[("TLX_MIXED_FORCE", force)]);
            assert!(mixed_functions(&notes) > 0, "{name}: no mixed function: {notes:?}");
        }
    }
}

#[test]
fn typed_functions_make_no_regions() {
    // Fully typed: loops over constant sets and integer ranges.
    let src = module(
        "MixedCGenTyped",
        r#"EXTENDS Naturals
CONSTANTS P
VARIABLES x, y
Init == x = 0 /\ y \in P
Inc == \E i \in 1..2 : x < 4 /\ x' = x + i /\ UNCHANGED y
Move == \E p \in P : y' = p /\ x' = CHOOSE k \in {0, 1, 2} : k = x % 3
Next == Inc \/ Move
Inv == \A p \in P : \E k \in 0..5 : x <= k \/ y # p
Mono == [][\A i \in 1..2 : x' + i > x]_<<x, y>>"#,
    );
    let cfg = "INIT Init\nNEXT Next\nCONSTANTS P = {p1, p2}\nINVARIANT Inv\nPROPERTY Mono\n";
    let (_, _, plain) = generate(&src, cfg, false, 0);
    let n = &plain.plan.native;
    assert!(n.init && all(&n.actions) && all(&n.invariants) && all(&n.action_properties), "fully native: {n:?}");
    let (_, _, lib) = generate(&src, cfg, true, 0);
    assert!(
        lib.plan.regions.is_empty(),
        "regions in natively compilable code: {:?}",
        lib.plan.regions.regions().iter().map(|r| &r.expr).collect::<Vec<_>>()
    );
    assert_eq!(lib.src, plain.src, "the same code with mixed mode on");
}

#[test]
fn subseteq_loop_routes_to_streaming_region_not_elems() {
    let src = module(
        "MixedCGenSubsetEq",
        r#"EXTENDS Naturals
VARIABLE x
Init == x = {}
Next == IF x = {} THEN x' = {1} ELSE x' = x
Inv == ENABLED (x' \subseteq (1..18) /\ x' = {})"#,
    );
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
    let (_, _, lib) = generate(&src, cfg, true, 0);
    assert!(
        !lib.src.contains("h->elems(cx, "),
        "x' \\subseteq S must route to the streaming executor, not materialize via h->elems:\n{}",
        lib.src
    );
    assert!(
        lib.plan.native.invariants[0]
            && lib.plan.native.mixed_invariants[0]
            && lib.plan.regions.regions().iter().any(|r| matches!(&*r.expr.kind, tlx_compile::ir::ExprKind::Enabled(_))),
        "ENABLED(x' \\subseteq S) should run as a streaming host region: {:?}, regions={}",
        lib.plan.native,
        lib.plan.regions.len()
    );
}
