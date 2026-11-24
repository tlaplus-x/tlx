//! Mixed mode in the Cranelift JIT (docs/design.md §6.6): the JIT
//! library calls the host regions of the C library where the C code calls
//! them, so that the two libraries share one region table and are
//! interchangeable (`TLX_JIT=tier` swaps them during a search).
//!
//! - `jit_calls_the_regions_of_the_c_code`: on specs with boxed parts
//!   (loops over boxed sets through `host->elems`, regions in `ENABLED`,
//!   handles released per loop iteration), also with forced regions, the JIT
//!   has the C library's native functions and mixed flags, reports its
//!   region table, and every action, invariant and action property gives
//!   the same results as the C library on all reachable states and steps;
//! - `*_search_matches_the_interpreter`: whole searches of `EncModel`s on
//!   the JIT library alone under `TLX_PARANOID`, and on the default tiers
//!   with the C library replacing the JIT library during the search.

use std::sync::Arc;

use tlx_compile::cgen::CGen;
use tlx_compile::enc::mixed::{FastRegions, HostRegions};
use tlx_compile::enc::EncModel;
use tlx_compile::lower::Lowerer;
use tlx_compile::native_plan::{Mixed, NativeSet};
use tlx_compile::settings::Settings;
use tlx_compile::types::Typing;
use tlx_native::build::{build, BuildOptions};
use tlx_native::mixed::MixedCx;
use tlx_native::native::{Mixed as MixedCall, NativeLib};
use tlx_runtime::{explore, Model, Options, Outcome};
use tlx_testkit::diff::Harness;
use tlx_testkit::module;

const CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv Live\nPROPERTY Mono\n";

/// `SUBSET` loops over boxed sets, `Cardinality` of boxed sets, functions
/// of boxed domains, `ENABLED` of an action with boxed parts.
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

/// Boxed values bound by LETs and used in loop bodies, records, sequences,
/// CHOOSE, IF on boxed values, filters with boxed predicates.
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
Inv == \A t \in SUBSET r.a : Cardinality(t) <= 4 /\ LET c == {Len(q)} \cup t IN c # {}
Live == ENABLED Shuffle \/ Cardinality(r.a) < 3 \/ r.b > 0
Mono == [][Len(q') <= Len(q) + 1 /\ (\A z \in r'.a : z \in r.a \/ z = n) /\ Cardinality({y \in r'.a : y > n}) < 3]_<<n, r, q>>"#;

fn key(n: &NativeSet) -> String {
    format!(
        "{:?}",
        (
            n.init,
            &n.actions,
            &n.invariants,
            &n.action_properties,
            n.mixed,
            n.mixed_init,
            &n.mixed_actions,
            &n.mixed_invariants,
            &n.mixed_action_properties
        )
    )
}

/// The C and JIT libraries of `src` in mixed mode (with `force`) give the
/// same results on all reachable states and steps.
fn check(name: &str, body: &str, force: u32) {
    let src = module(name, body);
    let h = Harness::new(&src, CFG);
    let ip = h.base.ip.clone();
    let mut lw = Lowerer::with_typing(&ip, Typing::new(h.layout.clone()));
    let init = lw.lower_init(h.base.init_expr()).ok();
    let actions: Vec<_> = h.base.actions().iter().map(|a| lw.lower_action(a).ok()).collect();
    let invariants: Vec<_> = h.base.invariant_exprs().iter().zip(h.base.invariant_names()).map(|(e, n)| lw.lower_pred(n, e)).collect();
    let aprops: Vec<_> =
        h.base.action_property_exprs().iter().zip(h.base.action_property_names()).map(|(e, n)| lw.lower_trans_pred(n, e)).collect();
    let typing = &lw.typing;
    let (names, inv_names) = (h.base.action_names(), h.base.invariant_names());
    let verified = tlx_compile::verify::Program::new(typing, init.as_ref(), &actions, &invariants, &aprops).expect("valid IR");
    let lib = CGen::new(&verified).with_mixed(Mixed { oracle: &lw, force, loops: true }).library(names, inv_names);
    assert!(lib.plan.native.mixed > 0 && !lib.plan.regions.is_empty(), "{name}: no regions");
    let regions = lib.plan.region_plan(&lw);
    let j = tlx_compile::jit::library(&verified, Some(regions), None, names, inv_names).expect("JIT library");
    assert_eq!(key(&j.native), key(&lib.plan.native), "{name} force {force}: native functions");
    assert_eq!(
        (j.lib.n_regions() as usize, j.lib.regions_hash()),
        (lib.plan.regions.len(), lib.plan.regions.hash()),
        "{name}: region table of the JIT library"
    );

    let dir = std::env::temp_dir().join(format!("tlx-jit-mixed-{}", std::process::id()));
    let prog = tlx_compile::exec::fast::Program::new(typing);
    let slots = FastRegions::slots(&lib.plan.regions);
    let host =
        HostRegions { ip: &h.base.ip, typing, table: &lib.plan.regions, memo: 0, fast: Some(FastRegions { prog: &prog, progs: &slots }) };
    let path = build(&lib.src, &BuildOptions { cache_dir: dir.clone(), ..Default::default() }).expect("generated C builds");
    // SAFETY: CGen emitted this library from verified IR with lib.plan.regions;
    // host uses those signatures. The test compiler/cache are trusted.
    let c = unsafe { NativeLib::load_with(&path, Some(&host), None) }.expect("load against the region table");
    let (states, steps) = h.reachable(2000);
    let enc: Vec<Box<[u64]>> = states.iter().map(|v| h.encode(v).expect("state fits the layout")).collect();
    let mut cx = MixedCx::new();
    {
        let mut both = |f: &dyn Fn(&NativeLib, MixedCall<'_>) -> String| {
            let a = f(&c, MixedCall { cx: &mut cx, regions: &host, level: 1 });
            let b = f(&j.lib, MixedCall { cx: &mut cx, regions: &host, level: 1 });
            (a, b)
        };
        let succ = |rc: i32, mut out: Vec<Box<[u64]>>| {
            out.sort();
            format!("{rc} {out:?}")
        };
        let (a, b) = both(&|l, m| {
            let mut out = Vec::new();
            succ(l.init_mixed(m, &mut out), out)
        });
        assert_eq!(a, b, "{name} force {force}: Init");
        for (k, s) in enc.iter().enumerate() {
            for i in 0..names.len() as u32 {
                let (a, b) = both(&|l, m| {
                    let mut out = Vec::new();
                    succ(l.next_mixed(m, s, i, &mut out), out)
                });
                assert_eq!(a, b, "{name} force {force}: action {} on {:?}", names[i as usize], states[k]);
            }
            for i in 0..inv_names.len() as u32 {
                let (a, b) = both(&|l, m| l.invariant_mixed(m, s, i).to_string());
                assert_eq!(a, b, "{name} force {force}: invariant {} on {:?}", inv_names[i as usize], states[k]);
            }
        }
        for &(x, y) in &steps {
            for i in 0..aprops.len() as u32 {
                let (a, b) = both(&|l, m| l.action_property_mixed(m, &enc[x], &enc[y], i).to_string());
                assert_eq!(a, b, "{name} force {force}: action property {i} on {:?} -> {:?}", states[x], states[y]);
            }
        }
    }
    assert_eq!(cx.live_values(), 0, "handles freed after the calls");
    assert!(cx.evals > 0);
    let _ = std::fs::remove_dir_all(dir);
}

#[test]
fn jit_calls_the_regions_of_the_c_code() {
    for force in [0, 1, 3] {
        check("JitMixedSets", SETS, force);
        check("JitMixedLoops", LOOPS, force);
    }
}

/// Search `body` with an `EncModel` with the given settings and compare
/// the result with the interpreter's. Returns the model's notes.
fn search(name: &str, body: &str, env: &[(&str, &str)]) -> Vec<String> {
    let src = module(name, body);
    let h = Harness::new(&src, CFG);
    let opts = Options::default();
    let want = explore(&h.base, &opts);
    let settings = Settings::from_lookup(|n| env.iter().find(|(k, _)| *k == n).map(|(_, v)| v.to_string())).expect("settings");
    let base = Arc::new(tlx_testkit::spec::load(&src, CFG));
    let m = EncModel::new(base, h.layout.clone(), Vec::new(), &settings);
    let got = explore(&m, &opts);
    let key = |s: &tlx_runtime::Stats| (s.distinct, s.generated, s.depth);
    assert_eq!(key(&got.stats), key(&want.stats), "{name} {env:?}: counts");
    assert_eq!(format!("{:?}", got.outcome), format!("{:?}", want.outcome), "{name} {env:?}: outcome");
    assert!(matches!(want.outcome, Outcome::Ok), "{name}: {:?}", want.outcome);
    assert!(!m.notes.iter().any(|n| n.contains("JIT disabled")), "{name} {env:?}: {:?}", m.notes);
    m.notes.clone()
}

#[test]
fn jit_search_matches_the_interpreter() {
    for (name, body) in [("JitMixedSets", SETS), ("JitMixedLoops", LOOPS)] {
        for force in ["0", "2"] {
            let notes = search(name, body, &[("TLX_JIT", "1"), ("TLX_PARANOID", "1"), ("TLX_MIXED_FORCE", force)]);
            assert!(notes.iter().any(|n| n.contains("mixed: ")), "{name}: no mixed function: {notes:?}");
        }
    }
}

/// The default tiers, with the C library built at once (it replaces the
/// JIT library during the search).
#[test]
fn tiered_search_matches_the_interpreter() {
    for (name, body) in [("JitMixedSets", SETS), ("JitMixedLoops", LOOPS)] {
        search(name, body, &[("TLX_CC_DELAY_MS", "0"), ("TLX_MIXED_ADAPT", "0")]);
    }
}
