//! Family-navigation snapshots for the symmetry analyzer: one spec per
//! operation family (the helpers `model/autosym/analyze/{builtins,expr}.rs`
//! dispatch to) that must report that family's breaker reason at the exact
//! call location, and one per family that must stay proven. Splitting
//! `analyze.rs` into family modules must not change any of these strings.
//!
//! The families are the ones the dispatchers in `analyze::builtins` and
//! `analyze::expr` name: the fold helpers, the order/name dependent
//! helpers (`set_order`, `to_string`, `causal_order`, `chi_square`,
//! `set_to_seq`), the random helpers, the effect helpers (`print`,
//! `tlc_effect`, `io_effect`) and the expression binders.

use tlx_eval::model::autosym::{self, Analysis, Verdict};
use tlx_eval::{Interp, InterpModel};
use tlx_sema::Program;

/// Load module `src` (complete text) with configuration `cfg`.
fn try_load_with(src: &str, cfg: &str) -> Result<InterpModel, String> {
    let dir = tlx_testkit::TempDir::new("autosym-families");
    let path = dir.write("M.tla", src);
    let prog = Program::load(&path, &[]).map_err(|es| es.iter().map(|e| e.to_string()).collect::<Vec<_>>().join("\n"))?;
    let cfg = tlx_front::cfg::parse_cfg(cfg).map_err(|e| format!("cfg: {e:?}"))?;
    Interp::new(prog, cfg).and_then(InterpModel::new).map_err(|e| e.into_message())
}

/// Every standard and community module the family specs use.
const HEAD: &str = "EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, TLCExt, Bags, SequencesExt, FiniteSetsExt, Functions, Json, Folds, BagsExt, VectorClocks, Statistics, Randomization\nCONSTANTS Proc, Leader\n";
const CFG: &str = "CONSTANTS\n  Proc = {p1, p2, p3}\n  Leader = q\nINIT Init\nNEXT Next\n";
/// `q` is the scalar result of the operation under test, `s` keeps a `Proc`
/// element in the state so a proven candidate is used (not `Unused`).
const VARS: &str = "VARIABLE q, s\nInit == q = 0 /\\ s = {}\n";

fn body(expr: &str) -> String {
    format!("{VARS}Next == \\E p \\in Proc : s' = s \\cup {{p}} /\\ q' = {expr}\n")
}

fn analysis(b: &str) -> Analysis {
    let src = tlx_testkit::module("M", &format!("{HEAD}{b}"));
    let model = try_load_with(&src, CFG).unwrap_or_else(|e| panic!("{e}\n{src}"));
    autosym::analyze(&model)
}

fn verdict<'a>(an: &'a Analysis, name: &str) -> &'a Verdict {
    &an.sets.iter().find(|s| s.candidate.name == name).unwrap_or_else(|| panic!("no candidate {name}: {an:?}")).verdict
}

/// `file:line:col` of the first occurrence of `needle` in the module built
/// from `b`; the analyzer reports spans with the same coordinates.
fn location_of(b: &str, needle: &str) -> String {
    let src = tlx_testkit::module("M", &format!("{HEAD}{b}"));
    let line = src.lines().position(|l| l.contains(needle)).expect("needle");
    let col = src.lines().nth(line).unwrap().find(needle).expect("needle") + 1;
    format!("M.tla:{}:{col}", line + 1)
}

/// The call `expr` must be rejected with reason `what` at the location of its
/// own occurrence (the family dispatcher reported the right reason and span).
fn assert_reason(expr: &str, what: &str) {
    let b = body(expr);
    let an = analysis(&b);
    match verdict(&an, "Proc") {
        Verdict::Rejected { what: w, at } => {
            assert_eq!(w, what, "reason for {expr:?}\n{b}");
            assert_eq!(at.as_str(), location_of(&b, expr).as_str(), "location for {expr:?}\n{b}");
        }
        v => panic!("expected a breaker for {expr:?}, got {v:?}\n{b}"),
    }
    assert!(an.suggestion(Some(true)).is_none(), "a rejected analysis suggests nothing: {expr:?}");
    assert!(!an.incomplete, "the spec is small enough: {expr:?}");
}

/// The call `expr` must be proven symmetric (no breaker in its family).
fn assert_symmetric(expr: &str) {
    let b = body(expr);
    let an = analysis(&b);
    let s = an.sets.iter().find(|s| s.candidate.name == "Proc").expect("candidate Proc");
    assert!(s.full(), "expected {expr:?} to be proven: {:?}\n{b}", s.verdict);
    assert_eq!(an.group_text(), "Permutations(Proc)");
    assert!(an.suggestion(Some(true)).is_some());
}

// --- order and name dependent families ---

#[test]
fn set_order_family_reports_the_extreme_operation() {
    assert_reason("Max(Proc)", "Max");
    assert_reason("Min(Proc)", "Min");
}

#[test]
fn to_string_family_reports_the_writer_operation() {
    assert_reason("ToString(p)", "ToString");
    assert_reason("TLCFP(p)", "TLCFP");
    assert_reason("ToJson(p)", "ToJson");
    assert_reason("ToJsonArray(p)", "ToJsonArray");
    assert_reason("ToJsonObject([a |-> p])", "ToJsonObject");
}

#[test]
fn causal_order_family_reports_its_operation() {
    assert_reason("CausalOrder(<<p>>, LAMBDA e : 0, LAMBDA e : 0, LAMBDA e : 0)", "CausalOrder");
}

#[test]
fn chi_square_family_reports_its_operation() {
    assert_reason("ChiSquare(Proc, Proc, 1)", "ChiSquare");
}

#[test]
fn set_to_seq_family_reports_its_operation() {
    assert_reason("SetToSeq(Proc)", "SetToSeq");
}

// --- fold families ---

#[test]
fn fold_families_report_the_fold_and_its_operator() {
    let nca = "with an operator not known to be commutative and associative";
    let nc = "LAMBDA x, y : <<x>> \\o y";
    assert_reason(&format!("FoldSet({nc}, <<>>, Proc)"), &format!("FoldSet {nca}"));
    assert_reason(&format!("FoldFunction({nc}, <<>>, [p2 \\in Proc |-> p2])"), &format!("FoldFunction {nca}"));
    assert_reason(&format!("FoldFunctionOnSet({nc}, <<>>, [p2 \\in Proc |-> p2], Proc)"), &format!("FoldFunctionOnSet {nca}"));
    assert_reason(&format!("FoldBag({nc}, <<>>, SetToBag(Proc))"), &format!("FoldBag {nca}"));
}

#[test]
fn map_then_fold_set_family_reports_the_fold_and_its_operator() {
    // A `choose` operator that ignores its set keeps this a pure snapshot of
    // `map_then_fold_set`: the only breaker is the fold order itself.
    assert_reason(
        "MapThenFoldSet(LAMBDA x, y : <<x>> \\o y, <<>>, LAMBDA x : x, LAMBDA S : 0, Proc)",
        "MapThenFoldSet with an operator not known to be commutative and associative",
    );
}

#[test]
fn index_fold_families_do_not_break_on_model_value_order() {
    // FoldSeq/FoldLeft/FoldRight iterate by index: no order of model values.
    let nc = "LAMBDA x, y : <<x>> \\o y";
    assert_symmetric(&format!("FoldSeq({nc}, <<>>, <<p>>)"));
    assert_symmetric(&format!("FoldLeft({nc}, <<>>, <<p>>)"));
    assert_symmetric(&format!("FoldRight({nc}, <<p>>, <<>>)"));
}

// --- random and effect families ---

#[test]
fn random_families_report_the_operation() {
    assert_reason("RandomElement(Proc)", "RandomElement");
    assert_reason("RandomSubset(2, Proc)", "RandomSubset");
    assert_reason("RandomSetOfSubsets(1, 1, Proc)", "RandomSetOfSubsets");
    assert_reason("TLCModelValue(\"x\")", "TLCModelValue");
}

#[test]
fn print_families_are_effects_not_breakers() {
    for (expr, what) in [("Print(\"x\", p)", "Print"), ("PrintT(p)", "PrintT")] {
        let b = body(expr);
        let an = analysis(&b);
        let s = an.sets.iter().find(|s| s.candidate.name == "Proc").expect("candidate Proc");
        assert!(s.full(), "{expr:?} must be proven: {:?}", s.verdict);
        assert_eq!(an.effects, vec![format!("{what} at {}", location_of(&b, expr))], "{expr:?}");
    }
}

#[test]
fn register_and_io_families_are_effects() {
    // `TLCGet`/`TLCSet` and the IO writers add an effect (and the values they
    // print break the symmetry of what they see).
    for (expr, what) in
        [("TLCGet(1)", "TLCGet"), ("JsonSerialize(\"f\", p)", "JsonSerialize"), ("ndJsonSerialize(\"f\", p)", "ndJsonSerialize")]
    {
        let b = body(expr);
        let an = analysis(&b);
        let want = format!("{what} at {}", location_of(&b, expr));
        assert!(an.effects.contains(&want), "{expr:?}: {:?}, want {want:?}", an.effects);
    }
    // `TLCGet("level")` is the same in every state of an orbit: no effect.
    let b = format!("{VARS}Next == \\E p \\in Proc : s' = s \\cup {{p}} /\\ TLCGet(\"level\") < 5 /\\ q' = 1\n");
    let an = analysis(&b);
    assert!(an.effects.is_empty(), "{:?}", an.effects);
    assert!(an.sets[0].full(), "{:?}", an.sets[0].verdict);
}

// --- expression families ---

#[test]
fn choose_family_reports_the_choice_site() {
    assert_reason("CHOOSE x \\in Proc : TRUE", "CHOOSE");
    assert_reason("CHOOSE x \\in Proc : x # p", "CHOOSE");
}

#[test]
fn expression_binders_stay_symmetric() {
    assert_symmetric("IF p = p THEN 1 ELSE 2");
    assert_symmetric("CASE p = p -> 1 [] OTHER -> 2");
    assert_symmetric("Cardinality({x \\in Proc : x = p})");
    assert_symmetric("Len(SelectSeq(<<p>>, LAMBDA x : x = p))");
    assert_symmetric("([x \\in Proc |-> x])[p]");
    assert_symmetric("{x \\in Proc : TRUE}");
    assert_symmetric("Len(SortSeq(<<p>>, LAMBDA a, b : a = b))");
    assert_symmetric("[a |-> p].a");
    assert_symmetric("(<<p, p>>)[1]");
}
