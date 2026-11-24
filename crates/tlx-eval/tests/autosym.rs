//! The static symmetry analysis (`model::autosym`): one spec per allowed
//! class of operations (proven) and per breaker class (rejected, with the
//! breaker's location).

use tlx_eval::model::autosym::{self, Analysis, Verdict};
use tlx_eval::{Interp, InterpModel};
use tlx_sema::Program;

/// Load module `src` (complete text) with configuration `cfg`.
fn try_load_with(src: &str, cfg: &str) -> Result<InterpModel, String> {
    let dir = tlx_testkit::TempDir::new("autosym");
    let path = dir.write("M.tla", src);
    let prog = Program::load(&path, &[]).map_err(|es| es.iter().map(|e| e.to_string()).collect::<Vec<_>>().join("\n"))?;
    let cfg = tlx_front::cfg::parse_cfg(cfg).map_err(|e| format!("cfg: {e:?}"))?;
    Interp::new(prog, cfg).and_then(InterpModel::new).map_err(|e| e.into_message())
}

const HEAD: &str = "EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, TLCExt, Bags, SequencesExt, FiniteSetsExt, Functions, Json\nCONSTANTS Proc, Leader\n";
const CFG: &str = "CONSTANTS\n  Proc = {p1, p2, p3}\n  Leader = q\nINIT Init\nNEXT Next\n";

/// Analyze a module with variables, Init and Next given in `body`.
fn analysis_with(body: &str, cfg: &str) -> Analysis {
    let src = tlx_testkit::module("M", &format!("{HEAD}{body}"));
    let model = try_load_with(&src, cfg).unwrap_or_else(|e| panic!("{e}\n{src}"));
    autosym::analyze(&model)
}

fn analysis(body: &str) -> Analysis {
    analysis_with(body, CFG)
}

fn verdict<'a>(an: &'a Analysis, name: &str) -> &'a Verdict {
    &an.sets.iter().find(|s| s.candidate.name == name).unwrap_or_else(|| panic!("no candidate {name}: {an:?}")).verdict
}

fn assert_proven(body: &str) {
    let an = analysis(body);
    let s = an.sets.iter().find(|s| s.candidate.name == "Proc").expect("candidate Proc");
    assert!(s.full(), "expected Permutations(Proc) to be proven: {:?}\n{body}", s.verdict);
    assert_eq!(an.group_text(), "Permutations(Proc)");
    assert_eq!(an.group_order(), 6);
}

/// The breaker reported for Proc, `what` at `line` (of the module, whose
/// first line is the MODULE header).
fn assert_rejected(body: &str, what: &str, line: usize) {
    let an = analysis(body);
    match verdict(&an, "Proc") {
        Verdict::Rejected { what: w, at } => {
            assert!(w.contains(what), "breaker {w:?}, expected {what:?}\n{body}");
            assert!(at.starts_with(&format!("M.tla:{line}:")), "breaker at {at}, expected line {line}\n{body}");
        }
        v => panic!("expected a breaker {what}, got {v:?}\n{body}"),
    }
    assert!(an.suggestion(Some(true)).is_none());
}

/// The line of the first occurrence of `needle` in the module built from `body`.
fn line_of(body: &str, needle: &str) -> usize {
    let src = tlx_testkit::module("M", &format!("{HEAD}{body}"));
    src.lines().position(|l| l.contains(needle)).expect("needle") + 1
}

const PC: &str = "VARIABLE pc\n";

// --- allowed classes ---

#[test]
fn equality_membership_and_functions_are_symmetric() {
    assert_proven(&format!(
        "{PC}Init == pc = [p \\in Proc |-> \"idle\"]\n\
         Next == \\E p \\in Proc : /\\ pc[p] = \"idle\" /\\ \\A q2 \\in Proc \\ {{p}} : pc[q2] # \"cs\"\n\
         \x20   /\\ pc' = [pc EXCEPT ![p] = \"cs\"] /\\ DOMAIN pc = Proc /\\ pc \\in [Proc -> {{\"idle\", \"cs\"}}]\n"
    ));
}

#[test]
fn set_operators_are_symmetric() {
    assert_proven(
        "VARIABLE s\nInit == s = {}\n\
         Next == \\E p \\in Proc : /\\ p \\notin s /\\ s \\subseteq Proc /\\ Cardinality(s \\cup {p}) <= 3\n\
         \x20   /\\ s' = (s \\cup {p}) \\ ({} \\cap s) /\\ s' \\in SUBSET Proc /\\ UNION {s, {p}} = s' /\\ IsFiniteSet(s')\n\
         \x20   /\\ {x \\in Proc : x \\in s} = s /\\ ({<<x, x>> : x \\in s} # {} \\/ s = {})\n",
    );
}

#[test]
fn records_tuples_and_sequences_are_symmetric() {
    assert_proven("VARIABLES msgs, log\nInit == msgs = {} /\\ log = <<>>\n\
         Next == \\E p \\in Proc : /\\ Len(log) < 3 /\\ log' = Append(log, p) \\o <<>>\n\
         \x20   /\\ msgs' = msgs \\cup {[from |-> p, n |-> Len(log)]} /\\ <<p, 1>>[1] = p /\\ (Len(log) > 0 => Head(log) \\in Proc)\n\
         \x20   /\\ \\A m \\in msgs : m.from \\in Proc /\\ msgs \\subseteq [from : Proc, n : Nat] /\\ SubSeq(log, 1, 1) = SubSeq(log, 1, 1)\n");
}

#[test]
fn if_case_and_bags_are_symmetric() {
    assert_proven(
        "VARIABLE b\nInit == b = EmptyBag\n\
         Next == \\E p \\in Proc : /\\ BagCardinality(b) < 3\n\
         \x20   /\\ b' = IF p \\in BagToSet(b) THEN b (+) SetToBag({p}) ELSE CASE CopiesIn(p, b) = 0 -> b (+) SetToBag({p}) [] OTHER -> b\n\
         \x20   /\\ (p :> 1) @@ b = (p :> 1) @@ b\n",
    );
}

#[test]
fn choose_over_integers_is_symmetric() {
    // The chosen element is an integer: the same in every permuted state.
    assert_proven(&format!(
        "{PC}Init == pc = [p \\in Proc |-> 0]\n\
         Top(S) == CHOOSE x \\in S : \\A y \\in S : x >= y\n\
         Next == \\E p \\in Proc : /\\ pc[p] < 2 /\\ pc' = [pc EXCEPT ![p] = Top({{pc[q2] : q2 \\in Proc}}) + 1 - pc[p] + pc[p]]\n"
    ));
}

#[test]
fn choose_of_a_unique_element_is_symmetric() {
    assert_proven(
        "VARIABLE cur\nInit == cur \\in Proc\n\
         Next == \\E p \\in Proc : cur' = CHOOSE x \\in Proc : x = p /\\ TRUE\n",
    );
}

#[test]
fn permutations_and_commutative_folds_are_symmetric() {
    assert_proven(&format!(
        "{PC}Init == pc = [p \\in Proc |-> 0]\n\
         Next == \\E p \\in Proc : /\\ pc[p] = 0 /\\ Cardinality(Permutations(Proc)) = 6\n\
         \x20   /\\ FoldSet(LAMBDA x, y : x + y, 0, {{pc[q2] : q2 \\in Proc}}) < 3 /\\ FoldFunction(LAMBDA x, y : x + y, 0, pc) < 3\n\
         \x20   /\\ pc' = [pc EXCEPT ![p] = 1]\n"
    ));
}

#[test]
fn print_is_allowed_by_the_proof_but_is_an_effect() {
    let an = analysis(&format!(
        "{PC}Init == pc = [p \\in Proc |-> 0]\nNext == \\E p \\in Proc : pc[p] = 0 /\\ PrintT(p) /\\ pc' = [pc EXCEPT ![p] = 1]\n"
    ));
    assert!(an.sets[0].full(), "{:?}", an.sets[0].verdict);
    assert_eq!(an.effects.len(), 1, "{:?}", an.effects);
    assert!(an.effects[0].starts_with("PrintT at M.tla:"));
}

#[test]
fn a_distinguished_constant_leaves_its_stabilizer() {
    let cfg = "CONSTANTS\n  Proc = {p1, p2, p3}\n  Leader = p1\nINIT Init\nNEXT Next\n";
    let an = analysis_with(
        &format!("{PC}Init == pc = [p \\in Proc |-> 0]\nNext == \\E p \\in Proc : pc[p] = 0 /\\ pc' = [pc EXCEPT ![p] = IF p = Leader THEN 2 ELSE 1]\n"),
        cfg,
    );
    match verdict(&an, "Proc") {
        Verdict::Proven { classes, pinned_by } => {
            assert_eq!(classes.len(), 1);
            assert_eq!(classes[0].iter().map(|v| v.to_string()).collect::<Vec<_>>(), ["p2", "p3"]);
            assert_eq!(pinned_by, &["Leader (the cfg)".to_string()]);
        }
        v => panic!("{v:?}"),
    }
    assert_eq!(an.group_text(), "Permutations(Proc \\ {p1})");
    assert!(an.symmetry_definition().is_none());
}

#[test]
fn a_constant_definition_chosen_from_the_set_is_pinned_too() {
    // A 0-ary constant definition is read as its value: CHOOSE picks p1.
    let an = analysis(&format!(
        "{PC}First == CHOOSE p \\in Proc : TRUE\nInit == pc = [p \\in Proc |-> 0]\n\
         Next == \\E p \\in Proc : pc[p] = 0 /\\ pc' = [pc EXCEPT ![p] = IF p = First THEN 2 ELSE 1]\n"
    ));
    assert_eq!(an.group_text(), "Permutations(Proc \\ {p1})");
}

#[test]
fn a_symmetric_constant_value_is_admitted() {
    let cfg = "CONSTANTS\n  Proc = {p1, p2, p3}\n  Leader = q\n  Pairs = {{p1, p2}, {p1, p3}, {p2, p3}}\nINIT Init\nNEXT Next\n";
    let an = analysis_with(
        &format!("CONSTANT Pairs\n{PC}Init == pc = [p \\in Proc |-> 0]\nNext == \\E Q \\in Pairs : \\E p \\in Q : pc[p] = 0 /\\ pc' = [pc EXCEPT ![p] = 1]\n"),
        cfg,
    );
    assert_eq!(an.group_text(), "Permutations(Proc)");
}

#[test]
fn integers_and_unused_sets_are_not_candidates() {
    let cfg = "CONSTANTS\n  Proc = {p1, p2, p3}\n  Leader = q\n  Ids = {1, 2, 3}\n  Other = {o1, o2}\nINIT Init\nNEXT Next\n";
    let an =
        analysis_with("CONSTANTS Ids, Other\nVARIABLE x\nInit == x = 0\nNext == x' = 1 - x /\\ Cardinality(Other) = 2 /\\ Ids # {}\n", cfg);
    assert!(an.sets.iter().all(|s| s.candidate.name != "Ids"));
    assert!(matches!(verdict(&an, "Other"), Verdict::Unused));
    assert!(matches!(verdict(&an, "Proc"), Verdict::Unused));
    assert!(an.suggestion(Some(true)).is_none());
}

#[test]
fn a_declared_symmetry_is_not_suggested_again() {
    let cfg = "CONSTANTS\n  Proc = {p1, p2, p3}\n  Leader = q\nINIT Init\nNEXT Next\nSYMMETRY Perms\n";
    let an = analysis_with(
        &format!(
            "Perms == Permutations(Proc)\n{PC}Init == pc = [p \\in Proc |-> 0]\nNext == \\E p \\in Proc : pc' = [pc EXCEPT ![p] = 1]\n"
        ),
        cfg,
    );
    assert!(matches!(verdict(&an, "Proc"), Verdict::Declared));
    assert!(an.suggestion(Some(true)).is_none());
}

#[test]
fn an_operator_parameter_bound_to_a_variable_is_assigned() {
    // `Set(v, e) == v' = e` applied to `cur` assigns `cur` a Proc value; the
    // CHOOSE over {cur} then depends on it.
    let body = "VARIABLE cur\nSet(v, e) == v' = e\nInit == cur = 0\nNext == \\E p \\in Proc : Set(cur, p) /\\ (CHOOSE y \\in {cur, 7} : TRUE) # 9\n";
    assert_rejected(body, "CHOOSE", line_of(body, "CHOOSE"));
}

// --- breakers ---

#[test]
fn choose_over_the_set_breaks() {
    let body =
        format!("{PC}Init == pc = [p \\in Proc |-> 0]\nNext == LET p == CHOOSE x \\in Proc : pc[x] = 0 IN pc' = [pc EXCEPT ![p] = 1]\n");
    assert_rejected(&body, "CHOOSE", line_of(&body, "CHOOSE"));
}

#[test]
fn choose_over_state_values_breaks() {
    // (In Next: not a constant.)
    let body = "VARIABLE s\nInit == s = Proc\nNext == s # {} /\\ s' = s \\ {CHOOSE x \\in s : TRUE}\n";
    assert_rejected(body, "CHOOSE", line_of(body, "CHOOSE"));
}

#[test]
fn a_model_value_from_a_string_breaks() {
    let body = format!("{PC}Init == pc = [p \\in Proc |-> 0]\nNext == pc' = [pc EXCEPT ![TLCModelValue(\"p1\")] = 1]\n");
    assert_rejected(&body, "TLCModelValue", line_of(&body, "TLCModelValue"));
}

#[test]
fn set_to_seq_breaks() {
    let body = "VARIABLE q\nInit == q = <<>>\nNext == Len(q) = 0 /\\ q' = SetToSeq(Proc)\n";
    assert_rejected(body, "SetToSeq", line_of(body, "SetToSeq"));
}

#[test]
fn to_string_breaks() {
    let body = "VARIABLE q\nInit == q = \"\"\nNext == \\E p \\in Proc : q' = ToString(p)\n";
    assert_rejected(body, "ToString", line_of(body, "ToString"));
}

#[test]
fn sort_seq_with_an_order_of_names_breaks() {
    let body = "VARIABLE q\nInit == q = <<>>\nNext == \\E p \\in Proc : Len(q) < 2 /\\ q' = SortSeq(Append(q, p), LAMBDA a, b : ToString(a) < ToString(b))\n";
    assert_rejected(body, "ToString", line_of(body, "ToString"));
}

#[test]
fn a_fold_with_an_order_dependent_operator_breaks() {
    let body = "VARIABLE q\nInit == q = <<>>\nNext == Len(q) = 0 /\\ q' = FoldSet(LAMBDA x, acc : <<x>> \\o acc, <<>>, Proc)\n";
    assert_rejected(body, "FoldSet", line_of(body, "FoldSet"));
    let body = "VARIABLE q\nInit == q = <<>>\nNext == Len(q) = 0 /\\ q' = FoldFunction(LAMBDA x, acc : <<x>> \\o acc, <<>>, [p \\in Proc |-> p])\n";
    assert_rejected(body, "FoldFunction", line_of(body, "FoldFunction"));
}

#[test]
fn random_choice_breaks_and_is_an_effect() {
    let body = "VARIABLE cur\nInit == cur \\in Proc\nNext == cur' = RandomElement(Proc)\n";
    assert_rejected(body, "RandomElement", line_of(body, "RandomElement"));
    let an = analysis(body);
    assert!(an.effects.iter().any(|e| e.starts_with("RandomElement")));
}

#[test]
fn json_of_a_set_element_breaks() {
    let body = "VARIABLE q\nInit == q = \"\"\nNext == \\E p \\in Proc : q' = ToJson(p)\n";
    assert_rejected(body, "ToJson", line_of(body, "ToJson"));
}

#[test]
fn registers_are_effects() {
    let an =
        analysis(&format!("{PC}Init == pc = [p \\in Proc |-> 0]\nNext == \\E p \\in Proc : TLCSet(1, p) /\\ pc' = [pc EXCEPT ![p] = 1]\n"));
    assert!(an.effects.iter().any(|e| e.starts_with("TLCSet")), "{:?}", an.effects);
    // `TLCGet("level")` is the same in every state of an orbit.
    let an = analysis(&format!(
        "{PC}Init == pc = [p \\in Proc |-> 0]\nNext == \\E p \\in Proc : TLCGet(\"level\") < 5 /\\ pc' = [pc EXCEPT ![p] = 1]\n"
    ));
    assert!(an.effects.is_empty(), "{:?}", an.effects);
    assert!(an.sets[0].full());
}

#[test]
fn breakers_in_invariants_and_constraints_count() {
    let body = format!("{PC}Init == pc = [p \\in Proc |-> 0]\nNext == \\E p \\in Proc : pc' = [pc EXCEPT ![p] = 1]\nInv == pc[CHOOSE p \\in Proc : TRUE] \\in {{0, 1}}\n");
    let src = tlx_testkit::module("M", &format!("{HEAD}{body}"));
    let model = try_load_with(&src, &format!("{CFG}INVARIANT Inv\n")).unwrap();
    let an = autosym::analyze(&model);
    assert!(matches!(verdict(&an, "Proc"), Verdict::Rejected { what, .. } if what == "CHOOSE"));
    let model = try_load_with(&src.replace("Inv ==", "Con =="), &format!("{CFG}CONSTRAINT Con\n")).unwrap();
    let an = autosym::analyze(&model);
    assert!(matches!(verdict(&an, "Proc"), Verdict::Rejected { what, .. } if what == "CHOOSE"));
}

#[test]
fn a_recursive_operator_over_the_set_is_analyzed() {
    // ReduceSet-style recursion with CHOOSE and an order-dependent
    // combination: rejected (with `\cup` it would be a fold, see below).
    let body =
        "VARIABLE q\nRECURSIVE Pick(_)\nPick(S) == IF S = {} THEN <<>> ELSE LET x == CHOOSE y \\in S : TRUE IN <<x>> \\o Pick(S \\ {x})\n\
                Init == q = <<>>\nNext == q' = Pick(Proc)\n";
    assert_rejected(body, "CHOOSE", line_of(body, "CHOOSE"));
    // The same recursion without CHOOSE: proven.
    assert_proven(
        "VARIABLE q\nRECURSIVE Copy(_)\nCopy(S) == IF S = {} THEN {} ELSE UNION {{x} \\cup Copy(S \\ {x}) : x \\in S}\nInit == q = {}\nNext == q' = Copy(Proc)\n",
    );
}

#[test]
fn a_lambda_is_analyzed_in_each_context() {
    // `Apply2(f, x) == f(x)` is applied to the same LAMBDA in two contexts:
    // its free variable `a` is an integer in the first and a set element in
    // the second, where the CHOOSE depends on it.
    let body = "VARIABLE q\nApply2(f(_), x) == f(x)\nUse(a) == Apply2(LAMBDA y : CHOOSE z \\in {a, y} : TRUE, 1)\n\
                Init == q = 0\nNext == q' = 1 /\\ Use(2) # 0 /\\ \\E p \\in Proc : Use(p) # 0\n";
    assert_rejected(body, "CHOOSE", line_of(body, "CHOOSE"));
}

#[test]
fn a_recursive_sum_over_the_set_is_symmetric() {
    // The element CHOOSE picks only decides the order of a commutative sum.
    assert_proven(
        "VARIABLE pc\nTotal == LET sum[S \\in SUBSET Proc] == IF S = {} THEN 0 ELSE LET p == CHOOSE x \\in S : TRUE IN pc[p] + sum[S \\ {p}] IN sum[Proc]\n\
         Init == pc = [p \\in Proc |-> 0]\nNext == \\E p \\in Proc : Total < 3 /\\ pc' = [pc EXCEPT ![p] = @ + 1]\n",
    );
    assert_proven(
        "VARIABLE pc\nRECURSIVE Sum(_, _)\nSum(f, S) == IF S = {} THEN 0 ELSE LET p == CHOOSE x \\in S : TRUE IN Sum(f, S \\ {p}) + f[p]\n\
         Init == pc = [p \\in Proc |-> 0]\nNext == \\E p \\in Proc : Sum(pc, Proc) < 3 /\\ pc' = [pc EXCEPT ![p] = @ + 1]\n",
    );
    // Not a fold: the element depends on the rest of the set.
    let body = "VARIABLE pc\nTotal == LET sum[S \\in SUBSET Proc] == IF S = {} THEN 0 ELSE LET p == CHOOSE x \\in S : TRUE IN Cardinality(S) * pc[p] + sum[S \\ {p}] IN sum[Proc]\n\
                Init == pc = [p \\in Proc |-> 0]\nNext == \\E p \\in Proc : Total < 3 /\\ pc' = [pc EXCEPT ![p] = @ + 1]\n";
    assert_rejected(body, "CHOOSE", line_of(body, "CHOOSE"));
}

#[test]
fn choose_of_the_only_satisfying_element_is_symmetric() {
    assert_proven(
        "VARIABLE cur\nOnly(S, P(_)) == CHOOSE x \\in S : P(x) /\\ \\A y \\in S : P(y) => y = x\n\
         Init == cur \\in Proc\nNext == \\E p \\in Proc : cur' = Only(Proc, LAMBDA z : z = p)\n",
    );
    // Without the uniqueness conjunct the choice is TLC's first element.
    let body = "VARIABLE cur\nSome(S, P(_)) == CHOOSE x \\in S : P(x) /\\ \\A y \\in S : P(y) => TRUE\n\
                Init == cur \\in Proc\nNext == \\E p \\in Proc : cur' = Some(Proc, LAMBDA z : z # p)\n";
    assert_rejected(body, "CHOOSE", line_of(body, "CHOOSE"));
}

#[test]
fn projected_choice_without_static_uniqueness_is_rejected_by_analyzer() {
    let body = "VARIABLE msgs\nInit == msgs = {[from |-> p, val |-> 1] : p \\in Proc}\n\
                Next == UNCHANGED msgs /\\ (CHOOSE m \\in msgs : TRUE).val = 1";
    assert_rejected(body, "CHOOSE", line_of(body, "CHOOSE"));
}

#[test]
fn subseteq_assignment_propagates_set_shape_and_detects_breakers() {
    assert_proven("VARIABLE s\nInit == s \\subseteq Proc\nNext == s' \\subseteq Proc\n");
    let body = "VARIABLE s\nInit == s \\subseteq Proc\nNext == UNCHANGED s /\\ (s = {} \\/ (CHOOSE x \\in s : TRUE) \\in s)\n";
    assert_rejected(body, "CHOOSE", line_of(body, "CHOOSE"));
}
