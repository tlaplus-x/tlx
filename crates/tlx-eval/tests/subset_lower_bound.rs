use std::sync::Arc;

use tlx_eval::env::Env;
use tlx_eval::eval::Ctx;
use tlx_eval::{Interp, InterpModel};
use tlx_runtime::{explore, Options, Outcome};
use tlx_sema::hir::{ExprKind, OpRef, RootSymbol};
use tlx_sema::Program;
use tlx_value::{Sym, Value};

fn load_model(body: &str, cfg: &str) -> InterpModel {
    let dir = tlx_testkit::TempDir::new("subset-lb");
    let path = dir.write("M.tla", &tlx_testkit::module("M", body));
    let prog = Program::load(&path, &[]).unwrap_or_else(|e| panic!("{e:?}"));
    let cfg = tlx_front::cfg::parse_cfg(cfg).unwrap();
    let ip = Interp::new(prog, cfg).unwrap_or_else(|e| panic!("{e}"));
    InterpModel::new(ip).unwrap_or_else(|e| panic!("{e}"))
}

fn next_successors(body: &str, cfg: &str, s0: Vec<Value>) -> Result<Vec<Vec<Value>>, String> {
    let model = load_model(body, cfg);
    let mut out = Vec::new();
    for action in model.actions() {
        model
            .ip
            .successors(&s0, 0, action, &mut |s1| {
                out.push(s1.iter().map(|v| v.clone().unwrap()).collect());
                Ok(true)
            })
            .map_err(|e| e.to_string())?;
    }
    Ok(out)
}

fn eval_const(body: &str, cfg: &str, name: &str) -> Result<Value, String> {
    let dir = tlx_testkit::TempDir::new("subset-lb-const");
    let path = dir.write("M.tla", &tlx_testkit::module("M", body));
    let mut prog = Program::load(&path, &[]).unwrap_or_else(|e| panic!("{e:?}"));
    let Some(RootSymbol::Def(d)) = prog.lookup_root(name) else {
        panic!("{name} not defined");
    };
    let cfg = tlx_front::cfg::parse_cfg(cfg).unwrap();
    let ip = Interp::new(prog, cfg).unwrap_or_else(|e| panic!("{e}"));
    let expr = tlx_sema::hir::Expr::new(ExprKind::Apply { op: OpRef::Def(d), args: vec![] }, Default::default());
    ip.eval(&expr, &Env::default(), &Ctx::NONE).map_err(|e| e.to_string())
}

#[test]
fn next_state_subset_lower_bound_streams_without_exponential_blowup() {
    let body = r#"
EXTENDS Integers
VARIABLE x
Init == x = (1..28)
Next == x' \in SUBSET (1..30) /\ x \subseteq x'
"#;
    let base: Value = Value::Set((1..=28).map(Value::Int).collect());
    let succs = next_successors(body, "INIT Init\nNEXT Next\n", vec![base]).unwrap();
    // Exact SUBSET order over delta \subseteq {29, 30}: {}, {29}, {30}, {29, 30}.
    assert_eq!(succs.len(), 4);
    let extras: Vec<Vec<i64>> = succs
        .iter()
        .map(|s| {
            let Value::Set(es) = &s[0] else { panic!("expected set") };
            es.iter().map(|v| v.as_int().unwrap()).filter(|&n| n > 28).collect()
        })
        .collect();
    assert_eq!(extras, vec![vec![], vec![29], vec![30], vec![29, 30]]);

    // Same via `x' \subseteq U` assignment syntax.
    let body_sub = r#"
EXTENDS Integers
VARIABLE x
Init == x = (1..28)
Next == x' \subseteq (1..30) /\ x \subseteq x'
"#;
    let base2: Value = Value::Set((1..=28).map(Value::Int).collect());
    let succs2 = next_successors(body_sub, "INIT Init\nNEXT Next\n", vec![base2]).unwrap();
    assert_eq!(succs2, succs);
}

#[test]
fn next_state_subset_multiple_bounds_and_order_match_brute_force() {
    let opt_body = r#"
EXTENDS Integers, FiniteSets
VARIABLE x, y
Init == x = {1, 3} /\ y = {2}
Next ==
    /\ y' = {2, 4}
    /\ x' \in SUBSET (1..6)
    /\ x \subseteq x'
    /\ y' \subseteq x'
    /\ 5 \notin x'
"#;
    // Reference prevents prefix matching with a harmless leading disjunction.
    let ref_body = r#"
EXTENDS Integers, FiniteSets
VARIABLE x, y
Init == x = {1, 3} /\ y = {2}
Next ==
    /\ y' = {2, 4}
    /\ x' \in SUBSET (1..6)
    /\ (TRUE \/ x' = {})
    /\ x \subseteq x'
    /\ y' \subseteq x'
    /\ 5 \notin x'
"#;
    let s0 = vec![Value::Set(vec![Value::Int(1), Value::Int(3)].into()), Value::Set(vec![Value::Int(2)].into())];
    let opt = next_successors(opt_body, "INIT Init\nNEXT Next\n", s0.clone()).unwrap();
    let reference = next_successors(ref_body, "INIT Init\nNEXT Next\n", s0).unwrap();
    assert_eq!(opt, reference);
    assert_eq!(opt.len(), 2);
}

#[test]
fn unassigned_primed_lhs_is_not_treated_as_guard() {
    let body = r#"
EXTENDS Integers
VARIABLE x, y
Init == x = {} /\ y = {}
Next ==
    /\ x' \in SUBSET {1, 2}
    /\ y' \subseteq x'
"#;
    let s0 = vec![Value::Set(Arc::from([])), Value::Set(Arc::from([]))];
    let succs = next_successors(body, "INIT Init\nNEXT Next\n", s0).unwrap();
    // |{(x', y') : y' \subseteq x' \subseteq {1,2}}| = 3^2 = 9.
    assert_eq!(succs.len(), 9);
}

#[test]
fn lower_bound_short_circuits_and_preserves_tlc_error_semantics() {
    // 1. Comparable lower bound not contained in U short-circuits immediately to 0 branches
    //    (without enumerating 2^30 and without evaluating the later erroring conjunct).
    let short_circuit = r#"
EXTENDS Integers
VARIABLE x
Init == x = {99}
Next == x' \in SUBSET (1..30) /\ x \subseteq x' /\ (1 \div 0 = 0)
"#;
    let succs = next_successors(short_circuit, "INIT Init\nNEXT Next\n", vec![Value::Set(vec![Value::Int(99)].into())]).unwrap();
    assert!(succs.is_empty());

    // 2. Incomparable element in L \not\subseteq U must still raise TLC's comparison error.
    let incomparable = r#"
EXTENDS Integers
VARIABLE x
Init == x = {"a"}
Next == x' \in SUBSET {1, 2} /\ x \subseteq x'
"#;
    let err =
        next_successors(incomparable, "INIT Init\nNEXT Next\n", vec![Value::Set(vec![Value::Str(Sym::new("a"))].into())]).unwrap_err();
    assert!(err.contains("compare"), "expected comparison error, got: {err}");

    // 3. Empty base U = {} with incomparable L: in TLC, `"a" \in {}` is FALSE with no error.
    let empty_base = r#"
EXTENDS Integers
VARIABLE x
Init == x = {"a"}
Next == x' \in SUBSET {} /\ x \subseteq x'
"#;
    let succs_empty =
        next_successors(empty_base, "INIT Init\nNEXT Next\n", vec![Value::Set(vec![Value::Str(Sym::new("a"))].into())]).unwrap();
    assert!(succs_empty.is_empty());

    // 4. Non-enumerable U must report the SUBSET non-enumerable error before touching L.
    let non_enum = r#"
EXTENDS Integers
VARIABLE x
Init == x = {1}
Next == x' \in SUBSET Nat /\ (1 \div 0) \subseteq x'
"#;
    let err_ne = next_successors(non_enum, "INIT Init\nNEXT Next\n", vec![Value::Set(vec![Value::Int(1)].into())]).unwrap_err();
    assert!(err_ne.contains("non-enumerable"), "expected non-enumerable error, got: {err_ne}");

    // 5. Non-set L must raise TLC's error rather than silently returning 0 branches.
    let non_set_l = r#"
EXTENDS Integers
VARIABLE x
Init == x = 42
Next == x' \in SUBSET {1, 2} /\ x \subseteq x'
"#;
    assert!(next_successors(non_set_l, "INIT Init\nNEXT Next\n", vec![Value::Int(42)]).is_err());

    // 6. Effectful L must NOT be hoisted out of the subset loop (4 subsets => 4 increments).
    let effectful_l = r#"
EXTENDS Integers, TLC
VARIABLE x
Init == x = {}
Next ==
    /\ TLCSet(9, 0)
    /\ x' \in SUBSET {1, 2}
    /\ (IF TLCSet(9, TLCGet(9) + 1) THEN {1} ELSE {1}) \subseteq x'
Check == TLCGet(9) = 4
"#;
    let model = load_model(effectful_l, "INIT Init\nNEXT Next\n");
    let mut count = 0;
    for a in model.actions() {
        model
            .ip
            .successors(&[Value::Set(Arc::from([]))], 0, a, &mut |_| {
                count += 1;
                Ok(true)
            })
            .unwrap();
    }
    assert_eq!(count, 2);
    let check_def = model.ip.root_def("Check").unwrap();
    let check_expr = tlx_sema::hir::Expr::new(ExprKind::Apply { op: OpRef::Def(check_def), args: vec![] }, Default::default());
    assert_eq!(model.ip.eval(&check_expr, &Env::default(), &Ctx::NONE).unwrap(), Value::Bool(true));
}

#[test]
fn quantifiers_prune_filtered_powersets_and_preserve_tlc_materialization_semantics() {
    let body = r#"
EXTENDS Integers, FiniteSets, TLC
Filtered == {R \in SUBSET (1..25) : \A r \in R : r <= 4}
ExWitness == \E R \in Filtered : 1 \in R
AllCounter == \A R \in Filtered : 1 \notin R
\* Effectful base must not skip side effects.
BadSet == {z \in SUBSET {1} : TLCSet(9, TLCGet(9) + 1) /\ z = {}}
EffBase == TLCSet(9, 0) /\ (\E S \in {S \in SUBSET {BadSet} : \A s \in S : {} \in s} : S = {}) /\ TLCGet(9) = 1
\* Predicate error on a later subset must still fire even when R = {} satisfies the body (TLC materializes SetPredValue bounds).
LatePredErr == \E R \in {R \in SUBSET {0, 1} : IF 0 \in R THEN (1 \div 0 = 0) ELSE TRUE} : R = {}
\* Unpruned huge filtered powerset must still hit -maxSetSize rather than bypassing it via early stop.
MaxSetErr == \E R \in {R \in SUBSET (1..25) : TRUE} : R = {}
"#;
    assert_eq!(eval_const(body, "", "ExWitness").unwrap(), Value::Bool(true));
    assert_eq!(eval_const(body, "", "AllCounter").unwrap(), Value::Bool(false));
    assert_eq!(eval_const(body, "", "EffBase").unwrap(), Value::Bool(true));
    assert!(eval_const(body, "", "LatePredErr").is_err(), "predicate error must not be swallowed");
    assert!(eval_const(body, "", "MaxSetErr").is_err(), "-maxSetSize must not be bypassed");

    // In model exploration, a predicate error in a quantifier bound must surface as Outcome::Error, not InvariantViolated.
    let err_model = r#"
EXTENDS Integers
VARIABLE x
D == {R \in SUBSET {0, 1} : IF 0 \in R THEN (1 \div 0 = 0) ELSE TRUE}
Init == x = 0
Next == \E R \in D : (R = {} /\ x' = 1)
Inv == x = 0
"#;
    let model = load_model(err_model, "INIT Init\nNEXT Next\nINVARIANT Inv\n");
    let res = explore(&model, &Options { workers: 1, ..Default::default() });
    assert!(matches!(res.outcome, Outcome::Error(_)), "expected Outcome::Error, got {:?}", res.outcome);
}

#[test]
fn primed_lazy_callable_and_let_captured_lazy_callable_preserve_effects() {
    // Finding 2: primed LazyFcn in s1 must NOT be hoisted out of `x' \in SUBSET {1, 2} /\ {f'[1]} \subseteq x'`.
    let primed_lazy = r#"
EXTENDS Integers, TLC
VARIABLES x, f
Init == x = {} /\ f = 0
Next ==
    /\ TLCSet(9, 0)
    /\ f' = [z \in Nat |-> IF TLCSet(9, TLCGet(9) + 1) THEN 1 ELSE 1]
    /\ x' \in SUBSET {1, 2}
    /\ {f'[1]} \subseteq x'
Count == TLCGet(9)
"#;
    let model = load_model(primed_lazy, "INIT Init\nNEXT Next\n");
    let mut succs = 0;
    for a in model.actions() {
        model
            .ip
            .successors(&[Value::Set(Arc::from([])), Value::Int(0)], 0, a, &mut |_| {
                succs += 1;
                Ok(true)
            })
            .unwrap();
    }
    assert_eq!(succs, 2);
    let cdef = model.ip.root_def("Count").unwrap();
    let cexpr = tlx_sema::hir::Expr::new(ExprKind::Apply { op: OpRef::Def(cdef), args: vec![] }, Default::default());
    assert_eq!(model.ip.eval(&cexpr, &Env::default(), &Ctx::NONE).unwrap(), Value::Int(4));

    // Finding 3: LazyFcn captured in env and invoked via a LET helper must NOT trigger FilterSet memoization.
    let let_lazy = r#"
EXTENDS Integers, FiniteSets, TLC
F == [z \in Nat |-> IF TLCSet(9, TLCGet(9) + 1) THEN z ELSE z]
TestStream(g) ==
    LET h(e) == g[e] = 1
        S == {R \in SUBSET {1, 2} : \A r \in R : h(r)}
    IN TLCSet(9, 0) /\ (\E R \in S : R = {}) /\ TLCGet(9) = 4
RunStream == TestStream(F)
Outer(g) ==
    LET h(e) == g[e] = 1
    IN {R \in SUBSET {1, 2} : \A r \in R : h(r)}
CheckTwice(S) == TLCSet(9, 0) /\ (Cardinality(S) = 2) /\ (Cardinality(S) = 2) /\ TLCGet(9) = 8
RunTwice == CheckTwice(Outer(F))
"#;
    assert_eq!(eval_const(let_lazy, "", "RunStream").unwrap(), Value::Bool(true));
    assert_eq!(eval_const(let_lazy, "", "RunTwice").unwrap(), Value::Bool(true));
}

#[test]
fn branching_forall_with_other_unassigned_vars_preserves_duplicate_transitions() {
    // Finding 4: `\A v \in x' : (v = 1 \/ v = 1)` while `y'` is unassigned must preserve TLC's 3 transitions.
    let body = r#"
EXTENDS Integers
VARIABLES x, y
Init == x = {} /\ y = 0
Next ==
    /\ x' \in SUBSET {1}
    /\ \A v \in x' : (v = 1 \/ v = 1)
    /\ y' = 1
"#;
    let s0 = vec![Value::Set(Arc::from([])), Value::Int(0)];
    let succs = next_successors(body, "INIT Init\nNEXT Next\n", s0).unwrap();
    assert_eq!(succs.len(), 3);
}

#[test]
fn primed_zero_arity_def_memo_reuses_loop_invariant_defs_and_preserves_effects() {
    // 1. Mini InnerSerial-shaped model: `totalOrder'` depends only on `n'` (not `rel'`),
    //    `rel' \in SUBSET (dom' \X dom') /\ rel \subseteq rel' /\ Valid'`.
    let body = r#"
EXTENDS Integers, FiniteSets
VARIABLE n, rel
Dom == 1..n
TotalOrders ==
    {R \in SUBSET (Dom \X Dom) :
        /\ \A a, b \in Dom : (a = b) \/ (<<a, b>> \in R) \/ (<<b, a>> \in R)
        /\ \A a, b, c \in Dom : (<<a, b>> \in R) /\ (<<b, c>> \in R) => (<<a, c>> \in R)
        /\ \A a \in Dom : <<a, a>> \notin R}
Valid == \E R \in TotalOrders : rel \subseteq R
Init == n = 1 /\ rel = {}
Next ==
    /\ n' \in {n, IF n < 3 THEN n + 1 ELSE n}
    /\ rel' \in SUBSET (Dom' \X Dom')
    /\ rel \subseteq rel'
    /\ Valid'
"#;
    let model = load_model(body, "INIT Init\nNEXT Next\n");
    let res = explore(&model, &Options { workers: 1, ..Default::default() });
    assert!(matches!(res.outcome, Outcome::Ok), "{:?}", res.outcome);
    // For n=1: 1 acyclic relation ({}); for n=2: 3 acyclic relations; for n=3: 25 acyclic relations.
    assert_eq!(res.stats.distinct, 1 + 3 + 25);

    // 2. Effectful 0-ary def (direct TLCSet, or through a constant LazyFcn) must NOT be memoized.
    let eff_body = r#"
EXTENDS Integers, TLC
VARIABLE x, y
F == [z \in Nat |-> IF TLCSet(9, TLCGet(9) + 1) THEN z ELSE z]
EffDirect == IF TLCSet(9, TLCGet(9) + 1) THEN x ELSE x
EffViaConstLazy == F[x]
Init == x = 1 /\ y = {}
NextDirect == x' = x /\ y' \in SUBSET {1, 2} /\ EffDirect' = 1
NextLazy == x' = x /\ y' \in SUBSET {1, 2} /\ EffViaConstLazy' = 1
Reset == TLCSet(9, 0)
Count == TLCGet(9)
"#;
    for (next_name, expected) in [("NextDirect", 4), ("NextLazy", 4)] {
        let m = load_model(eff_body, &format!("INIT Init\nNEXT {next_name}\n"));
        let rdef = m.ip.root_def("Reset").unwrap();
        let rexpr = tlx_sema::hir::Expr::new(ExprKind::Apply { op: OpRef::Def(rdef), args: vec![] }, Default::default());
        m.ip.eval(&rexpr, &Env::default(), &Ctx::NONE).unwrap();
        for a in m.actions() {
            m.ip.successors(&[Value::Int(1), Value::Set(Arc::from([]))], 0, a, &mut |_| Ok(true)).unwrap();
        }
        let cdef = m.ip.root_def("Count").unwrap();
        let cexpr = tlx_sema::hir::Expr::new(ExprKind::Apply { op: OpRef::Def(cdef), args: vec![] }, Default::default());
        assert_eq!(m.ip.eval(&cexpr, &Env::default(), &Ctx::NONE).unwrap(), Value::Int(expected), "{next_name}");
    }
}
