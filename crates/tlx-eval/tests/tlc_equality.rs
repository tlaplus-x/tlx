//! Regression tests for fallible `eq_tlc` equality, `SeqPred` prefix filters,
//! liveness `WF`/`SF` uncovered enabledness, `Steps` BFS level threading, and
//! action composition `A \cdot B` with `InstVar` slots.

use tlx_eval::model::liveness::StateAtom;
use tlx_eval::{Interp, InterpModel};
use tlx_runtime::{explore, Options, Outcome};
use tlx_sema::Program;
use tlx_value::Value;

fn build_model(name: &str, body: &str, cfg_src: &str) -> Result<InterpModel, String> {
    let dir = tlx_testkit::TempDir::new("tlc-eq");
    let path = dir.write(&format!("{name}.tla"), &tlx_testkit::module(name, body));
    let prog = Program::load(&path, &[]).map_err(|e| format!("{e:?}"))?;
    let cfg = tlx_front::cfg::parse_cfg(cfg_src).map_err(|e| format!("{e:?}"))?;
    let ip = Interp::new(prog, cfg).map_err(|e| e.to_string())?;
    InterpModel::new(ip).map_err(|e| e.to_string())
}

fn run_model(name: &str, body: &str, cfg_src: &str) -> Result<Outcome, String> {
    let model = build_model(name, body, cfg_src)?;
    let opts = Options { check_deadlock: model.check_deadlock, ..Default::default() };
    Ok(explore(&model, &opts).outcome)
}

fn run_multi(modules: &[(&str, &str)], main: &str, cfg_src: &str) -> Result<Outcome, String> {
    let dir = tlx_testkit::TempDir::new("tlc-eq-multi");
    let mut main_path = None;
    for (name, body) in modules {
        let p = dir.write(&format!("{name}.tla"), &tlx_testkit::module(name, body));
        if *name == main {
            main_path = Some(p);
        }
    }
    let path = main_path.expect("main module present");
    let prog = Program::load(&path, &[dir.path().to_path_buf()]).map_err(|e| format!("{e:?}"))?;
    let cfg = tlx_front::cfg::parse_cfg(cfg_src).map_err(|e| format!("{e:?}"))?;
    let ip = Interp::new(prog, cfg).map_err(|e| e.to_string())?;
    let model = InterpModel::new(ip).map_err(|e| e.to_string())?;
    let opts = Options { check_deadlock: model.check_deadlock, ..Default::default() };
    Ok(explore(&model, &opts).outcome)
}

#[test]
fn seq_filter_lazy_value_does_not_panic() {
    let body = "\
EXTENDS Naturals
VARIABLE x
Op(f, g) == {s \\in [1..2 -> 1..5] : (IF s[1] = 1 THEN f ELSE g) \\in {}}
Init == x = Op([n \\in Nat |-> n], [n \\in Nat |-> n + 1])
Next == UNCHANGED x
Inv == x = {}
";
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    let outcome = run_model("SeqFilterPanic", body, cfg).unwrap();
    assert!(matches!(outcome, Outcome::Ok), "expected Ok, got {outcome:?}");
}

#[test]
fn seq_filter_short_circuits_singleton_unknown_boolean() {
    let body = "\
EXTENDS Naturals, FiniteSets
VARIABLES a, b
Init ==
  /\\ a = {s \\in [1..2 -> 1..5] : s[1] = 99 /\\ (1 = \"a\")}
  /\\ b = {s \\in [1..2 -> 1..5] : s[1] < 10 \\/ (1 = \"a\")}
Next == UNCHANGED <<a, b>>
Inv == a = {} /\\ Cardinality(b) = 25
";
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    let outcome = run_model("SeqFilterShortCircuit", body, cfg).unwrap();
    assert!(matches!(outcome, Outcome::Ok), "expected Ok, got {outcome:?}");
}

#[test]
fn fair_uncovered_uses_pred_atom_and_reports_enabled() {
    let body = "\
VARIABLES x, y
Keep(v) == UNCHANGED v
Init == x = 0 /\\ y = 0
Next == UNCHANGED <<x, y>>
A == x' = 1 /\\ Keep(y)
Spec == Init /\\ [][Next]_<<x, y>>
Prop == WF_<<x, y>>(A)
";
    let cfg = "SPECIFICATION Spec\nPROPERTY Prop\n";
    let model = build_model("FairUncovered", body, cfg).unwrap();
    assert!(model.live.state_atoms.iter().all(|a| matches!(a, StateAtom::Pred(_))), "uncovered fairness action must not use EnabledVia");
    let s = [Value::Int(0), Value::Int(0)];
    // Even with no outgoing Next edges satisfying <<A>>_<<x, y>>, ENABLED <<A>>_<<x, y>> is TRUE.
    let bits = model.live.state_bits(&model.ip, &s, 1, &[]).unwrap();
    assert_eq!(bits, [1]);
}

#[test]
fn fair_uncovered_primed_expr_uses_pred_atom_and_reports_enabled() {
    let body = "\
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == UNCHANGED x
A == x' = 1 /\\ (x + 1)' = 2
Spec == Init /\\ [][Next]_x
Prop == WF_x(A)
";
    let cfg = "SPECIFICATION Spec\nPROPERTY Prop\n";
    let model = build_model("FairUncoveredPrimed", body, cfg).unwrap();
    assert!(
        model.live.state_atoms.iter().all(|a| matches!(a, StateAtom::Pred(_))),
        "uncovered fairness action with primed expr must not use EnabledVia"
    );
    let s = [Value::Int(0)];
    let bits = model.live.state_bits(&model.ip, &s, 1, &[]).unwrap();
    assert_eq!(bits, [1]);
}

#[test]
fn liveness_subscript_lazy_fcn_and_type_mismatch_return_eval_error() {
    // Subscript with unmaterializable lazy function (both constant and state-dependent).
    let body_lazy = "\
EXTENDS Naturals
VARIABLE x
Init == x = 1
Next == UNCHANGED x
Spec == Init /\\ [][Next]_x /\\ WF_<<x, [n \\in Nat |-> n]>>(Next)
Prop == <>(x = 2)
";
    let cfg = "SPECIFICATION Spec\nPROPERTY Prop\n";
    let m_lazy = build_model("SubscriptPanic", body_lazy, cfg).unwrap();
    let s = [Value::Int(1)];
    assert!(m_lazy.live.action_bits(&m_lazy.ip, &s, &s, 1).is_err(), "expected lazy subscript comparison error");

    let body_lazy_distinct = "\
EXTENDS Naturals
VARIABLE x
Init == x = 1
Next == x' = 3 - x
Spec == Init /\\ [][Next]_x /\\ WF_<<[n \\in Nat |-> n + x], x>>(Next)
Prop == <>(x = 2)
";
    let m_lazy_d = build_model("SubscriptPanicDistinct", body_lazy_distinct, cfg).unwrap();
    let s2 = [Value::Int(2)];
    assert!(m_lazy_d.live.action_bits(&m_lazy_d.ip, &s, &s2, 1).is_err(), "expected distinct lazy subscript comparison error");

    // Covered subscript type mismatch (step_atom path).
    let body_covered = "\
VARIABLE x
Init == x = 1
Next == IF x = 1 THEN x' = \"a\" ELSE UNCHANGED x
Spec == Init /\\ [][Next]_x /\\ WF_x(Next)
Prop == <>(x = \"a\")
";
    let m_cov = build_model("SubscriptTypeMismatchCovered", body_covered, cfg).unwrap();
    let t = [Value::Str(tlx_value::Sym::new("a"))];
    assert!(m_cov.live.action_bits(&m_cov.ip, &s, &t, 1).is_err(), "expected covered subscript type mismatch error");

    // Uncovered subscript type mismatch (Steps::angle and Steps::enabled paths).
    let body_uncov = "\
VARIABLE x
Init == x = 1
Next == UNCHANGED x
A == x = 1 /\\ x' = \"a\"
Spec == Init /\\ [][Next]_x
Prop == WF_x(A)
";
    let m_uncov = build_model("SubscriptTypeMismatchUncovered", body_uncov, cfg).unwrap();
    assert!(m_uncov.live.action_bits(&m_uncov.ip, &s, &t, 1).is_err(), "expected uncovered angle subscript type mismatch error");
    assert!(m_uncov.live.state_bits(&m_uncov.ip, &s, 1, &[]).is_err(), "expected uncovered enabled subscript type mismatch error");
}

#[test]
fn compose_inside_enabled_preserves_inst_var_slots() {
    // ENABLED inside an instantiated module with an expression substitution creates
    // InstVar slots; action composition A \cdot B must preserve those slots and
    // compare pre-assigned InstVar values with eq_tlc.
    let sub = "\
EXTENDS Naturals
VARIABLES u, v
A == u' = u + 1 /\\ UNCHANGED v
B == v' = 2
CanCompose == ENABLED (A \\cdot B)
PreAssignedAgree == ENABLED (v' = 2 /\\ (A \\cdot B))
PreAssignedClash == ENABLED (v' = 3 /\\ (A \\cdot B))
PostAssigned == ENABLED ((A \\cdot (u' = u)) /\\ v' = 2)
";
    let main = "\
EXTENDS Naturals
VARIABLE x
I == INSTANCE Sub WITH u <- x + 1, v <- x + 10
Init == x = 0
Next == UNCHANGED x
Inv ==
  /\\ I!CanCompose
  /\\ I!PreAssignedAgree
  /\\ ~I!PreAssignedClash
  /\\ I!PostAssigned
";
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    let outcome = run_multi(&[("Sub", sub), ("Main", main)], "Main", cfg).unwrap();
    assert!(matches!(outcome, Outcome::Ok), "expected Ok, got {outcome:?}");
}

#[test]
fn compose_preassigned_var_uses_eq_tlc() {
    let body = "\
VARIABLE x
Init == x = 0
Next == x' = 1 /\\ ((UNCHANGED x) \\cdot (x' = \"a\"))
";
    let cfg = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";
    let outcome = run_model("ComposeTypeMismatch", body, cfg).unwrap();
    assert!(matches!(outcome, Outcome::Error(_)), "expected Error, got {outcome:?}");

    let body_lazy = "\
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = [n \\in Nat |-> n] /\\ ((UNCHANGED x) \\cdot (x' = [n \\in Nat |-> n + 1]))
";
    let outcome_lazy = run_model("ComposeLazyConflict", body_lazy, cfg).unwrap();
    assert!(matches!(outcome_lazy, Outcome::Error(_)), "expected Error, got {outcome_lazy:?}");
}
