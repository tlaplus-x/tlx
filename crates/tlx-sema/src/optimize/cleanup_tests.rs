use super::analysis::AnalysisManager;
use super::constant::ConstantState;
use super::counter::CounterSaturation;
use super::dead::DeadActions;
use super::ir::*;
use super::passes::{Evidence, Pass, Pipeline, Proposal};
use super::simplify::SimplifyPredicates;
use super::{tests::model, verify};

fn propose(pass: &impl Pass, source: &Model) -> Proposal {
    pass.run(source, &mut AnalysisManager::default()).unwrap().unwrap()
}

#[test]
fn constants_require_induction_not_a_target_invariant() {
    let mut source = model();
    for a in &mut source.actions {
        a.updates[0] = Update::Keep;
    }
    let p = propose(&ConstantState, &source);
    verify::transformation(&source, &p).unwrap();
    assert_eq!(p.model.variables[0].domain, Domain::Constant(10));
    assert_eq!(p.model.properties[0].predicate, Predicate::Bool(false));
    // Neither x=10 in Init nor an invariant claiming x=10 proves that
    // increment or reset from 10 preserves it.
    for update in [Update::Increment, Update::Reset] {
        let mut changed = source.clone();
        changed.actions[0].updates[0] = update;
        assert!(verify::transformation(&changed, &p).is_err());
        assert!(ConstantState.run(&changed, &mut AnalysisManager::default()).unwrap().is_none());
    }
    source.initial[0] = 0;
    source.actions[0].updates[0] = Update::Reset;
    verify::transformation(&source, &propose(&ConstantState, &source)).unwrap();
}

#[test]
fn constant_evidence_cannot_change_other_semantics() {
    let mut source = model();
    for a in &mut source.actions {
        a.updates[0] = Update::Keep;
    }
    let mutations: &[fn(&mut Proposal)] = &[
        |p| p.evidence = Evidence::ConstantState { variables: vec![99] },
        |p| p.evidence = Evidence::ConstantState { variables: vec![0, 0] },
        |p| p.evidence = Evidence::ConstantState { variables: vec![] },
        |p| p.model.properties[0].predicate = Predicate::Bool(true),
        |p| p.model.properties[0].name = "other".into(),
        |p| p.model.actions.pop().map(|_| ()).unwrap(),
        |p| p.model.actions[0].guard = Predicate::Bool(false),
        |p| p.model.variables[0].domain = Domain::Interval(10),
    ];
    for mutate in mutations {
        let mut p = propose(&ConstantState, &source);
        mutate(&mut p);
        assert!(verify::transformation(&source, &p).is_err());
    }
}

#[test]
fn saturated_representatives_are_not_reported_as_exact_constants() {
    let mut source = model();
    source.properties[0].predicate = Predicate::Bool(true);
    let p = propose(&CounterSaturation, &source);
    assert_eq!(p.model.variables[0].domain, Domain::Interval(0));
    assert!(ConstantState.run(&p.model, &mut AnalysisManager::default()).unwrap().is_none());
    let mut forged = p.model.clone();
    forged.variables[0].domain = Domain::Constant(0);
    for a in &mut forged.actions {
        a.updates[0] = Update::Keep;
    }
    assert!(
        verify::transformation(&p.model, &Proposal { model: forged, evidence: Evidence::ConstantState { variables: vec![0] } }).is_err()
    );
}

#[test]
fn dead_action_evidence_cannot_remove_live_actions_or_reorder_them() {
    let mut source = model();
    source.actions[0].guard = Predicate::Bool(false);
    let good = propose(&DeadActions, &source);
    verify::transformation(&source, &good).unwrap();
    let mutations: &[fn(&mut Proposal)] = &[
        |p| {
            p.model.actions.pop();
            p.evidence = Evidence::DeadActions { retained: vec![1] };
        },
        |p| {
            p.model.actions.swap(0, 1);
            p.evidence = Evidence::DeadActions { retained: vec![2, 1] };
        },
        |p| p.evidence = Evidence::DeadActions { retained: vec![1, 99] },
        |p| p.model.actions[0].updates[0] = Update::Increment,
        |p| p.model.properties[0].predicate = Predicate::Bool(true),
    ];
    for mutate in mutations {
        let mut p = propose(&DeadActions, &source);
        mutate(&mut p);
        assert!(verify::transformation(&source, &p).is_err());
    }
    for a in &mut source.actions {
        a.guard = Predicate::Bool(false);
    }
    let p = propose(&DeadActions, &source);
    verify::transformation(&source, &p).unwrap();
    assert!(p.model.actions.is_empty());
}

fn eval(p: &Predicate, value: u64) -> bool {
    match p {
        Predicate::Bool(b) => *b,
        Predicate::Compare { op, value: n, .. } => op.test(value, (*n).into()),
        Predicate::Not(p) => !eval(p, value),
        Predicate::And(ps) => ps.iter().all(|p| eval(p, value)),
        Predicate::Or(ps) => ps.iter().any(|p| eval(p, value)),
    }
}

#[test]
fn simplified_predicates_preserve_boundary_and_interior_truth() {
    for domain in [Domain::Natural, Domain::Interval(4), Domain::Constant(2)] {
        for op in [Comparison::Eq, Comparison::Ne, Comparison::Lt, Comparison::Le, Comparison::Gt, Comparison::Ge] {
            for value in 0..7 {
                let mut source = model();
                source.variables[0].domain = domain.clone();
                source.initial[0] = if domain == Domain::Constant(2) { 2 } else { 0 };
                for a in &mut source.actions {
                    a.updates[0] = Update::Keep;
                }
                let comparison = Predicate::Compare { var: 0, op, value };
                source.properties[0].predicate =
                    Predicate::And(vec![Predicate::Bool(true), Predicate::Or(vec![Predicate::Bool(false), comparison])]);
                let p = propose(&SimplifyPredicates, &source);
                verify::transformation(&source, &p).unwrap();
                for state in 0..9 {
                    if match domain {
                        Domain::Natural => true,
                        Domain::Interval(n) => state <= n.into(),
                        Domain::Constant(n) => state == n.into(),
                    } {
                        assert_eq!(eval(&source.properties[0].predicate, state), eval(&p.model.properties[0].predicate, state));
                    }
                }
            }
        }
    }
}

#[test]
fn simplification_checker_rejects_an_interior_equality_fold_and_unrelated_edits() {
    let mut source = model();
    source.variables[0].domain = Domain::Interval(4);
    source.initial[0] = 0;
    for a in &mut source.actions {
        a.updates[0] = Update::Keep;
    }
    source.properties[0].predicate = Predicate::Compare { var: 0, op: Comparison::Eq, value: 2 };
    let mut bad = source.clone();
    bad.properties[0].predicate = Predicate::Bool(false); // False at both endpoints, true at 2.
    assert!(verify::transformation(&source, &Proposal { model: bad, evidence: Evidence::SimplifyPredicates }).is_err());
    let mut p = propose(&SimplifyPredicates, &source);
    p.model.initial[0] = 1;
    assert!(verify::transformation(&source, &p).is_err());
}

#[test]
fn cleanup_reaches_a_fixed_point_before_saturation_and_invalidates_facts() {
    let mut source = model();
    // First remove the only increment, then discover that the zero counter
    // is constant under reset/keep. No target property is assumed.
    source.initial[0] = 0;
    source.actions[0].guard = Predicate::Compare { var: 0, op: Comparison::Lt, value: 0 };
    let mut cache = AnalysisManager::default();
    assert!(cache.constants(&source).is_empty());
    let (result, remarks) = Pipeline::default().run(source.clone()).unwrap();
    assert_eq!(result.variables[0].domain, Domain::Constant(0));
    assert_eq!(result.properties[0].predicate, Predicate::Bool(true));
    assert!(remarks.iter().any(|r| r.starts_with("dead-action-elimination/")));
    assert!(remarks.iter().any(|r| r.starts_with("constant-state-propagation/")));
    source.actions.remove(0);
    cache.invalidate();
    assert_eq!(cache.constants(&source), &[0]);
}

#[test]
fn cascading_constants_converge_or_refuse_at_the_stage_budget() {
    for count in [3, 66] {
        let mut source = model();
        let variable = source.variables[0].clone();
        let action = source.actions[0].clone();
        source.variables = (0..count).map(|i| Variable { name: format!("x{i}"), ..variable.clone() }).collect();
        source.initial = vec![0; count];
        // x0 is fixed. Once xi is proved zero, the only increment of
        // x(i+1) becomes unreachable, exposing the next singleton.
        source.actions = (1..count)
            .map(|i| {
                let mut updates = vec![Update::Keep; count];
                updates[i] = Update::Increment;
                Action { guard: Predicate::Compare { var: i - 1, op: Comparison::Eq, value: 1 }, updates, ..action.clone() }
            })
            .collect();
        let result = Pipeline::default().run(source);
        if count == 3 {
            let (model, _) = result.unwrap();
            assert!(model.variables.iter().all(|v| v.domain == Domain::Constant(0)));
            assert!(model.actions.is_empty());
        } else {
            let error = result.unwrap_err();
            assert!(error.message.contains("did not converge within 64 rounds"), "{error:?}");
        }
    }
}
