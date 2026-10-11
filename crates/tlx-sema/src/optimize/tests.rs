use super::analysis::AnalysisManager;
use super::counter::CounterSaturation;
use super::ir::*;
use super::passes::{Evidence, Pass, Pipeline, Proposal};
use super::{lower, verify};

pub(super) fn model() -> Model {
    let dir = tlx_testkit::TempDir::new("abstraction-validator");
    let path = dir.write("M.tla", "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE c\nInit == c = 10\nNext == c' = c + 1 \\/ c' = 0 \\/ UNCHANGED c\nInv == c <= 3\n====\n");
    let mut program = crate::Program::load(&path, &[]).unwrap();
    let cfg = tlx_front::cfg::parse_cfg("INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n").unwrap();
    lower::lower(&mut program, &cfg).unwrap()
}

fn proposal(model: &Model) -> Proposal {
    CounterSaturation.run(model, &mut AnalysisManager::default()).unwrap().unwrap()
}

#[test]
fn corrupted_evidence_and_each_rewrite_component_are_rejected() {
    let original = model();
    verify::transformation(&original, &proposal(&original)).unwrap();
    let mutations: &[fn(&mut Proposal)] = &[
        |p| p.evidence = Evidence::CounterSaturation { caps: vec![2] },
        |p| p.evidence = Evidence::CounterSaturation { caps: vec![] },
        |p| p.model.actions.clear(),
        |p| {
            p.model.actions.pop();
        },
        |p| p.model.actions[0].updates[0] = Update::Reset,
        |p| p.model.actions[0].updates.clear(),
        |p| p.model.actions[0].guard = Predicate::Bool(false),
        |p| p.model.properties[0].predicate = Predicate::Bool(true),
        |p| p.model.properties[0].name = "Different".to_string(),
        |p| p.model.initial[0] = 0,
        |p| p.model.variables[0].domain = Domain::Natural,
        |p| p.model.variables[0].name = "Different".to_string(),
        |p| p.model.properties[0].predicate = Predicate::Compare { var: 99, op: Comparison::Ge, value: 0 },
    ];
    for mutate in mutations {
        let mut proposed = proposal(&original);
        mutate(&mut proposed);
        assert!(verify::transformation(&original, &proposed).is_err());
    }
}

#[test]
fn internally_consistent_but_insufficient_partition_is_rejected() {
    let original = model();
    let mut proposed = proposal(&original);
    proposed.evidence = Evidence::CounterSaturation { caps: vec![3] };
    proposed.model.variables[0].domain = Domain::Interval(3);
    proposed.model.initial[0] = 3;
    proposed.model.actions[0].updates[0] = Update::SaturatingIncrement(3);
    verify::well_formed(&proposed.model).unwrap();
    assert!(verify::transformation(&original, &proposed).is_err());
}

#[test]
fn changed_source_or_property_cannot_reuse_an_old_proposal() {
    let mut original = model();
    let proposed = proposal(&original);
    original.properties[0].predicate = Predicate::Compare { var: 0, op: Comparison::Eq, value: 7 };
    assert!(verify::transformation(&original, &proposed).is_err());
    let mut original = model();
    original.actions[0].updates[0] = Update::Keep;
    assert!(verify::transformation(&original, &proposed).is_err());
}

#[test]
fn analysis_invalidation_recomputes_changed_observations() {
    let mut original = model();
    let mut analyses = AnalysisManager::default();
    assert_eq!(analyses.thresholds(&original), &[4]);
    original.properties[0].predicate = Predicate::Compare { var: 0, op: Comparison::Gt, value: 12 };
    analyses.invalidate();
    assert_eq!(analyses.thresholds(&original), &[13]);
}

#[test]
fn pipeline_is_idempotent_and_requires_finite_closure() {
    let original = model();
    assert!(verify::finite(&original).is_err());
    let (once, remarks) = Pipeline::default().run(original).unwrap();
    assert_eq!(remarks.iter().filter(|r| r.starts_with("threshold-counter-saturation/")).count(), 1);
    verify::finite(&once).unwrap();
    let (twice, remarks) = Pipeline::default().run(once.clone()).unwrap();
    assert!(remarks.is_empty());
    assert_eq!(once, twice);
}

#[test]
fn pass_manager_composes_passes_and_refuses_a_bad_proposal() {
    struct BadPass;
    impl Pass for BadPass {
        fn name(&self) -> &'static str {
            "bad-pass"
        }
        fn run(&self, model: &Model, _: &mut AnalysisManager) -> Result<Option<Proposal>, super::Diagnostic> {
            let mut p = proposal(model);
            p.model.actions[0].guard = Predicate::Bool(false);
            Ok(Some(p))
        }
    }
    let original = model();
    assert!(Pipeline::new(vec![Box::new(BadPass)]).run(original.clone()).is_err());
    let (finite, remarks) = Pipeline::new(vec![Box::new(CounterSaturation), Box::new(CounterSaturation)]).run(original).unwrap();
    verify::finite(&finite).unwrap();
    assert_eq!(remarks.len(), 1);
}

#[test]
fn counter_rule_commutes_with_updates_and_preserves_observations_at_boundaries() {
    // Finite regression vectors exercise the implementation; the general
    // algebraic argument is documented separately, never inferred from them.
    for op in [Comparison::Eq, Comparison::Ne, Comparison::Lt, Comparison::Le, Comparison::Gt, Comparison::Ge] {
        for value in 0..5 {
            let mut original = model();
            original.properties[0].predicate = Predicate::Compare { var: 0, op, value };
            let proposed = proposal(&original);
            verify::transformation(&original, &proposed).unwrap();
            let Evidence::CounterSaturation { caps } = proposed.evidence else { panic!("wrong evidence kind") };
            let cap = u64::from(caps[0]);
            for concrete in 0..12u64 {
                let abstract_value = concrete.min(cap);
                assert_eq!(op.test(concrete, value.into()), op.test(abstract_value, value.into()));
                for (source, target) in original.actions.iter().zip(&proposed.model.actions) {
                    let concrete_next = match source.updates[0] {
                        Update::Keep => concrete,
                        Update::Reset => 0,
                        Update::Increment => concrete + 1,
                        _ => panic!("unexpected source"),
                    };
                    let abstract_next = match target.updates[0] {
                        Update::Keep => abstract_value,
                        Update::Reset => 0,
                        Update::SaturatingIncrement(k) => {
                            if abstract_value < k.into() {
                                abstract_value + 1
                            } else {
                                k.into()
                            }
                        }
                        _ => panic!("unexpected target"),
                    };
                    assert_eq!(concrete_next.min(cap), abstract_next);
                }
            }
        }
    }
}
