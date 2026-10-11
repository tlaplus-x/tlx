//! Replace observations of inductively constant state by their truth values.

use super::analysis::AnalysisManager;
use super::ir::{Domain, Model, Predicate, Update};
use super::passes::{Evidence, Pass, Proposal};
use super::Diagnostic;

pub(super) struct ConstantState;

impl Pass for ConstantState {
    fn name(&self) -> &'static str {
        "constant-state-propagation/v1"
    }

    fn run(&self, model: &Model, analyses: &mut AnalysisManager) -> Result<Option<Proposal>, Diagnostic> {
        let variables = analyses.constants(model).to_vec();
        let mut result = model.clone();
        let mut values = vec![None; model.variables.len()];
        for &i in &variables {
            values[i] = Some(model.initial[i]);
            result.variables[i].domain = Domain::Constant(model.initial[i]);
            for action in &mut result.actions {
                action.updates[i] = Update::Keep;
            }
        }
        for action in &mut result.actions {
            action.guard = substitute(&action.guard, &values);
        }
        for property in &mut result.properties {
            property.predicate = substitute(&property.predicate, &values);
        }
        Ok((result != *model).then_some(Proposal { model: result, evidence: Evidence::ConstantState { variables } }))
    }
}

fn substitute(predicate: &Predicate, values: &[Option<u32>]) -> Predicate {
    match predicate {
        Predicate::Compare { var, op, value } => match values[*var] {
            Some(n) => Predicate::Bool(op.test(n.into(), (*value).into())),
            None => predicate.clone(),
        },
        Predicate::Bool(_) => predicate.clone(),
        Predicate::Not(p) => Predicate::Not(Box::new(substitute(p, values))),
        Predicate::And(ps) => Predicate::And(ps.iter().map(|p| substitute(p, values)).collect()),
        Predicate::Or(ps) => Predicate::Or(ps.iter().map(|p| substitute(p, values)).collect()),
    }
}
