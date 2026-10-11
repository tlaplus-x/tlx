//! Delete actions whose simplified guards are FALSE; retain source order.

use super::analysis::AnalysisManager;
use super::ir::{Model, Predicate};
use super::passes::{Evidence, Pass, Proposal};
use super::Diagnostic;

pub(super) struct DeadActions;

impl Pass for DeadActions {
    fn name(&self) -> &'static str {
        "dead-action-elimination/v1"
    }

    fn run(&self, model: &Model, _: &mut AnalysisManager) -> Result<Option<Proposal>, Diagnostic> {
        let retained: Vec<_> =
            model.actions.iter().enumerate().filter_map(|(i, a)| (a.guard != Predicate::Bool(false)).then_some(i)).collect();
        if retained.len() == model.actions.len() {
            return Ok(None);
        }
        let mut result = model.clone();
        result.actions = retained.iter().map(|&i| model.actions[i].clone()).collect();
        Ok(Some(Proposal { model: result, evidence: Evidence::DeadActions { retained } }))
    }
}
