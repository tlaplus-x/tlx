//! Threshold-counter saturation v1. The verifier owns the proof conditions;
//! this module only chooses parameters and proposes the rewrite.

use super::analysis::AnalysisManager;
use super::ir::{Domain, Model, Update};
use super::passes::{Evidence, Pass, Proposal};
use super::Diagnostic;

pub(super) struct CounterSaturation;

impl Pass for CounterSaturation {
    fn name(&self) -> &'static str {
        "threshold-counter-saturation/v1"
    }

    fn run(&self, model: &Model, analyses: &mut AnalysisManager) -> Result<Option<Proposal>, Diagnostic> {
        if model.variables.iter().all(|v| v.domain != Domain::Natural) {
            return Ok(None);
        }
        let caps: Vec<u32> = analyses
            .thresholds(model)
            .iter()
            .enumerate()
            .map(|(i, &cap)| {
                if let Domain::Constant(value) | Domain::Interval(value) = model.variables[i].domain {
                    return Ok(value);
                }
                u32::try_from(cap)
                    .ok()
                    .filter(|&cap| cap <= i32::MAX as u32)
                    .ok_or_else(|| Diagnostic::new("threshold partition exceeds the generated backend's integer range"))
            })
            .collect::<Result<_, _>>()?;
        let mut result = model.clone();
        for (i, &cap) in caps.iter().enumerate() {
            if model.variables[i].domain != Domain::Natural {
                continue;
            }
            result.variables[i].domain = Domain::Interval(cap);
            result.initial[i] = result.initial[i].min(cap);
            for action in &mut result.actions {
                if action.updates[i] == Update::Increment {
                    action.updates[i] = Update::SaturatingIncrement(cap);
                }
            }
        }
        Ok(Some(Proposal { model: result, evidence: Evidence::CounterSaturation { caps } }))
    }
}
