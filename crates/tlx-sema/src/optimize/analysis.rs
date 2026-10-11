//! Analyses are scoped to a pipeline invocation. A committed mutation
//! invalidates all cached results; passes cannot claim preservation themselves.

use super::ir::{Comparison, Domain, Model, Update};

#[derive(Default)]
pub(super) struct AnalysisManager {
    thresholds: Option<Vec<u64>>,
    constants: Option<Vec<usize>>,
}

impl AnalysisManager {
    pub fn constants(&mut self, model: &Model) -> &[usize] {
        self.constants.get_or_insert_with(|| {
            (0..model.variables.len())
                .filter(|&i| {
                    !matches!(model.variables[i].domain, Domain::Interval(_))
                        && model.actions.iter().all(|a| match a.updates[i] {
                            Update::Keep => true,
                            Update::Reset => model.initial[i] == 0,
                            Update::SaturatingIncrement(_) => false,
                            Update::Increment => false,
                        })
                })
                .collect()
        })
    }

    pub fn thresholds(&mut self, model: &Model) -> &[u64] {
        self.thresholds.get_or_insert_with(|| {
            let mut limits = vec![0; model.variables.len()];
            model.observations(&mut |var, op, value| {
                let boundary =
                    u64::from(value) + u64::from(matches!(op, Comparison::Eq | Comparison::Ne | Comparison::Le | Comparison::Gt));
                limits[var] = limits[var].max(boundary);
            });
            limits
        })
    }

    pub fn invalidate(&mut self) {
        self.thresholds = None;
        self.constants = None;
    }
}
