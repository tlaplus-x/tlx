//! Analyses are scoped to a pipeline invocation. A committed mutation
//! invalidates all cached results; passes cannot claim preservation themselves.

use super::ir::{Comparison, Model};

#[derive(Default)]
pub(super) struct AnalysisManager {
    thresholds: Option<Vec<u64>>,
}

impl AnalysisManager {
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
    }
}
