//! Transactional pass manager: propose -> verify -> commit -> invalidate.

use super::analysis::AnalysisManager;
use super::constant::ConstantState;
use super::counter::CounterSaturation;
use super::dead::DeadActions;
use super::ir::Model;
use super::simplify::SimplifyPredicates;
use super::{verify, Diagnostic};

/// A rule-specific certificate, checked against both actual IR versions.
pub(super) enum Evidence {
    CounterSaturation { caps: Vec<u32> },
    ConstantState { variables: Vec<usize> },
    SimplifyPredicates,
    DeadActions { retained: Vec<usize> },
}

pub(super) struct Proposal {
    pub model: Model,
    pub evidence: Evidence,
}

/// New transforms implement this interface and register in the pipeline.
/// A pass never mutates the current model or authorizes its own result.
pub(super) trait Pass {
    fn name(&self) -> &'static str;
    fn run(&self, model: &Model, analyses: &mut AnalysisManager) -> Result<Option<Proposal>, Diagnostic>;
}

pub(super) struct Pipeline {
    stages: Vec<Vec<Box<dyn Pass>>>,
}

impl Default for Pipeline {
    fn default() -> Self {
        Self {
            stages: vec![
                vec![Box::new(ConstantState), Box::new(SimplifyPredicates), Box::new(DeadActions)],
                vec![Box::new(CounterSaturation), Box::new(SimplifyPredicates), Box::new(DeadActions)],
            ],
        }
    }
}

impl Pipeline {
    /// Concrete-state-preserving rules only. Saturation requires a separate
    /// verdict/trace transfer contract and must not enter ordinary checking.
    pub fn exact() -> Self {
        Self { stages: vec![vec![Box::new(ConstantState), Box::new(SimplifyPredicates), Box::new(DeadActions)]] }
    }

    #[cfg(test)]
    pub fn new(passes: Vec<Box<dyn Pass>>) -> Self {
        Self { stages: vec![passes] }
    }

    pub fn run(&self, mut model: Model) -> Result<(Model, Vec<String>), Diagnostic> {
        verify::well_formed(&model)?;
        let mut analyses = AnalysisManager::default();
        let mut remarks = Vec::new();
        // Cleanup can expose another constant after deleting an impossible
        // action. Bound convergence so an oscillating future pass cannot hang.
        for stage in &self.stages {
            let mut converged = false;
            for _ in 0..64 {
                let mut changed = false;
                for pass in stage {
                    if let Some(proposal) = pass.run(&model, &mut analyses)? {
                        verify::transformation(&model, &proposal)?;
                        if proposal.model != model {
                            model = proposal.model;
                            analyses.invalidate();
                            changed = true;
                            remarks.push(format!("{}: applicability and rewrite validated", pass.name()));
                        }
                    }
                }
                if !changed {
                    converged = true;
                    break;
                }
            }
            if !converged {
                return Err(Diagnostic::new("optimization stage did not converge within 64 rounds"));
            }
        }
        Ok((model, remarks))
    }
}
