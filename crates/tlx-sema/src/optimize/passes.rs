//! Transactional pass manager: propose -> verify -> commit -> invalidate.

use super::analysis::AnalysisManager;
use super::counter::CounterSaturation;
use super::ir::Model;
use super::{verify, Diagnostic};

/// A rule-specific certificate, checked against both actual IR versions.
pub(super) enum Evidence {
    CounterSaturation { caps: Vec<u32> },
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
    passes: Vec<Box<dyn Pass>>,
}

impl Default for Pipeline {
    fn default() -> Self {
        Self::new(vec![Box::new(CounterSaturation)])
    }
}

impl Pipeline {
    pub fn new(passes: Vec<Box<dyn Pass>>) -> Self {
        Self { passes }
    }

    pub fn run(&self, mut model: Model) -> Result<(Model, Vec<String>), Diagnostic> {
        verify::well_formed(&model)?;
        let mut analyses = AnalysisManager::default();
        let mut remarks = Vec::new();
        for pass in &self.passes {
            if let Some(proposal) = pass.run(&model, &mut analyses)? {
                verify::transformation(&model, &proposal)?;
                model = proposal.model;
                analyses.invalidate();
                remarks.push(format!("{}: applicability and rewrite validated", pass.name()));
            }
        }
        Ok((model, remarks))
    }
}
