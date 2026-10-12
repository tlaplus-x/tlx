//! Rule-based state reduction on HIR and a restricted transition IR.
//!
//! Checking uses a proved projection of concrete states. Artifact generation
//! cleans up the transition IR before mathematical counter saturation.
//! See docs/optimization.md for the preservation contracts and trust boundary.

mod analysis;
mod lean;
mod phase;
mod projection;

pub use lean::projection_lean;
pub use phase::{
    age_projection, history_projection, ordered_projection, phase_projection, sequence_length_projection, symmetry_certificate,
    symmetry_projection_certificate, unobserved_projection, FieldProjection, OrderedHistory, OrderedPlan, OrderedShape,
};
pub use projection::unobserved_variables;
mod certify;
mod constant;
mod counter;
mod dead;
mod emit;
mod ir;
mod lower;
mod passes;
mod simplify;
mod verify;
mod verify_cleanup;

#[cfg(test)]
mod cleanup_tests;
#[cfg(test)]
mod tests;

use crate::hir::Span;
use crate::Program;
use tlx_front::cfg::Config;

/// A refusal to translate or validate, retaining its source location.
#[derive(Clone, Debug)]
pub struct Diagnostic {
    pub span: Option<Span>,
    pub message: String,
}

impl Diagnostic {
    fn new(message: impl Into<String>) -> Self {
        Self { span: None, message: message.into() }
    }

    fn at(span: Span, message: impl Into<String>) -> Self {
        Self { span: Some(span), message: message.into() }
    }
}

/// Generated artifacts, constructed only after every pass and finite domain
/// has been validated. The report is explanatory, not a reusable proof token.
#[derive(Debug)]
pub struct Artifact {
    pub module: String,
    pub config: String,
    pub report: String,
    /// Connected pass certificates; None means an internal proposal only.
    pub certificate: Option<String>,
}

/// Lower the complete configured observation set, run the default pass
/// pipeline, and emit a standalone `Optimized` module. Does not model check or
/// claim safety. Unsupported inputs never produce a partial optimization.
pub fn optimize_model(program: &mut Program, config: &Config) -> Result<Artifact, Diagnostic> {
    let model = lower::lower(program, config)?;
    let (model, remarks, certificate) = passes::Pipeline::default().run(model)?;
    verify::finite(&model)?;
    let mut artifact = emit::emit(&model, &remarks);
    artifact.certificate = Some(certificate);
    Ok(artifact)
}
