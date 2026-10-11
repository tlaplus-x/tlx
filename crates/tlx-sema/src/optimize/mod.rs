//! Property-relative optimization of a restricted, mathematical transition IR.
//!
//! This pipeline is separate from execution lowering: its rewrites may change
//! state counts and machine-overflow behavior. Only validated rewrites reach
//! emission. See docs/abstraction.md for the fragment and trust boundary.

mod analysis;
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
}

/// Lower the complete configured observation set, run the default pass
/// pipeline, and emit a standalone `Abstract` module. Does not model check or
/// claim safety. Unsupported inputs never produce a partial abstraction.
pub fn abstract_model(program: &mut Program, config: &Config) -> Result<Artifact, Diagnostic> {
    let model = lower::lower(program, config)?;
    let (model, remarks) = passes::Pipeline::default().run(model)?;
    verify::finite(&model)?;
    Ok(emit::emit(&model, &remarks))
}
