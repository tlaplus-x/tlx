//! Trusted structural checker, independent of pass candidate generation.
//!
//! For naturals, alpha(n)=min(n,k) commutes with keep, reset and increment
//! (using saturated increment in the codomain). A comparison is constant on
//! [k,infinity) exactly under the conditions checked below. Boolean closure
//! preserves that equality. With unchanged action guards and complete updates,
//! each concrete action maps to the same abstract action; every abstract action
//! lifts from every concrete representative. Initialization is checked directly.
//! These are rule-instance checks, not a machine-checked proof of this Rust code.

use super::ir::{Comparison, Domain, Model, Update};
use super::passes::{Evidence, Proposal};
use super::Diagnostic;

pub(super) fn well_formed(model: &Model) -> Result<(), Diagnostic> {
    let n = model.variables.len();
    if n == 0 || model.initial.len() != n || model.actions.is_empty() || model.properties.is_empty() {
        return Err(Diagnostic::new("invalid transition IR: missing variables, initial values, actions or properties"));
    }
    let mut valid = true;
    model.observations(&mut |var, _, value| valid &= var < n && value <= i32::MAX as u32);
    for (i, variable) in model.variables.iter().enumerate() {
        valid &= model.initial[i] <= i32::MAX as u32;
        if let Domain::Interval(cap) = variable.domain {
            valid &= cap <= i32::MAX as u32 && model.initial[i] <= cap;
        }
    }
    for action in &model.actions {
        if action.updates.len() != n {
            return Err(Diagnostic::at(action.span, "invalid transition IR: incomplete update vector"));
        }
        for (variable, update) in model.variables.iter().zip(&action.updates) {
            valid &= match (&variable.domain, update) {
                (_, Update::Keep | Update::Reset) | (Domain::Natural, Update::Increment) => true,
                (Domain::Interval(cap), Update::SaturatingIncrement(k)) => cap == k,
                _ => false,
            };
        }
    }
    if !valid {
        return Err(Diagnostic::new("invalid transition IR: variable reference, domain or update"));
    }
    Ok(())
}

pub(super) fn finite(model: &Model) -> Result<(), Diagnostic> {
    well_formed(model)?;
    if model.variables.iter().any(|v| v.domain == Domain::Natural) {
        return Err(Diagnostic::new("finite-domain closure failed: an unbounded variable remains"));
    }
    Ok(())
}

pub(super) fn transformation(before: &Model, proposal: &Proposal) -> Result<(), Diagnostic> {
    well_formed(before)?;
    well_formed(&proposal.model)?;
    match &proposal.evidence {
        Evidence::CounterSaturation { caps } => counter(before, &proposal.model, caps),
    }
}

fn counter(before: &Model, after: &Model, caps: &[u32]) -> Result<(), Diagnostic> {
    let invalid = || Diagnostic::new("invalid threshold-counter-saturation evidence or rewrite");
    let n = before.variables.len();
    if caps.len() != n || after.variables.len() != n || before.actions.len() != after.actions.len() || before.properties != after.properties
    {
        return Err(invalid());
    }
    for (i, &cap) in caps.iter().enumerate() {
        let a = &before.variables[i];
        let b = &after.variables[i];
        if a.domain != Domain::Natural
            || b.domain != Domain::Interval(cap)
            || a.name != b.name
            || a.span != b.span
            || after.initial[i] != before.initial[i].min(cap)
        {
            return Err(invalid());
        }
    }
    let mut compatible = true;
    // Inspect actual source observations, never the pass's analysis cache.
    before.observations(&mut |var, op, value| {
        compatible &= match op {
            Comparison::Lt | Comparison::Ge => value <= caps[var],
            Comparison::Eq | Comparison::Ne | Comparison::Le | Comparison::Gt => value < caps[var],
        };
    });
    if !compatible {
        return Err(invalid());
    }
    for (a, b) in before.actions.iter().zip(&after.actions) {
        if a.span != b.span || a.guard != b.guard {
            return Err(invalid());
        }
        for (i, (source, target)) in a.updates.iter().zip(&b.updates).enumerate() {
            let valid = match (source, target) {
                (Update::Keep, Update::Keep) | (Update::Reset, Update::Reset) => true,
                (Update::Increment, Update::SaturatingIncrement(cap)) => *cap == caps[i],
                _ => false,
            };
            if !valid {
                return Err(invalid());
            }
        }
    }
    Ok(())
}
