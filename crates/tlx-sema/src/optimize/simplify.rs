//! Fold domain-implied comparisons and Boolean identities in pure predicates.

use super::analysis::AnalysisManager;
use super::ir::{Comparison as C, Domain, Model, Predicate as P};
use super::passes::{Evidence, Pass, Proposal};
use super::Diagnostic;

pub(super) struct SimplifyPredicates;

impl Pass for SimplifyPredicates {
    fn name(&self) -> &'static str {
        "predicate-simplification/v1"
    }

    fn run(&self, model: &Model, _: &mut AnalysisManager) -> Result<Option<Proposal>, Diagnostic> {
        let mut result = model.clone();
        for action in &mut result.actions {
            action.guard = simplify(&action.guard, model);
        }
        for property in &mut result.properties {
            property.predicate = simplify(&property.predicate, model);
        }
        Ok((result != *model).then_some(Proposal { model: result, evidence: Evidence::SimplifyPredicates }))
    }
}

fn simplify(p: &P, model: &Model) -> P {
    match p {
        P::Bool(_) => p.clone(),
        P::Compare { var, op, value } => {
            let (lo, hi) = match model.variables[*var].domain {
                Domain::Natural => (0, None),
                Domain::Constant(n) => (n, Some(n)),
                Domain::Interval(n) => (0, Some(n)),
            };
            let truth = match op {
                C::Eq | C::Ne => {
                    let eq = if lo == *value && hi == Some(*value) {
                        Some(true)
                    } else if *value < lo || hi.is_some_and(|hi| *value > hi) {
                        Some(false)
                    } else {
                        None
                    };
                    eq.map(|b| if *op == C::Eq { b } else { !b })
                }
                C::Lt => {
                    if hi.is_some_and(|hi| hi < *value) {
                        Some(true)
                    } else if lo >= *value {
                        Some(false)
                    } else {
                        None
                    }
                }
                C::Le => {
                    if hi.is_some_and(|hi| hi <= *value) {
                        Some(true)
                    } else if lo > *value {
                        Some(false)
                    } else {
                        None
                    }
                }
                C::Gt => {
                    if lo > *value {
                        Some(true)
                    } else if hi.is_some_and(|hi| hi <= *value) {
                        Some(false)
                    } else {
                        None
                    }
                }
                C::Ge => {
                    if lo >= *value {
                        Some(true)
                    } else if hi.is_some_and(|hi| hi < *value) {
                        Some(false)
                    } else {
                        None
                    }
                }
            };
            truth.map(P::Bool).unwrap_or_else(|| p.clone())
        }
        P::Not(child) => match simplify(child, model) {
            P::Bool(b) => P::Bool(!b),
            child => P::Not(Box::new(child)),
        },
        P::And(children) | P::Or(children) => {
            let and = matches!(p, P::And(_));
            let mut live = Vec::new();
            for child in children {
                match simplify(child, model) {
                    P::Bool(b) if b != and => return P::Bool(b),
                    P::Bool(_) => {}
                    child => live.push(child),
                }
            }
            match live.len() {
                0 => P::Bool(and),
                1 => live.pop().unwrap(),
                _ => {
                    if and {
                        P::And(live)
                    } else {
                        P::Or(live)
                    }
                }
            }
        }
    }
}
