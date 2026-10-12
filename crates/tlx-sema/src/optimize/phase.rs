//! Structural state projections: field liveness, sequence length and finite
//! history summaries. These reuse normalized branches and forward domains.

mod age;
mod domain;
mod history;
mod liveness;
mod normalize;
mod sequence;

pub use age::age_projection;
pub use history::history_projection;
pub use sequence::sequence_length_projection;

use tlx_front::cfg::Config;

use crate::{builtins::Builtin as B, hir::*, Program};

use domain::{Domain, Domains};

/// A proved state-key expression and labels for the information it forgets.
pub struct FieldProjection {
    pub view: Expr,
    pub fields: Vec<String>,
    /// Generated certificate for the supported rule IR, never implicitly verified.
    pub certificate: Option<String>,
}

/// Derive one field projection. An unknown transfer, observation, effect or
/// exhausted analysis budget cannot authorize dropping information. The caller
/// supplies all observations, excludes overrides and liveness, and checks
/// equivariance before composing the result with symmetry.
pub fn phase_projection(program: &Program, cfg: &Config, init: &Expr, next: &Expr, observations: &[Expr]) -> Option<FieldProjection> {
    let mut expand = normalize::Normalizer::new(program);
    let initial = branches(&expand.root(init)?)?;
    let steps = branches(&expand.root(next)?)?;
    let observations: Vec<_> = observations.iter().map(|e| expand.root(e)).collect::<Option<_>>()?;
    let domains = Domains::infer(program, cfg, &initial, &steps)?;
    let mut best: Option<FieldProjection> = None;
    for (i, d) in domains.vars.iter().enumerate() {
        let fields = match d {
            Domain::Record(fs) => fs,
            Domain::Function(keys, range) if !keys.is_empty() => {
                let Domain::Record(fs) = &**range else { continue };
                fs
            }
            _ => continue,
        };
        if fields.len() > 32 {
            continue;
        }
        for (control, values) in fields {
            let Some(phases) = values.atoms() else { continue };
            if phases.is_empty()
                || phases.len() > 32
                || !domain::compatible(phases)
                || phases.iter().any(|p| domains.atom_expr(p, init.span).is_none())
            {
                continue;
            }
            if let Some(projection) = liveness::derive(program, &domains, VarId(i as u32), control, phases, &steps, &observations) {
                // A Boolean flag can be a valid but unhelpful control field.
                // Prefer the candidate that forgets more fields; the proof
                // is independent of this selection heuristic.
                if best.as_ref().is_none_or(|old| projection.fields.len() > old.fields.len()) {
                    best = Some(projection);
                }
            }
        }
    }
    best
}

#[derive(Clone)]
struct Branch {
    bounds: Vec<Bound>,
    terms: Vec<Expr>,
}

fn branches(e: &Expr) -> Option<Vec<Branch>> {
    fn split(e: &Expr, remaining: &mut usize, depth: usize) -> Option<Vec<Branch>> {
        if *remaining == 0 || depth >= 128 {
            return None;
        }
        *remaining -= 1;
        match &*e.kind {
            ExprKind::Or(es) => {
                let mut out = Vec::new();
                for e in es {
                    out.extend(split(e, remaining, depth + 1)?);
                    if out.len() > 512 {
                        return None;
                    }
                }
                Some(out)
            }
            ExprKind::And(es) => {
                let mut out = vec![Branch { bounds: vec![], terms: vec![] }];
                for e in es {
                    let alternatives = split(e, remaining, depth + 1)?;
                    if out.len().saturating_mul(alternatives.len()) > 512 {
                        return None;
                    }
                    let mut combined = Vec::new();
                    for a in &out {
                        for b in &alternatives {
                            if a.terms.len() + b.terms.len() > 512 || a.bounds.len() + b.bounds.len() > 128 {
                                return None;
                            }
                            let mut branch = a.clone();
                            branch.bounds.extend(b.bounds.iter().cloned());
                            branch.terms.extend(b.terms.iter().cloned());
                            combined.push(branch);
                        }
                    }
                    out = combined;
                }
                Some(out)
            }
            ExprKind::Quant { kind: QuantKind::Exists, bounds, body } => {
                let mut out = split(body, remaining, depth + 1)?;
                for b in &mut out {
                    if bounds.len() + b.bounds.len() > 128 {
                        return None;
                    }
                    let mut combined = bounds.clone();
                    combined.append(&mut b.bounds);
                    b.bounds = combined;
                }
                Some(out)
            }
            _ => Some(vec![Branch { bounds: vec![], terms: vec![e.clone()] }]),
        }
    }
    split(e, &mut 100_000, 0)
}

fn variable(e: &Expr, primed: bool) -> Option<VarId> {
    let e = if primed {
        let ExprKind::Builtin { op: B::Prime, args } = &*e.kind else { return None };
        if args.len() != 1 {
            return None;
        }
        &args[0]
    } else {
        e
    };
    if let ExprKind::Var(v) = &*e.kind {
        Some(*v)
    } else {
        None
    }
}

fn unchanged(e: &Expr, v: VarId) -> usize {
    match &*e.kind {
        ExprKind::Var(x) => usize::from(*x == v),
        ExprKind::Tuple(es) => es.iter().map(|e| unchanged(e, v)).sum(),
        _ => 0,
    }
}

fn binding(branch: &Branch, v: VarId, primed: bool) -> Option<Expr> {
    let mut values = Vec::new();
    for e in &branch.terms {
        match &*e.kind {
            ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 && variable(&args[0], primed) == Some(v) => {
                values.push(args[1].clone());
            }
            ExprKind::Builtin { op: B::Unchanged, args } if primed && args.len() == 1 => {
                values.extend((0..unchanged(&args[0], v)).map(|_| Expr::new(ExprKind::Var(v), e.span)));
            }
            _ => {}
        }
    }
    if values.len() == 1 {
        values.pop()
    } else {
        None
    }
}
