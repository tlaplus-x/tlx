//! Commit validated exact rewrites to configured HIR roots before evaluation.
//! Keep source variables, definition names and spans: traces remain concrete.

use tlx_front::cfg::Config;

use crate::builtins::Builtin as B;
use crate::hir::{Expr, ExprKind, RootSymbol, Span, VarId};
use crate::Program;

use super::ir::{Comparison, Domain, Predicate, Update};
use super::{lower, passes::Pipeline, Diagnostic};

/// Optimize the supported configured fragment without quotienting state values.
/// Refusal occurs before any definition is rewritten. Lazy source resolution
/// may still populate the program's caches. Call before building an interpreter.
pub fn optimize_check(program: &mut Program, cfg: &Config) -> Result<Vec<String>, Diagnostic> {
    let original = lower::lower(program, cfg)?;
    let (model, remarks) = Pipeline::exact().run(original)?;
    if remarks.is_empty() {
        return Ok(remarks);
    }
    // Defense at the execution boundary: only identity-on-state rules may
    // supply HIR to ordinary checking, even if the pipeline gains new passes.
    if model.variables.iter().any(|v| matches!(v.domain, Domain::Interval(_)))
        || model.actions.iter().any(|a| a.updates.iter().any(|u| matches!(u, Update::SaturatingIncrement(_))))
    {
        return Err(Diagnostic::new("state-space quotient requires concrete trace reconstruction"));
    }
    let mut roots = Vec::new();
    for name in cfg.init.iter().chain(cfg.next.iter()).chain(&cfg.invariants) {
        let Some(RootSymbol::Def(id)) = program.lookup_root(name) else {
            return Err(Diagnostic::new(format!("missing configured definition {name}")));
        };
        if roots.contains(&id) {
            return Err(Diagnostic::new("exact optimization requires distinct INIT, NEXT and INVARIANT definitions"));
        }
        roots.push(id);
    }
    let init_span = program.defs[roots[0].idx()].span;
    let next_span = program.defs[roots[1].idx()].span;
    let init = Expr::new(
        ExprKind::And(
            model
                .initial
                .iter()
                .enumerate()
                .map(|(i, n)| builtin(B::Eq, vec![var(i, init_span), number(*n, init_span)], init_span))
                .collect(),
        ),
        init_span,
    );
    let next = if model.actions.is_empty() {
        Expr::new(
            ExprKind::And(vec![
                state_bool(false, next_span),
                builtin(
                    B::Unchanged,
                    vec![Expr::new(ExprKind::Tuple((0..model.variables.len()).map(|i| var(i, next_span)).collect()), next_span)],
                    next_span,
                ),
            ]),
            next_span,
        )
    } else {
        Expr::new(
            ExprKind::Or(
                model
                    .actions
                    .iter()
                    .map(|action| {
                        let span = action.span;
                        let mut terms = vec![predicate(&action.guard, span)];
                        for (i, update) in action.updates.iter().enumerate() {
                            let rhs = match update {
                                Update::Keep => var(i, span),
                                Update::Reset => number(0, span),
                                Update::Increment => builtin(B::Plus, vec![var(i, span), number(1, span)], span),
                                Update::SaturatingIncrement(_) => unreachable!("quotients rejected above"),
                            };
                            terms.push(builtin(B::Eq, vec![builtin(B::Prime, vec![var(i, span)], span), rhs], span));
                        }
                        Expr::new(ExprKind::And(terms), span)
                    })
                    .collect(),
            ),
            next_span,
        )
    };
    let mut bodies = vec![init, next];
    bodies.extend(model.properties.iter().map(|p| match p.predicate {
        Predicate::Bool(b) => state_bool(b, p.span),
        _ => predicate(&p.predicate, p.span),
    }));
    // No fallible work after this point. Invalidate source analyses before
    // consumers create caches keyed by definitions or expression IDs.
    program.replace_operator_bodies(roots.into_iter().zip(bodies));
    Ok(remarks)
}

fn builtin(op: B, args: Vec<Expr>, span: Span) -> Expr {
    Expr::new(ExprKind::Builtin { op, args }, span)
}

fn var(index: usize, span: Span) -> Expr {
    Expr::new(ExprKind::Var(VarId(u32::try_from(index).expect("existing variable index"))), span)
}

fn number(value: u32, span: Span) -> Expr {
    Expr::new(ExprKind::Num(i128::from(value)), span)
}

fn state_bool(value: bool, span: Span) -> Expr {
    builtin(if value { B::Eq } else { B::Neq }, vec![var(0, span), var(0, span)], span)
}

fn predicate(p: &Predicate, span: Span) -> Expr {
    let kind = match p {
        Predicate::Bool(b) => ExprKind::Bool(*b),
        Predicate::Compare { var: i, op, value } => {
            let op = match op {
                Comparison::Eq => B::Eq,
                Comparison::Ne => B::Neq,
                Comparison::Lt => B::Lt,
                Comparison::Le => B::Le,
                Comparison::Gt => B::Gt,
                Comparison::Ge => B::Ge,
            };
            return builtin(op, vec![var(*i, span), number(*value, span)], span);
        }
        Predicate::Not(p) => return builtin(B::Not, vec![predicate(p, span)], span),
        Predicate::And(ps) => ExprKind::And(ps.iter().map(|p| predicate(p, span)).collect()),
        Predicate::Or(ps) => ExprKind::Or(ps.iter().map(|p| predicate(p, span)).collect()),
    };
    Expr::new(kind, span)
}
