//! Finite summaries of append-only histories observed by prefix predicates.
//!
//! For P(h) = forall i in 1..Len(h): Q(h[i], prefix(h, i)), appending x
//! preserves every old obligation and adds Q(x, elements(h) union {x}).
//! Thus elements(h) and P(h), together, determine every future observation.
//! Prefix quantifiers may inspect values, but never positions or multiplicity.
//! Existential monitors use the dual: retain the absence of any witness, so
//! the same conjunction fold applies to the negated event predicate.

pub(super) mod lean;

use std::collections::BTreeSet;

use tlx_front::cfg::Config;

use crate::{builtins::Builtin as B, hir::*, visit, Program};

use super::{
    binding, branches,
    domain::{compatible, Domain, Domains, Locals},
    normalize::Normalizer,
    ordinary_unchanged, unchanged, variable, Branch, FieldProjection,
};

/// Prove a finite summary for one history, retaining concrete execution and
/// the shared safety-only checking boundary. All observations are required.
pub fn history_projection(program: &Program, cfg: &Config, init: &Expr, next: &Expr, observations: &[Expr]) -> Option<FieldProjection> {
    history_projection_with_spec(program, cfg, init, next, super::CheckSpec::invariants_only(observations))
}

/// Prove a finite summary for one history covering invariants, state constraints,
/// and init properties.
pub fn history_projection_with_spec(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: super::CheckSpec<'_>,
) -> Option<FieldProjection> {
    let spec = spec.state_only()?;
    if !super::cfg_constants_supported(program, cfg) {
        return None;
    }
    let mut expand = Normalizer::with_config(program, cfg);
    let initial = branches(&expand.root(init)?)?;
    let steps = branches(&expand.root(next)?)?;
    let norm = spec.try_map(|e| expand.root(e))?;
    let norm_spec = norm.as_spec();
    let domains = Domains::infer(program, cfg, &initial, &steps)?;
    for (i, domain) in domains.vars.iter().enumerate() {
        let Some(candidate) = candidate(program, &domains, i, domain, &initial, &steps, norm_spec) else { continue };
        if spec.is_constrained() && !super::sym_totality::check_projection_observations_total(program, cfg, init, next, spec) {
            return None;
        }
        let certificate = match lean::emit(candidate.var, &initial, &steps, norm_spec, &candidate.monitors) {
            Some(c) => Some(expand.attach_const_subst(c)?),
            None => None,
        };
        let summary = candidate.summary;
        let span = program.vars[i].span;
        let values = program
            .vars
            .iter()
            .enumerate()
            .map(|(j, v)| if i == j { summary.clone() } else { Expr::new(ExprKind::Var(VarId(j as u32)), v.span) })
            .collect();
        return Some(FieldProjection {
            ordered: None,
            view: Expr::new(ExprKind::Tuple(values), span),
            fields: vec![format!("{}.history", program.vars[i].name)],
            certificate,
            mathematical_counter_arithmetic: false,
        });
    }
    None
}

pub(super) struct Candidate {
    pub var: VarId,
    pub monitors: Vec<Expr>,
    pub summary: Expr,
}

pub(super) fn candidate(
    program: &Program,
    domains: &Domains,
    i: usize,
    domain: &Domain,
    initial: &[Branch],
    steps: &[Branch],
    spec: super::CheckSpec<'_>,
) -> Option<Candidate> {
    let Domain::Seq(element) = domain else { return None };
    if !finite(element) {
        return None;
    }
    let mut proof = Proof { var: VarId(i as u32), domains, element, monitors: vec![], appends: false };
    if !initial.iter().all(|b| proof.branch(b, false))
        || !steps.iter().all(|b| proof.branch(b, true))
        || !spec.all_state_preds().all(|e| proof.read(e))
        || !proof.appends
    {
        return None;
    }
    let span = program.vars[i].span;
    let history = Expr::new(ExprKind::Var(proof.var), span);
    let local = LocalId(program.locals.len() as u32);
    let index = Expr::new(ExprKind::Local(local), span);
    let set = Expr::new(ExprKind::Builtin { op: B::Domain, args: vec![history.clone()] }, span);
    let elements = Expr::new(
        ExprKind::SetMap {
            expr: Expr::new(ExprKind::FnApp { func: history, args: vec![index] }, span),
            bounds: vec![Bound { vars: BoundVars::Many(vec![local]), set }],
        },
        span,
    );
    let monitors = proof.monitors.iter().cloned().map(|e| {
        if matches!(&*e.kind, ExprKind::Quant { kind: QuantKind::Exists, .. }) {
            Expr::new(ExprKind::Builtin { op: B::Not, args: vec![e] }, span)
        } else {
            e
        }
    });
    let summary = Expr::new(ExprKind::Tuple(std::iter::once(elements).chain(monitors).collect()), span);
    Some(Candidate { var: proof.var, monitors: proof.monitors, summary })
}

fn finite(d: &Domain) -> bool {
    match d {
        Domain::Bottom => true,
        Domain::Atoms(values) => compatible(values),
        Domain::Record(fs) => fs.values().all(finite),
        Domain::Set(d) | Domain::Function(_, d) => finite(d),
        _ => false,
    }
}

struct Proof<'a> {
    var: VarId,
    domains: &'a Domains,
    element: &'a Domain,
    monitors: Vec<Expr>,
    appends: bool,
}

impl Proof<'_> {
    fn branch(&mut self, b: &Branch, primed: bool) -> bool {
        let Some(rhs) = binding(b, self.var, primed) else { return false };
        if !self.transfer(&rhs) || !b.bounds.iter().all(|b| self.read(&b.set)) {
            return false;
        }
        b.terms.iter().all(|e| match &*e.kind {
            ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 && variable(&args[0], primed) == Some(self.var) => true,
            ExprKind::Builtin { op: B::Unchanged, args } if primed && args.len() == 1 && unchanged(&args[0], self.var) == 1 => {
                ordinary_unchanged(&args[0])
            }
            _ => self.read(e),
        })
    }

    fn transfer(&mut self, e: &Expr) -> bool {
        match &*e.kind {
            ExprKind::Var(v) => *v == self.var,
            ExprKind::Tuple(es) => es.iter().all(|e| self.read(e)),
            ExprKind::Builtin { op: B::Append, args } if args.len() == 2 => {
                self.appends = true;
                self.transfer(&args[0]) && self.read(&args[1])
            }
            ExprKind::If { cond, then, els } => self.read(cond) && self.transfer(then) && self.transfer(els),
            _ => false,
        }
    }

    fn read(&mut self, e: &Expr) -> bool {
        match &*e.kind {
            ExprKind::Var(v) if *v == self.var => return false,
            ExprKind::Builtin { op: B::In, args }
                if args.len() == 2
                    && variable(&args[0], false) == Some(self.var)
                    && self.domains.belongs(&self.domains.vars[self.var.idx()], &args[1]) =>
            {
                return true;
            }
            ExprKind::Builtin { op: B::Eq | B::Neq, args } if args.len() == 2 => {
                let empty = |e: &Expr| matches!(&*e.kind, ExprKind::Tuple(es) if es.is_empty());
                if (variable(&args[0], false) == Some(self.var) && empty(&args[1]))
                    || (variable(&args[1], false) == Some(self.var) && empty(&args[0]))
                {
                    return true;
                }
            }
            ExprKind::Quant { bounds, body, .. } if bounds.len() == 1 => {
                let b = &bounds[0];
                if let Some(i) = one_local(b) {
                    if interval_end(&b.set).is_some_and(|end| {
                        matches!(&*end.kind, ExprKind::Builtin { op: B::Len, args }
                            if args.len() == 1 && variable(&args[0], false) == Some(self.var))
                    }) && self.predicate(body, i, &[i])
                    {
                        if self.monitors.len() >= 32 {
                            return false;
                        }
                        self.monitors.push(e.clone());
                        return true;
                    }
                }
            }
            _ => {}
        }
        let mut valid = true;
        visit::children(e, &mut |e| valid &= self.read(e));
        valid
    }

    // Prove total, state-independent Boolean predicates. Index locals can
    // appear only as in-bounds history subscripts, never as observed numbers.
    fn predicate(&self, e: &Expr, outer: LocalId, indices: &[LocalId]) -> bool {
        match &*e.kind {
            ExprKind::Bool(_) => true,
            ExprKind::And(es) | ExprKind::Or(es) => es.iter().all(|e| self.predicate(e, outer, indices)),
            ExprKind::Builtin { op: B::Eq | B::Neq, args } if args.len() == 2 => {
                let atoms = |e| match self.term(e, indices) {
                    Some(Domain::Atoms(a)) => Some(a),
                    _ => None,
                };
                match (atoms(&args[0]), atoms(&args[1])) {
                    (Some(a), Some(b)) => compatible(&a.union(&b).cloned().collect::<BTreeSet<_>>()),
                    _ => false,
                }
            }
            ExprKind::Builtin { op: B::Not, args } if args.len() == 1 => self.predicate(&args[0], outer, indices),
            ExprKind::Builtin { op: B::Implies | B::Equiv, args } if args.len() == 2 => {
                args.iter().all(|e| self.predicate(e, outer, indices))
            }
            ExprKind::If { cond, then, els } => [cond, then, els].iter().all(|e| self.predicate(e, outer, indices)),
            ExprKind::Quant { bounds, body, .. } if bounds.len() == 1 => {
                let b = &bounds[0];
                let Some(j) = one_local(b) else { return false };
                if !interval_end(&b.set).is_some_and(|e| matches!(&*e.kind, ExprKind::Local(i) if *i == outer)) {
                    return false;
                }
                let mut indices = indices.to_vec();
                indices.push(j);
                self.predicate(body, outer, &indices)
            }
            _ => false,
        }
    }

    fn term(&self, e: &Expr, indices: &[LocalId]) -> Option<Domain> {
        match &*e.kind {
            ExprKind::Const(_) | ExprKind::Num(_) | ExprKind::Str(_) | ExprKind::Bool(_) => Some(self.domains.value(e, &Locals::new())),
            ExprKind::FnApp { func, args }
                if variable(func, false) == Some(self.var)
                    && args.len() == 1
                    && matches!(&*args[0].kind, ExprKind::Local(i) if indices.contains(i)) =>
            {
                Some(self.element.clone())
            }
            ExprKind::Field { record, field } => match self.term(record, indices)? {
                Domain::Record(fs) => fs.get(field).cloned(),
                _ => None,
            },
            _ => None,
        }
    }
}

fn one_local(b: &Bound) -> Option<LocalId> {
    match &b.vars {
        BoundVars::Many(ids) if ids.len() == 1 => Some(ids[0]),
        _ => None,
    }
}

fn interval_end(e: &Expr) -> Option<&Expr> {
    match &*e.kind {
        ExprKind::Builtin { op: B::DotDot, args } if args.len() == 2 && matches!(&*args[0].kind, ExprKind::Num(1)) => Some(&args[1]),
        _ => None,
    }
}
