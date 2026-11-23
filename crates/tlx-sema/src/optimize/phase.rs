//! Structural state projections: field liveness, sequence length and finite
//! history summaries. These reuse normalized branches and forward domains.

mod age;
mod choose_sym;
mod domain;
mod equiv_sym;
mod erasure;
mod history;
mod keyed;
mod liveness;
mod normalize;
mod ordered;
mod sequence;
mod sym_groups;
pub(crate) mod sym_norm;
mod sym_totality;

pub use age::age_projection;
pub use choose_sym::choose_symmetry_certificate;
pub use equiv_sym::symmetry_certificate as equiv_symmetry_certificate;
pub use erasure::unobserved_projection;
pub use history::history_projection;
pub use keyed::symmetry_projection_certificate;
pub use ordered::{ordered_projection, OrderedHistory, OrderedPlan, OrderedShape};
pub use sequence::sequence_length_projection;
pub use sym_norm::{infer_var_domains, proves_var_membership, SymNormalizer};

/// Generate a connected Lean symmetry certificate for a disjoint product of full
/// permutation groups. Prefers the specialized keyed-state IR, then falls back
/// to the generic recursive equivariant value & expression IR, and finally to
/// certified choice-irrelevant symmetry when `CHOOSE` expressions are present.
pub fn symmetry_certificate(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    observations: &[Expr],
    groups: &[Vec<String>],
) -> Option<String> {
    keyed::symmetry_certificate(program, cfg, init, next, observations, groups)
        .or_else(|| equiv_sym::symmetry_certificate(program, cfg, init, next, observations, groups))
        .or_else(|| choose_sym::choose_symmetry_certificate(program, cfg, init, next, observations, groups))
}

use tlx_front::cfg::Config;

use crate::{builtins::Builtin as B, hir::*, Program};

use domain::{Domain, Domains};

/// A checked state-key projection and labels for the information it forgets.
pub struct FieldProjection {
    pub view: Expr,
    pub fields: Vec<String>,
    /// Generated certificate for the supported rule IR, never implicitly verified.
    pub certificate: Option<String>,
    /// When present, replaces the identity VIEW with a structural runtime key.
    pub ordered: Option<OrderedPlan>,
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
            if let Some(projection) =
                liveness::derive(program, &domains, VarId(i as u32), control, phases, (&initial, &steps), &observations)
            {
                // A Boolean flag can be a valid but unhelpful control field.
                // Prefer certified candidates, then more forgotten fields;
                // the proof is independent of this selection heuristic.
                if best.as_ref().is_none_or(|old| {
                    (projection.certificate.is_some(), projection.fields.len()) > (old.certificate.is_some(), old.fields.len())
                }) {
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

fn collect_unchanged_vars(e: &Expr, out: &mut Vec<VarId>) {
    match &*e.kind {
        ExprKind::Var(x) => out.push(*x),
        ExprKind::Tuple(es) => es.iter().for_each(|x| collect_unchanged_vars(x, out)),
        _ => {}
    }
}

fn mentions_phase_var(e: &Expr, primed: bool) -> bool {
    match &*e.kind {
        ExprKind::Var(_) => !primed,
        ExprKind::Builtin { op: B::Prime | B::Unchanged, args } => primed && args.iter().any(|a| mentions_phase_var(a, false)),
        ExprKind::Builtin { op: B::Enabled, .. } => false,
        _ => {
            let mut found = false;
            crate::visit::children(e, &mut |c| found |= mentions_phase_var(c, primed));
            found
        }
    }
}

fn collect_phase_vars(e: &Expr, primed: bool, out: &mut std::collections::BTreeSet<VarId>) {
    match &*e.kind {
        ExprKind::Var(v) if !primed => {
            out.insert(*v);
        }
        ExprKind::Builtin { op: B::Prime | B::Unchanged, args } if primed => {
            for a in args {
                collect_phase_vars(a, false, out);
            }
        }
        ExprKind::Builtin { op: B::Enabled, .. } => {}
        _ => crate::visit::children(e, &mut |c| collect_phase_vars(c, primed, out)),
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum GroundState {
    Visiting,
    Grounded(bool),
}

struct BranchBindings {
    primed: bool,
    single_eq: std::collections::HashMap<VarId, (usize, Expr)>,
    single_rev_eq: std::collections::HashMap<VarId, (usize, Expr)>,
    first_membership: std::collections::HashMap<VarId, usize>,
    state: std::cell::RefCell<std::collections::HashMap<VarId, GroundState>>,
}

impl BranchBindings {
    fn new(branch: &Branch, primed: bool) -> Self {
        let mut eq_counts: std::collections::HashMap<VarId, usize> = std::collections::HashMap::new();
        let mut rev_counts: std::collections::HashMap<VarId, usize> = std::collections::HashMap::new();
        let mut single_eq = std::collections::HashMap::new();
        let mut single_rev_eq = std::collections::HashMap::new();
        let mut first_membership = std::collections::HashMap::new();
        let mut unch = Vec::new();
        for (idx, e) in branch.terms.iter().enumerate() {
            match &*e.kind {
                ExprKind::Builtin { op: B::In | B::SubsetEq, args } if args.len() == 2 => {
                    if let Some(v) = variable(&args[0], primed) {
                        first_membership.entry(v).or_insert(idx);
                    }
                }
                ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 => {
                    let lhs_v = variable(&args[0], primed);
                    let rhs_v = variable(&args[1], primed);
                    if let Some(v) = lhs_v {
                        let c = eq_counts.entry(v).or_insert(0);
                        *c += 1;
                        if *c == 1 {
                            single_eq.insert(v, (idx, args[1].clone()));
                        } else {
                            single_eq.remove(&v);
                        }
                    }
                    if let Some(v) = rhs_v {
                        if lhs_v != Some(v) {
                            let rc = rev_counts.entry(v).or_insert(0);
                            *rc += 1;
                            if *rc == 1 {
                                single_rev_eq.insert(v, (idx, args[0].clone()));
                            } else {
                                single_rev_eq.remove(&v);
                            }
                        }
                    }
                }
                ExprKind::Builtin { op: B::Unchanged, args } if primed && args.len() == 1 => {
                    unch.clear();
                    collect_unchanged_vars(&args[0], &mut unch);
                    for &v in &unch {
                        let c = eq_counts.entry(v).or_insert(0);
                        *c += 1;
                        if *c == 1 {
                            single_eq.insert(v, (idx, Expr::new(ExprKind::Var(v), e.span)));
                        } else {
                            single_eq.remove(&v);
                        }
                    }
                }
                _ => {}
            }
        }
        Self { primed, single_eq, single_rev_eq, first_membership, state: std::cell::RefCell::new(std::collections::HashMap::new()) }
    }

    fn has_earlier_membership(&self, v: VarId, limit_idx: usize) -> bool {
        self.first_membership.get(&v).is_some_and(|&first| first < limit_idx)
    }

    fn var_is_grounded(&self, u: VarId, state: &mut std::collections::HashMap<VarId, GroundState>) -> bool {
        match state.get(&u).copied() {
            Some(GroundState::Grounded(ok)) => return ok,
            Some(GroundState::Visiting) => return false,
            None => {}
        }
        state.insert(u, GroundState::Visiting);
        let ok = match self.single_eq.get(&u) {
            Some((_, u_rhs)) if !mentions_phase_var(u_rhs, self.primed) => true,
            Some((idx, u_rhs)) if !self.has_earlier_membership(u, *idx) => {
                let mut deps = std::collections::BTreeSet::new();
                collect_phase_vars(u_rhs, self.primed, &mut deps);
                deps.into_iter().all(|w| self.var_is_grounded(w, state))
            }
            _ => self.first_membership.contains_key(&u),
        };
        state.insert(u, GroundState::Grounded(ok));
        ok
    }

    fn get(&self, v: VarId) -> Option<Expr> {
        let (idx, rhs) = self.single_eq.get(&v)?;
        if mentions_phase_var(rhs, self.primed)
            && (self.has_earlier_membership(v, *idx) || !self.var_is_grounded(v, &mut self.state.borrow_mut()))
        {
            return None;
        }
        Some(rhs.clone())
    }

    fn get_or_reversed(&self, v: VarId) -> Option<Expr> {
        self.get(v).or_else(|| {
            let (idx, lhs) = self.single_rev_eq.get(&v)?;
            if mentions_phase_var(lhs, self.primed) || self.has_earlier_membership(v, *idx) {
                return None;
            }
            Some(lhs.clone())
        })
    }
}

fn binding(branch: &Branch, v: VarId, primed: bool) -> Option<Expr> {
    BranchBindings::new(branch, primed).get(v)
}

// Bound declarations, even unused ones, must not capture inserted inputs.
pub(super) fn max_local(e: &Expr) -> u32 {
    let mut max = 0;
    let mut ids = |ids: &[LocalId]| {
        for id in ids {
            max = max.max(id.0);
        }
    };
    match &*e.kind {
        ExprKind::Local(id) => ids(&[*id]),
        ExprKind::Quant { bounds, .. } | ExprKind::FnConstruct { bounds, .. } | ExprKind::SetMap { bounds, .. } => {
            for b in bounds {
                ids(b.vars.locals());
            }
        }
        ExprKind::SetFilter { bound, .. } => ids(bound.vars.locals()),
        ExprKind::Choose { vars, .. } => ids(vars.locals()),
        ExprKind::Lambda { params, .. } => ids(params),
        ExprKind::QuantUnbounded { vars, .. } | ExprKind::TemporalQuant { vars, .. } => ids(vars),
        _ => {}
    }
    crate::visit::children(e, &mut |e| max = max.max(max_local(e)));
    max
}
