//! Disjunctive branch splitting and the variable-binding queries computed over
//! one normalized branch.

use crate::builtins::Builtin as B;
use crate::hir::{Bound, Expr, ExprKind, QuantKind, VarId};

#[derive(Clone)]
pub(in crate::optimize::phase) struct Branch {
    pub(in crate::optimize::phase) bounds: Vec<Bound>,
    pub(in crate::optimize::phase) terms: Vec<Expr>,
}

pub(in crate::optimize::phase) fn branches(e: &Expr) -> Option<Vec<Branch>> {
    Some(split_branches(e, false)?.into_iter().map(|(b, _)| b).collect())
}

pub(in crate::optimize::phase) fn branches_with_if(e: &Expr) -> Option<Vec<Branch>> {
    Some(split_branches(e, true)?.into_iter().map(|(b, _)| b).collect())
}

pub(in crate::optimize::phase) fn branches_positioned(e: &Expr) -> Option<Vec<(Branch, Vec<usize>)>> {
    split_branches(e, false)
}

pub(in crate::optimize::phase) fn branches_with_if_positioned(e: &Expr) -> Option<Vec<(Branch, Vec<usize>)>> {
    split_branches(e, true)
}

fn split_branches(e: &Expr, split_if: bool) -> Option<Vec<(Branch, Vec<usize>)>> {
    fn split(e: &Expr, split_if: bool, remaining: &mut usize, depth: usize) -> Option<Vec<(Branch, Vec<usize>)>> {
        if *remaining == 0 || depth >= 128 {
            return None;
        }
        *remaining -= 1;
        match &*e.kind {
            ExprKind::Or(es) => {
                let mut out = Vec::new();
                for e in es {
                    out.extend(split(e, split_if, remaining, depth + 1)?);
                    if out.len() > 512 {
                        return None;
                    }
                }
                Some(out)
            }
            ExprKind::And(es) => {
                let mut out = vec![(Branch { bounds: vec![], terms: vec![] }, vec![])];
                for e in es {
                    let alternatives = split(e, split_if, remaining, depth + 1)?;
                    if out.len().saturating_mul(alternatives.len()) > 512 {
                        return None;
                    }
                    let mut combined = Vec::new();
                    for (a, a_pos) in &out {
                        let offset = a.terms.len();
                        for (b, b_pos) in &alternatives {
                            if a.terms.len() + b.terms.len() > 512 || a.bounds.len() + b.bounds.len() > 128 {
                                return None;
                            }
                            let mut branch = a.clone();
                            let mut pos = a_pos.clone();
                            branch.bounds.extend(b.bounds.iter().cloned());
                            pos.extend(b_pos.iter().map(|p| p + offset));
                            branch.terms.extend(b.terms.iter().cloned());
                            combined.push((branch, pos));
                        }
                    }
                    out = combined;
                }
                Some(out)
            }
            ExprKind::Quant { kind: QuantKind::Exists, bounds, body } => {
                let mut out = split(body, split_if, remaining, depth + 1)?;
                for (b, pos) in &mut out {
                    if bounds.len() + b.bounds.len() > 128 {
                        return None;
                    }
                    let mut combined = bounds.clone();
                    combined.append(&mut b.bounds);
                    b.bounds = combined;
                    let mut combined_pos = vec![0; bounds.len()];
                    combined_pos.append(pos);
                    *pos = combined_pos;
                }
                Some(out)
            }
            ExprKind::If { cond, then, els } if split_if => {
                let mut left = split(then, split_if, remaining, depth + 1)?;
                let mut right = split(els, split_if, remaining, depth + 1)?;
                let neg = Expr::new(ExprKind::Builtin { op: B::Not, args: vec![cond.clone()] }, cond.span);
                for (b, pos) in &mut left {
                    b.terms.insert(0, cond.clone());
                    for p in pos {
                        *p += 1;
                    }
                }
                for (b, pos) in &mut right {
                    b.terms.insert(0, neg.clone());
                    for p in pos {
                        *p += 1;
                    }
                }
                left.extend(right);
                if left.len() > 512 {
                    return None;
                }
                Some(left)
            }
            _ => Some(vec![(Branch { bounds: vec![], terms: vec![e.clone()] }, vec![])]),
        }
    }
    split(e, split_if, &mut 100_000, 0)
}

pub(in crate::optimize::phase) fn variable(e: &Expr, primed: bool) -> Option<VarId> {
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

pub(in crate::optimize::phase) fn unchanged(e: &Expr, v: VarId) -> usize {
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

pub(in crate::optimize::phase) fn mentions_phase_var(e: &Expr, primed: bool) -> bool {
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

pub(in crate::optimize::phase) struct BranchBindings {
    primed: bool,
    single_eq: std::collections::HashMap<VarId, (usize, Expr)>,
    single_rev_eq: std::collections::HashMap<VarId, (usize, Expr)>,
    first_membership: std::collections::HashMap<VarId, usize>,
    state: std::cell::RefCell<std::collections::HashMap<VarId, GroundState>>,
}

impl BranchBindings {
    pub(in crate::optimize::phase) fn new(branch: &Branch, primed: bool) -> Self {
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

    pub(in crate::optimize::phase) fn get_with_index(&self, v: VarId) -> Option<(usize, Expr)> {
        let (idx, rhs) = self.single_eq.get(&v)?;
        if mentions_phase_var(rhs, self.primed)
            && (self.has_earlier_membership(v, *idx) || !self.var_is_grounded(v, &mut self.state.borrow_mut()))
        {
            return None;
        }
        Some((*idx, rhs.clone()))
    }

    pub(in crate::optimize::phase) fn get(&self, v: VarId) -> Option<Expr> {
        self.get_with_index(v).map(|(_, rhs)| rhs)
    }

    pub(in crate::optimize::phase) fn get_or_reversed(&self, v: VarId) -> Option<Expr> {
        self.get(v).or_else(|| {
            let (idx, lhs) = self.single_rev_eq.get(&v)?;
            if mentions_phase_var(lhs, self.primed) || self.has_earlier_membership(v, *idx) {
                return None;
            }
            Some(lhs.clone())
        })
    }
}

pub(in crate::optimize::phase) fn binding(branch: &Branch, v: VarId, primed: bool) -> Option<Expr> {
    BranchBindings::new(branch, primed).get(v)
}

pub(in crate::optimize::phase) fn binding_with_index(branch: &Branch, v: VarId, primed: bool) -> Option<(usize, Expr)> {
    BranchBindings::new(branch, primed).get_with_index(v)
}
