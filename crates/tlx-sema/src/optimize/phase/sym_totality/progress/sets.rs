//! Monotone-growing and coupled-shrinking finite-subset potential components.

use super::super::shape::*;
use super::super::{Shape, TotalityChecker};
use super::branches::{
    eval_const_bool, guards_prove_in, guards_prove_nonempty_set, guards_prove_not_in, key_in_exact_dom, ActionBranch, VarUpdate,
};
use super::dag::{eval_dag_strict_on_branch, DagComponent};
use super::{MAX_DOM_SIZE, MAX_UNIV_SIZE};
use crate::{builtins::Builtin as B, hir::*};

#[derive(Clone)]
pub(super) struct GrowSetComponent {
    var: usize,
    dom: Option<(Shape, u32)>,
    pub(super) max_potential: u32,
}

#[derive(Clone)]
pub(super) struct ShrinkSetComponent {
    var: usize,
    dom: Option<(Shape, u32)>,
    pub(super) max_potential: u32,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum ShrinkEffect {
    Unchanged,
    Shrink { strict: bool },
    GrowOne,
    Invalid,
}

// ---- Monotone-growing finite-subset components ----

pub(super) fn find_grow_set_components(
    checker: &TotalityChecker<'_>,
    cur_shapes: &[Shape],
    branches: &[ActionBranch],
) -> Vec<GrowSetComponent> {
    let mut out = Vec::new();
    for var in 0..checker.program.vars.len() {
        let (dom, univ) = match &cur_shapes[var] {
            Shape::Set { elem, finite: true, .. } => {
                let Some(u) = shape_universe_size(elem, checker.groups).filter(|u| (1..=MAX_UNIV_SIZE).contains(u)) else {
                    continue;
                };
                (None, u)
            }
            Shape::Func { dom, exact_dom: true, range, max_dom: Some(d) } if *d >= 1 && *d <= MAX_DOM_SIZE => {
                let Shape::Set { elem, finite: true, .. } = &**range else { continue };
                let Some(u) = shape_universe_size(elem, checker.groups).filter(|u| (1..=MAX_UNIV_SIZE).contains(u)) else {
                    continue;
                };
                (Some(((**dom).clone(), *d)), u)
            }
            _ => continue,
        };
        let mut any_grow = false;
        let mut valid = true;
        for b in branches {
            match classify_grow_set_branch(checker, var, dom.as_ref().map(|(d, _)| d), cur_shapes, b) {
                Some(grew) => any_grow |= grew,
                None => {
                    valid = false;
                    break;
                }
            }
        }
        if !valid || !any_grow {
            continue;
        }
        let slots = dom.as_ref().map_or(1, |(_, d)| *d);
        let Some(max_potential) = slots.checked_mul(univ) else { continue };
        out.push(GrowSetComponent { var, dom, max_potential });
    }
    out
}

/// Returns `None` if `branch` may shrink/replace `var`, `Some(false)` if unchanged or unguarded grow,
/// `Some(true)` if strictly grows by adding an element guarded by `e \notin slot`.
fn classify_grow_set_branch(
    checker: &TotalityChecker<'_>,
    var: usize,
    dom: Option<&Shape>,
    cur_shapes: &[Shape],
    branch: &ActionBranch,
) -> Option<bool> {
    match branch.updates[var].as_ref()? {
        VarUpdate::Unchanged => Some(false),
        VarUpdate::Other => None,
        VarUpdate::Expr(rhs) => {
            let var_expr = Expr::new(ExprKind::Var(VarId(var as u32)), rhs.span);
            if expr_alpha_eq(rhs, false, &var_expr, false) {
                return Some(false);
            }
            let Some(dom_shape) = dom else {
                let added = extract_cup_added(rhs, &var_expr, false)?;
                let strict = extract_singleton_elem(added).is_some_and(|e| guards_prove_not_in(&branch.guards, e, &var_expr));
                return Some(strict);
            };
            let ExprKind::Except { base, updates } = &*rhs.kind else { return None };
            if !expr_alpha_eq(base, false, &var_expr, false) || updates.len() != 1 {
                return None;
            }
            let (path, urhs) = &updates[0];
            let [ExceptKey::Index(ixs)] = path.as_slice() else { return None };
            let [key] = ixs.as_slice() else { return None };
            let slot = Expr::new(ExprKind::FnApp { func: var_expr, args: vec![key.clone()] }, rhs.span);
            let added = extract_cup_added(urhs, &slot, true)?;
            let strict = key_in_exact_dom(checker, key, cur_shapes, branch, dom_shape)
                && extract_singleton_elem(added).is_some_and(|e| guards_prove_not_in(&branch.guards, e, &slot));
            Some(strict)
        }
    }
}

pub(super) fn eval_grow_strict_on_branch(
    checker: &TotalityChecker<'_>,
    gc: &GrowSetComponent,
    cur_shapes: &[Shape],
    branch: &ActionBranch,
) -> bool {
    classify_grow_set_branch(checker, gc.var, gc.dom.as_ref().map(|(d, _)| d), cur_shapes, branch) == Some(true)
}

fn extract_cup_added<'a>(rhs: &'a Expr, slot: &Expr, allow_at: bool) -> Option<&'a Expr> {
    let is_slot = |e: &Expr| (allow_at && matches!(&*e.kind, ExprKind::At)) || expr_alpha_eq(e, false, slot, false);
    let ExprKind::Builtin { op: B::Cup, args } = &*rhs.kind else { return None };
    let [a, b] = args.as_slice() else { return None };
    if is_slot(a) {
        Some(b)
    } else if is_slot(b) {
        Some(a)
    } else {
        None
    }
}

fn extract_singleton_elem(e: &Expr) -> Option<&Expr> {
    let ExprKind::SetEnum(es) = &*e.kind else { return None };
    let [x] = es.as_slice() else { return None };
    Some(x)
}

// ---- Shrinking / coupled finite-subset components ----

pub(super) fn find_shrink_set_components(
    checker: &TotalityChecker<'_>,
    cur_shapes: &[Shape],
    branches: &[ActionBranch],
    dag_comps: &[DagComponent],
    grow_comps: &[GrowSetComponent],
) -> Vec<ShrinkSetComponent> {
    let mut out = Vec::new();
    for var in 0..checker.program.vars.len() {
        // Do not double-count a variable already tracked as a GrowSet component.
        if grow_comps.iter().any(|g| g.var == var) {
            continue;
        }
        let (dom, univ) = match &cur_shapes[var] {
            Shape::Set { elem, finite: true, .. } => {
                let Some(u) = shape_universe_size(elem, checker.groups).filter(|u| (1..=MAX_UNIV_SIZE).contains(u)) else {
                    continue;
                };
                (None, u)
            }
            Shape::Func { dom, exact_dom: true, range, max_dom: Some(d) } if *d >= 1 && *d <= MAX_DOM_SIZE => {
                let Shape::Set { elem, finite: true, .. } = &**range else { continue };
                let Some(u) = shape_universe_size(elem, checker.groups).filter(|u| (1..=MAX_UNIV_SIZE).contains(u)) else {
                    continue;
                };
                (Some(((**dom).clone(), *d)), u)
            }
            _ => continue,
        };
        let slots = dom.as_ref().map_or(1, |(_, d)| *d);
        let Some(max_potential) = slots.checked_mul(univ) else { continue };
        let candidate = ShrinkSetComponent { var, dom, max_potential };
        let mut any_strict = false;
        let mut valid = true;
        for b in branches {
            match eval_shrink_on_branch(checker, &candidate, cur_shapes, b) {
                ShrinkEffect::Unchanged | ShrinkEffect::Shrink { strict: false } => {}
                ShrinkEffect::Shrink { strict: true } => any_strict = true,
                ShrinkEffect::GrowOne => {
                    let offset = grow_comps.iter().any(|gc| eval_grow_strict_on_branch(checker, gc, cur_shapes, b))
                        || dag_comps.iter().any(|dc| eval_dag_strict_on_branch(checker, dc, cur_shapes, b));
                    if !offset {
                        valid = false;
                        break;
                    }
                }
                ShrinkEffect::Invalid => {
                    valid = false;
                    break;
                }
            }
        }
        if valid && any_strict {
            out.push(candidate);
        }
    }
    out
}

pub(super) fn eval_shrink_on_branch(
    checker: &TotalityChecker<'_>,
    sc: &ShrinkSetComponent,
    cur_shapes: &[Shape],
    branch: &ActionBranch,
) -> ShrinkEffect {
    let Some(upd) = branch.updates[sc.var].as_ref() else {
        return ShrinkEffect::Invalid;
    };
    match upd {
        VarUpdate::Unchanged => ShrinkEffect::Unchanged,
        VarUpdate::Other => ShrinkEffect::Invalid,
        VarUpdate::Expr(rhs) => {
            let var_expr = Expr::new(ExprKind::Var(VarId(sc.var as u32)), rhs.span);
            if expr_alpha_eq(rhs, false, &var_expr, false) {
                return ShrinkEffect::Unchanged;
            }
            let Some((dom_shape, _)) = &sc.dom else {
                return eval_shrink_slot_rhs(checker, rhs, &var_expr, false, true, branch);
            };
            let ExprKind::Except { base, updates } = &*rhs.kind else {
                return ShrinkEffect::Invalid;
            };
            if !expr_alpha_eq(base, false, &var_expr, false) || updates.len() != 1 {
                return ShrinkEffect::Invalid;
            }
            let (path, urhs) = &updates[0];
            let [ExceptKey::Index(ixs)] = path.as_slice() else {
                return ShrinkEffect::Invalid;
            };
            let [key] = ixs.as_slice() else {
                return ShrinkEffect::Invalid;
            };
            let slot = Expr::new(ExprKind::FnApp { func: var_expr, args: vec![key.clone()] }, rhs.span);
            let guaranteed = key_in_exact_dom(checker, key, cur_shapes, branch, dom_shape);
            eval_shrink_slot_rhs(checker, urhs, &slot, true, guaranteed, branch)
        }
    }
}

fn eval_shrink_slot_rhs(
    checker: &TotalityChecker<'_>,
    rhs: &Expr,
    slot: &Expr,
    allow_at: bool,
    guaranteed_slot: bool,
    branch: &ActionBranch,
) -> ShrinkEffect {
    let is_slot = |e: &Expr| (allow_at && matches!(&*e.kind, ExprKind::At)) || expr_alpha_eq(e, false, slot, false);
    if is_slot(rhs) {
        return ShrinkEffect::Unchanged;
    }
    match &*rhs.kind {
        ExprKind::SetEnum(es) if es.is_empty() => {
            ShrinkEffect::Shrink { strict: guaranteed_slot && guards_prove_nonempty_set(&branch.guards, slot) }
        }
        ExprKind::Builtin { op: B::SetMinus, args } if args.len() == 2 && is_slot(&args[0]) => {
            let strict = guaranteed_slot && is_nonempty_subset_of(&args[1], slot, branch);
            ShrinkEffect::Shrink { strict }
        }
        ExprKind::Builtin { op: B::Cup, .. } => {
            if let Some(added) = extract_cup_added(rhs, slot, allow_at) {
                if extract_singleton_elem(added).is_some() {
                    return ShrinkEffect::GrowOne;
                }
            }
            ShrinkEffect::Invalid
        }
        ExprKind::If { cond, then, els } => match eval_const_bool(checker, cond) {
            Some(true) => eval_shrink_slot_rhs(checker, then, slot, allow_at, guaranteed_slot, branch),
            Some(false) => eval_shrink_slot_rhs(checker, els, slot, allow_at, guaranteed_slot, branch),
            None => combine_shrink_effects(
                eval_shrink_slot_rhs(checker, then, slot, allow_at, guaranteed_slot, branch),
                eval_shrink_slot_rhs(checker, els, slot, allow_at, guaranteed_slot, branch),
            ),
        },
        ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => {
            eval_shrink_slot_rhs(checker, &args[0], slot, allow_at, guaranteed_slot, branch)
        }
        _ => ShrinkEffect::Invalid,
    }
}

fn combine_shrink_effects(a: ShrinkEffect, b: ShrinkEffect) -> ShrinkEffect {
    match (a, b) {
        (ShrinkEffect::Invalid, _) | (_, ShrinkEffect::Invalid) => ShrinkEffect::Invalid,
        (ShrinkEffect::GrowOne, _) | (_, ShrinkEffect::GrowOne) => ShrinkEffect::GrowOne,
        (ShrinkEffect::Shrink { strict: true }, ShrinkEffect::Shrink { strict: true }) => ShrinkEffect::Shrink { strict: true },
        (ShrinkEffect::Unchanged, ShrinkEffect::Unchanged) => ShrinkEffect::Unchanged,
        _ => ShrinkEffect::Shrink { strict: false },
    }
}

fn is_syntactic_subset_of(sub: &Expr, target: &Expr) -> bool {
    if expr_alpha_eq(sub, false, target, false) {
        return true;
    }
    match &*sub.kind {
        ExprKind::SetFilter { bound, .. } => is_syntactic_subset_of(&bound.set, target),
        ExprKind::Builtin { op: B::SetMinus, args } if args.len() == 2 => is_syntactic_subset_of(&args[0], target),
        ExprKind::Builtin { op: B::Cap, args } if args.len() == 2 => {
            is_syntactic_subset_of(&args[0], target) || is_syntactic_subset_of(&args[1], target)
        }
        ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => is_syntactic_subset_of(&args[0], target),
        _ => false,
    }
}

fn is_nonempty_subset_of(sub: &Expr, target: &Expr, branch: &ActionBranch) -> bool {
    // Case 1: `{e}` with `e \in target` in guards.
    if let Some(elem) = extract_singleton_elem(sub) {
        if guards_prove_in(&branch.guards, elem, target) {
            return true;
        }
    }
    // Case 2: local `batch` bound in `(SUBSET S) \ {{}}` (or `SUBSET S` with `batch # {}`) where `S \subseteq target`.
    if let ExprKind::Local(l) = &*sub.kind {
        if let Some((_, bound_set, _)) = branch.locals.iter().rev().find(|(id, _, _)| id == l) {
            if let ExprKind::Builtin { op: B::SetMinus, args } = &*bound_set.kind {
                if args.len() == 2
                    && matches!(&*args[1].kind, ExprKind::SetEnum(es) if es.len() == 1 && matches!(&*es[0].kind, ExprKind::SetEnum(inner) if inner.is_empty()))
                {
                    if let ExprKind::Builtin { op: B::Subset, args: sa } = &*args[0].kind {
                        if sa.len() == 1 && is_syntactic_subset_of(&sa[0], target) {
                            return true;
                        }
                    }
                }
            }
            if let ExprKind::Builtin { op: B::Subset, args: sa } = &*bound_set.kind {
                if sa.len() == 1 && is_syntactic_subset_of(&sa[0], target) && guards_prove_nonempty_set(&branch.guards, sub) {
                    return true;
                }
            }
        }
    }
    // Case 3: direct subset with non-empty guard.
    is_syntactic_subset_of(sub, target) && guards_prove_nonempty_set(&branch.guards, sub)
}
