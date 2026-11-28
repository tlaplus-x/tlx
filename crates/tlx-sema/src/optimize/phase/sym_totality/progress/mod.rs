//! Sound `Init`+`Next`-only finite-progress step bounds for monotone step counters
//! and append-only history logs.
//!
//! When a specification's `Next` relation strictly decreases a composite finite
//! natural potential `Phi(s) <= B` (`B <= 4096`) on every disjunct that increments
//! a counter (`c' = c + k`, `0 <= k <= 16`) or appends to a log (`Append(log[e], x)`),
//! and never increases `Phi(s)` on any other disjunct, the total number of mutating
//! steps in any finite execution from `Init` is bounded by `B`.
//!
//! Strictly conservative: derived exclusively from `Init` and `Next` (never from
//! checked invariants) and fails closed on any unrecognized action shape, cycle,
//! unguarded growth, or potential exceeding `MAX_PROGRESS_BOUND`.

mod branches;
mod dag;
mod sets;

use super::shape::*;
use super::{Shape, TotalityChecker, MAX_I32_U32};
use crate::{builtins::Builtin as B, hir::*};
use branches::{collect_action_branches, eval_const_bool, refine_branches_on_shared_ifs, ActionBranch, VarUpdate};
use dag::{eval_dag_strict_on_branch, find_dag_components};
use sets::{eval_grow_strict_on_branch, eval_shrink_on_branch, find_grow_set_components, find_shrink_set_components, ShrinkEffect};

pub(super) const MAX_DOM_SIZE: u32 = 16;
pub(super) const MAX_UNIV_SIZE: u32 = 16;
const MAX_STEP_DELTA: i32 = 16;
const MAX_PROGRESS_BOUND: u32 = 4096;

/// Sound progress-derived upper bound on a widened variable's integer range or
/// sequence length, proved from `Init` and `Next` alone.
#[derive(Clone, Debug)]
pub(super) enum ProgressBound {
    IntUpper { lo: i32, hi: i32 },
    SeqMaxLen(u32),
    FuncSeqMaxLen(u32),
}

pub(super) fn seed_progress_bound(shape: &Shape, bound: &ProgressBound) -> Shape {
    match (shape, bound) {
        (Shape::Int(_), ProgressBound::IntUpper { lo, hi }) => Shape::Int(Some((*lo, *hi))),
        (Shape::Seq { elem, min_len, .. }, ProgressBound::SeqMaxLen(cap)) => {
            Shape::Seq { elem: elem.clone(), min_len: *min_len, max_len: Some(*cap) }
        }
        (Shape::Func { dom, exact_dom, range, max_dom }, ProgressBound::FuncSeqMaxLen(cap)) => Shape::Func {
            dom: dom.clone(),
            exact_dom: *exact_dom,
            range: Box::new(seed_progress_bound(range, &ProgressBound::SeqMaxLen(*cap))),
            max_dom: *max_dom,
        },
        _ => shape.clone(),
    }
}

pub(super) fn apply_progress_bound(shape: &Shape, bound: &ProgressBound) -> Shape {
    match (shape, bound) {
        (Shape::Int(None), ProgressBound::IntUpper { lo, hi }) => Shape::Int(Some((*lo, *hi))),
        (Shape::Int(Some((a, b))), ProgressBound::IntUpper { lo, hi }) => {
            let nlo = (*a).max(*lo);
            let nhi = (*b).min(*hi);
            if nlo <= nhi {
                Shape::Int(Some((nlo, nhi)))
            } else {
                Shape::Int(Some((*lo, *hi)))
            }
        }
        (Shape::Seq { elem, min_len, max_len }, ProgressBound::SeqMaxLen(cap)) => {
            Shape::Seq { elem: elem.clone(), min_len: *min_len, max_len: Some(max_len.map_or(*cap, |m| m.min(*cap))) }
        }
        (Shape::Func { dom, exact_dom, range, max_dom }, ProgressBound::FuncSeqMaxLen(cap)) => Shape::Func {
            dom: dom.clone(),
            exact_dom: *exact_dom,
            range: Box::new(apply_progress_bound(range, &ProgressBound::SeqMaxLen(*cap))),
            max_dom: *max_dom,
        },
        _ => shape.clone(),
    }
}

#[derive(Clone)]
enum Candidate {
    Counter { var: usize, init_lo: i32, init_hi: i32, max_delta: i32 },
    SeqLog { var: usize, init_max: u32 },
    FuncSeqLog { var: usize, init_max: u32 },
}

/// Infer sound finite-progress bounds for widened counters and append-only logs
/// from `Init` shapes and `Next` alone.
pub(super) fn infer_progress_bounds(
    checker: &TotalityChecker<'_>,
    next: &Expr,
    init_shapes: &[Shape],
    cur_shapes: &[Shape],
) -> Vec<Option<ProgressBound>> {
    let n = checker.program.vars.len();
    let empty = vec![None; n];
    if n == 0 || !has_widened_candidate(init_shapes, cur_shapes) {
        return empty;
    }

    let Some(branches) = collect_action_branches(checker, next, cur_shapes) else {
        return empty;
    };
    if branches.is_empty() {
        return empty;
    }

    let candidates = collect_candidates(checker, init_shapes, cur_shapes, &branches);
    if candidates.is_empty() {
        return empty;
    }

    // Refine branches by splitting on shared IF conditions inside candidate DAG/Shrink updates
    // (e.g., `fin` shared between `phase'` and `pending'` in Accord's `Run(t)`).
    let refined_branches = refine_branches_on_shared_ifs(checker, &branches, cur_shapes);

    let dag_comps = find_dag_components(checker, cur_shapes, &refined_branches);
    let grow_comps = find_grow_set_components(checker, cur_shapes, &refined_branches);
    let shrink_comps = find_shrink_set_components(checker, cur_shapes, &refined_branches, &dag_comps, &grow_comps);

    if dag_comps.is_empty() && grow_comps.is_empty() && shrink_comps.is_empty() {
        return empty;
    }

    // Compute weights so that every `GrowOne` on shrink components is strictly offset by a
    // simultaneously strictly-decreasing `Dag` or `GrowSet` component on that same branch.
    let mut dag_weights = vec![1u32; dag_comps.len()];
    let mut grow_weights = vec![1u32; grow_comps.len()];
    for branch in &refined_branches {
        let grow_ones: u32 = shrink_comps
            .iter()
            .filter(|sc| matches!(eval_shrink_on_branch(checker, sc, cur_shapes, branch), ShrinkEffect::GrowOne))
            .count() as u32;
        if grow_ones == 0 {
            continue;
        }
        let needed = grow_ones.saturating_add(1);
        let mut covered = false;
        for (i, gc) in grow_comps.iter().enumerate() {
            if eval_grow_strict_on_branch(checker, gc, cur_shapes, branch) {
                grow_weights[i] = grow_weights[i].max(needed);
                covered = true;
            }
        }
        if !covered {
            for (i, dc) in dag_comps.iter().enumerate() {
                if eval_dag_strict_on_branch(checker, dc, cur_shapes, branch) {
                    dag_weights[i] = dag_weights[i].max(needed);
                    covered = true;
                }
            }
        }
        if !covered {
            return empty;
        }
    }

    // Compute total maximum potential `B = sum w_i * M_i`.
    let mut bound: u32 = 0;
    for (dc, &w) in dag_comps.iter().zip(&dag_weights) {
        let Some(next_b) = w.checked_mul(dc.max_potential).and_then(|t| bound.checked_add(t)) else {
            return empty;
        };
        bound = next_b;
    }
    for (gc, &w) in grow_comps.iter().zip(&grow_weights) {
        let Some(next_b) = w.checked_mul(gc.max_potential).and_then(|t| bound.checked_add(t)) else {
            return empty;
        };
        bound = next_b;
    }
    for sc in &shrink_comps {
        let Some(next_b) = bound.checked_add(sc.max_potential) else {
            return empty;
        };
        bound = next_b;
    }
    if bound == 0 || bound > MAX_PROGRESS_BOUND {
        return empty;
    }

    // Precompute delta upper bound of composite potential Phi on every refined branch.
    // Every branch MUST satisfy `delta_phi <= 0`!
    let mut branch_deltas: Vec<i64> = Vec::with_capacity(refined_branches.len());
    for branch in &refined_branches {
        let mut delta: i64 = 0;
        for (dc, &w) in dag_comps.iter().zip(&dag_weights) {
            if eval_dag_strict_on_branch(checker, dc, cur_shapes, branch) {
                delta -= i64::from(w);
            }
        }
        for (gc, &w) in grow_comps.iter().zip(&grow_weights) {
            if eval_grow_strict_on_branch(checker, gc, cur_shapes, branch) {
                delta -= i64::from(w);
            }
        }
        for sc in &shrink_comps {
            match eval_shrink_on_branch(checker, sc, cur_shapes, branch) {
                ShrinkEffect::Unchanged | ShrinkEffect::Shrink { strict: false } => {}
                ShrinkEffect::Shrink { strict: true } => delta -= 1,
                ShrinkEffect::GrowOne => delta += 1,
                ShrinkEffect::Invalid => return empty,
            }
        }
        if delta > 0 {
            return empty;
        }
        branch_deltas.push(delta);
    }

    // Certify each candidate whose EVERY mutating branch has `delta_phi <= -1`.
    let mut out = vec![None; n];
    for cand in candidates {
        let mut all_ok = true;
        for (branch, &delta) in refined_branches.iter().zip(&branch_deltas) {
            let mutates = match &cand {
                Candidate::Counter { var, .. } => match branch.updates[*var].as_ref() {
                    Some(VarUpdate::Unchanged) => false,
                    Some(VarUpdate::Expr(rhs)) => counter_delta(checker, *var, rhs).is_none_or(|d| d > 0),
                    _ => true,
                },
                Candidate::SeqLog { var, .. } => match branch.updates[*var].as_ref() {
                    Some(VarUpdate::Unchanged) => false,
                    Some(VarUpdate::Expr(rhs)) => seq_log_delta(checker, *var, rhs).is_none_or(|d| d > 0),
                    _ => true,
                },
                Candidate::FuncSeqLog { var, .. } => match branch.updates[*var].as_ref() {
                    Some(VarUpdate::Unchanged) => false,
                    Some(VarUpdate::Expr(rhs)) => func_seq_log_delta(checker, *var, rhs).is_none_or(|d| d > 0),
                    _ => true,
                },
            };
            if mutates && delta >= 0 {
                all_ok = false;
                break;
            }
        }
        if !all_ok {
            continue;
        }
        match cand {
            Candidate::Counter { var, init_lo, init_hi, max_delta } => {
                let Some(hi) = i32::try_from(i128::from(init_hi) + i128::from(max_delta) * i128::from(bound)).ok() else {
                    continue;
                };
                if init_lo <= hi {
                    out[var] = Some(ProgressBound::IntUpper { lo: init_lo, hi });
                }
            }
            Candidate::SeqLog { var, init_max } => {
                if let Some(cap) = init_max.checked_add(bound).filter(|&v| v <= MAX_I32_U32) {
                    out[var] = Some(ProgressBound::SeqMaxLen(cap));
                }
            }
            Candidate::FuncSeqLog { var, init_max } => {
                if let Some(cap) = init_max.checked_add(bound).filter(|&v| v <= MAX_I32_U32) {
                    out[var] = Some(ProgressBound::FuncSeqMaxLen(cap));
                }
            }
        }
    }
    out
}

fn has_widened_candidate(init_shapes: &[Shape], cur_shapes: &[Shape]) -> bool {
    init_shapes.iter().zip(cur_shapes).any(|(init, cur)| {
        matches!((init, cur), (Shape::Int(Some(_)), Shape::Int(None)))
            || (seq_elem_bounds(init).is_some_and(|(_, _, hi)| hi.is_some()) && matches!(cur, Shape::Seq { max_len: None, .. }))
            || matches!(
                (init, cur),
                (Shape::Func { range: r1, .. }, Shape::Func { range: r2, .. })
                    if seq_elem_bounds(r1).is_some_and(|(_, _, hi)| hi.is_some())
                        && matches!(&**r2, Shape::Seq { max_len: None, .. })
            )
    })
}

// ---- Candidate counters & append-only logs ----

fn collect_candidates(
    checker: &TotalityChecker<'_>,
    init_shapes: &[Shape],
    cur_shapes: &[Shape],
    branches: &[ActionBranch],
) -> Vec<Candidate> {
    let mut out = Vec::new();
    for var in 0..checker.program.vars.len() {
        if let (Shape::Int(Some((init_lo, init_hi))), Shape::Int(None)) = (&init_shapes[var], &cur_shapes[var]) {
            let mut max_delta = 0i32;
            let mut ok = true;
            for b in branches {
                match b.updates[var].as_ref() {
                    Some(VarUpdate::Unchanged) => {}
                    Some(VarUpdate::Expr(rhs)) => match counter_delta(checker, var, rhs) {
                        Some(d) => max_delta = max_delta.max(d),
                        None => {
                            ok = false;
                            break;
                        }
                    },
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok && max_delta > 0 {
                out.push(Candidate::Counter { var, init_lo: *init_lo, init_hi: *init_hi, max_delta });
            }
            continue;
        }
        if let (Some((_, _, Some(init_max))), Shape::Seq { max_len: None, .. }) = (seq_elem_bounds(&init_shapes[var]), &cur_shapes[var]) {
            let mut any_mut = false;
            let mut ok = true;
            for b in branches {
                match b.updates[var].as_ref() {
                    Some(VarUpdate::Unchanged) => {}
                    Some(VarUpdate::Expr(rhs)) => match seq_log_delta(checker, var, rhs) {
                        Some(d) => any_mut |= d > 0,
                        None => {
                            ok = false;
                            break;
                        }
                    },
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok && any_mut {
                out.push(Candidate::SeqLog { var, init_max });
            }
            continue;
        }
        if let (Shape::Func { range: r1, .. }, Shape::Func { range: r2, .. }) = (&init_shapes[var], &cur_shapes[var]) {
            if let (Some((_, _, Some(init_max))), Shape::Seq { max_len: None, .. }) = (seq_elem_bounds(r1), &**r2) {
                let mut any_mut = false;
                let mut ok = true;
                for b in branches {
                    match b.updates[var].as_ref() {
                        Some(VarUpdate::Unchanged) => {}
                        Some(VarUpdate::Expr(rhs)) => match func_seq_log_delta(checker, var, rhs) {
                            Some(d) => any_mut |= d > 0,
                            None => {
                                ok = false;
                                break;
                            }
                        },
                        _ => {
                            ok = false;
                            break;
                        }
                    }
                }
                if ok && any_mut {
                    out.push(Candidate::FuncSeqLog { var, init_max });
                }
            }
        }
    }
    out
}

fn counter_delta(checker: &TotalityChecker<'_>, var: usize, rhs: &Expr) -> Option<i32> {
    match &*rhs.kind {
        ExprKind::Var(v) if v.idx() == var => Some(0),
        ExprKind::Builtin { op: B::Plus, args } if args.len() == 2 => {
            if matches!(&*args[0].kind, ExprKind::Var(v) if v.idx() == var) {
                checker.const_exact_i32(&args[1]).filter(|&k| (0..=MAX_STEP_DELTA).contains(&k))
            } else if matches!(&*args[1].kind, ExprKind::Var(v) if v.idx() == var) {
                checker.const_exact_i32(&args[0]).filter(|&k| (0..=MAX_STEP_DELTA).contains(&k))
            } else {
                None
            }
        }
        ExprKind::If { cond, then, els } => match eval_const_bool(checker, cond) {
            Some(true) => counter_delta(checker, var, then),
            Some(false) => counter_delta(checker, var, els),
            None => Some(counter_delta(checker, var, then)?.max(counter_delta(checker, var, els)?)),
        },
        ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => counter_delta(checker, var, &args[0]),
        _ => None,
    }
}

fn seq_log_delta(checker: &TotalityChecker<'_>, var: usize, rhs: &Expr) -> Option<u32> {
    match &*rhs.kind {
        ExprKind::Var(v) if v.idx() == var => Some(0),
        ExprKind::Builtin { op: B::Append, args } if args.len() == 2 && matches!(&*args[0].kind, ExprKind::Var(v) if v.idx() == var) => {
            Some(1)
        }
        ExprKind::If { cond, then, els } => match eval_const_bool(checker, cond) {
            Some(true) => seq_log_delta(checker, var, then),
            Some(false) => seq_log_delta(checker, var, els),
            None => Some(seq_log_delta(checker, var, then)?.max(seq_log_delta(checker, var, els)?)),
        },
        ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => seq_log_delta(checker, var, &args[0]),
        _ => None,
    }
}

fn func_seq_log_slot_delta(checker: &TotalityChecker<'_>, var: usize, key: &Expr, rhs: &Expr, allow_at: bool) -> Option<u32> {
    let is_slot = |e: &Expr| -> bool {
        (allow_at && matches!(&*e.kind, ExprKind::At))
            || matches!(
                &*e.kind,
                ExprKind::FnApp { func, args }
                    if args.len() == 1
                        && matches!(&*func.kind, ExprKind::Var(v) if v.idx() == var)
                        && expr_alpha_eq(&args[0], false, key, false)
            )
    };
    match &*rhs.kind {
        _ if is_slot(rhs) => Some(0),
        ExprKind::Builtin { op: B::Append, args } if args.len() == 2 && is_slot(&args[0]) => Some(1),
        ExprKind::If { cond, then, els } => match eval_const_bool(checker, cond) {
            Some(true) => func_seq_log_slot_delta(checker, var, key, then, allow_at),
            Some(false) => func_seq_log_slot_delta(checker, var, key, els, allow_at),
            None => Some(
                func_seq_log_slot_delta(checker, var, key, then, allow_at)?.max(func_seq_log_slot_delta(checker, var, key, els, allow_at)?),
            ),
        },
        ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => func_seq_log_slot_delta(checker, var, key, &args[0], allow_at),
        _ => None,
    }
}

fn func_seq_log_delta(checker: &TotalityChecker<'_>, var: usize, rhs: &Expr) -> Option<u32> {
    match &*rhs.kind {
        ExprKind::Var(v) if v.idx() == var => Some(0),
        ExprKind::Except { base, updates } if matches!(&*base.kind, ExprKind::Var(v) if v.idx() == var) && updates.len() == 1 => {
            let (path, urhs) = &updates[0];
            let [ExceptKey::Index(ixs)] = path.as_slice() else { return None };
            let [key] = ixs.as_slice() else { return None };
            func_seq_log_slot_delta(checker, var, key, urhs, true)
        }
        ExprKind::FnConstruct { bounds, body } if bounds.len() == 1 => {
            let BoundVars::Many(ids) = &bounds[0].vars else { return None };
            let [u] = ids.as_slice() else { return None };
            let key = Expr::new(ExprKind::Local(*u), rhs.span);
            func_seq_log_slot_delta(checker, var, &key, body, false)
        }
        ExprKind::If { cond, then, els } => match eval_const_bool(checker, cond) {
            Some(true) => func_seq_log_delta(checker, var, then),
            Some(false) => func_seq_log_delta(checker, var, els),
            None => Some(func_seq_log_delta(checker, var, then)?.max(func_seq_log_delta(checker, var, els)?)),
        },
        ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => func_seq_log_delta(checker, var, &args[0]),
        _ => None,
    }
}
