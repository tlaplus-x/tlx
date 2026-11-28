//! Finite-literal DAG potential components for finite-progress step bounds.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::Arc;

use super::super::shape::*;
use super::super::{CheckEnv, ConstInfo, Shape, TotalityChecker};
use super::branches::{eval_const_bool, key_in_exact_dom, ActionBranch, VarUpdate};
use super::MAX_DOM_SIZE;
use crate::{builtins::Builtin as B, hir::*};

const MAX_DAG_VALUES: usize = 16;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum LitVal {
    Str(Arc<str>),
    Int(i32),
    Bool(bool),
}

#[derive(Clone)]
pub(super) struct DagComponent {
    var: usize,
    dom: Option<(Shape, u32)>,
    values: BTreeSet<LitVal>,
    ranks: BTreeMap<LitVal, u32>,
    pub(super) max_potential: u32,
}

// ---- Finite-literal DAG components ----

pub(super) fn extract_lit(checker: &TotalityChecker<'_>, e: &Expr) -> Option<LitVal> {
    match &*e.kind {
        ExprKind::Str(s) => Some(LitVal::Str(s.clone())),
        ExprKind::Bool(b) => Some(LitVal::Bool(*b)),
        ExprKind::Num(n) => i32::try_from(*n).ok().map(LitVal::Int),
        ExprKind::Const(c) => match checker.consts.get(c) {
            Some(ConstInfo::Value(tlx_front::cfg::CfgValue::Str(s))) => Some(LitVal::Str(Arc::from(s.as_str()))),
            Some(ConstInfo::Value(tlx_front::cfg::CfgValue::Bool(b))) => Some(LitVal::Bool(*b)),
            Some(ConstInfo::Value(tlx_front::cfg::CfgValue::Int(n))) => i32::try_from(*n).ok().map(LitVal::Int),
            _ => None,
        },
        ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => extract_lit(checker, &args[0]),
        _ => None,
    }
}

pub(super) fn extract_finite_lit_domain(s: &Shape) -> Option<BTreeSet<LitVal>> {
    match s {
        Shape::Bool => Some(BTreeSet::from([LitVal::Bool(false), LitVal::Bool(true)])),
        Shape::Str(Some(ss)) if (2..=MAX_DAG_VALUES).contains(&ss.len()) => Some(ss.iter().cloned().map(LitVal::Str).collect()),
        Shape::Int(Some((lo, hi))) if *lo < *hi && (*hi as i128 - *lo as i128 + 1) <= MAX_DAG_VALUES as i128 => {
            Some((*lo..=*hi).map(LitVal::Int).collect())
        }
        _ => None,
    }
}

fn narrow_lit_set_from_guards(checker: &TotalityChecker<'_>, place: &Expr, base: &BTreeSet<LitVal>, guards: &[Expr]) -> BTreeSet<LitVal> {
    let mut cur = base.clone();
    for g in guards {
        narrow_lit_set_from_expr(checker, place, g, true, &mut cur);
    }
    cur
}

fn narrow_lit_set_from_expr(checker: &TotalityChecker<'_>, place: &Expr, g: &Expr, positive: bool, cur: &mut BTreeSet<LitVal>) {
    match &*g.kind {
        ExprKind::And(es) if positive => {
            for item in es {
                narrow_lit_set_from_expr(checker, place, item, true, cur);
            }
        }
        ExprKind::Or(es) if !positive => {
            for item in es {
                narrow_lit_set_from_expr(checker, place, item, false, cur);
            }
        }
        ExprKind::Builtin { op: B::Not, args } if args.len() == 1 => {
            narrow_lit_set_from_expr(checker, place, &args[0], !positive, cur);
        }
        ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 => {
            let lit = if expr_alpha_eq(&args[0], false, place, false) {
                extract_lit(checker, &args[1])
            } else if expr_alpha_eq(&args[1], false, place, false) {
                extract_lit(checker, &args[0])
            } else {
                None
            };
            if let Some(lv) = lit {
                if positive {
                    cur.retain(|x| x == &lv);
                } else {
                    cur.remove(&lv);
                }
            }
        }
        ExprKind::Builtin { op: B::Neq, args } if args.len() == 2 => {
            let lit = if expr_alpha_eq(&args[0], false, place, false) {
                extract_lit(checker, &args[1])
            } else if expr_alpha_eq(&args[1], false, place, false) {
                extract_lit(checker, &args[0])
            } else {
                None
            };
            if let Some(lv) = lit {
                if positive {
                    cur.remove(&lv);
                } else {
                    cur.retain(|x| x == &lv);
                }
            }
        }
        ExprKind::Builtin { op: B::In, args } if positive && args.len() == 2 => {
            if expr_alpha_eq(&args[0], false, place, false) {
                if let ExprKind::SetEnum(es) = &*args[1].kind {
                    if let Some(allowed) = es.iter().map(|x| extract_lit(checker, x)).collect::<Option<BTreeSet<_>>>() {
                        cur.retain(|x| allowed.contains(x));
                    }
                }
            }
        }
        ExprKind::Builtin { op: B::NotIn, args } if positive && args.len() == 2 => {
            if expr_alpha_eq(&args[0], false, place, false) {
                if let ExprKind::SetEnum(es) = &*args[1].kind {
                    for x in es {
                        if let Some(lv) = extract_lit(checker, x) {
                            cur.remove(&lv);
                        }
                    }
                }
            }
        }
        _ => {}
    }
}

/// Collect possible literal post-values of a DAG slot RHS; returns `None` if unrecognized.
/// `unchanged_marker` signals that a branch leaves the slot unchanged (adds no transition edge).
fn collect_dag_rhs_lits(
    checker: &TotalityChecker<'_>,
    e: &Expr,
    unchanged_place: &Expr,
    allow_at: bool,
    out: &mut BTreeSet<LitVal>,
    may_be_unchanged: &mut bool,
) -> bool {
    if (allow_at && matches!(&*e.kind, ExprKind::At)) || expr_alpha_eq(e, false, unchanged_place, false) {
        *may_be_unchanged = true;
        return true;
    }
    if let Some(lv) = extract_lit(checker, e) {
        out.insert(lv);
        return true;
    }
    match &*e.kind {
        ExprKind::If { cond, then, els } => match eval_const_bool(checker, cond) {
            Some(true) => collect_dag_rhs_lits(checker, then, unchanged_place, allow_at, out, may_be_unchanged),
            Some(false) => collect_dag_rhs_lits(checker, els, unchanged_place, allow_at, out, may_be_unchanged),
            None => {
                collect_dag_rhs_lits(checker, then, unchanged_place, allow_at, out, may_be_unchanged)
                    && collect_dag_rhs_lits(checker, els, unchanged_place, allow_at, out, may_be_unchanged)
            }
        },
        ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => {
            collect_dag_rhs_lits(checker, &args[0], unchanged_place, allow_at, out, may_be_unchanged)
        }
        _ => false,
    }
}

struct DagSlotTransition {
    pre: BTreeSet<LitVal>,
    post: BTreeSet<LitVal>,
    may_be_unchanged: bool,
    guaranteed_slot: bool,
}

fn collect_dag_branch_transitions(
    checker: &TotalityChecker<'_>,
    var: usize,
    dom: Option<&Shape>,
    values: &BTreeSet<LitVal>,
    cur_shapes: &[Shape],
    branch: &ActionBranch,
) -> Option<Vec<DagSlotTransition>> {
    match branch.updates[var].as_ref()? {
        VarUpdate::Unchanged => Some(Vec::new()),
        VarUpdate::Other => None,
        VarUpdate::Expr(rhs) => {
            let var_expr = Expr::new(ExprKind::Var(VarId(var as u32)), rhs.span);
            if expr_alpha_eq(rhs, false, &var_expr, false) {
                return Some(Vec::new());
            }
            let Some(dom_shape) = dom else {
                let pre = narrow_lit_set_from_guards(checker, &var_expr, values, &branch.guards);
                let mut post = BTreeSet::new();
                let mut may_unch = false;
                if !collect_dag_rhs_lits(checker, rhs, &var_expr, false, &mut post, &mut may_unch) {
                    return None;
                }
                return Some(vec![DagSlotTransition { pre, post, may_be_unchanged: may_unch, guaranteed_slot: true }]);
            };
            match &*rhs.kind {
                ExprKind::Except { base, updates } if expr_alpha_eq(base, false, &var_expr, false) && updates.len() == 1 => {
                    let (path, urhs) = &updates[0];
                    let [ExceptKey::Index(ixs)] = path.as_slice() else { return None };
                    let [key] = ixs.as_slice() else { return None };
                    let slot = Expr::new(ExprKind::FnApp { func: var_expr, args: vec![key.clone()] }, rhs.span);
                    let pre = narrow_lit_set_from_guards(checker, &slot, values, &branch.guards);
                    let mut post = BTreeSet::new();
                    let mut may_unch = false;
                    if !collect_dag_rhs_lits(checker, urhs, &slot, true, &mut post, &mut may_unch) {
                        return None;
                    }
                    let guaranteed = key_in_exact_dom(checker, key, cur_shapes, branch, dom_shape);
                    Some(vec![DagSlotTransition { pre, post, may_be_unchanged: may_unch, guaranteed_slot: guaranteed }])
                }
                ExprKind::FnConstruct { bounds, body } if bounds.len() == 1 => {
                    let BoundVars::Many(ids) = &bounds[0].vars else { return None };
                    let [u] = ids.as_slice() else { return None };
                    // Verify constructed domain matches `dom_shape`.
                    let mut env = CheckEnv::default();
                    for (id, _, sh) in &branch.locals {
                        env.bind_local(*id, sh.clone(), None);
                    }
                    let mut steps = 2000;
                    let (elem, finite, _) = checker.infer_set_info(&bounds[0].set, false, cur_shapes, &env, &mut steps);
                    if !finite || !checker.is_exact_static_set(&bounds[0].set) || &elem != dom_shape {
                        return None;
                    }
                    let u_expr = Expr::new(ExprKind::Local(*u), rhs.span);
                    let u_slot = Expr::new(ExprKind::FnApp { func: var_expr.clone(), args: vec![u_expr.clone()] }, rhs.span);
                    let mut transitions = Vec::new();
                    let mut cur = body;
                    loop {
                        match &*cur.kind {
                            _ if expr_alpha_eq(cur, false, &u_slot, false) => break,
                            ExprKind::If { cond, then, els } => {
                                if let Some(b) = eval_const_bool(checker, cond) {
                                    cur = if b { then } else { els };
                                    continue;
                                }
                                // Check `u = k` / `k = u`:
                                if let ExprKind::Builtin { op: B::Eq, args } = &*cond.kind {
                                    if args.len() == 2 {
                                        let key = if matches!(&*args[0].kind, ExprKind::Local(l) if *l == *u) {
                                            Some(&args[1])
                                        } else if matches!(&*args[1].kind, ExprKind::Local(l) if *l == *u) {
                                            Some(&args[0])
                                        } else {
                                            None
                                        };
                                        if let Some(k) = key {
                                            if !expr_mentions_local(k, *u) {
                                                let slot =
                                                    Expr::new(ExprKind::FnApp { func: var_expr.clone(), args: vec![k.clone()] }, rhs.span);
                                                let pre = narrow_lit_set_from_guards(checker, &slot, values, &branch.guards);
                                                let mut post = BTreeSet::new();
                                                let mut may_unch = false;
                                                if !collect_dag_rhs_lits(checker, then, &u_slot, false, &mut post, &mut may_unch) {
                                                    return None;
                                                }
                                                let guaranteed =
                                                    transitions.is_empty() && key_in_exact_dom(checker, k, cur_shapes, branch, dom_shape);
                                                transitions.push(DagSlotTransition {
                                                    pre,
                                                    post,
                                                    may_be_unchanged: may_unch,
                                                    guaranteed_slot: guaranteed,
                                                });
                                                cur = els;
                                                continue;
                                            }
                                        }
                                    }
                                }
                                // Check `u \in set_e` (e.g. `u \in newKids`):
                                if let ExprKind::Builtin { op: B::In, args } = &*cond.kind {
                                    if args.len() == 2 && matches!(&*args[0].kind, ExprKind::Local(l) if *l == *u) {
                                        let set_e = unwrap_const_if(checker, &args[1]);
                                        if matches!(&*set_e.kind, ExprKind::SetEnum(es) if es.is_empty()) {
                                            cur = els;
                                            continue;
                                        }
                                        let mut pre = values.clone();
                                        if let ExprKind::SetFilter { bound, pred } = &*set_e.kind {
                                            if let BoundVars::Many(fids) = &bound.vars {
                                                if fids.len() == 1 {
                                                    let f_slot = Expr::new(
                                                        ExprKind::FnApp {
                                                            func: var_expr.clone(),
                                                            args: vec![Expr::new(ExprKind::Local(fids[0]), rhs.span)],
                                                        },
                                                        rhs.span,
                                                    );
                                                    narrow_lit_set_from_expr(checker, &f_slot, pred, true, &mut pre);
                                                }
                                            }
                                        }
                                        let mut post = BTreeSet::new();
                                        let mut may_unch = false;
                                        if !collect_dag_rhs_lits(checker, then, &u_slot, false, &mut post, &mut may_unch) {
                                            return None;
                                        }
                                        transitions.push(DagSlotTransition {
                                            pre,
                                            post,
                                            may_be_unchanged: may_unch,
                                            guaranteed_slot: false,
                                        });
                                        cur = els;
                                        continue;
                                    }
                                }
                                // Generic conservative fallback: any value in `values` may transition to `then`.
                                let mut post = BTreeSet::new();
                                let mut may_unch = false;
                                if !collect_dag_rhs_lits(checker, then, &u_slot, false, &mut post, &mut may_unch) {
                                    return None;
                                }
                                transitions.push(DagSlotTransition {
                                    pre: values.clone(),
                                    post,
                                    may_be_unchanged: may_unch,
                                    guaranteed_slot: false,
                                });
                                cur = els;
                            }
                            _ => return None,
                        }
                    }
                    Some(transitions)
                }
                _ => None,
            }
        }
    }
}

fn unwrap_const_if<'a>(checker: &TotalityChecker<'_>, mut e: &'a Expr) -> &'a Expr {
    while let ExprKind::If { cond, then, els } = &*e.kind {
        match eval_const_bool(checker, cond) {
            Some(true) => e = then,
            Some(false) => e = els,
            None => break,
        }
    }
    e
}

pub(super) fn find_dag_components(checker: &TotalityChecker<'_>, cur_shapes: &[Shape], branches: &[ActionBranch]) -> Vec<DagComponent> {
    let mut out = Vec::new();
    for var in 0..checker.program.vars.len() {
        let (dom, values) = match &cur_shapes[var] {
            Shape::Func { dom, exact_dom: true, range, max_dom: Some(d) } if *d >= 1 && *d <= MAX_DOM_SIZE => {
                let Some(vals) = extract_finite_lit_domain(range) else { continue };
                (Some(((**dom).clone(), *d)), vals)
            }
            other => {
                let Some(vals) = extract_finite_lit_domain(other) else { continue };
                (None, vals)
            }
        };
        let mut edges: BTreeMap<LitVal, BTreeSet<LitVal>> = values.iter().map(|v| (v.clone(), BTreeSet::new())).collect();
        let mut valid = true;
        for b in branches {
            let Some(trans) = collect_dag_branch_transitions(checker, var, dom.as_ref().map(|(d, _)| d), &values, cur_shapes, b) else {
                valid = false;
                break;
            };
            for t in trans {
                for a in &t.pre {
                    for p in &t.post {
                        if a != p {
                            if !values.contains(p) {
                                valid = false;
                                break;
                            }
                            edges.entry(a.clone()).or_default().insert(p.clone());
                        }
                    }
                }
            }
            if !valid {
                break;
            }
        }
        if !valid || edges.values().all(BTreeSet::is_empty) {
            continue;
        }
        let Some(ranks) = compute_dag_ranks(&values, &edges) else { continue };
        let max_rank = ranks.values().copied().max().unwrap_or(0);
        if max_rank == 0 {
            continue;
        }
        let slots = dom.as_ref().map_or(1, |(_, d)| *d);
        let Some(max_potential) = slots.checked_mul(max_rank) else { continue };
        out.push(DagComponent { var, dom, values, ranks, max_potential });
    }
    out
}

/// Topological sort & longest-path-to-sink ranks on `(values, edges)`; returns `None` if cyclic.
fn compute_dag_ranks(values: &BTreeSet<LitVal>, edges: &BTreeMap<LitVal, BTreeSet<LitVal>>) -> Option<BTreeMap<LitVal, u32>> {
    let mut in_deg: BTreeMap<&LitVal, usize> = values.iter().map(|v| (v, 0)).collect();
    for targets in edges.values() {
        for t in targets {
            *in_deg.get_mut(t)? += 1;
        }
    }
    let mut q: VecDeque<&LitVal> = in_deg.iter().filter(|&(_, &d)| d == 0).map(|(&v, _)| v).collect();
    let mut topo: Vec<&LitVal> = Vec::with_capacity(values.len());
    while let Some(u) = q.pop_front() {
        topo.push(u);
        if let Some(targets) = edges.get(u) {
            for t in targets {
                let d = in_deg.get_mut(t)?;
                *d -= 1;
                if *d == 0 {
                    q.push_back(t);
                }
            }
        }
    }
    if topo.len() != values.len() {
        return None;
    }
    let mut ranks: BTreeMap<LitVal, u32> = BTreeMap::new();
    for &u in topo.iter().rev() {
        let r = edges.get(u).map_or(0, |ts| ts.iter().map(|t| ranks[t] + 1).max().unwrap_or(0));
        ranks.insert(u.clone(), r);
    }
    Some(ranks)
}

pub(super) fn eval_dag_strict_on_branch(
    checker: &TotalityChecker<'_>,
    dc: &DagComponent,
    cur_shapes: &[Shape],
    branch: &ActionBranch,
) -> bool {
    let Some(trans) = collect_dag_branch_transitions(checker, dc.var, dc.dom.as_ref().map(|(d, _)| d), &dc.values, cur_shapes, branch)
    else {
        return false;
    };
    trans.iter().any(|t| {
        if !t.guaranteed_slot || t.may_be_unchanged || t.pre.is_empty() || t.post.is_empty() {
            return false;
        }
        let min_pre = t.pre.iter().filter_map(|a| dc.ranks.get(a).copied()).min();
        let max_post = t.post.iter().filter_map(|b| dc.ranks.get(b).copied()).max();
        matches!((min_pre, max_post), (Some(a), Some(b)) if b < a)
    })
}
