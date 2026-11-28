//! Action branch decomposition, shared-`IF` refinement, and pre-state guard queries.

use std::collections::BTreeSet;

use super::super::super::ordinary_unchanged;
use super::super::shape::*;
use super::super::{CheckEnv, Shape, TotalityChecker};
use super::dag::{extract_finite_lit_domain, extract_lit};
use super::MAX_DOM_SIZE;
use crate::{builtins::Builtin as B, hir::*};

const MAX_BRANCHES: usize = 128;

#[derive(Clone)]
pub(super) enum VarUpdate {
    Unchanged,
    Expr(Expr),
    Other,
}

#[derive(Clone)]
pub(super) struct ActionBranch {
    pub(super) locals: Vec<(LocalId, Expr, Shape)>,
    pub(super) guards: Vec<Expr>,
    pub(super) updates: Vec<Option<VarUpdate>>,
}

// ---- Constant boolean evaluation & branch decomposition ----

pub(super) fn eval_const_bool(checker: &TotalityChecker<'_>, e: &Expr) -> Option<bool> {
    match &*e.kind {
        ExprKind::Bool(b) => Some(*b),
        ExprKind::Const(c) => match checker.consts.get(c) {
            Some(super::super::ConstInfo::Value(tlx_front::cfg::CfgValue::Bool(b))) => Some(*b),
            Some(super::super::ConstInfo::Subst(did)) => match &checker.program.defs[did.idx()].kind {
                DefKind::Op(body) => eval_const_bool(checker, body),
                _ => None,
            },
            _ => None,
        },
        ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => eval_const_bool(checker, &args[0]),
        ExprKind::Builtin { op: B::Not, args } if args.len() == 1 => eval_const_bool(checker, &args[0]).map(|b| !b),
        ExprKind::And(es) => {
            let mut all_true = true;
            for item in es {
                match eval_const_bool(checker, item) {
                    Some(false) => return Some(false),
                    Some(true) => {}
                    None => all_true = false,
                }
            }
            all_true.then_some(true)
        }
        ExprKind::Or(es) => {
            let mut all_false = true;
            for item in es {
                match eval_const_bool(checker, item) {
                    Some(true) => return Some(true),
                    Some(false) => {}
                    None => all_false = false,
                }
            }
            all_false.then_some(false)
        }
        ExprKind::Builtin { op: op @ (B::Eq | B::Neq), args } if args.len() == 2 => {
            let eq = match (extract_lit(checker, &args[0]), extract_lit(checker, &args[1])) {
                (Some(a), Some(b)) => a == b,
                _ => return None,
            };
            Some(if *op == B::Eq { eq } else { !eq })
        }
        _ => None,
    }
}

fn negate_expr(e: &Expr) -> Expr {
    match &*e.kind {
        ExprKind::Builtin { op: B::Not, args } if args.len() == 1 => args[0].clone(),
        ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 => Expr::new(ExprKind::Builtin { op: B::Neq, args: args.clone() }, e.span),
        ExprKind::Builtin { op: B::Neq, args } if args.len() == 2 => Expr::new(ExprKind::Builtin { op: B::Eq, args: args.clone() }, e.span),
        _ => Expr::new(ExprKind::Builtin { op: B::Not, args: vec![e.clone()] }, e.span),
    }
}

fn push_guard(checker: &TotalityChecker<'_>, branch: &mut ActionBranch, g: Expr) -> bool {
    match eval_const_bool(checker, &g) {
        Some(false) => return false,
        Some(true) => return true,
        None => {}
    }
    match &*g.kind {
        ExprKind::And(es) => {
            for item in es {
                if !push_guard(checker, branch, item.clone()) {
                    return false;
                }
            }
            true
        }
        ExprKind::Builtin { op: B::Not, args } if args.len() == 1 => {
            if let ExprKind::Or(es) = &*args[0].kind {
                for item in es {
                    if !push_guard(checker, branch, negate_expr(item)) {
                        return false;
                    }
                }
                return true;
            }
            // Simplify `~(TRUE /\ P)` to `~P`.
            if let ExprKind::And(es) = &*args[0].kind {
                let non_true: Vec<&Expr> = es.iter().filter(|x| eval_const_bool(checker, x) != Some(true)).collect();
                if non_true.is_empty() {
                    return false;
                }
                if non_true.len() == 1 {
                    return push_guard(checker, branch, negate_expr(non_true[0]));
                }
            }
            branch.guards.push(g);
            true
        }
        _ => {
            branch.guards.push(g);
            true
        }
    }
}

pub(super) fn collect_action_branches(checker: &TotalityChecker<'_>, next: &Expr, cur_shapes: &[Shape]) -> Option<Vec<ActionBranch>> {
    let n = checker.program.vars.len();
    let seed = ActionBranch { locals: Vec::new(), guards: Vec::new(), updates: vec![None; n] };
    let mut out = Vec::new();
    split_action(checker, next, seed, cur_shapes, &mut out)?;
    // Every surviving branch must assign every state variable.
    if out.iter().any(|b| b.updates.iter().any(Option::is_none)) {
        return None;
    }
    Some(out)
}

fn split_action(
    checker: &TotalityChecker<'_>,
    e: &Expr,
    mut branch: ActionBranch,
    cur_shapes: &[Shape],
    out: &mut Vec<ActionBranch>,
) -> Option<()> {
    if out.len() >= MAX_BRANCHES {
        return None;
    }
    match &*e.kind {
        ExprKind::Bool(true) => {
            out.push(branch);
            Some(())
        }
        ExprKind::Bool(false) => Some(()),
        ExprKind::Or(es) => {
            for item in es {
                split_action(checker, item, branch.clone(), cur_shapes, out)?;
            }
            Some(())
        }
        ExprKind::And(es) => {
            let mut active = vec![branch];
            for item in es {
                let mut next_active = Vec::new();
                for b in active {
                    split_action(checker, item, b, cur_shapes, &mut next_active)?;
                    if next_active.len() > MAX_BRANCHES {
                        return None;
                    }
                }
                active = next_active;
                if active.is_empty() {
                    break;
                }
            }
            if out.len() + active.len() > MAX_BRANCHES {
                return None;
            }
            out.extend(active);
            Some(())
        }
        ExprKind::If { cond, then, els } => {
            match eval_const_bool(checker, cond) {
                Some(true) => return split_action(checker, then, branch, cur_shapes, out),
                Some(false) => return split_action(checker, els, branch, cur_shapes, out),
                None => {}
            }
            let mut t_branch = branch.clone();
            if push_guard(checker, &mut t_branch, cond.clone()) {
                split_action(checker, then, t_branch, cur_shapes, out)?;
            }
            if push_guard(checker, &mut branch, negate_expr(cond)) {
                split_action(checker, els, branch, cur_shapes, out)?;
            }
            Some(())
        }
        ExprKind::Case { arms, other } => {
            for (cond, body) in arms {
                let mut arm_branch = branch.clone();
                if push_guard(checker, &mut arm_branch, cond.clone()) {
                    split_action(checker, body, arm_branch, cur_shapes, out)?;
                }
            }
            if let Some(o) = other {
                split_action(checker, o, branch, cur_shapes, out)?;
            }
            Some(())
        }
        ExprKind::Quant { kind: QuantKind::Exists, bounds, body } => split_exists_bounds(checker, bounds, body, branch, cur_shapes, out),
        ExprKind::BoxAction { action, sub } => {
            split_action(checker, action, branch.clone(), cur_shapes, out)?;
            if ordinary_unchanged(sub) {
                let mut frame = BTreeSet::new();
                collect_var_frame(sub, &mut frame);
                for v in frame {
                    if branch.updates[v.idx()].is_none() {
                        branch.updates[v.idx()] = Some(VarUpdate::Unchanged);
                    }
                }
                out.push(branch);
                Some(())
            } else {
                None
            }
        }
        ExprKind::AngleAction { action, .. } => split_action(checker, action, branch, cur_shapes, out),
        ExprKind::Builtin { op: B::Unchanged, args } if args.len() == 1 => {
            if ordinary_unchanged(&args[0]) {
                let mut frame = BTreeSet::new();
                collect_var_frame(&args[0], &mut frame);
                for v in frame {
                    if branch.updates[v.idx()].is_none() {
                        branch.updates[v.idx()] = Some(VarUpdate::Unchanged);
                    }
                }
                out.push(branch);
                Some(())
            } else {
                None
            }
        }
        ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 => {
            if let Some(v) = target_var(&args[0], true) {
                if branch.updates[v.idx()].is_none() {
                    if expr_mentions_prime(&args[1]) {
                        return None;
                    }
                    branch.updates[v.idx()] = Some(VarUpdate::Expr(args[1].clone()));
                    out.push(branch);
                    return Some(());
                }
            }
            if expr_mentions_prime(e) {
                return None;
            }
            if push_guard(checker, &mut branch, e.clone()) {
                out.push(branch);
            }
            Some(())
        }
        ExprKind::Builtin { op: B::In | B::SubsetEq, args } if args.len() == 2 => {
            if let Some(v) = target_var(&args[0], true) {
                if branch.updates[v.idx()].is_none() {
                    if expr_mentions_prime(&args[1]) {
                        return None;
                    }
                    branch.updates[v.idx()] = Some(VarUpdate::Other);
                    out.push(branch);
                    return Some(());
                }
            }
            if expr_mentions_prime(e) {
                return None;
            }
            if push_guard(checker, &mut branch, e.clone()) {
                out.push(branch);
            }
            Some(())
        }
        ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => split_action(checker, &args[0], branch, cur_shapes, out),
        ExprKind::Builtin { op: B::Compose | B::Implies, .. } | ExprKind::Let { .. } | ExprKind::Apply { .. } => {
            if expr_mentions_prime(e) {
                None
            } else {
                if push_guard(checker, &mut branch, e.clone()) {
                    out.push(branch);
                }
                Some(())
            }
        }
        _ => {
            if expr_mentions_prime(e) {
                return None;
            }
            if push_guard(checker, &mut branch, e.clone()) {
                out.push(branch);
            }
            Some(())
        }
    }
}

fn split_exists_bounds(
    checker: &TotalityChecker<'_>,
    bounds: &[Bound],
    body: &Expr,
    branch: ActionBranch,
    cur_shapes: &[Shape],
    out: &mut Vec<ActionBranch>,
) -> Option<()> {
    if bounds.is_empty() {
        return split_action(checker, body, branch, cur_shapes, out);
    }
    let b = &bounds[0];
    let rest = &bounds[1..];
    split_bound_set_ifs(checker, &b.vars, &b.set, rest, body, branch, cur_shapes, out)
}

#[allow(clippy::too_many_arguments)]
fn split_bound_set_ifs(
    checker: &TotalityChecker<'_>,
    vars: &BoundVars,
    set: &Expr,
    rest: &[Bound],
    body: &Expr,
    mut branch: ActionBranch,
    cur_shapes: &[Shape],
    out: &mut Vec<ActionBranch>,
) -> Option<()> {
    if let ExprKind::If { cond, then, els } = &*set.kind {
        match eval_const_bool(checker, cond) {
            Some(true) => return split_bound_set_ifs(checker, vars, then, rest, body, branch, cur_shapes, out),
            Some(false) => return split_bound_set_ifs(checker, vars, els, rest, body, branch, cur_shapes, out),
            None => {}
        }
        let mut t_branch = branch.clone();
        if push_guard(checker, &mut t_branch, cond.clone()) {
            split_bound_set_ifs(checker, vars, then, rest, body, t_branch, cur_shapes, out)?;
        }
        if push_guard(checker, &mut branch, negate_expr(cond)) {
            split_bound_set_ifs(checker, vars, els, rest, body, branch, cur_shapes, out)?;
        }
        return Some(());
    }
    let mut env = CheckEnv::default();
    for (id, _, sh) in &branch.locals {
        env.bind_local(*id, sh.clone(), None);
    }
    let mut steps = 2000;
    let elem = checker.infer_set_info(set, false, cur_shapes, &env, &mut steps).0;
    match vars {
        BoundVars::Many(ids) => {
            for &id in ids {
                branch.locals.push((id, set.clone(), elem.clone()));
            }
        }
        BoundVars::Tuple(ids) => {
            if let Some(parts) = extract_exact_tuple_arity(&elem, ids.len()) {
                for (&id, p) in ids.iter().zip(parts) {
                    branch.locals.push((id, set.clone(), p));
                }
            } else {
                for &id in ids {
                    branch.locals.push((id, set.clone(), Shape::Top));
                }
            }
        }
    }
    split_exists_bounds(checker, rest, body, branch, cur_shapes, out)
}

fn expr_mentions_prime(e: &Expr) -> bool {
    if matches!(&*e.kind, ExprKind::Builtin { op: B::Prime | B::Unchanged, .. } | ExprKind::BoxAction { .. } | ExprKind::AngleAction { .. })
    {
        return true;
    }
    let mut found = false;
    crate::visit::children(e, &mut |c| {
        if !found {
            found = expr_mentions_prime(c);
        }
    });
    found
}

// ---- Shared IF splitting inside branch updates ----

pub(super) fn refine_branches_on_shared_ifs(
    checker: &TotalityChecker<'_>,
    branches: &[ActionBranch],
    cur_shapes: &[Shape],
) -> Vec<ActionBranch> {
    let mut out = Vec::new();
    for b in branches {
        let branch_locals: Vec<LocalId> = b.locals.iter().map(|(id, _, _)| *id).collect();
        let mut conds: Vec<Expr> = Vec::new();
        for (vi, upd) in b.updates.iter().enumerate() {
            let Some(VarUpdate::Expr(rhs)) = upd else { continue };
            if !is_potential_candidate_shape(&cur_shapes[vi]) {
                continue;
            }
            collect_update_if_conds(checker, rhs, &branch_locals, &mut conds);
            if conds.len() >= 2 {
                break;
            }
        }
        if conds.is_empty() {
            out.push(b.clone());
            continue;
        }
        let mut active = vec![b.clone()];
        for c in conds.into_iter().take(2) {
            let mut next = Vec::new();
            for ab in active {
                if guard_proves_true(checker, &ab.guards, &c) {
                    next.push(simplify_branch_cond(&ab, &c, true));
                } else if guard_proves_true(checker, &ab.guards, &negate_expr(&c)) {
                    next.push(simplify_branch_cond(&ab, &c, false));
                } else {
                    let mut tb = simplify_branch_cond(&ab, &c, true);
                    if push_guard(checker, &mut tb, c.clone()) {
                        next.push(tb);
                    }
                    let mut fb = simplify_branch_cond(&ab, &c, false);
                    if push_guard(checker, &mut fb, negate_expr(&c)) {
                        next.push(fb);
                    }
                }
            }
            active = next;
        }
        out.extend(active);
    }
    out
}

fn is_potential_candidate_shape(s: &Shape) -> bool {
    extract_finite_lit_domain(s).is_some()
        || matches!(s, Shape::Set { finite: true, .. })
        || matches!(
            s,
            Shape::Func { exact_dom: true, range, max_dom: Some(d), .. }
                if *d <= MAX_DOM_SIZE && (extract_finite_lit_domain(range).is_some() || matches!(&**range, Shape::Set { finite: true, .. }))
        )
}

fn push_bound_locals(vars: &BoundVars, bound: &mut Vec<LocalId>) {
    match vars {
        BoundVars::Many(ids) | BoundVars::Tuple(ids) => bound.extend(ids.iter().copied()),
    }
}

/// True iff `e` evaluates identically anywhere in the action branch (contains no `EXCEPT`-scoped
/// `@`, no primed expressions, and no free local outside `branch_locals`).
fn expr_is_branch_scoped(e: &Expr, branch_locals: &[LocalId]) -> bool {
    let mut bound = Vec::new();
    expr_is_branch_scoped_rec(e, branch_locals, &mut bound)
}

fn expr_is_branch_scoped_rec(e: &Expr, branch_locals: &[LocalId], bound: &mut Vec<LocalId>) -> bool {
    match &*e.kind {
        ExprKind::At => false,
        ExprKind::Local(l) => bound.contains(l) || branch_locals.contains(l),
        ExprKind::Builtin { op: B::Prime | B::Unchanged, .. } | ExprKind::BoxAction { .. } | ExprKind::AngleAction { .. } => false,
        ExprKind::Lambda { params, body } => {
            let saved = bound.len();
            bound.extend(params.iter().copied());
            let ok = expr_is_branch_scoped_rec(body, branch_locals, bound);
            bound.truncate(saved);
            ok
        }
        ExprKind::SetFilter { bound: b, pred } => {
            if !expr_is_branch_scoped_rec(&b.set, branch_locals, bound) {
                return false;
            }
            let saved = bound.len();
            push_bound_locals(&b.vars, bound);
            let ok = expr_is_branch_scoped_rec(pred, branch_locals, bound);
            bound.truncate(saved);
            ok
        }
        ExprKind::SetMap { expr, bounds } | ExprKind::FnConstruct { bounds, body: expr } => {
            let saved = bound.len();
            for b in bounds {
                if !expr_is_branch_scoped_rec(&b.set, branch_locals, bound) {
                    bound.truncate(saved);
                    return false;
                }
                push_bound_locals(&b.vars, bound);
            }
            let ok = expr_is_branch_scoped_rec(expr, branch_locals, bound);
            bound.truncate(saved);
            ok
        }
        ExprKind::Quant { bounds, body, .. } => {
            let saved = bound.len();
            for b in bounds {
                if !expr_is_branch_scoped_rec(&b.set, branch_locals, bound) {
                    bound.truncate(saved);
                    return false;
                }
                push_bound_locals(&b.vars, bound);
            }
            let ok = expr_is_branch_scoped_rec(body, branch_locals, bound);
            bound.truncate(saved);
            ok
        }
        ExprKind::Choose { vars, set, body } => {
            if let Some(s) = set {
                if !expr_is_branch_scoped_rec(s, branch_locals, bound) {
                    return false;
                }
            }
            let saved = bound.len();
            push_bound_locals(vars, bound);
            let ok = expr_is_branch_scoped_rec(body, branch_locals, bound);
            bound.truncate(saved);
            ok
        }
        _ => {
            let mut ok = true;
            crate::visit::children(e, &mut |child| {
                if ok {
                    ok = expr_is_branch_scoped_rec(child, branch_locals, bound);
                }
            });
            ok
        }
    }
}

fn collect_update_if_conds(checker: &TotalityChecker<'_>, e: &Expr, branch_locals: &[LocalId], out: &mut Vec<Expr>) {
    let push_unique = |c: &Expr, out: &mut Vec<Expr>| {
        if out.len() < 2
            && eval_const_bool(checker, c).is_none()
            && expr_is_branch_scoped(c, branch_locals)
            && !out.iter().any(|x| expr_alpha_eq(x, false, c, false))
        {
            out.push(c.clone());
        }
    };
    match &*e.kind {
        ExprKind::If { cond, .. } => push_unique(cond, out),
        ExprKind::Except { updates, .. } => {
            for (_, rhs) in updates {
                if let ExprKind::If { cond, .. } = &*rhs.kind {
                    push_unique(cond, out);
                }
            }
        }
        ExprKind::FnConstruct { bounds, body } if bounds.len() == 1 => {
            if let BoundVars::Many(ids) = &bounds[0].vars {
                if ids.len() == 1 {
                    let mut cur = body;
                    while let ExprKind::If { cond, then, els } = &*cur.kind {
                        push_unique(cond, out);
                        if let ExprKind::If { cond: inner_c, .. } = &*then.kind {
                            push_unique(inner_c, out);
                        }
                        cur = els;
                    }
                }
            }
        }
        _ => {}
    }
}

fn simplify_branch_cond(branch: &ActionBranch, cond: &Expr, val: bool) -> ActionBranch {
    let mut out = branch.clone();
    for upd in &mut out.updates {
        if let Some(VarUpdate::Expr(rhs)) = upd {
            *rhs = replace_if_cond(rhs, cond, val);
        }
    }
    out
}

fn replace_if_cond(e: &Expr, cond: &Expr, val: bool) -> Expr {
    if let ExprKind::If { cond: c, then, els } = &*e.kind {
        if expr_alpha_eq(c, false, cond, false) {
            return if val { replace_if_cond(then, cond, val) } else { replace_if_cond(els, cond, val) };
        }
    }
    let mut out = e.clone();
    crate::visit::children_mut(&mut out, &mut |child| {
        *child = replace_if_cond(child, cond, val);
    });
    out
}

fn guard_proves_true(checker: &TotalityChecker<'_>, guards: &[Expr], expr: &Expr) -> bool {
    if eval_const_bool(checker, expr) == Some(true) {
        return true;
    }
    if guards.iter().any(|g| expr_alpha_eq(g, false, expr, false)) {
        return true;
    }
    match &*expr.kind {
        ExprKind::Or(ds) => ds.iter().any(|d| guard_proves_true(checker, guards, d)),
        ExprKind::And(cs) => cs.iter().all(|c| guard_proves_true(checker, guards, c)),
        ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 => {
            // `S \ T = {}` holds whenever `S = {}` is proved in `guards`.
            let is_emp = |x: &Expr| matches!(&*x.kind, ExprKind::SetEnum(es) if es.is_empty());
            let target = if is_emp(&args[1]) {
                Some(&args[0])
            } else if is_emp(&args[0]) {
                Some(&args[1])
            } else {
                None
            };
            if let Some(t) = target {
                if let ExprKind::Builtin { op: B::SetMinus, args: sa } = &*t.kind {
                    if sa.len() == 2 {
                        return guards_prove_empty_set(guards, &sa[0]);
                    }
                }
            }
            false
        }
        ExprKind::Builtin { op: B::Neq, args } if args.len() == 2 => {
            let neg = Expr::new(
                ExprKind::Builtin { op: B::Not, args: vec![Expr::new(ExprKind::Builtin { op: B::Eq, args: args.clone() }, expr.span)] },
                expr.span,
            );
            let swapped = Expr::new(ExprKind::Builtin { op: B::Neq, args: vec![args[1].clone(), args[0].clone()] }, expr.span);
            guards.iter().any(|g| expr_alpha_eq(g, false, &neg, false) || expr_alpha_eq(g, false, &swapped, false))
        }
        _ => false,
    }
}

fn guards_prove_empty_set(guards: &[Expr], set: &Expr) -> bool {
    let is_emp = |x: &Expr| matches!(&*x.kind, ExprKind::SetEnum(es) if es.is_empty());
    guards.iter().any(|g| {
        matches!(
            &*g.kind,
            ExprKind::Builtin { op: B::Eq, args }
                if args.len() == 2
                    && ((expr_alpha_eq(&args[0], false, set, false) && is_emp(&args[1]))
                        || (expr_alpha_eq(&args[1], false, set, false) && is_emp(&args[0])))
        )
    })
}

pub(super) fn guards_prove_nonempty_set(guards: &[Expr], set: &Expr) -> bool {
    let is_emp = |x: &Expr| matches!(&*x.kind, ExprKind::SetEnum(es) if es.is_empty());
    guards.iter().any(|g| match &*g.kind {
        ExprKind::Builtin { op: B::Neq, args } if args.len() == 2 => {
            (expr_alpha_eq(&args[0], false, set, false) && is_emp(&args[1]))
                || (expr_alpha_eq(&args[1], false, set, false) && is_emp(&args[0]))
        }
        ExprKind::Builtin { op: B::Not, args } if args.len() == 1 => matches!(
            &*args[0].kind,
            ExprKind::Builtin { op: B::Eq, args: ea }
                if ea.len() == 2
                    && ((expr_alpha_eq(&ea[0], false, set, false) && is_emp(&ea[1]))
                        || (expr_alpha_eq(&ea[1], false, set, false) && is_emp(&ea[0])))
        ),
        ExprKind::Builtin { op: B::In, args } if args.len() == 2 => expr_alpha_eq(&args[1], false, set, false),
        _ => false,
    })
}

pub(super) fn key_in_exact_dom(
    checker: &TotalityChecker<'_>,
    key: &Expr,
    cur_shapes: &[Shape],
    branch: &ActionBranch,
    dom: &Shape,
) -> bool {
    let mut env = CheckEnv::default();
    for (id, _, sh) in &branch.locals {
        env.bind_local(*id, sh.clone(), None);
    }
    let mut steps = 2000;
    let ks = checker.infer_expr(key, false, cur_shapes, &env, &mut steps);
    !matches!(ks, Shape::Bottom | Shape::Top) && shape_in_exact_domain(&ks, dom)
}

pub(super) fn guards_prove_not_in(guards: &[Expr], elem: &Expr, set: &Expr) -> bool {
    guards.iter().any(|g| match &*g.kind {
        ExprKind::Builtin { op: B::NotIn, args } if args.len() == 2 => {
            expr_alpha_eq(&args[0], false, elem, false) && expr_alpha_eq(&args[1], false, set, false)
        }
        ExprKind::Builtin { op: B::Not, args } if args.len() == 1 => matches!(
            &*args[0].kind,
            ExprKind::Builtin { op: B::In, args: ia }
                if ia.len() == 2 && expr_alpha_eq(&ia[0], false, elem, false) && expr_alpha_eq(&ia[1], false, set, false)
        ),
        _ => false,
    })
}

pub(super) fn guards_prove_in(guards: &[Expr], elem: &Expr, set: &Expr) -> bool {
    guards.iter().any(|g| {
        matches!(
            &*g.kind,
            ExprKind::Builtin { op: B::In, args }
                if args.len() == 2 && expr_alpha_eq(&args[0], false, elem, false) && expr_alpha_eq(&args[1], false, set, false)
        )
    })
}
