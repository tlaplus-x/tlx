//! Shared structural HIR walkers and predicates used by several projection
//! passes.
//!
//! These queries inspect only [`Expr`] structure: the shape of an `UNCHANGED`
//! argument, whether a variable or local is referenced, the highest allocated
//! `LocalId`, and syntactic comparison. They carry no pass-specific domain,
//! field-summary or certificate-IR rules; those stay with the pass that owns
//! them (for example the `independent` rules of the age, threshold and nested
//! ordered emitters).

use super::domain::{Atom, Domains};
use crate::builtins::Builtin as B;
use crate::hir::*;
use crate::visit;

/// True for an `UNCHANGED` argument that is a bare variable or a tuple of such
/// frames. Any computed expression makes `UNCHANGED` a guard rather than a
/// frame, so it is not accepted here.
pub(in crate::optimize::phase) fn ordinary_unchanged(e: &Expr) -> bool {
    match &*e.kind {
        ExprKind::Var(_) => true,
        ExprKind::Tuple(es) => es.iter().all(ordinary_unchanged),
        _ => false,
    }
}

/// Collect every variable expression inside an ordinary `UNCHANGED` frame that
/// is not excluded by `exclude`. Fails closed (`None`) on non-variable /
/// non-tuple expressions.
pub(in crate::optimize::phase) fn collect_unchanged_excluding(
    e: &Expr,
    exclude: &mut impl FnMut(VarId) -> bool,
    out: &mut Vec<Expr>,
) -> Option<()> {
    match &*e.kind {
        ExprKind::Var(v) => {
            if !exclude(*v) {
                out.push(e.clone());
            }
            Some(())
        }
        ExprKind::Tuple(es) => {
            for x in es {
                collect_unchanged_excluding(x, exclude, out)?;
            }
            Some(())
        }
        _ => None,
    }
}

/// Whether `e` references any state variable accepted by `selected`.
pub(in crate::optimize::phase) fn mentions_var_where(e: &Expr, selected: &mut impl FnMut(VarId) -> bool) -> bool {
    let selected_var = match &*e.kind {
        ExprKind::Var(v) => selected(*v),
        _ => false,
    };
    if selected_var {
        return true;
    }
    let mut found = false;
    visit::children(e, &mut |child| found |= mentions_var_where(child, selected));
    found
}

/// Whether `e` references state variable `var`.
pub(in crate::optimize::phase) fn mentions_var(e: &Expr, var: VarId) -> bool {
    mentions_var_where(e, &mut |v| v == var)
}

/// Whether `e` references any state variable in `vars`.
pub(in crate::optimize::phase) fn mentions_vars(e: &Expr, vars: &[VarId]) -> bool {
    mentions_var_where(e, &mut |v| vars.contains(&v))
}

/// Whether `e` references bound variable or operator parameter `local`.
pub(in crate::optimize::phase) fn mentions_local(e: &Expr, local: LocalId) -> bool {
    if matches!(&*e.kind, ExprKind::Local(id) if *id == local) {
        return true;
    }
    let mut found = false;
    visit::children(e, &mut |child| found |= mentions_local(child, local));
    found
}

/// The highest `LocalId` used by `e` or declared by one of its binders.
///
/// Bound declarations are included even when the body never references them:
/// a fresh hole allocated above this id cannot be captured by an unused bound
/// variable.
pub(in crate::optimize::phase) fn max_local(e: &Expr) -> u32 {
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

/// A natural-number scalar atom in `0..=i32::MAX`, if `domains` proves one.
pub(in crate::optimize::phase) fn atom_nat(domains: &Domains, e: &Expr) -> Option<i128> {
    let Atom::Num(n) = domains.atom_value(e)? else { return None };
    (0..=i128::from(i32::MAX)).contains(&n).then_some(n)
}

/// Whether `a` and `b` are structurally identical over the scalar, tuple,
/// set-enumeration, field, function-application and builtin applications that
/// the threshold-counter passes compare.
pub(in crate::optimize::phase) fn expr_structurally_eq(a: &Expr, b: &Expr) -> bool {
    match (&*a.kind, &*b.kind) {
        (ExprKind::Var(x), ExprKind::Var(y)) => x == y,
        (ExprKind::Local(x), ExprKind::Local(y)) => x == y,
        (ExprKind::Const(x), ExprKind::Const(y)) => x == y,
        (ExprKind::Num(x), ExprKind::Num(y)) => x == y,
        (ExprKind::Str(x), ExprKind::Str(y)) => x == y,
        (ExprKind::Bool(x), ExprKind::Bool(y)) => x == y,
        (ExprKind::Tuple(xs), ExprKind::Tuple(ys)) | (ExprKind::SetEnum(xs), ExprKind::SetEnum(ys)) => {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| expr_structurally_eq(x, y))
        }
        (ExprKind::Field { record: r1, field: f1 }, ExprKind::Field { record: r2, field: f2 }) => f1 == f2 && expr_structurally_eq(r1, r2),
        (ExprKind::FnApp { func: f1, args: a1 }, ExprKind::FnApp { func: f2, args: a2 }) => {
            a1.len() == a2.len() && expr_structurally_eq(f1, f2) && a1.iter().zip(a2).all(|(x, y)| expr_structurally_eq(x, y))
        }
        (ExprKind::Builtin { op: o1, args: a1 }, ExprKind::Builtin { op: o2, args: a2 }) => {
            o1 == o2 && a1.len() == a2.len() && a1.iter().zip(a2).all(|(x, y)| expr_structurally_eq(x, y))
        }
        _ => false,
    }
}

/// Alpha-equivalent structural equality on HIR expressions (ignoring spans).
pub(in crate::optimize::phase) fn expr_alpha_eq(a: &Expr, b: &Expr) -> bool {
    expr_alpha_eq_primed(a, false, b, false, &[])
}

/// Alpha-equivalent structural equality seeded with an initial local-binder mapping.
pub(in crate::optimize::phase) fn expr_alpha_eq_with_locals(a: &Expr, b: &Expr, locals: &[(LocalId, LocalId)]) -> bool {
    expr_alpha_eq_primed(a, false, b, false, locals)
}

/// Budgeted, bijective, prime-context-aware alpha-equivalent structural equality on HIR
/// expressions (ignoring spans and transparent `TLCEval` wrappers).
pub(in crate::optimize::phase) fn expr_alpha_eq_primed(a: &Expr, ap: bool, b: &Expr, bp: bool, locals: &[(LocalId, LocalId)]) -> bool {
    let mut map = locals.to_vec();
    let mut budget = 4096usize;
    expr_alpha_eq_rec(a, ap, b, bp, &mut map, &mut budget)
}

fn push_bound_vars_alpha(v1: &BoundVars, v2: &BoundVars, map: &mut Vec<(LocalId, LocalId)>) -> Option<usize> {
    match (v1, v2) {
        (BoundVars::Many(a), BoundVars::Many(b)) | (BoundVars::Tuple(a), BoundVars::Tuple(b)) if a.len() == b.len() => {
            for (&x, &y) in a.iter().zip(b.iter()) {
                map.push((x, y));
            }
            Some(a.len())
        }
        _ => None,
    }
}

fn expr_alpha_eq_rec(a: &Expr, ap: bool, b: &Expr, bp: bool, map: &mut Vec<(LocalId, LocalId)>, budget: &mut usize) -> bool {
    if *budget == 0 {
        return false;
    }
    *budget -= 1;
    match (&*a.kind, &*b.kind) {
        (ExprKind::Builtin { op: B::TLCEval, args }, _) if args.len() == 1 => expr_alpha_eq_rec(&args[0], ap, b, bp, map, budget),
        (_, ExprKind::Builtin { op: B::TLCEval, args }) if args.len() == 1 => expr_alpha_eq_rec(a, ap, &args[0], bp, map, budget),
        (ExprKind::Builtin { op: B::Prime, args: aa }, _) if !ap && aa.len() == 1 => expr_alpha_eq_rec(&aa[0], true, b, bp, map, budget),
        (_, ExprKind::Builtin { op: B::Prime, args: ba }) if !bp && ba.len() == 1 => expr_alpha_eq_rec(a, ap, &ba[0], true, map, budget),
        (ExprKind::Var(v1), ExprKind::Var(v2)) => v1 == v2 && ap == bp,
        (ExprKind::Local(l1), ExprKind::Local(l2)) => {
            for &(x, y) in map.iter().rev() {
                if x == *l1 || y == *l2 {
                    return x == *l1 && y == *l2;
                }
            }
            l1 == l2
        }
        (ExprKind::Const(c1), ExprKind::Const(c2)) => c1 == c2,
        (ExprKind::Num(n1), ExprKind::Num(n2)) => n1 == n2,
        (ExprKind::Decimal(d1), ExprKind::Decimal(d2)) => d1 == d2,
        (ExprKind::Str(s1), ExprKind::Str(s2)) => s1 == s2,
        (ExprKind::Bool(b1), ExprKind::Bool(b2)) => b1 == b2,
        (ExprKind::At, ExprKind::At) => true,
        (ExprKind::Field { record: r1, field: f1 }, ExprKind::Field { record: r2, field: f2 }) => {
            f1 == f2 && expr_alpha_eq_rec(r1, ap, r2, bp, map, budget)
        }
        (ExprKind::FnApp { func: f1, args: a1 }, ExprKind::FnApp { func: f2, args: a2 }) => {
            a1.len() == a2.len()
                && expr_alpha_eq_rec(f1, ap, f2, bp, map, budget)
                && a1.iter().zip(a2).all(|(x, y)| expr_alpha_eq_rec(x, ap, y, bp, map, budget))
        }
        (ExprKind::Tuple(a1), ExprKind::Tuple(a2))
        | (ExprKind::SetEnum(a1), ExprKind::SetEnum(a2))
        | (ExprKind::And(a1), ExprKind::And(a2))
        | (ExprKind::Or(a1), ExprKind::Or(a2)) => {
            a1.len() == a2.len() && a1.iter().zip(a2).all(|(x, y)| expr_alpha_eq_rec(x, ap, y, bp, map, budget))
        }
        (ExprKind::Record(f1), ExprKind::Record(f2)) | (ExprKind::RecordSet(f1), ExprKind::RecordSet(f2)) => {
            f1.len() == f2.len() && f1.iter().zip(f2).all(|((k1, v1), (k2, v2))| k1 == k2 && expr_alpha_eq_rec(v1, ap, v2, bp, map, budget))
        }
        (ExprKind::FnSet { domain: d1, range: r1 }, ExprKind::FnSet { domain: d2, range: r2 }) => {
            expr_alpha_eq_rec(d1, ap, d2, bp, map, budget) && expr_alpha_eq_rec(r1, ap, r2, bp, map, budget)
        }
        (ExprKind::If { cond: c1, then: t1, els: e1 }, ExprKind::If { cond: c2, then: t2, els: e2 }) => {
            expr_alpha_eq_rec(c1, ap, c2, bp, map, budget)
                && expr_alpha_eq_rec(t1, ap, t2, bp, map, budget)
                && expr_alpha_eq_rec(e1, ap, e2, bp, map, budget)
        }
        (ExprKind::Case { arms: a1, other: o1 }, ExprKind::Case { arms: a2, other: o2 }) => {
            a1.len() == a2.len()
                && a1.iter().zip(a2).all(|((c1, v1), (c2, v2))| {
                    expr_alpha_eq_rec(c1, ap, c2, bp, map, budget) && expr_alpha_eq_rec(v1, ap, v2, bp, map, budget)
                })
                && match (o1, o2) {
                    (Some(x), Some(y)) => expr_alpha_eq_rec(x, ap, y, bp, map, budget),
                    (None, None) => true,
                    _ => false,
                }
        }
        (ExprKind::Builtin { op: op1, args: a1 }, ExprKind::Builtin { op: op2, args: a2 }) => {
            op1 == op2 && a1.len() == a2.len() && a1.iter().zip(a2).all(|(x, y)| expr_alpha_eq_rec(x, ap, y, bp, map, budget))
        }
        (ExprKind::Apply { op: op1, args: a1 }, ExprKind::Apply { op: op2, args: a2 }) => {
            op1 == op2 && a1.len() == a2.len() && a1.iter().zip(a2).all(|(x, y)| expr_alpha_eq_rec(x, ap, y, bp, map, budget))
        }
        (ExprKind::Lambda { params: p1, body: b1 }, ExprKind::Lambda { params: p2, body: b2 }) if p1.len() == p2.len() => {
            let saved = map.len();
            for (&x, &y) in p1.iter().zip(p2.iter()) {
                map.push((x, y));
            }
            let eq = expr_alpha_eq_rec(b1, ap, b2, bp, map, budget);
            map.truncate(saved);
            eq
        }
        (ExprKind::SetFilter { bound: b1, pred: p1 }, ExprKind::SetFilter { bound: b2, pred: p2 }) => {
            if !expr_alpha_eq_rec(&b1.set, ap, &b2.set, bp, map, budget) {
                return false;
            }
            let saved = map.len();
            if push_bound_vars_alpha(&b1.vars, &b2.vars, map).is_none() {
                return false;
            }
            let eq = expr_alpha_eq_rec(p1, ap, p2, bp, map, budget);
            map.truncate(saved);
            eq
        }
        (ExprKind::SetMap { expr: e1, bounds: bs1 }, ExprKind::SetMap { expr: e2, bounds: bs2 })
        | (ExprKind::FnConstruct { bounds: bs1, body: e1 }, ExprKind::FnConstruct { bounds: bs2, body: e2 }) => {
            if bs1.len() != bs2.len() {
                return false;
            }
            let saved = map.len();
            for (b1, b2) in bs1.iter().zip(bs2.iter()) {
                if !expr_alpha_eq_rec(&b1.set, ap, &b2.set, bp, map, budget) || push_bound_vars_alpha(&b1.vars, &b2.vars, map).is_none() {
                    map.truncate(saved);
                    return false;
                }
            }
            let eq = expr_alpha_eq_rec(e1, ap, e2, bp, map, budget);
            map.truncate(saved);
            eq
        }
        (ExprKind::Quant { kind: k1, bounds: bs1, body: e1 }, ExprKind::Quant { kind: k2, bounds: bs2, body: e2 })
            if k1 == k2 && bs1.len() == bs2.len() =>
        {
            let saved = map.len();
            for (b1, b2) in bs1.iter().zip(bs2.iter()) {
                if !expr_alpha_eq_rec(&b1.set, ap, &b2.set, bp, map, budget) || push_bound_vars_alpha(&b1.vars, &b2.vars, map).is_none() {
                    map.truncate(saved);
                    return false;
                }
            }
            let eq = expr_alpha_eq_rec(e1, ap, e2, bp, map, budget);
            map.truncate(saved);
            eq
        }
        (ExprKind::Choose { vars: v1, set: s1, body: e1 }, ExprKind::Choose { vars: v2, set: s2, body: e2 }) => {
            let sets_eq = match (s1, s2) {
                (Some(x), Some(y)) => expr_alpha_eq_rec(x, ap, y, bp, map, budget),
                (None, None) => true,
                _ => false,
            };
            if !sets_eq {
                return false;
            }
            let saved = map.len();
            if push_bound_vars_alpha(v1, v2, map).is_none() {
                return false;
            }
            let eq = expr_alpha_eq_rec(e1, ap, e2, bp, map, budget);
            map.truncate(saved);
            eq
        }
        (ExprKind::Except { base: b1, updates: u1 }, ExprKind::Except { base: b2, updates: u2 }) => {
            u1.len() == u2.len()
                && expr_alpha_eq_rec(b1, ap, b2, bp, map, budget)
                && u1.iter().zip(u2).all(|((p1, r1), (p2, r2))| {
                    p1.len() == p2.len()
                        && p1.iter().zip(p2).all(|(k1, k2)| match (k1, k2) {
                            (ExceptKey::Field(f1), ExceptKey::Field(f2)) => f1 == f2,
                            (ExceptKey::Index(x1), ExceptKey::Index(x2)) => {
                                x1.len() == x2.len() && x1.iter().zip(x2).all(|(i1, i2)| expr_alpha_eq_rec(i1, ap, i2, bp, map, budget))
                            }
                            _ => false,
                        })
                        && expr_alpha_eq_rec(r1, ap, r2, bp, map, budget)
                })
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::builtins::Builtin as B;

    fn e(kind: ExprKind) -> Expr {
        Expr::new(kind, Span::default())
    }

    fn var(id: u32) -> Expr {
        e(ExprKind::Var(VarId(id)))
    }

    fn local(id: u32) -> Expr {
        e(ExprKind::Local(LocalId(id)))
    }

    fn num(n: i128) -> Expr {
        e(ExprKind::Num(n))
    }

    fn quant(bound: u32, body: Expr) -> Expr {
        let bound = Bound { vars: BoundVars::Many(vec![LocalId(bound)]), set: num(1) };
        e(ExprKind::Quant { kind: QuantKind::Forall, bounds: vec![bound], body })
    }

    #[test]
    fn ordinary_unchanged_accepts_variable_frames_only() {
        assert!(ordinary_unchanged(&var(0)));
        assert!(ordinary_unchanged(&e(ExprKind::Tuple(vec![var(0), e(ExprKind::Tuple(vec![var(1)]))]))));
        assert!(!ordinary_unchanged(&num(1)));
        assert!(!ordinary_unchanged(&e(ExprKind::Tuple(vec![var(0), num(1)]))));
        assert!(!ordinary_unchanged(&e(ExprKind::FnApp { func: var(0), args: vec![] })));

        let nested = e(ExprKind::Tuple(vec![var(0), e(ExprKind::Tuple(vec![var(1), var(2)]))]));
        let mut kept = Vec::new();
        assert!(collect_unchanged_excluding(&nested, &mut |v| v == VarId(1), &mut kept).is_some());
        assert_eq!(kept.len(), 2);
        assert!(matches!(&*kept[0].kind, ExprKind::Var(VarId(0))));
        assert!(matches!(&*kept[1].kind, ExprKind::Var(VarId(2))));
        assert!(collect_unchanged_excluding(&e(ExprKind::Tuple(vec![var(0), num(1)])), &mut |_| false, &mut kept).is_none());
    }

    #[test]
    fn mentions_var_follows_children_and_distinguishes_selection() {
        let expr = e(ExprKind::FnApp { func: var(0), args: vec![local(1), num(2)] });
        assert!(mentions_var(&expr, VarId(0)));
        assert!(!mentions_var(&expr, VarId(1)));
        assert!(mentions_var_where(&expr, &mut |v| v == VarId(0)));
        assert!(mentions_vars(&expr, &[VarId(3), VarId(0)]));
        assert!(!mentions_vars(&expr, &[VarId(2)]));
        assert!(!mentions_local(&expr, LocalId(0)));
        assert!(mentions_local(&expr, LocalId(1)));
    }

    #[test]
    fn mentions_var_sees_nested_binders() {
        let expr = quant(4, e(ExprKind::Tuple(vec![local(4), e(ExprKind::Builtin { op: B::Prime, args: vec![var(6)] })])));
        assert!(mentions_var(&expr, VarId(6)));
        assert!(!mentions_var(&expr, VarId(5)));
    }

    #[test]
    fn max_local_counts_unused_binder_declarations() {
        assert_eq!(max_local(&num(0)), 0);
        assert_eq!(max_local(&local(7)), 7);
        assert_eq!(max_local(&e(ExprKind::Tuple(vec![local(2), local(5)]))), 5);
        // The binder body does not mention local 9, but a fresh hole above the
        // reported maximum must still not capture it.
        assert_eq!(max_local(&quant(9, num(0))), 9);

        let lambda = e(ExprKind::Lambda { params: vec![LocalId(3)], body: local(1) });
        assert_eq!(max_local(&lambda), 3);

        let choose = e(ExprKind::Choose { vars: BoundVars::Tuple(vec![LocalId(8)]), set: None, body: num(0) });
        assert_eq!(max_local(&choose), 8);
    }

    #[test]
    fn expr_structurally_eq_covers_scalar_container_and_builtin_arms() {
        assert!(expr_structurally_eq(&var(0), &var(0)));
        assert!(!expr_structurally_eq(&var(0), &var(1)));

        let set = e(ExprKind::SetEnum(vec![num(1), e(ExprKind::SetEnum(vec![num(2)]))]));
        assert!(expr_structurally_eq(&set, &set));
        assert!(!expr_structurally_eq(&set, &e(ExprKind::SetEnum(vec![num(1)]))));

        let sum = |a: i128, b: i128| e(ExprKind::Builtin { op: B::Plus, args: vec![num(a), num(b)] });
        assert!(expr_structurally_eq(&sum(1, 2), &sum(1, 2)));
        assert!(!expr_structurally_eq(&sum(1, 2), &sum(2, 1)));
        assert!(!expr_structurally_eq(&sum(1, 2), &e(ExprKind::Builtin { op: B::Minus, args: vec![num(1), num(2)] })));

        let field = |f: &str| e(ExprKind::Field { record: e(ExprKind::Tuple(vec![num(0)])), field: f.into() });
        assert!(expr_structurally_eq(&field("a"), &field("a")));
        assert!(!expr_structurally_eq(&field("a"), &field("b")));

        let app = |arg: Expr| e(ExprKind::FnApp { func: var(0), args: vec![arg] });
        assert!(expr_structurally_eq(&app(num(1)), &app(num(1))));
        assert!(!expr_structurally_eq(&app(num(1)), &app(num(2))));
        assert!(!expr_structurally_eq(&e(ExprKind::Tuple(vec![num(1)])), &e(ExprKind::SetEnum(vec![num(1)]))));
    }

    #[test]
    fn expr_alpha_eq_matches_renamed_fn_binders_and_respects_free_locals() {
        let fn1 = e(ExprKind::FnConstruct {
            bounds: vec![Bound { vars: BoundVars::Many(vec![LocalId(1)]), set: var(0) }],
            body: e(ExprKind::FnApp { func: var(1), args: vec![local(1)] }),
        });
        let fn2 = e(ExprKind::FnConstruct {
            bounds: vec![Bound { vars: BoundVars::Many(vec![LocalId(9)]), set: var(0) }],
            body: e(ExprKind::FnApp { func: var(1), args: vec![local(9)] }),
        });
        assert!(expr_alpha_eq(&fn1, &fn2));
        assert!(!expr_alpha_eq(&local(1), &local(9)));
        assert!(expr_alpha_eq_with_locals(&local(1), &local(9), &[(LocalId(1), LocalId(9))]));
    }
}
