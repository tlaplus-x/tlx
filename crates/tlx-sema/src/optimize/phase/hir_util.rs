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
}
