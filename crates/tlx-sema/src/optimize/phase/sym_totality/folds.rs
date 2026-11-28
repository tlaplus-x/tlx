//! Totality, interval-bound, and domain-subset checks for commutative-associative
//! finite folds and index-ordered sequence folds.

use super::super::sym_norm::{classify_ac_op, is_chooses_first_lambda, AcOpKind};
use super::shape::*;
use super::{CheckEnv, Shape, TotalityChecker, MAX_I32_U32};
use crate::{builtins::Builtin as B, hir::*};

/// Single shared checked 32-bit `i32` interval calculation for commutative-associative
/// integer folds (`+` and `*`) over up to `max_card` elements, sound across every
/// evaluation order and every prefix subset (rejecting intermediate `i32` overflow and
/// `i32::MIN` sign flips).
pub(super) fn ac_int_fold_bounds(ac: AcOpKind, (bl, bh): (i32, i32), (el, eh): (i32, i32), max_card: u32) -> Option<(i32, i32)> {
    match ac {
        AcOpKind::IntAdd => {
            let lo = i32::try_from((bl as i128) + (max_card as i128) * (el.min(0) as i128)).ok()?;
            let hi = i32::try_from((bh as i128) + (max_card as i128) * (eh.max(0) as i128)).ok()?;
            Some((lo, hi))
        }
        AcOpKind::IntMul => {
            let b_abs = (bl as i128).abs().max((bh as i128).abs());
            let e_abs = (el as i128).abs().max((eh as i128).abs());
            if b_abs == 0 {
                return Some((0, 0));
            }
            if e_abs == 0 {
                return Some((bl.min(0), bh.max(0)));
            }
            if b_abs > i32::MAX as i128 {
                return None;
            }
            let mut mag = b_abs;
            if e_abs >= 2 {
                for _ in 0..max_card {
                    mag = mag.checked_mul(e_abs).filter(|&v| v <= i32::MAX as i128)?;
                }
            }
            let m = mag as i32;
            if bl >= 0 && el >= 0 {
                Some((if el >= 1 { bl } else { 0 }, m))
            } else {
                Some((-m, m))
            }
        }
        AcOpKind::SetCup | AcOpKind::SetCap | AcOpKind::BoolAnd | AcOpKind::BoolOr => None,
    }
}

/// Whether a normalized lambda body is a bare integer or string literal, which
/// `Interp::native_op_val` rejects with an `ArgumentError` (mirroring TLC's
/// SANY literal-value lookup) even on empty collections.
pub(super) fn is_native_op_literal(body: &Expr) -> bool {
    matches!(&*body.kind, ExprKind::Num(_) | ExprKind::Str(_))
}

impl<'a> TotalityChecker<'a> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn check_fold_set(
        &self,
        op_lam: &Expr,
        base: &Expr,
        set: &Expr,
        allow_prime: bool,
        in_prime: bool,
        env: &CheckEnv,
        steps: &mut usize,
    ) -> Option<Shape> {
        let ac = classify_ac_op(op_lam)?;
        let base_s = self.check_expr(base, allow_prime, in_prime, env, steps)?;
        let (elem_s, max_card) = self.check_enumerable_set(set, allow_prime, in_prime, env, steps)?;
        self.check_ac_fold(ac, &base_s, &elem_s, max_card)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn check_fold_function(
        &self,
        op_lam: &Expr,
        base: &Expr,
        fun: &Expr,
        allow_prime: bool,
        in_prime: bool,
        env: &CheckEnv,
        steps: &mut usize,
    ) -> Option<Shape> {
        let ac = classify_ac_op(op_lam)?;
        let base_s = self.check_expr(base, allow_prime, in_prime, env, steps)?;
        let fun_s = self.check_expr(fun, allow_prime, in_prime, env, steps)?;
        let (dom, range, max_dom) = fn_dom_range(&fun_s)?;
        if !shape_self_comparable(&dom) || !shape_has_safe_set_cards(&dom, self.groups) {
            return None;
        }
        let max_card = max_dom.or_else(|| shape_universe_size(&dom, self.groups)).filter(|&v| v <= MAX_I32_U32)?;
        self.check_ac_fold(ac, &base_s, &range, max_card)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn check_fold_function_on_set(
        &self,
        op_lam: &Expr,
        base: &Expr,
        fun: &Expr,
        indices: &Expr,
        allow_prime: bool,
        in_prime: bool,
        env: &CheckEnv,
        steps: &mut usize,
    ) -> Option<Shape> {
        let ac = classify_ac_op(op_lam)?;
        let base_s = self.check_expr(base, allow_prime, in_prime, env, steps)?;
        let fun_s = self.check_expr(fun, allow_prime, in_prime, env, steps)?;
        let (idx_s, max_card) = self.check_enumerable_set(indices, allow_prime, in_prime, env, steps)?;
        let val_s = if matches!(idx_s, Shape::Bottom) || max_card == 0 {
            fn_dom_range(&fun_s)?;
            Shape::Bottom
        } else if is_subset_of_fn_domain(indices, fun, in_prime) && fnapp_index_valid_for(&fun_s, &idx_s, self.groups) {
            fn_dom_range(&fun_s)?.1
        } else {
            match &fun_s {
                Shape::Func { dom, exact_dom: true, range, .. }
                    if shape_in_exact_domain(&idx_s, dom) && fnapp_index_valid_for(&fun_s, &idx_s, self.groups) =>
                {
                    (**range).clone()
                }
                Shape::Tuple(ts) => {
                    let Shape::Int(Some((lo, hi))) = idx_s else { return None };
                    if lo < 1 || (hi as usize) > ts.len() {
                        return None;
                    }
                    let mut out = Shape::Bottom;
                    for item in &ts[(lo as usize - 1)..(hi as usize)] {
                        out = join_shape(&out, item);
                    }
                    out
                }
                Shape::Seq { elem, min_len, .. } => {
                    let Shape::Int(Some((lo, hi))) = idx_s else { return None };
                    if lo < 1 || (hi as u32) > *min_len {
                        return None;
                    }
                    (**elem).clone()
                }
                Shape::Record(fs) => {
                    let Shape::Str { groups: 0, unmoved: Some(ks) } = &idx_s else { return None };
                    let mut out = Shape::Bottom;
                    for k in ks {
                        out = join_shape(&out, fs.get(k)?);
                    }
                    out
                }
                _ => return None,
            }
        };
        self.check_ac_fold(ac, &base_s, &val_s, max_card)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn check_map_then_fold_set(
        &self,
        op_lam: &Expr,
        base: &Expr,
        f_lam: &Expr,
        choose_lam: &Expr,
        set: &Expr,
        dom_superset: Option<&Expr>,
        allow_prime: bool,
        in_prime: bool,
        env: &CheckEnv,
        steps: &mut usize,
    ) -> Option<Shape> {
        let ac = classify_ac_op(op_lam)?;
        if !is_chooses_first_lambda(choose_lam) {
            return None;
        }
        let ExprKind::Lambda { params, body } = &*f_lam.kind else { return None };
        let [p] = params.as_slice() else { return None };
        let base_s = self.check_expr(base, allow_prime, in_prime, env, steps)?;
        let (elem_s, max_card) = self.check_enumerable_set(set, allow_prime, in_prime, env, steps)?;
        if let Some(superset) = dom_superset {
            let (_, sup_card) = self.check_enumerable_set(superset, allow_prime, in_prime, env, steps)?;
            if sup_card > 30 || !self.is_provably_subset_of(set, superset, &elem_s, in_prime, env) {
                return None;
            }
        }
        let mut local_env = env.clone();
        let (_, origin) = self.bound_elem_info(set, in_prime, env);
        local_env.bind_local(*p, elem_s, origin);
        let mapped_s = self.check_expr(body, allow_prime, in_prime, &local_env, steps)?;
        self.check_ac_fold(ac, &base_s, &mapped_s, max_card)
    }

    pub(super) fn check_ac_fold(&self, ac: AcOpKind, base: &Shape, elem: &Shape, max_card: u32) -> Option<Shape> {
        let empty = max_card == 0 || matches!(elem, Shape::Bottom);
        match ac {
            AcOpKind::IntAdd | AcOpKind::IntMul => {
                let Shape::Int(Some(b_bounds)) = *base else { return None };
                if empty {
                    return Some(Shape::Int(Some(b_bounds)));
                }
                let Shape::Int(Some(e_bounds)) = *elem else { return None };
                Some(Shape::Int(Some(ac_int_fold_bounds(ac, b_bounds, e_bounds, max_card)?)))
            }
            AcOpKind::SetCup => {
                let Shape::Set { elem: be, finite: true, max_card: bc } = base else { return None };
                if !shape_self_comparable(be) || !shape_has_safe_set_cards(base, self.groups) {
                    return None;
                }
                let bc_u = bc.or_else(|| shape_universe_size(be, self.groups)).filter(|&v| v <= MAX_I32_U32)?;
                if empty {
                    return Some(Shape::Set { elem: be.clone(), finite: true, max_card: Some(bc_u) });
                }
                let Shape::Set { elem: ee, finite: true, max_card: ec } = elem else { return None };
                if !shape_self_comparable(ee) || !shape_has_safe_set_cards(elem, self.groups) || !shapes_comparable(be, ee) {
                    return None;
                }
                let joined = join_shape(be, ee);
                let ec_u = ec.or_else(|| shape_universe_size(ee, self.groups)).filter(|&v| v <= MAX_I32_U32);
                let card = ec_u
                    .and_then(|e| max_card.checked_mul(e)?.checked_add(bc_u))
                    .or_else(|| shape_universe_size(&joined, self.groups))
                    .filter(|&v| v <= MAX_I32_U32)?;
                Some(Shape::Set { elem: Box::new(joined), finite: true, max_card: Some(card) })
            }
            AcOpKind::SetCap => {
                let Shape::Set { elem: be, finite: true, max_card: bc } = base else { return None };
                if !shape_self_comparable(be) || !shape_has_safe_set_cards(base, self.groups) {
                    return None;
                }
                let bc_u = bc.or_else(|| shape_universe_size(be, self.groups)).filter(|&v| v <= MAX_I32_U32)?;
                if empty {
                    return Some(Shape::Set { elem: be.clone(), finite: true, max_card: Some(bc_u) });
                }
                let Shape::Set { elem: ee, finite: true, .. } = elem else { return None };
                if !shape_self_comparable(ee)
                    || !shape_has_safe_set_cards(elem, self.groups)
                    || !shapes_comparable(be, ee)
                    || !shape_safe_for_lazy_membership(be, ee, self.groups)
                    || !shape_safe_for_lazy_membership(ee, be, self.groups)
                {
                    return None;
                }
                Some(Shape::Set { elem: be.clone(), finite: true, max_card: Some(bc_u) })
            }
            AcOpKind::BoolAnd | AcOpKind::BoolOr => (is_bool_shape(base) && (empty || is_bool_shape(elem))).then_some(Shape::Bool),
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn check_seq_fold(
        &self,
        op_lam: &Expr,
        base: &Expr,
        seq: &Expr,
        right: bool,
        on_domain: bool,
        acc_first: bool,
        allow_prime: bool,
        in_prime: bool,
        env: &CheckEnv,
        steps: &mut usize,
    ) -> Option<Shape> {
        let ExprKind::Lambda { params, body } = &*op_lam.kind else { return None };
        let [p0, p1] = params.as_slice() else { return None };
        if is_native_op_literal(body) {
            return None;
        }
        let seq_s = self.check_expr(seq, allow_prime, in_prime, env, steps)?;
        let (elem_s, _, max_len) = seq_elem_bounds(&seq_s)?;
        let max_len = max_len.filter(|&v| v <= MAX_I32_U32)?;
        let mut acc = self.check_expr(base, allow_prime, in_prime, env, steps)?;
        if max_len == 0 {
            return Some(acc);
        }
        let (acc_param, item_param) = if acc_first { (*p0, *p1) } else { (*p1, *p0) };
        let dom_origin = on_domain.then(|| (seq.clone(), in_prime));
        if let Shape::Tuple(ts) = &seq_s {
            let n = ts.len();
            if n <= 64 {
                for step_idx in 0..n {
                    let pos = if right { n - 1 - step_idx } else { step_idx };
                    let item = if on_domain { Shape::Int(Some(((pos + 1) as i32, (pos + 1) as i32))) } else { ts[pos].clone() };
                    let mut local_env = env.clone();
                    local_env.bind_local(acc_param, acc.clone(), None);
                    local_env.bind_local(item_param, item, dom_origin.clone());
                    acc = self.check_expr(body, allow_prime, in_prime, &local_env, steps)?;
                }
                return Some(acc);
            }
        }
        let item_s = if on_domain { Shape::Int(Some((1, max_len as i32))) } else { elem_s };
        let limit = max_len.min(64);
        let mut converged = false;
        for _ in 0..limit {
            let mut local_env = env.clone();
            local_env.bind_local(acc_param, acc.clone(), None);
            local_env.bind_local(item_param, item_s.clone(), dom_origin.clone());
            let next = self.check_expr(body, allow_prime, in_prime, &local_env, steps)?;
            let joined = cap_shape(join_shape(&acc, &next));
            if joined == acc {
                converged = true;
                break;
            }
            acc = joined;
        }
        if max_len > 64 && !converged {
            return None;
        }
        Some(acc)
    }

    fn is_provably_subset_of(&self, sub: &Expr, sup: &Expr, sub_elem: &Shape, in_prime: bool, env: &CheckEnv) -> bool {
        if expr_struct_eq(sub, in_prime, sup, in_prime) {
            return true;
        }
        match &*sub.kind {
            ExprKind::SetEnum(es) if es.is_empty() => return true,
            ExprKind::SetFilter { bound, .. } => return self.is_provably_subset_of(&bound.set, sup, sub_elem, in_prime, env),
            ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => {
                return self.is_provably_subset_of(&args[0], sup, sub_elem, in_prime, env);
            }
            ExprKind::Builtin { op: B::SetMinus, args } if args.len() == 2 => {
                return self.is_provably_subset_of(&args[0], sup, sub_elem, in_prime, env);
            }
            ExprKind::Builtin { op: B::Cap, args } if args.len() == 2 => {
                return self.is_provably_subset_of(&args[0], sup, sub_elem, in_prime, env)
                    || self.is_provably_subset_of(&args[1], sup, sub_elem, in_prime, env);
            }
            ExprKind::Builtin { op: B::Cup, args } if args.len() == 2 => {
                return self.is_provably_subset_of(&args[0], sup, sub_elem, in_prime, env)
                    && self.is_provably_subset_of(&args[1], sup, sub_elem, in_prime, env);
            }
            _ => {}
        }
        if self.is_exact_static_set(sup) {
            let mut steps = super::MAX_STEPS;
            let sup_elem = self.set_elem_shape(sup, in_prime, env, &mut steps);
            if shape_in_exact_domain(sub_elem, &sup_elem) {
                return true;
            }
        }
        false
    }
}

fn is_subset_of_fn_domain(indices: &Expr, fun: &Expr, in_prime: bool) -> bool {
    match &*indices.kind {
        ExprKind::Builtin { op: B::Domain, args } if args.len() == 1 => expr_struct_eq(&args[0], in_prime, fun, in_prime),
        ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => is_subset_of_fn_domain(&args[0], fun, in_prime),
        ExprKind::SetFilter { bound, .. } => is_subset_of_fn_domain(&bound.set, fun, in_prime),
        ExprKind::Builtin { op: B::SetMinus, args } if args.len() == 2 => is_subset_of_fn_domain(&args[0], fun, in_prime),
        ExprKind::Builtin { op: B::Cap, args } if args.len() == 2 => {
            is_subset_of_fn_domain(&args[0], fun, in_prime) || is_subset_of_fn_domain(&args[1], fun, in_prime)
        }
        ExprKind::Builtin { op: B::Cup, args } if args.len() == 2 => {
            is_subset_of_fn_domain(&args[0], fun, in_prime) && is_subset_of_fn_domain(&args[1], fun, in_prime)
        }
        _ => false,
    }
}
