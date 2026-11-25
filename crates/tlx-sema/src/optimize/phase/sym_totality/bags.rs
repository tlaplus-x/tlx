//! Totality, shape inference, and 32-bit count overflow checks for standard
//! `Bags` and `BagsExt!FoldBag` operators.

use super::super::equiv_sym::GroupInfo;
use super::super::sym_norm::{classify_ac_op, AcOpKind};
use super::folds::is_native_op_literal;
use super::shape::*;
use super::{CheckEnv, Shape, TotalityChecker, MAX_I32_U32};
use crate::{builtins::Builtin as B, hir::*};

pub(super) fn empty_bag_shape() -> Shape {
    Shape::Func { dom: Box::new(Shape::Bottom), exact_dom: true, range: Box::new(Shape::Bottom), max_dom: Some(0) }
}

/// Domain, range, and optional finite domain-size upper bound for any finite
/// function-like value (`Func`, `Tuple`, `Seq`, `Record`, `Bottom`, or a
/// union of function-like values).
pub(super) fn bag_fn_info(s: &Shape) -> Option<(Shape, Shape, Option<u32>)> {
    match s {
        Shape::Bottom => Some((Shape::Bottom, Shape::Bottom, Some(0))),
        Shape::Union(us) if !us.is_empty() => {
            let mut dom = Shape::Bottom;
            let mut range = Shape::Bottom;
            let mut max_dom: Option<u32> = Some(0);
            for u in us {
                let (d, r, c) = bag_fn_info(u)?;
                dom = join_shape(&dom, &d);
                range = join_shape(&range, &r);
                max_dom = max_dom.and_then(|a| c.map(|b| a.max(b)));
            }
            Some((dom, range, max_dom))
        }
        _ => fn_dom_range(s),
    }
}

/// Verify that a function-like value is a proved TLC bag (all entries have
/// positive `i32` counts `c >= 1`). Returns `Some(None)` for a provably empty
/// bag and `Some(Some((lo, hi)))` with `lo >= 1` for a non-empty proved bag.
pub(super) fn proved_bag_bounds(dom: &Shape, range: &Shape, max_dom: Option<u32>) -> Option<Option<(i32, i32)>> {
    if max_dom == Some(0) || matches!(dom, Shape::Bottom) || matches!(range, Shape::Bottom) {
        return Some(None);
    }
    match *range {
        Shape::Int(Some((lo, hi))) if lo >= 1 => Some(Some((lo, hi))),
        _ => None,
    }
}

/// Normalized function-like operand info shared between shape inference and
/// totality checking (`max_dom` resolved via `shape_universe_size` and capped
/// at `MAX_I32_U32`).
struct BagInfo {
    dom: Shape,
    range: Shape,
    max_dom: Option<u32>,
}

impl BagInfo {
    fn from_shape(s: &Shape, groups: &[GroupInfo]) -> Option<Self> {
        let (dom, range, raw_max_dom) = bag_fn_info(s)?;
        let max_dom = raw_max_dom.or_else(|| shape_universe_size(&dom, groups)).filter(|&v| v <= MAX_I32_U32);
        Some(Self { dom, range, max_dom })
    }

    fn is_empty(&self) -> bool {
        self.max_dom == Some(0) || matches!(self.dom, Shape::Bottom) || matches!(self.range, Shape::Bottom)
    }

    fn proved_counts(&self) -> Option<Option<(i32, i32)>> {
        proved_bag_bounds(&self.dom, &self.range, self.max_dom)
    }
}

/// Checked 32-bit product `factor * hi` used for worst-case bag count sums.
fn mul_i32_count(factor: u32, hi: i32) -> Option<i32> {
    i32::try_from((factor as i128) * (hi as i128)).ok()
}

/// Shared result shape for `SetToBag(S)`.
fn set_to_bag_shape(elem: Shape, exact_dom: bool, max_card: Option<u32>) -> Shape {
    if max_card == Some(0) || matches!(elem, Shape::Bottom) {
        empty_bag_shape()
    } else {
        Shape::Func { dom: Box::new(elem), exact_dom, range: Box::new(Shape::Int(Some((1, 1)))), max_dom: max_card }
    }
}

/// Shared result shape for `CopiesIn(e, B)` over a function-like operand.
fn bag_copies_in_shape(info: &BagInfo) -> Option<Shape> {
    if info.is_empty() {
        return Some(Shape::Int(Some((0, 0))));
    }
    match info.range {
        Shape::Int(Some((lo, hi))) => Some(Shape::Int(Some((lo.min(0), hi.max(0))))),
        Shape::Int(None) => Some(Shape::Int(None)),
        _ => None,
    }
}

/// Shared domain, domain-size bound, and proved count range for `B1 (+) B2`.
/// Returns `range = None` when either operand is not a proved bag or the count
/// sum overflows `i32` (inference widens unknown bounds; checking refuses `None`).
fn bag_cup_bounds(b1: &BagInfo, b2: &BagInfo, groups: &[GroupInfo]) -> (Shape, Option<u32>, Option<Shape>) {
    let dom = join_shape(&b1.dom, &b2.dom);
    let max_dom = b1
        .max_dom
        .and_then(|x| b2.max_dom.and_then(|y| x.checked_add(y)))
        .or_else(|| shape_universe_size(&dom, groups))
        .filter(|&v| v <= MAX_I32_U32);
    let range = match (b1.proved_counts(), b2.proved_counts()) {
        (Some(None), Some(None)) => Some(Shape::Bottom),
        (Some(Some(c)), Some(None)) | (Some(None), Some(Some(c))) => Some(Shape::Int(Some(c))),
        (Some(Some((l1, h1))), Some(Some((l2, h2)))) => h1.checked_add(h2).map(|hi| Shape::Int(Some((l1.min(l2), hi)))),
        _ => None,
    };
    (dom, max_dom, range)
}

/// Shared result shape for `B1 (-) B2` when operand count bounds are known and
/// overflow-free. Returns `None` when bounds are unknown or `h1 - l2` overflows
/// `i32` (inference widens unknown `Int` bounds; checking refuses `None`).
fn bag_diff_shape(b1: &BagInfo, b2: &BagInfo) -> Option<Shape> {
    if b1.is_empty() {
        return Some(empty_bag_shape());
    }
    let Shape::Int(Some((_, h1))) = b1.range else { return None };
    let max_out = if b2.is_empty() {
        h1
    } else {
        let Shape::Int(Some((l2, _))) = b2.range else { return None };
        i32::try_from((h1 as i128).max(h1 as i128 - l2 as i128)).ok()?
    };
    if max_out <= 0 {
        Some(empty_bag_shape())
    } else {
        Some(Shape::Func {
            dom: Box::new(b1.dom.clone()),
            exact_dom: false,
            range: Box::new(Shape::Int(Some((1, max_out)))),
            max_dom: b1.max_dom,
        })
    }
}

/// Shared result shape for `BagCardinality(B)` when `B` is a proved bag whose
/// worst-case total count fits in `i32`.
fn bag_card_shape(info: &BagInfo) -> Option<Shape> {
    match info.proved_counts()? {
        None => Some(Shape::Int(Some((0, 0)))),
        Some((_, hi)) => Some(Shape::Int(Some((0, mul_i32_count(info.max_dom?, hi)?)))),
    }
}

/// Shared domain-size bound and proved count range for `BagUnion(S)`.
fn bag_union_bounds(outer: &BagInfo, max_bags: Option<u32>, groups: &[GroupInfo]) -> (Option<u32>, Option<Shape>) {
    let total_dom = max_bags
        .and_then(|mb| outer.max_dom.and_then(|m| mb.checked_mul(m)))
        .or_else(|| shape_universe_size(&outer.dom, groups))
        .filter(|&v| v <= MAX_I32_U32);
    let range = match outer.proved_counts() {
        Some(None) => Some(Shape::Bottom),
        Some(Some((lo, hi))) => max_bags.and_then(|mb| mul_i32_count(mb, hi)).map(|hi_c| Shape::Int(Some((lo, hi_c)))),
        None => None,
    };
    (total_dom, range)
}

/// Shared domain-size bound and proved count range for `BagOfAll(F, B)`.
fn bag_of_all_bounds(info: &BagInfo, img: &Shape, groups: &[GroupInfo]) -> (Option<u32>, Option<Shape>) {
    let out_max_dom = info.max_dom.or_else(|| shape_universe_size(img, groups)).filter(|&v| v <= MAX_I32_U32);
    let range = match info.proved_counts() {
        Some(None) => Some(Shape::Bottom),
        Some(Some((lo, hi))) => info.max_dom.and_then(|m| mul_i32_count(m, hi)).map(|hi_c| Shape::Int(Some((lo, hi_c)))),
        None => None,
    };
    (out_max_dom, range)
}

/// Shared effective fold cardinality for `FoldBag(op, base, B)`: `0` on an
/// empty bag, checked worst-case total multiplicity `max_dom * hi` for integer
/// `+`/`*` folds, and `max_dom` for idempotent set/boolean folds.
fn fold_bag_eff_card(ac: AcOpKind, info: &BagInfo) -> Option<u32> {
    match info.proved_counts()? {
        None => Some(0),
        Some((_, hi)) => {
            let m = info.max_dom?;
            if matches!(ac, AcOpKind::IntAdd | AcOpKind::IntMul) {
                mul_i32_count(m, hi).map(|v| v as u32)
            } else {
                Some(m)
            }
        }
    }
}

/// True iff `IsABag(v)` cannot raise an evaluation error on values of shape `s`:
/// non-functions return `FALSE` without error, while function-like values must
/// have finitely enumerable, self-comparable domains with safe set cardinalities.
fn is_a_bag_arg_total(s: &Shape, groups: &[GroupInfo]) -> bool {
    match s {
        Shape::Top => false,
        Shape::Bottom | Shape::Bool | Shape::Int(_) | Shape::Str(_) | Shape::Model { .. } | Shape::Set { .. } => true,
        Shape::Func { .. } | Shape::Tuple(_) | Shape::Seq { .. } | Shape::Record(_) => fn_dom_range(s).is_some_and(|(d, _, c)| {
            shape_self_comparable(&d)
                && shape_has_safe_set_cards(&d, groups)
                && c.or_else(|| shape_universe_size(&d, groups)).is_some_and(|v| v <= MAX_I32_U32)
        }),
        Shape::Union(us) => !us.is_empty() && us.iter().all(|u| is_a_bag_arg_total(u, groups)),
    }
}

/// Extract `(f, excluded_expr)` when `set` is `DOMAIN f \cup {x}` or `{x} \cup DOMAIN f`
/// (as in `BagsExt!BagAdd`), allowing `e # x` to prove `e \in DOMAIN f`.
pub(super) fn dom_cup_singleton(set: &Expr) -> Option<(&Expr, &Expr)> {
    fn unwrap_dom(e: &Expr) -> Option<&Expr> {
        match &*e.kind {
            ExprKind::Builtin { op: B::Domain | B::BagToSet, args } if args.len() == 1 => Some(&args[0]),
            _ => None,
        }
    }
    fn unwrap_single(e: &Expr) -> Option<&Expr> {
        match &*e.kind {
            ExprKind::SetEnum(es) if es.len() == 1 => Some(&es[0]),
            _ => None,
        }
    }
    let ExprKind::Builtin { op: B::Cup, args } = &*set.kind else { return None };
    let [a, b] = args.as_slice() else { return None };
    if let (Some(f), Some(x)) = (unwrap_dom(a), unwrap_single(b)) {
        return Some((f, x));
    }
    if let (Some(x), Some(f)) = (unwrap_single(a), unwrap_dom(b)) {
        return Some((f, x));
    }
    None
}

impl<'a> TotalityChecker<'a> {
    pub(super) fn infer_bag_builtin(
        &self,
        op: B,
        args: &[Expr],
        in_prime: bool,
        vars: &[Shape],
        env: &CheckEnv,
        steps: &mut usize,
    ) -> Option<Shape> {
        match (op, args) {
            (B::EmptyBag, []) => Some(empty_bag_shape()),
            (B::IsABag, [_]) | (B::BagIn | B::SqSubseteq, [_, _]) => Some(Shape::Bool),
            (B::SetToBag, [s]) => {
                let (elem, finite, max_card) = self.infer_set_info(s, in_prime, vars, env, steps);
                Some(if finite { set_to_bag_shape(elem, self.is_exact_static_set(s), max_card) } else { Shape::Top })
            }
            (B::BagToSet, [b]) => {
                let sb = self.infer_expr(b, in_prime, vars, env, steps);
                Some(match bag_fn_info(&sb) {
                    Some((dom, _, max_dom)) => Shape::Set { elem: Box::new(dom), finite: true, max_card: max_dom },
                    None => Shape::Top,
                })
            }
            (B::CopiesIn, [_, b]) => {
                let sb = self.infer_expr(b, in_prime, vars, env, steps);
                Some(BagInfo::from_shape(&sb, self.groups).and_then(|info| bag_copies_in_shape(&info)).unwrap_or(Shape::Top))
            }
            (B::BagCup, [b1, b2]) => {
                let s1 = self.infer_expr(b1, in_prime, vars, env, steps);
                let s2 = self.infer_expr(b2, in_prime, vars, env, steps);
                let (Some(i1), Some(i2)) = (BagInfo::from_shape(&s1, self.groups), BagInfo::from_shape(&s2, self.groups)) else {
                    return Some(Shape::Top);
                };
                let (dom, max_dom, proved_range) = bag_cup_bounds(&i1, &i2, self.groups);
                let range = proved_range.unwrap_or_else(|| {
                    if (i1.is_empty() || is_int_shape(&i1.range)) && (i2.is_empty() || is_int_shape(&i2.range)) {
                        Shape::Int(None)
                    } else {
                        Shape::Top
                    }
                });
                Some(Shape::Func { dom: Box::new(dom), exact_dom: false, range: Box::new(range), max_dom })
            }
            (B::BagDiff, [b1, b2]) => {
                let s1 = self.infer_expr(b1, in_prime, vars, env, steps);
                let s2 = self.infer_expr(b2, in_prime, vars, env, steps);
                let (Some(i1), Some(i2)) = (BagInfo::from_shape(&s1, self.groups), BagInfo::from_shape(&s2, self.groups)) else {
                    return Some(Shape::Top);
                };
                Some(bag_diff_shape(&i1, &i2).unwrap_or_else(|| {
                    if is_int_shape(&i1.range) && (i2.is_empty() || is_int_shape(&i2.range)) {
                        Shape::Func { dom: Box::new(i1.dom), exact_dom: false, range: Box::new(Shape::Int(None)), max_dom: i1.max_dom }
                    } else {
                        Shape::Top
                    }
                }))
            }
            (B::BagCardinality, [b]) => {
                let sb = self.infer_expr(b, in_prime, vars, env, steps);
                Some(match BagInfo::from_shape(&sb, self.groups) {
                    Some(info) => bag_card_shape(&info).unwrap_or(Shape::Int(None)),
                    None => Shape::Top,
                })
            }
            (B::BagUnion, [s]) => {
                let (outer, finite, max_bags) = self.infer_set_info(s, in_prime, vars, env, steps);
                if !finite {
                    return Some(Shape::Top);
                }
                if max_bags == Some(0) || matches!(outer, Shape::Bottom) {
                    return Some(empty_bag_shape());
                }
                let Some(info) = BagInfo::from_shape(&outer, self.groups) else { return Some(Shape::Top) };
                let (total_dom, proved_range) = bag_union_bounds(&info, max_bags, self.groups);
                let out_range = proved_range.unwrap_or_else(|| if is_int_shape(&info.range) { Shape::Int(None) } else { Shape::Top });
                Some(Shape::Func { dom: Box::new(info.dom), exact_dom: false, range: Box::new(out_range), max_dom: total_dom })
            }
            (B::BagOfAll, [f_lam, bag]) => {
                let ExprKind::Lambda { params, body } = &*f_lam.kind else { return Some(Shape::Top) };
                let [p] = params.as_slice() else { return Some(Shape::Top) };
                let sb = self.infer_expr(bag, in_prime, vars, env, steps);
                let Some(info) = BagInfo::from_shape(&sb, self.groups) else { return Some(Shape::Top) };
                if info.is_empty() {
                    return Some(empty_bag_shape());
                }
                let mut local_env = env.clone();
                local_env.bind_local(*p, info.dom.clone(), None);
                let img = self.infer_expr(body, in_prime, vars, &local_env, steps);
                let (out_max_dom, proved_range) = bag_of_all_bounds(&info, &img, self.groups);
                let out_range = proved_range.unwrap_or_else(|| if is_int_shape(&info.range) { Shape::Int(None) } else { Shape::Top });
                Some(Shape::Func { dom: Box::new(img), exact_dom: false, range: Box::new(out_range), max_dom: out_max_dom })
            }
            (B::FoldBag, [op_lam, base, bag]) => {
                let Some(ac) = classify_ac_op(op_lam) else { return Some(Shape::Top) };
                let base_s = self.infer_expr(base, in_prime, vars, env, steps);
                let sb = self.infer_expr(bag, in_prime, vars, env, steps);
                let Some(info) = BagInfo::from_shape(&sb, self.groups) else { return Some(Shape::Top) };
                let max_iters = fold_bag_eff_card(ac, &info);
                Some(self.infer_ac_fold_shape(ac, &base_s, &info.dom, max_iters))
            }
            _ => None,
        }
    }

    pub(super) fn check_bag_form(
        &self,
        op: B,
        args: &[Expr],
        allow_prime: bool,
        in_prime: bool,
        env: &CheckEnv,
        steps: &mut usize,
    ) -> Option<bool> {
        match (op, args) {
            (B::IsABag, [b]) => {
                Some(self.check_expr(b, allow_prime, in_prime, env, steps).is_some_and(|sb| is_a_bag_arg_total(&sb, self.groups)))
            }
            (B::BagIn, [e, b]) => Some(self.check_bag_lookup(e, b, allow_prime, in_prime, env, steps).is_some()),
            (B::SqSubseteq, [b1, b2]) => {
                let ok = (|| -> Option<()> {
                    let s1 = self.check_expr(b1, allow_prime, in_prime, env, steps)?;
                    let s2 = self.check_expr(b2, allow_prime, in_prime, env, steps)?;
                    let i1 = BagInfo::from_shape(&s1, self.groups)?;
                    let i2 = BagInfo::from_shape(&s2, self.groups)?;
                    if !shapes_comparable(&i1.dom, &i2.dom)
                        || !shape_self_comparable(&i1.dom)
                        || !shape_self_comparable(&i2.dom)
                        || !shape_has_safe_set_cards(&i1.dom, self.groups)
                        || !shape_has_safe_set_cards(&i2.dom, self.groups)
                    {
                        return None;
                    }
                    i1.max_dom?;
                    i2.max_dom?;
                    let r1_ok = i1.is_empty() || is_int_shape(&i1.range);
                    let r2_ok = i2.is_empty() || is_int_shape(&i2.range);
                    (r1_ok && r2_ok).then_some(())
                })()
                .is_some();
                Some(ok)
            }
            _ => None,
        }
    }

    pub(super) fn check_bag_lookup(
        &self,
        e: &Expr,
        b: &Expr,
        allow_prime: bool,
        in_prime: bool,
        env: &CheckEnv,
        steps: &mut usize,
    ) -> Option<Shape> {
        let se = self.check_expr(e, allow_prime, in_prime, env, steps)?;
        let sb = self.check_expr(b, allow_prime, in_prime, env, steps)?;
        let info = BagInfo::from_shape(&sb, self.groups)?;
        if !shape_self_comparable(&info.dom)
            || !shape_has_safe_set_cards(&info.dom, self.groups)
            || !shape_has_safe_set_cards(&se, self.groups)
            || !shapes_comparable(&se, &info.dom)
        {
            return None;
        }
        info.max_dom?;
        bag_copies_in_shape(&info)
    }

    pub(super) fn check_bag_builtin(
        &self,
        op: B,
        args: &[Expr],
        allow_prime: bool,
        in_prime: bool,
        env: &CheckEnv,
        steps: &mut usize,
    ) -> Option<Shape> {
        match (op, args) {
            (B::EmptyBag, []) => Some(empty_bag_shape()),
            (B::SetToBag, [s]) => {
                let (elem, max_card) = self.check_enumerable_set(s, allow_prime, in_prime, env, steps)?;
                Some(set_to_bag_shape(elem, self.is_exact_static_set(s), Some(max_card)))
            }
            (B::BagToSet, [b]) => {
                let sb = self.check_expr(b, allow_prime, in_prime, env, steps)?;
                let info = BagInfo::from_shape(&sb, self.groups)?;
                if !shape_self_comparable(&info.dom) || !shape_has_safe_set_cards(&info.dom, self.groups) {
                    return None;
                }
                let card = info.max_dom?;
                Some(Shape::Set { elem: Box::new(info.dom), finite: true, max_card: Some(card) })
            }
            (B::CopiesIn, [e, b]) => self.check_bag_lookup(e, b, allow_prime, in_prime, env, steps),
            (B::BagCup, [b1, b2]) => {
                let s1 = self.check_expr(b1, allow_prime, in_prime, env, steps)?;
                let s2 = self.check_expr(b2, allow_prime, in_prime, env, steps)?;
                let i1 = BagInfo::from_shape(&s1, self.groups)?;
                let i2 = BagInfo::from_shape(&s2, self.groups)?;
                if !shapes_comparable(&i1.dom, &i2.dom)
                    || !shape_self_comparable(&i1.dom)
                    || !shape_self_comparable(&i2.dom)
                    || !shape_has_safe_set_cards(&i1.dom, self.groups)
                    || !shape_has_safe_set_cards(&i2.dom, self.groups)
                {
                    return None;
                }
                i1.max_dom?;
                i2.max_dom?;
                let (dom, max_dom, range) = bag_cup_bounds(&i1, &i2, self.groups);
                Some(Shape::Func { dom: Box::new(dom), exact_dom: false, range: Box::new(range?), max_dom: Some(max_dom?) })
            }
            (B::BagDiff, [b1, b2]) => {
                let s1 = self.check_expr(b1, allow_prime, in_prime, env, steps)?;
                let s2 = self.check_expr(b2, allow_prime, in_prime, env, steps)?;
                let i1 = BagInfo::from_shape(&s1, self.groups)?;
                let i2 = BagInfo::from_shape(&s2, self.groups)?;
                if !shapes_comparable(&i1.dom, &i2.dom)
                    || !shape_self_comparable(&i1.dom)
                    || !shape_self_comparable(&i2.dom)
                    || !shape_has_safe_set_cards(&i1.dom, self.groups)
                    || !shape_has_safe_set_cards(&i2.dom, self.groups)
                {
                    return None;
                }
                i1.max_dom?;
                i2.max_dom?;
                bag_diff_shape(&i1, &i2)
            }
            (B::BagCardinality, [b]) => {
                let sb = self.check_expr(b, allow_prime, in_prime, env, steps)?;
                let info = BagInfo::from_shape(&sb, self.groups)?;
                if !shape_self_comparable(&info.dom) || !shape_has_safe_set_cards(&info.dom, self.groups) {
                    return None;
                }
                info.max_dom?;
                bag_card_shape(&info)
            }
            (B::BagUnion, [s]) => {
                let (outer, max_bags) = self.check_enumerable_set(s, allow_prime, in_prime, env, steps)?;
                if max_bags == 0 || matches!(outer, Shape::Bottom) {
                    return Some(empty_bag_shape());
                }
                let info = BagInfo::from_shape(&outer, self.groups)?;
                if !shape_self_comparable(&info.dom) || !shape_has_safe_set_cards(&info.dom, self.groups) {
                    return None;
                }
                info.max_dom?;
                let (total_dom, range) = bag_union_bounds(&info, Some(max_bags), self.groups);
                Some(Shape::Func { dom: Box::new(info.dom), exact_dom: false, range: Box::new(range?), max_dom: Some(total_dom?) })
            }
            (B::BagOfAll, [f_lam, bag]) => {
                let ExprKind::Lambda { params, body } = &*f_lam.kind else { return None };
                let [p] = params.as_slice() else { return None };
                if is_native_op_literal(body) {
                    return None;
                }
                let sb = self.check_expr(bag, allow_prime, in_prime, env, steps)?;
                let info = BagInfo::from_shape(&sb, self.groups)?;
                info.proved_counts()?;
                if !shape_self_comparable(&info.dom) || !shape_has_safe_set_cards(&info.dom, self.groups) {
                    return None;
                }
                info.max_dom?;
                if info.is_empty() {
                    return Some(empty_bag_shape());
                }
                let mut local_env = env.clone();
                local_env.bind_local(*p, info.dom.clone(), Some((bag.clone(), in_prime)));
                let img = self.check_expr(body, allow_prime, in_prime, &local_env, steps)?;
                if !shape_self_comparable(&img) || !shape_has_safe_set_cards(&img, self.groups) {
                    return None;
                }
                let (out_max_dom, range) = bag_of_all_bounds(&info, &img, self.groups);
                Some(Shape::Func { dom: Box::new(img), exact_dom: false, range: Box::new(range?), max_dom: Some(out_max_dom?) })
            }
            (B::FoldBag, [op_lam, base, bag]) => {
                let ac = classify_ac_op(op_lam)?;
                let base_s = self.check_expr(base, allow_prime, in_prime, env, steps)?;
                let sb = self.check_expr(bag, allow_prime, in_prime, env, steps)?;
                let info = BagInfo::from_shape(&sb, self.groups)?;
                if !shape_self_comparable(&info.dom) || !shape_has_safe_set_cards(&info.dom, self.groups) {
                    return None;
                }
                info.max_dom?;
                let eff_card = fold_bag_eff_card(ac, &info)?;
                self.check_ac_fold(ac, &base_s, &info.dom, eff_card)
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_bag_cup_returns_bottom_range() {
        // Even if an empty bag carries a non-Bottom range (e.g. `max_dom = Some(0)`),
        // `bag_cup_bounds` returns `Shape::Bottom` for both inference and checking.
        let empty_with_unit_range =
            Shape::Func { dom: Box::new(Shape::Bottom), exact_dom: true, range: Box::new(Shape::Int(Some((1, 1)))), max_dom: Some(0) };
        let b1 = BagInfo::from_shape(&empty_with_unit_range, &[]).unwrap();
        let b2 = BagInfo::from_shape(&empty_with_unit_range, &[]).unwrap();
        let (dom, max_dom, range) = bag_cup_bounds(&b1, &b2, &[]);
        assert_eq!(dom, Shape::Bottom);
        assert_eq!(max_dom, Some(0));
        assert_eq!(range, Some(Shape::Bottom));
        assert_eq!(set_to_bag_shape(Shape::Bottom, true, Some(0)), empty_bag_shape());
    }

    #[test]
    fn shared_bag_bounds_overflow_and_fold_card() {
        let big = Shape::Func {
            dom: Box::new(Shape::Int(Some((1, 2)))),
            exact_dom: false,
            range: Box::new(Shape::Int(Some((1, i32::MAX)))),
            max_dom: Some(2),
        };
        let info = BagInfo::from_shape(&big, &[]).unwrap();
        assert_eq!(bag_card_shape(&info), None);
        assert_eq!(bag_union_bounds(&info, Some(2), &[]).1, None);
        assert_eq!(bag_of_all_bounds(&info, &Shape::Int(Some((1, 1))), &[]).1, None);
        assert_eq!(fold_bag_eff_card(AcOpKind::IntAdd, &info), None);
        assert_eq!(fold_bag_eff_card(AcOpKind::SetCup, &info), Some(2));
    }
}
