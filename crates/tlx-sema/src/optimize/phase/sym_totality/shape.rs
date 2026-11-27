//! Checked 32-bit interval arithmetic, shape lattice operations, comparability,
//! lazy-membership safety, and container projection helpers.

use std::collections::BTreeSet;
use std::sync::Arc;

use super::super::equiv_sym::GroupInfo;
use super::{
    CheckEnv, GroupMask, IntBoundHint, MvType, PlaceKey, Shape, MAX_I32_U32, MAX_SHAPE_DEPTH, MAX_SHAPE_NODES, MAX_STR_SET,
    MAX_UNION_MEMBERS, MAX_UNMOVED_SET,
};
use crate::{builtins::Builtin as B, hir::*};

pub(super) fn arith_add((al, ah): (i32, i32), (bl, bh): (i32, i32)) -> Option<(i32, i32)> {
    let lo = i32::try_from(al as i128 + bl as i128).ok()?;
    let hi = i32::try_from(ah as i128 + bh as i128).ok()?;
    Some((lo, hi))
}

pub(super) fn arith_sub((al, ah): (i32, i32), (bl, bh): (i32, i32)) -> Option<(i32, i32)> {
    let lo = i32::try_from(al as i128 - bh as i128).ok()?;
    let hi = i32::try_from(ah as i128 - bl as i128).ok()?;
    Some((lo, hi))
}

pub(super) fn arith_mul((al, ah): (i32, i32), (bl, bh): (i32, i32)) -> Option<(i32, i32)> {
    let corners = [al as i128 * bl as i128, al as i128 * bh as i128, ah as i128 * bl as i128, ah as i128 * bh as i128];
    let lo = i32::try_from(*corners.iter().min()?).ok()?;
    let hi = i32::try_from(*corners.iter().max()?).ok()?;
    Some((lo, hi))
}

pub(super) fn arith_neg(lo: i32, hi: i32) -> Option<(i32, i32)> {
    let nlo = i32::try_from(-(hi as i128)).ok()?;
    let nhi = i32::try_from(-(lo as i128)).ok()?;
    Some((nlo, nhi))
}

/// Conservative positive-divisor `\div` covering BOTH `Integers` (floor) and `Naturals` (quirky trunc).
pub(super) fn arith_div_pos((al, ah): (i32, i32), (bl, bh): (i32, i32)) -> Option<(i32, i32)> {
    if bl <= 0 {
        return None;
    }
    let mut lo = i32::MAX;
    let mut hi = i32::MIN;
    for a in [al, ah] {
        for b in [bl, bh] {
            let floor = a.div_euclid(b);
            let mut nat = a.wrapping_div(b);
            if nat < 0 && nat.wrapping_mul(b) != a {
                nat -= 1;
            }
            lo = lo.min(floor).min(nat);
            hi = hi.max(floor).max(nat);
        }
    }
    Some((lo, hi))
}

pub(super) fn arith_mod_pos(_: (i32, i32), (bl, bh): (i32, i32)) -> Option<(i32, i32)> {
    if bl <= 0 {
        return None;
    }
    Some((0, bh - 1))
}

pub(super) fn arith_pow((al, ah): (i32, i32), (bl, bh): (i32, i32)) -> Option<(i32, i32)> {
    if al < 0 || bl < 0 || (al == 0 && bl == 0) {
        return None;
    }
    let lo = if bl == 0 {
        1
    } else if al == 0 {
        0
    } else {
        i32::try_from((al as i128).checked_pow(bl as u32)?).ok()?
    };
    let hi = i32::try_from((ah as i128).checked_pow(bh as u32)?).ok()?;
    Some((lo.min(hi), lo.max(hi)))
}

pub(super) fn arith_bin_shape(a: Shape, b: Shape, op: fn((i32, i32), (i32, i32)) -> Option<(i32, i32)>) -> Shape {
    match (a, b) {
        (Shape::Bottom, _) | (_, Shape::Bottom) => Shape::Bottom,
        (Shape::Int(Some(ba)), Shape::Int(Some(bb))) => op(ba, bb).map_or(Shape::Int(None), |r| Shape::Int(Some(r))),
        (Shape::Int(_), Shape::Int(_)) => Shape::Int(None),
        _ => Shape::Top,
    }
}

// ---- Shape lattice & comparability helpers ----

pub(super) fn place_key_of(e: &Expr, in_prime: bool) -> Option<PlaceKey> {
    match &*e.kind {
        ExprKind::Local(l) => Some(PlaceKey::Local(*l)),
        ExprKind::Var(v) => Some(PlaceKey::Var(*v, in_prime)),
        ExprKind::Builtin { op: B::Prime, args } if !in_prime && args.len() == 1 => match &*args[0].kind {
            ExprKind::Var(v) => Some(PlaceKey::Var(*v, true)),
            _ => None,
        },
        _ => None,
    }
}

pub(super) fn fn_app_place(func: &Expr, args: &[Expr], in_prime: bool) -> Option<(VarId, bool, Vec<PlaceKey>)> {
    if args.len() != 1 {
        return None;
    }
    let last_key = place_key_of(&args[0], in_prime)?;
    let mut keys = vec![last_key];
    let mut cur = func;
    for _ in 0..8 {
        match &*cur.kind {
            ExprKind::Var(v) => {
                keys.reverse();
                return Some((*v, in_prime, keys));
            }
            ExprKind::Builtin { op: B::Prime, args: pa } if !in_prime && pa.len() == 1 => match &*pa[0].kind {
                ExprKind::Var(v) => {
                    keys.reverse();
                    return Some((*v, true, keys));
                }
                _ => return None,
            },
            ExprKind::FnApp { func: inner, args: iargs } if iargs.len() == 1 => {
                keys.push(place_key_of(&iargs[0], in_prime)?);
                cur = inner;
            }
            _ => return None,
        }
    }
    None
}

/// Resolve the `@` shape for an `EXCEPT` update, consulting `env.fn_app_overrides` when the base
/// variable has not yet been modified by an earlier update in the same `EXCEPT`.
pub(super) fn except_old_at_shape(base: &Expr, cur: &Shape, path: &[ExceptKey], in_prime: bool, env: &CheckEnv, unmodified: bool) -> Shape {
    if unmodified {
        let base_var = match &*base.kind {
            ExprKind::Var(v) => Some((*v, in_prime)),
            ExprKind::Builtin { op: B::Prime, args: pa } if !in_prime && pa.len() == 1 => match &*pa[0].kind {
                ExprKind::Var(v) => Some((*v, true)),
                _ => None,
            },
            _ => None,
        };
        if let Some((v, primed)) = base_var {
            let mut prefix_keys = Vec::new();
            for step in path {
                let ExceptKey::Index(ixs) = step else { break };
                if ixs.len() != 1 {
                    break;
                }
                let Some(pk) = place_key_of(&ixs[0], in_prime) else { break };
                prefix_keys.push(pk);
            }
            for len in (1..=prefix_keys.len()).rev() {
                if let Some(ov) = env.fn_app_overrides.get(&(v, primed, prefix_keys[..len].to_vec())) {
                    return lookup_except_path(ov, &path[len..]);
                }
            }
        }
    }
    lookup_except_path(cur, path)
}

pub(super) fn tighten_shape_with_hint(shape: &Shape, hint: &IntBoundHint) -> Shape {
    match (shape, hint) {
        (Shape::Int(cur), IntBoundHint::Int(hlo, hhi)) => match cur {
            Some((lo, hi)) => Shape::Int(Some(((*lo).max(*hlo), (*hi).min(*hhi)))),
            None => Shape::Int(Some((*hlo, *hhi))),
        },
        (Shape::Func { dom, exact_dom, range, max_dom }, IntBoundHint::Map(rh)) => {
            Shape::Func { dom: dom.clone(), exact_dom: *exact_dom, range: Box::new(tighten_shape_with_hint(range, rh)), max_dom: *max_dom }
        }
        (Shape::Set { elem, finite, max_card }, IntBoundHint::Set(eh)) => {
            Shape::Set { elem: Box::new(tighten_shape_with_hint(elem, eh)), finite: *finite, max_card: *max_card }
        }
        (Shape::Record(fs), IntBoundHint::Record(hfs)) => Shape::Record(
            fs.iter().map(|(k, v)| (k.clone(), hfs.get(k).map_or_else(|| v.clone(), |h| tighten_shape_with_hint(v, h)))).collect(),
        ),
        (Shape::Union(us), _) => Shape::Union(us.iter().map(|u| tighten_shape_with_hint(u, hint)).collect()),
        _ => shape.clone(),
    }
}

pub(super) fn expr_struct_eq(a: &Expr, ap: bool, b: &Expr, bp: bool) -> bool {
    match (&*a.kind, &*b.kind) {
        (ExprKind::Builtin { op: B::Prime, args: aa }, _) if !ap && aa.len() == 1 => expr_struct_eq(&aa[0], true, b, bp),
        (_, ExprKind::Builtin { op: B::Prime, args: ba }) if !bp && ba.len() == 1 => expr_struct_eq(a, ap, &ba[0], true),
        (ExprKind::Var(v1), ExprKind::Var(v2)) => v1 == v2 && ap == bp,
        (ExprKind::Local(l1), ExprKind::Local(l2)) => l1 == l2,
        (ExprKind::Const(c1), ExprKind::Const(c2)) => c1 == c2,
        (ExprKind::Num(n1), ExprKind::Num(n2)) => n1 == n2,
        (ExprKind::Str(s1), ExprKind::Str(s2)) => s1 == s2,
        (ExprKind::Bool(b1), ExprKind::Bool(b2)) => b1 == b2,
        (ExprKind::Field { record: r1, field: f1 }, ExprKind::Field { record: r2, field: f2 }) => {
            f1 == f2 && expr_struct_eq(r1, ap, r2, bp)
        }
        (ExprKind::FnApp { func: f1, args: a1 }, ExprKind::FnApp { func: f2, args: a2 }) => {
            a1.len() == a2.len() && expr_struct_eq(f1, ap, f2, bp) && a1.iter().zip(a2).all(|(x, y)| expr_struct_eq(x, ap, y, bp))
        }
        _ => false,
    }
}

pub(super) fn target_var(e: &Expr, primed: bool) -> Option<VarId> {
    if primed {
        let ExprKind::Builtin { op: B::Prime, args } = &*e.kind else { return None };
        if args.len() != 1 {
            return None;
        }
        match &*args[0].kind {
            ExprKind::Var(v) => Some(*v),
            _ => None,
        }
    } else {
        match &*e.kind {
            ExprKind::Var(v) => Some(*v),
            _ => None,
        }
    }
}

pub(super) fn join_shape(a: &Shape, b: &Shape) -> Shape {
    if a == b {
        return a.clone();
    }
    match (a, b) {
        (Shape::Bottom, x) | (x, Shape::Bottom) => x.clone(),
        (Shape::Top, _) | (_, Shape::Top) => Shape::Top,
        (Shape::Int(Some((al, ah))), Shape::Int(Some((bl, bh)))) => Shape::Int(Some(((*al).min(*bl), (*ah).max(*bh)))),
        (Shape::Int(_), Shape::Int(_)) => Shape::Int(None),
        (Shape::Str(Some(s1)), Shape::Str(Some(s2))) => {
            let mut m = s1.clone();
            m.extend(s2.iter().cloned());
            if m.len() > MAX_STR_SET {
                Shape::Str(None)
            } else {
                Shape::Str(Some(m))
            }
        }
        (Shape::Str(_), Shape::Str(_)) => Shape::Str(None),
        (Shape::Model { groups: g1, mv_type: t1, unmoved: u1 }, Shape::Model { groups: g2, mv_type: t2, unmoved: u2 }) => {
            let unmoved = match (u1, u2) {
                (Some(a), Some(b)) => {
                    let mut m = a.clone();
                    m.extend(b.iter().cloned());
                    (m.len() <= MAX_UNMOVED_SET).then_some(m)
                }
                _ => None,
            };
            Shape::Model { groups: g1 | g2, mv_type: t1.join(*t2), unmoved }
        }
        (Shape::Set { elem: e1, finite: f1, max_card: c1 }, Shape::Set { elem: e2, finite: f2, max_card: c2 }) => {
            let max_card = match (c1, c2) {
                (Some(x), Some(y)) => Some((*x).max(*y)),
                _ => None,
            };
            Shape::Set { elem: Box::new(join_shape(e1, e2)), finite: *f1 && *f2, max_card }
        }
        (Shape::Tuple(t1), Shape::Tuple(t2)) if t1.len() == t2.len() => {
            Shape::Tuple(t1.iter().zip(t2).map(|(x, y)| join_shape(x, y)).collect())
        }
        (Shape::Tuple(t1), Shape::Tuple(t2)) => {
            let mut e = Shape::Bottom;
            for x in t1.iter().chain(t2.iter()) {
                e = join_shape(&e, x);
            }
            Shape::Seq { elem: Box::new(e), min_len: t1.len().min(t2.len()) as u32, max_len: u32::try_from(t1.len().max(t2.len())).ok() }
        }
        (Shape::Seq { elem: e1, min_len: lo1, max_len: hi1 }, Shape::Seq { elem: e2, min_len: lo2, max_len: hi2 }) => {
            Shape::Seq { elem: Box::new(join_shape(e1, e2)), min_len: (*lo1).min(*lo2), max_len: hi1.and_then(|x| hi2.map(|y| x.max(y))) }
        }
        (Shape::Seq { elem, min_len, max_len }, Shape::Tuple(ts)) | (Shape::Tuple(ts), Shape::Seq { elem, min_len, max_len }) => {
            let mut e = (**elem).clone();
            for x in ts {
                e = join_shape(&e, x);
            }
            let len = ts.len() as u32;
            Shape::Seq { elem: Box::new(e), min_len: (*min_len).min(len), max_len: max_len.map(|h| h.max(len)) }
        }
        (Shape::Record(r1), Shape::Record(r2)) if r1.len() == r2.len() && r1.keys().eq(r2.keys()) => {
            Shape::Record(r1.iter().map(|(k, v)| (k.clone(), join_shape(v, &r2[k]))).collect())
        }
        (
            Shape::Func { dom: d1, exact_dom: ed1, range: r1, max_dom: c1 },
            Shape::Func { dom: d2, exact_dom: ed2, range: r2, max_dom: c2 },
        ) => Shape::Func {
            dom: Box::new(join_shape(d1, d2)),
            exact_dom: *ed1 && *ed2 && d1 == d2,
            range: Box::new(join_shape(r1, r2)),
            max_dom: c1.and_then(|x| c2.map(|y| x.max(y))),
        },
        _ => {
            let mut members = Vec::new();
            let mut push = |s: &Shape| match s {
                Shape::Union(us) => members.extend(us.iter().cloned()),
                other => members.push(other.clone()),
            };
            push(a);
            push(b);
            let mut merged: Vec<Shape> = Vec::new();
            for m in members {
                if let Some(slot) = merged.iter_mut().find(|x| same_variant_family(x, &m)) {
                    *slot = join_shape(slot, &m);
                } else {
                    merged.push(m);
                }
            }
            if merged.len() == 1 {
                merged.pop().unwrap()
            } else if merged.len() <= MAX_UNION_MEMBERS {
                merged.sort();
                Shape::Union(merged)
            } else {
                Shape::Top
            }
        }
    }
}

pub(super) fn same_variant_family(a: &Shape, b: &Shape) -> bool {
    matches!(
        (a, b),
        (Shape::Bool, Shape::Bool)
            | (Shape::Int(_), Shape::Int(_))
            | (Shape::Str(_), Shape::Str(_))
            | (Shape::Model { .. }, Shape::Model { .. })
            | (Shape::Set { .. }, Shape::Set { .. })
            | (Shape::Seq { .. }, Shape::Seq { .. })
            | (Shape::Func { .. }, Shape::Func { .. })
    ) || matches!((a, b), (Shape::Tuple(x), Shape::Tuple(y)) if x.len() == y.len())
        || matches!((a, b), (Shape::Record(x), Shape::Record(y)) if x.len() == y.len() && x.keys().eq(y.keys()))
}

/// Pairwise widening: only widens sub-shapes that actually grew between `old` and `new`,
/// preserving already-converged bounds (e.g. bounded integer fields inside growing sets).
pub(super) fn widen_diff(old: &Shape, new: &Shape) -> Shape {
    if old == new {
        return new.clone();
    }
    match (old, new) {
        (Shape::Int(_), Shape::Int(_)) => Shape::Int(None),
        (Shape::Set { elem: e1, max_card: c1, .. }, Shape::Set { elem: e2, finite, max_card: c2 }) => {
            Shape::Set { elem: Box::new(widen_diff(e1, e2)), finite: *finite, max_card: if c1 == c2 { *c2 } else { None } }
        }
        (Shape::Seq { elem: e1, min_len: lo1, max_len: hi1 }, Shape::Seq { elem: e2, min_len: lo2, max_len: hi2 }) => Shape::Seq {
            elem: Box::new(widen_diff(e1, e2)),
            min_len: if lo1 == lo2 { *lo2 } else { 0 },
            max_len: if hi1 == hi2 { *hi2 } else { None },
        },
        (Shape::Tuple(t1), Shape::Tuple(t2)) if t1.len() == t2.len() => {
            Shape::Tuple(t1.iter().zip(t2).map(|(a, b)| widen_diff(a, b)).collect())
        }
        (Shape::Record(r1), Shape::Record(r2)) if r1.len() == r2.len() && r1.keys().eq(r2.keys()) => {
            Shape::Record(r1.iter().map(|(k, v)| (k.clone(), widen_diff(v, &r2[k]))).collect())
        }
        (Shape::Func { dom: d1, range: r1, max_dom: c1, .. }, Shape::Func { dom: d2, exact_dom, range: r2, max_dom: c2 }) => {
            let wdom = widen_diff(d1, d2);
            let exact = *exact_dom && wdom == **d2;
            Shape::Func {
                dom: Box::new(wdom),
                exact_dom: exact,
                range: Box::new(widen_diff(r1, r2)),
                max_dom: if c1 == c2 { *c2 } else { None },
            }
        }
        (Shape::Union(u1), Shape::Union(u2)) if u1.len() == u2.len() => {
            let mut next: Vec<Shape> = u1.iter().zip(u2).map(|(a, b)| widen_diff(a, b)).collect();
            next.sort();
            Shape::Union(next)
        }
        _ => widen_shape(new),
    }
}

pub(super) fn widen_shape(s: &Shape) -> Shape {
    match s {
        Shape::Int(_) => Shape::Int(None),
        Shape::Set { elem, finite, .. } => Shape::Set { elem: Box::new(widen_shape(elem)), finite: *finite, max_card: None },
        Shape::Seq { elem, .. } => Shape::Seq { elem: Box::new(widen_shape(elem)), min_len: 0, max_len: None },
        Shape::Tuple(ts) => Shape::Tuple(ts.iter().map(widen_shape).collect()),
        Shape::Record(fs) => Shape::Record(fs.iter().map(|(k, v)| (k.clone(), widen_shape(v))).collect()),
        Shape::Func { dom, exact_dom, range, max_dom } => {
            let wdom = widen_shape(dom);
            let exact = *exact_dom && wdom == **dom;
            Shape::Func { dom: Box::new(wdom), exact_dom: exact, range: Box::new(widen_shape(range)), max_dom: *max_dom }
        }
        Shape::Union(us) => {
            let mut next: Vec<Shape> = us.iter().map(widen_shape).collect();
            next.sort();
            Shape::Union(next)
        }
        other => other.clone(),
    }
}

/// Sound narrowing of a single `Record` or tagged `Union` of `Record`s under
/// `m.field = lit` or `m.field /= lit`.
pub(super) fn narrow_record_field_eq(cur: &Shape, field: &str, other: &Shape, eq: bool) -> Option<Shape> {
    if let Shape::Record(fs) = cur {
        let fval = fs.get(field)?;
        let updated = if eq {
            if matches!(other, Shape::Top | Shape::Bottom) {
                return None;
            }
            narrow_shape(fval, other)
        } else {
            exclude_single_value(fval, other)?
        };
        if &updated == fval {
            return None;
        }
        let mut next = fs.clone();
        next.insert(Arc::from(field), updated);
        return Some(Shape::Record(next));
    }
    let Shape::Union(us) = cur else { return None };
    let mut kept = Vec::new();
    let mut changed = false;
    for u in us {
        let Shape::Record(fs) = u else {
            kept.push(u.clone());
            continue;
        };
        let Some(fval) = fs.get(field) else {
            if eq {
                changed = true;
            } else {
                kept.push(u.clone());
            }
            continue;
        };
        if eq {
            if disjoint_shapes(fval, other)
                || matches!((fval, other), (Shape::Str(Some(a)), Shape::Str(Some(b))) if a.is_disjoint(b))
                || matches!((fval, other), (Shape::Int(Some((a1, a2))), Shape::Int(Some((b1, b2)))) if a2 < b1 || b2 < a1)
            {
                changed = true;
            } else {
                kept.push(u.clone());
            }
        } else if is_singleton_equal(fval, other) {
            changed = true;
        } else {
            kept.push(u.clone());
        }
    }
    if !changed {
        return None;
    }
    match kept.len() {
        0 => Some(Shape::Bottom),
        1 => Some(kept.pop().unwrap()),
        _ => {
            kept.sort();
            Some(Shape::Union(kept))
        }
    }
}

pub(super) fn shape_leq(a: &Shape, b: &Shape) -> bool {
    &join_shape(a, b) == b
}

pub(super) fn min_opt_u32(a: Option<u32>, b: Option<u32>) -> Option<u32> {
    match (a, b) {
        (Some(x), Some(y)) => Some(x.min(y)),
        (Some(x), None) | (None, Some(x)) => Some(x),
        (None, None) => None,
    }
}

/// Lattice meet (`cur ⊓ fact`): refines `cur` with `fact` without ever widening `cur`.
pub(super) fn narrow_shape(cur: &Shape, fact: &Shape) -> Shape {
    match (cur, fact) {
        (Shape::Bottom, _) | (_, Shape::Bottom) => Shape::Bottom,
        (Shape::Top, x) => x.clone(),
        (x, Shape::Top) => x.clone(),
        (Shape::Union(us), f) => {
            let mut kept: Vec<_> =
                us.iter().filter(|u| !disjoint_shapes(u, f)).map(|u| narrow_shape(u, f)).filter(|u| !matches!(u, Shape::Bottom)).collect();
            match kept.len() {
                0 => Shape::Bottom,
                1 => kept.pop().unwrap(),
                _ => {
                    kept.sort();
                    Shape::Union(kept)
                }
            }
        }
        (Shape::Int(Some((al, ah))), Shape::Int(Some((bl, bh)))) => {
            let lo = (*al).max(*bl);
            let hi = (*ah).min(*bh);
            if lo <= hi {
                Shape::Int(Some((lo, hi)))
            } else {
                Shape::Bottom
            }
        }
        (Shape::Int(None), Shape::Int(Some(b))) => Shape::Int(Some(*b)),
        (Shape::Int(Some(a)), Shape::Int(None)) => Shape::Int(Some(*a)),
        (Shape::Str(Some(s1)), Shape::Str(Some(s2))) => {
            let inter: BTreeSet<_> = s1.intersection(s2).cloned().collect();
            if inter.is_empty() {
                Shape::Bottom
            } else {
                Shape::Str(Some(inter))
            }
        }
        (Shape::Str(None), Shape::Str(Some(s))) => Shape::Str(Some(s.clone())),
        (Shape::Str(Some(s)), Shape::Str(None)) => Shape::Str(Some(s.clone())),
        (Shape::Model { groups: g1, mv_type: t1, unmoved: u1 }, Shape::Model { groups: g2, mv_type: t2, unmoved: u2 }) => {
            let g = g1 & g2;
            let u = match (u1, u2) {
                (Some(a), Some(b)) => Some(a.intersection(b).cloned().collect()),
                (Some(a), None) | (None, Some(a)) => Some(a.clone()),
                (None, None) => None,
            };
            if g == 0 && u.as_ref().is_some_and(BTreeSet::is_empty) {
                Shape::Bottom
            } else {
                let mv_type = if *t1 == MvType::Unknown { *t2 } else { *t1 };
                Shape::Model { groups: g, mv_type, unmoved: u }
            }
        }
        (Shape::Set { elem: e1, finite: f1, max_card: c1 }, Shape::Set { elem: e2, finite: f2, max_card: c2 }) => {
            Shape::Set { elem: Box::new(narrow_shape(e1, e2)), finite: *f1 || *f2, max_card: min_opt_u32(*c1, *c2) }
        }
        (Shape::Seq { elem: e1, min_len: lo1, max_len: hi1 }, Shape::Seq { elem: e2, min_len: lo2, max_len: hi2 }) => {
            Shape::Seq { elem: Box::new(narrow_shape(e1, e2)), min_len: (*lo1).max(*lo2), max_len: min_opt_u32(*hi1, *hi2) }
        }
        (Shape::Tuple(ts), Shape::Seq { .. }) => Shape::Tuple(ts.clone()),
        (Shape::Record(r1), Shape::Record(r2)) if r1.len() == r2.len() && r1.keys().eq(r2.keys()) => {
            Shape::Record(r1.iter().map(|(k, v)| (k.clone(), narrow_shape(v, &r2[k]))).collect())
        }
        (
            Shape::Func { dom: d1, exact_dom: ed1, range: r1, max_dom: c1 },
            Shape::Func { dom: d2, exact_dom: ed2, range: r2, max_dom: c2 },
        ) => {
            let (dom, exact_dom) = if *ed1 {
                ((**d1).clone(), true)
            } else if *ed2 {
                ((**d2).clone(), true)
            } else {
                (narrow_shape(d1, d2), false)
            };
            Shape::Func { dom: Box::new(dom), exact_dom, range: Box::new(narrow_shape(r1, r2)), max_dom: min_opt_u32(*c1, *c2) }
        }
        _ => cur.clone(),
    }
}

pub(super) fn disjoint_shapes(a: &Shape, b: &Shape) -> bool {
    match (a, b) {
        (Shape::Bool, Shape::Bool)
        | (Shape::Int(_), Shape::Int(_))
        | (Shape::Str(_), Shape::Str(_))
        | (Shape::Model { .. }, Shape::Model { .. })
        | (Shape::Set { .. }, Shape::Set { .. })
        // In TLA+, Func, Tuple, Seq, and Record are all extensionally equal function values
        // (e.g. `<<0>> = [i \in 1..1 |-> 0]`, `[a |-> 1] = ("a" :> 1)`, `<<>> = [x \in {} |-> 0]`).
        | (Shape::Func { .. }, Shape::Func { .. } | Shape::Tuple(_) | Shape::Seq { .. } | Shape::Record(_))
        | (Shape::Tuple(_) | Shape::Seq { .. } | Shape::Record(_), Shape::Func { .. })
        | (Shape::Seq { .. }, Shape::Seq { .. } | Shape::Tuple(_) | Shape::Record(_))
        | (Shape::Tuple(_) | Shape::Record(_), Shape::Seq { .. })
        | (Shape::Top, _)
        | (_, Shape::Top)
        | (Shape::Union(_), _)
        | (_, Shape::Union(_)) => false,
        (Shape::Tuple(t1), Shape::Tuple(t2)) => t1.len() != t2.len(),
        (Shape::Tuple(ts), Shape::Record(r)) | (Shape::Record(r), Shape::Tuple(ts)) => !(ts.is_empty() && r.is_empty()),
        (Shape::Record(r1), Shape::Record(r2)) => !(r1.len() == r2.len() && r1.keys().eq(r2.keys())),
        _ => true,
    }
}

/// Exact single-value exclusion for `x # lit` (NEVER drops other unmoved values!).
pub(super) fn exclude_single_value(cur: &Shape, lit: &Shape) -> Option<Shape> {
    match (cur, lit) {
        (Shape::Model { groups, mv_type, unmoved: Some(set) }, Shape::Model { groups: 0, unmoved: Some(ex), .. }) if ex.len() == 1 => {
            let removed = ex.iter().next().unwrap();
            if !set.contains(removed) {
                return None;
            }
            let mut next = set.clone();
            next.remove(removed);
            if *groups == 0 && next.is_empty() {
                Some(Shape::Bottom)
            } else {
                Some(Shape::Model { groups: *groups, mv_type: *mv_type, unmoved: Some(next) })
            }
        }
        (Shape::Union(us), ex) => {
            let mut changed = false;
            let mut kept = Vec::new();
            for u in us {
                if let Some(n) = exclude_single_value(u, ex) {
                    changed = true;
                    if !matches!(n, Shape::Bottom) {
                        kept.push(n);
                    }
                } else if is_singleton_equal(u, ex) {
                    changed = true;
                } else {
                    kept.push(u.clone());
                }
            }
            if !changed {
                return None;
            }
            match kept.len() {
                0 => Some(Shape::Bottom),
                1 => Some(kept.pop().unwrap()),
                _ => Some(Shape::Union(kept)),
            }
        }
        (Shape::Str(Some(set)), Shape::Str(Some(ex))) if ex.len() == 1 => {
            let s = ex.iter().next().unwrap();
            if !set.contains(s) {
                return None;
            }
            let mut next = set.clone();
            next.remove(s);
            if next.is_empty() {
                Some(Shape::Bottom)
            } else {
                Some(Shape::Str(Some(next)))
            }
        }
        (Shape::Int(Some((lo, hi))), Shape::Int(Some((k, k2)))) if k == k2 => {
            if lo == k && hi == k {
                Some(Shape::Bottom)
            } else if lo == k {
                Some(Shape::Int(Some((lo + 1, *hi))))
            } else if hi == k {
                Some(Shape::Int(Some((*lo, hi - 1))))
            } else {
                None
            }
        }
        _ => None,
    }
}

pub(super) fn is_singleton_equal(a: &Shape, b: &Shape) -> bool {
    match (a, b) {
        (Shape::Str(Some(s1)), Shape::Str(Some(s2))) => s1.len() == 1 && s1 == s2,
        (Shape::Int(Some((a1, a2))), Shape::Int(Some((b1, b2)))) => a1 == a2 && a1 == b1 && b1 == b2,
        (Shape::Model { groups: 0, unmoved: Some(u1), .. }, Shape::Model { groups: 0, unmoved: Some(u2), .. }) => u1.len() == 1 && u1 == u2,
        (Shape::Tuple(t1), Shape::Tuple(t2)) => t1.is_empty() && t2.is_empty(),
        (Shape::Record(r1), Shape::Record(r2)) => {
            r1.len() == r2.len() && r1.iter().all(|(k, v)| r2.get(k).is_some_and(|w| is_singleton_equal(v, w)))
        }
        _ => false,
    }
}

pub(super) fn shapes_comparable(a: &Shape, b: &Shape) -> bool {
    match (a, b) {
        (Shape::Top, _) | (_, Shape::Top) => false,
        (Shape::Bottom, _) | (_, Shape::Bottom) => true,
        (Shape::Union(us), x) | (x, Shape::Union(us)) => us.iter().all(|u| shapes_comparable(u, x)),
        (Shape::Model { mv_type: MvType::Untyped, .. }, _) | (_, Shape::Model { mv_type: MvType::Untyped, .. }) => true,
        (Shape::Model { mv_type: MvType::Typed(c1), .. }, Shape::Model { mv_type: MvType::Typed(c2), .. }) => c1 == c2,
        (Shape::Model { .. }, _) | (_, Shape::Model { .. }) => false,
        (Shape::Bool, Shape::Bool) | (Shape::Int(_), Shape::Int(_)) | (Shape::Str(_), Shape::Str(_)) => true,
        (Shape::Set { elem: e1, .. }, Shape::Set { elem: e2, .. }) => shapes_comparable(e1, e2),
        (Shape::Tuple(t1), Shape::Tuple(t2)) => t1.len() != t2.len() || t1.iter().zip(t2).all(|(x, y)| shapes_comparable(x, y)),
        (Shape::Seq { elem: e1, .. }, Shape::Seq { elem: e2, .. }) => shapes_comparable(e1, e2),
        (Shape::Seq { elem, .. }, Shape::Tuple(ts)) | (Shape::Tuple(ts), Shape::Seq { elem, .. }) => {
            ts.iter().all(|t| shapes_comparable(elem, t))
        }
        (Shape::Record(r1), Shape::Record(r2)) => {
            r1.len() != r2.len() || !r1.keys().eq(r2.keys()) || r1.iter().all(|(k, v)| shapes_comparable(v, &r2[k]))
        }
        (Shape::Func { dom: d1, range: r1, .. }, Shape::Func { dom: d2, range: r2, .. }) => {
            shapes_comparable(d1, d2) && shapes_comparable(r1, r2)
        }
        (Shape::Func { dom, range, .. }, Shape::Tuple(ts)) | (Shape::Tuple(ts), Shape::Func { dom, range, .. }) => {
            ts.is_empty() || (shapes_comparable(dom, &Shape::Int(None)) && ts.iter().all(|t| shapes_comparable(range, t)))
        }
        (Shape::Func { dom, range, .. }, Shape::Seq { elem, .. }) | (Shape::Seq { elem, .. }, Shape::Func { dom, range, .. }) => {
            shapes_comparable(dom, &Shape::Int(None)) && shapes_comparable(range, elem)
        }
        (Shape::Func { dom, range, .. }, Shape::Record(r)) | (Shape::Record(r), Shape::Func { dom, range, .. }) => {
            shapes_comparable(dom, &Shape::Str(None)) && r.values().all(|v| shapes_comparable(range, v))
        }
        (Shape::Tuple(ts), Shape::Record(_)) | (Shape::Record(_), Shape::Tuple(ts)) => ts.is_empty(),
        _ => false,
    }
}

pub(super) fn shape_self_comparable(s: &Shape) -> bool {
    shapes_comparable(s, s)
}

pub(super) fn shape_may_contain_lazy_strict(s: &Shape) -> bool {
    match s {
        Shape::Set { .. } | Shape::Record(_) | Shape::Top => true,
        Shape::Seq { elem, .. } => shape_may_contain_lazy_strict(elem),
        Shape::Tuple(ts) | Shape::Union(ts) => ts.iter().any(shape_may_contain_lazy_strict),
        Shape::Func { dom, range, .. } => shape_may_contain_lazy_strict(dom) || shape_may_contain_lazy_strict(range),
        _ => false,
    }
}

/// True iff `val \in S` cannot fail on a nested lazy `SUBSET`, `KSubset`, `RecordSet`,
/// `Product`, `FcnSet`, or `Seq` check when `S` is a non-materialized set whose element shape is `elem`.
pub(super) fn shape_safe_for_lazy_membership(val: &Shape, elem: &Shape, groups: &[GroupInfo]) -> bool {
    match val {
        Shape::Bottom => true,
        Shape::Union(us) => !us.is_empty() && us.iter().all(|u| shape_safe_for_lazy_membership(u, elem, groups)),
        _ => match elem {
            Shape::Bottom => true,
            Shape::Union(es) => !es.is_empty() && es.iter().all(|e| shape_safe_for_lazy_membership(val, e, groups)),
            Shape::Set { elem: ee, .. } => match val {
                Shape::Set { elem: ve, finite: true, .. } => {
                    shape_has_safe_set_cards(val, groups) && shape_safe_for_lazy_membership(ve, ee, groups)
                }
                _ => false,
            },
            Shape::Func { dom: ed, range: er, .. } => match val {
                Shape::Model { mv_type: MvType::Untyped, .. } => true,
                _ => match fn_dom_range(val) {
                    Some((vd, vr, _)) => {
                        shapes_comparable(&vd, ed)
                            && shape_has_safe_set_cards(&vd, groups)
                            && shape_has_safe_set_cards(ed, groups)
                            && shape_safe_for_lazy_membership(&vr, er, groups)
                    }
                    None => false,
                },
            },
            Shape::Seq { elem: ee, .. } => match val {
                Shape::Model { mv_type: MvType::Untyped, .. } => true,
                Shape::Seq { elem: ve, .. } => shape_safe_for_lazy_membership(ve, ee, groups),
                Shape::Tuple(ts) => ts.iter().all(|t| shape_safe_for_lazy_membership(t, ee, groups)),
                _ => false,
            },
            Shape::Tuple(es) => match val {
                Shape::Model { mv_type: MvType::Untyped, .. } => true,
                Shape::Tuple(ts) => ts.len() != es.len() || ts.iter().zip(es).all(|(t, e)| shape_safe_for_lazy_membership(t, e, groups)),
                Shape::Seq { elem: ve, .. } => es.iter().all(|e| shape_safe_for_lazy_membership(ve, e, groups)),
                Shape::Func { dom, range: vr, .. } => is_int_shape(dom) && es.iter().all(|e| shape_safe_for_lazy_membership(vr, e, groups)),
                _ => false,
            },
            Shape::Record(ef) => match val {
                Shape::Model { mv_type: MvType::Untyped, .. } => true,
                Shape::Tuple(ts) => ts.is_empty(),
                // Lazy `RecordSet` membership compares shared fields in `Sym` intern order before
                // noticing a differing field name, so every shared field must be comparable and safe.
                Shape::Record(vf) => {
                    vf.len() != ef.len()
                        || vf.iter().all(|(k, v)| match ef.get(k) {
                            Some(e) => shapes_comparable(v, e) && shape_safe_for_lazy_membership(v, e, groups),
                            None => true,
                        })
                }
                Shape::Func { dom, range: vr, .. } => {
                    matches!(&**dom, Shape::Str(_) | Shape::Bottom)
                        && ef.values().all(|e| shapes_comparable(vr, e) && shape_safe_for_lazy_membership(vr, e, groups))
                }
                _ => false,
            },
            Shape::Top => false,
            _ => true,
        },
    }
}

pub(super) fn shape_contains_top(s: &Shape) -> bool {
    match s {
        Shape::Top => true,
        Shape::Set { elem, .. } | Shape::Seq { elem, .. } => shape_contains_top(elem),
        Shape::Tuple(ts) | Shape::Union(ts) => ts.iter().any(shape_contains_top),
        Shape::Record(fs) => fs.values().any(shape_contains_top),
        Shape::Func { dom, range, .. } => shape_contains_top(dom) || shape_contains_top(range),
        _ => false,
    }
}

/// True iff every `Shape::Set` appearing in `s` has a verified `<= i32::MAX` cardinality bound,
/// preventing `eq_tlc` from overflowing 32-bit cardinality checks (e.g. `[1..32 -> BOOLEAN] = {}`).
pub(super) fn shape_has_safe_set_cards(s: &Shape, groups: &[GroupInfo]) -> bool {
    match s {
        Shape::Set { elem, finite, max_card } => {
            *finite
                && max_card.or_else(|| shape_universe_size(elem, groups)).is_some_and(|c| c <= MAX_I32_U32)
                && shape_has_safe_set_cards(elem, groups)
        }
        Shape::Seq { elem, .. } => shape_has_safe_set_cards(elem, groups),
        Shape::Tuple(ts) | Shape::Union(ts) => ts.iter().all(|t| shape_has_safe_set_cards(t, groups)),
        Shape::Record(fs) => fs.values().all(|v| shape_has_safe_set_cards(v, groups)),
        Shape::Func { dom, range, .. } => shape_has_safe_set_cards(dom, groups) && shape_has_safe_set_cards(range, groups),
        _ => true,
    }
}

pub(super) fn is_bool_shape(s: &Shape) -> bool {
    matches!(s, Shape::Bool | Shape::Bottom)
}

pub(super) fn is_int_shape(s: &Shape) -> bool {
    matches!(s, Shape::Int(_) | Shape::Bottom)
}

pub(super) fn is_finite_set_arg(s: &Shape) -> bool {
    match s {
        Shape::Set { finite: true, .. } | Shape::Func { .. } | Shape::Record(_) | Shape::Tuple(_) | Shape::Seq { .. } | Shape::Bottom => {
            true
        }
        Shape::Union(us) if !us.is_empty() => us.iter().all(is_finite_set_arg),
        _ => false,
    }
}

pub(super) fn is_seq_shape(s: &Shape) -> bool {
    match s {
        Shape::Tuple(_) | Shape::Seq { .. } | Shape::Bottom => true,
        Shape::Union(us) if !us.is_empty() => us.iter().all(is_seq_shape),
        _ => false,
    }
}

pub(super) fn shape_is_exact_cup_scalar(s: &Shape) -> bool {
    match s {
        Shape::Bottom | Shape::Bool | Shape::Str(Some(_)) | Shape::Model { unmoved: Some(_), .. } => true,
        Shape::Union(us) => us.iter().all(shape_is_exact_cup_scalar),
        _ => false,
    }
}

pub(super) fn collect_var_frame(e: &Expr, out: &mut BTreeSet<VarId>) {
    match &*e.kind {
        ExprKind::Var(v) => {
            out.insert(*v);
        }
        ExprKind::Tuple(es) => {
            for item in es {
                collect_var_frame(item, out);
            }
        }
        _ => {}
    }
}

pub(super) fn cap_shape(s: Shape) -> Shape {
    let mut budget = MAX_SHAPE_NODES;
    if shape_within_bounds(&s, MAX_SHAPE_DEPTH, &mut budget) {
        s
    } else {
        Shape::Top
    }
}

pub(super) fn shape_within_bounds(s: &Shape, depth: usize, budget: &mut usize) -> bool {
    if depth == 0 || *budget == 0 {
        return false;
    }
    *budget -= 1;
    match s {
        Shape::Set { elem, .. } | Shape::Seq { elem, .. } => shape_within_bounds(elem, depth - 1, budget),
        Shape::Tuple(ts) | Shape::Union(ts) => ts.iter().all(|t| shape_within_bounds(t, depth - 1, budget)),
        Shape::Record(fs) => fs.values().all(|v| shape_within_bounds(v, depth - 1, budget)),
        Shape::Func { dom, range, .. } => shape_within_bounds(dom, depth - 1, budget) && shape_within_bounds(range, depth - 1, budget),
        _ => true,
    }
}

pub(super) fn except_field_valid_for(s: &Shape) -> bool {
    match s {
        Shape::Record(_) | Shape::Bottom => true,
        Shape::Union(us) if !us.is_empty() => us.iter().all(except_field_valid_for),
        _ => false,
    }
}

pub(super) fn fnapp_index_valid_for(container: &Shape, key: &Shape, groups: &[GroupInfo]) -> bool {
    match container {
        Shape::Bottom => true,
        Shape::Tuple(_) | Shape::Seq { .. } => is_int_shape(key),
        Shape::Record(_) => matches!(key, Shape::Str(_) | Shape::Bottom),
        Shape::Func { dom, exact_dom, .. } => key_inhabits_domain_kind(key, dom, *exact_dom, groups),
        Shape::Union(us) if !us.is_empty() => us.iter().all(|u| fnapp_index_valid_for(u, key, groups)),
        _ => false,
    }
}

fn shape_disjoint_from_model_dom(key: &Shape, dom_groups: GroupMask, dom_unmoved: Option<&BTreeSet<Arc<str>>>) -> bool {
    match key {
        Shape::Bottom => true,
        Shape::Bool
        | Shape::Int(_)
        | Shape::Str(_)
        | Shape::Set { finite: true, .. }
        | Shape::Seq { .. }
        | Shape::Tuple(_)
        | Shape::Record(_)
        | Shape::Func { .. } => true,
        Shape::Model { groups: kg, unmoved: Some(ku), .. } => (*kg & dom_groups) == 0 && dom_unmoved.is_some_and(|du| ku.is_disjoint(du)),
        Shape::Union(ks) => !ks.is_empty() && ks.iter().all(|k| shape_disjoint_from_model_dom(k, dom_groups, dom_unmoved)),
        _ => false,
    }
}

/// True iff every runtime set matching exact domain shape `s` has at least one element,
/// guaranteeing a function with `exact_dom: true` is never materialized as empty `<<>>`.
pub(super) fn shape_provably_nonempty(s: &Shape, groups: &[GroupInfo]) -> bool {
    match s {
        Shape::Bool => true,
        Shape::Int(Some((lo, hi))) => lo <= hi,
        Shape::Str(Some(ss)) => !ss.is_empty(),
        Shape::Model { groups: mask, unmoved, .. } => {
            unmoved.as_ref().is_some_and(|u| !u.is_empty())
                || groups.iter().enumerate().any(|(gi, g)| (*mask & (1u16 << gi)) != 0 && !g.keys.is_empty())
        }
        Shape::Tuple(ts) => ts.iter().all(|t| shape_provably_nonempty(t, groups)),
        Shape::Record(fs) => fs.values().all(|v| shape_provably_nonempty(v, groups)),
        Shape::Union(us) => !us.is_empty() && us.iter().all(|u| shape_provably_nonempty(u, groups)),
        _ => false,
    }
}

/// True iff `key` is guaranteed to miss `container`'s domain without raising a lookup error
/// in either the interpreter or the compiled tier (`ops::select` returns `Ok(None)`).
pub(super) fn except_key_provably_absent(container: &Shape, key: &Shape, groups: &[GroupInfo]) -> bool {
    if matches!(container, Shape::Bottom) || matches!(key, Shape::Bottom) {
        return true;
    }
    if let Shape::Union(cs) = container {
        return !cs.is_empty() && cs.iter().all(|c| except_key_provably_absent(c, key, groups));
    }
    if let Shape::Union(ks) = key {
        return !ks.is_empty() && ks.iter().all(|k| except_key_provably_absent(container, k, groups));
    }
    match container {
        Shape::Tuple(ts) => matches!(key, Shape::Int(Some((lo, hi))) if (*hi as i128) < 1 || (*lo as i128) > ts.len() as i128),
        Shape::Record(fs) => matches!(key, Shape::Str(Some(ks)) if ks.iter().all(|k| !fs.contains_key(k))),
        // A non-empty exact untyped model-value domain is always materialized as an enumerated
        // `Value::Fcn` (never `Value::Tuple([])`), whose untyped model-value keys compare safely
        // with any well-formed finite value and return `Ok(None)` on any provably disjoint key.
        Shape::Func { dom, exact_dom: true, .. } if shape_provably_nonempty(dom, groups) => match &**dom {
            Shape::Model { groups: dg, mv_type: MvType::Untyped, unmoved } => {
                !shape_contains_top(key)
                    && shape_self_comparable(key)
                    && shape_has_safe_set_cards(key, groups)
                    && shape_disjoint_from_model_dom(key, *dg, unmoved.as_ref())
            }
            _ => false,
        },
        _ => false,
    }
}

pub(super) fn except_index_valid_for_with_dom_proof(container: &Shape, key: &Shape, dom_nonempty: bool, groups: &[GroupInfo]) -> bool {
    match container {
        Shape::Bottom => true,
        Shape::Union(us) if !us.is_empty() => us.iter().all(|u| except_index_valid_for_with_dom_proof(u, key, dom_nonempty, groups)),
        Shape::Func { dom, exact_dom, .. } => {
            if is_int_shape(dom) {
                // Integer keys safely return `Ok(None)` on empty `<<>>`, out-of-range `Tuple`,
                // and missing `Value::Fcn` integer entries alike.
                is_int_shape(key)
            } else if (*exact_dom && shape_provably_nonempty(dom, groups)) || dom_nonempty {
                fnapp_index_valid_for(container, key, groups) || except_key_provably_absent(container, key, groups)
            } else {
                // `container` may decode to empty `Value::Tuple([])` (`<<>>`), where `ops::select`
                // errors on any non-integer key while non-empty states reject integer keys on
                // string/typed-model domains.
                matches!(key, Shape::Bottom)
            }
        }
        _ => fnapp_index_valid_for(container, key, groups) || except_key_provably_absent(container, key, groups),
    }
}

/// True iff `key` inhabits the runtime domain representation of `dom` (preventing untyped
/// model values from indexing integer-interval functions, tuples, or records, while preserving
/// exact heterogeneous enumerated domains such as `Proc \cup {"fixed"}`).
fn key_inhabits_domain_kind(key: &Shape, dom: &Shape, exact_dom: bool, groups: &[GroupInfo]) -> bool {
    if matches!(key, Shape::Bottom) {
        return true;
    }
    if let Shape::Union(ks) = key {
        return !ks.is_empty() && ks.iter().all(|k| key_inhabits_domain_kind(k, dom, exact_dom, groups));
    }
    match dom {
        Shape::Bottom | Shape::Top => false,
        Shape::Int(_) => is_int_shape(key),
        Shape::Str(_) => matches!(key, Shape::Str(_)),
        Shape::Bool => matches!(key, Shape::Bool),
        Shape::Model { .. } => matches!(key, Shape::Model { .. }) && shapes_comparable(key, dom),
        Shape::Set { elem: de, finite: true, .. } => match key {
            Shape::Set { elem: ke, finite: true, .. } => {
                key_inhabits_domain_kind(ke, de, false, groups)
                    && shape_has_safe_set_cards(key, groups)
                    && shape_has_safe_set_cards(dom, groups)
            }
            _ => false,
        },
        Shape::Set { finite: false, .. } => false,
        Shape::Tuple(ds) => match key {
            Shape::Tuple(ks) => ks.len() != ds.len() || ks.iter().zip(ds).all(|(k, d)| key_inhabits_domain_kind(k, d, false, groups)),
            _ => false,
        },
        Shape::Seq { elem: de, .. } => match key {
            Shape::Tuple(ks) => ks.iter().all(|k| key_inhabits_domain_kind(k, de, false, groups)),
            Shape::Seq { elem: ke, .. } => key_inhabits_domain_kind(ke, de, false, groups),
            _ => false,
        },
        Shape::Record(df) => match key {
            Shape::Record(kf) => {
                kf.len() != df.len()
                    || kf.iter().all(|(name, kv)| match df.get(name) {
                        Some(dv) => key_inhabits_domain_kind(kv, dv, false, groups),
                        None => true,
                    })
            }
            _ => false,
        },
        Shape::Func { dom: dd, range: dr, .. } => match key {
            Shape::Func { dom: kd, range: kr, .. } => {
                key_inhabits_domain_kind(kd, dd, false, groups)
                    && key_inhabits_domain_kind(kr, dr, false, groups)
                    && shape_has_safe_set_cards(key, groups)
                    && shape_has_safe_set_cards(dom, groups)
            }
            _ => false,
        },
        Shape::Union(ds) if !ds.is_empty() => {
            let forced_enumerated = exact_dom
                && shape_self_comparable(dom)
                && ds.iter().any(|d| {
                    matches!(
                        d,
                        Shape::Model { groups: g, unmoved, .. } if *g != 0 || unmoved.as_ref().is_some_and(|u| !u.is_empty())
                    )
                });
            if forced_enumerated {
                shapes_comparable(key, dom) && ds.iter().any(|d| key_inhabits_domain_kind(key, d, false, groups))
            } else {
                ds.iter().all(|d| key_inhabits_domain_kind(key, d, false, groups))
            }
        }
        Shape::Union(_) => false,
    }
}

pub(super) fn set_elem_of_shape_strict(s: &Shape) -> Option<Shape> {
    match s {
        Shape::Set { elem, finite: true, .. } => Some((**elem).clone()),
        Shape::Bottom => Some(Shape::Bottom),
        Shape::Union(us) if !us.is_empty() => {
            let mut acc = Shape::Bottom;
            for u in us {
                acc = join_shape(&acc, &set_elem_of_shape_strict(u)?);
            }
            Some(acc)
        }
        _ => None,
    }
}

pub(super) fn is_seq_or_untyped_model(s: &Shape) -> bool {
    match s {
        Shape::Tuple(_) | Shape::Seq { .. } | Shape::Bottom | Shape::Model { mv_type: MvType::Untyped, .. } => true,
        Shape::Union(us) if !us.is_empty() => us.iter().all(is_seq_or_untyped_model),
        _ => false,
    }
}

pub(super) fn is_tuple_or_untyped_model(s: &Shape) -> bool {
    match s {
        Shape::Tuple(_) | Shape::Bottom | Shape::Model { mv_type: MvType::Untyped, .. } => true,
        Shape::Union(us) if !us.is_empty() => us.iter().all(is_tuple_or_untyped_model),
        _ => false,
    }
}

pub(super) fn is_record_or_empty_tuple_or_untyped_model(s: &Shape) -> bool {
    match s {
        Shape::Record(_) | Shape::Bottom | Shape::Model { mv_type: MvType::Untyped, .. } => true,
        Shape::Tuple(ts) => ts.is_empty(),
        Shape::Union(us) if !us.is_empty() => us.iter().all(is_record_or_empty_tuple_or_untyped_model),
        _ => false,
    }
}

pub(super) fn is_fn_like_or_untyped_model(s: &Shape) -> bool {
    match s {
        Shape::Func { .. }
        | Shape::Tuple(_)
        | Shape::Seq { .. }
        | Shape::Record(_)
        | Shape::Bottom
        | Shape::Model { mv_type: MvType::Untyped, .. } => true,
        Shape::Union(us) if !us.is_empty() => us.iter().all(is_fn_like_or_untyped_model),
        _ => false,
    }
}

pub(super) fn set_elem_of_shape(s: &Shape) -> Option<Shape> {
    set_elem_of_shape_strict(s)
}

pub(super) fn field_of_shape(s: &Shape, field: &str) -> Shape {
    match s {
        Shape::Bottom => Shape::Bottom,
        Shape::Record(fs) => fs.get(field).cloned().unwrap_or(Shape::Top),
        Shape::Union(us) => {
            let mut acc = Shape::Bottom;
            for u in us {
                acc = join_shape(&acc, &field_of_shape(u, field));
            }
            acc
        }
        _ => Shape::Top,
    }
}

pub(super) fn field_of_shape_total(s: &Shape, field: &str) -> Option<Shape> {
    match s {
        Shape::Record(fs) => fs.get(field).cloned(),
        Shape::Union(us) if !us.is_empty() => {
            let mut acc = Shape::Bottom;
            for u in us {
                acc = join_shape(&acc, &field_of_shape_total(u, field)?);
            }
            Some(acc)
        }
        Shape::Bottom => Some(Shape::Bottom),
        _ => None,
    }
}

pub(super) fn fn_app_range(s: &Shape) -> Shape {
    match s {
        Shape::Bottom => Shape::Bottom,
        Shape::Func { range, .. } => (**range).clone(),
        Shape::Seq { elem, .. } => (**elem).clone(),
        Shape::Tuple(ts) => ts.iter().fold(Shape::Bottom, |acc, x| join_shape(&acc, x)),
        Shape::Record(fs) => fs.values().fold(Shape::Bottom, |acc, x| join_shape(&acc, x)),
        _ => Shape::Top,
    }
}

pub(super) fn fn_dom_range(s: &Shape) -> Option<(Shape, Shape, Option<u32>)> {
    match s {
        Shape::Func { dom, range, max_dom, .. } => Some(((**dom).clone(), (**range).clone(), *max_dom)),
        Shape::Tuple(ts) => {
            let range = ts.iter().fold(Shape::Bottom, |acc, x| join_shape(&acc, x));
            let dom = if ts.is_empty() { Shape::Bottom } else { Shape::Int(Some((1, ts.len() as i32))) };
            Some((dom, range, u32::try_from(ts.len()).ok()))
        }
        Shape::Seq { elem, max_len, .. } => Some((Shape::Int(None), (**elem).clone(), *max_len)),
        Shape::Record(fs) => {
            let keys: BTreeSet<Arc<str>> = fs.keys().cloned().collect();
            let range = fs.values().fold(Shape::Bottom, |acc, x| join_shape(&acc, x));
            Some((Shape::Str(Some(keys)), range, u32::try_from(fs.len()).ok()))
        }
        _ => None,
    }
}

pub(super) fn domain_of_shape(s: &Shape) -> Shape {
    match fn_dom_range(s) {
        Some((dom, _, max_dom)) => Shape::Set { elem: Box::new(dom), finite: true, max_card: max_dom },
        None => Shape::Top,
    }
}

pub(super) fn seq_elem_bounds(s: &Shape) -> Option<(Shape, u32, Option<u32>)> {
    match s {
        Shape::Seq { elem, min_len, max_len } => Some(((**elem).clone(), *min_len, *max_len)),
        Shape::Tuple(ts) => {
            let elem = ts.iter().fold(Shape::Bottom, |acc, x| join_shape(&acc, x));
            Some((elem, ts.len() as u32, u32::try_from(ts.len()).ok()))
        }
        _ => None,
    }
}

pub(super) fn extract_exact_tuple_arity(s: &Shape, arity: usize) -> Option<Vec<Shape>> {
    match s {
        Shape::Tuple(ts) if ts.len() == arity => Some(ts.clone()),
        Shape::Bottom => Some(vec![Shape::Bottom; arity]),
        Shape::Union(us) if !us.is_empty() => {
            let mut acc = vec![Shape::Bottom; arity];
            for u in us {
                let parts = extract_exact_tuple_arity(u, arity)?;
                for (a, p) in acc.iter_mut().zip(parts) {
                    *a = join_shape(a, &p);
                }
            }
            Some(acc)
        }
        _ => None,
    }
}

/// Sound check that every value in `key` is guaranteed to belong to exact finite domain `dom`.
pub(super) fn shape_in_exact_domain(key: &Shape, dom: &Shape) -> bool {
    match (key, dom) {
        (Shape::Bottom, _) => true,
        (Shape::Union(us), d) => us.iter().all(|u| shape_in_exact_domain(u, d)),
        (Shape::Bool, Shape::Bool) => true,
        (Shape::Int(Some((kl, kh))), Shape::Int(Some((dl, dh)))) => kl >= dl && kh <= dh,
        (Shape::Str(Some(ks)), Shape::Str(Some(ds))) => ks.is_subset(ds),
        (Shape::Model { groups: kg, unmoved: Some(ku), .. }, Shape::Model { groups: dg, unmoved: Some(du), .. }) => {
            (kg & !dg) == 0 && ku.is_subset(du)
        }
        (Shape::Tuple(ks), Shape::Tuple(ds)) if ks.len() == ds.len() => ks.iter().zip(ds).all(|(k, d)| shape_in_exact_domain(k, d)),
        (k, Shape::Union(ds)) => ds.iter().any(|d| shape_in_exact_domain(k, d)),
        _ => false,
    }
}

/// Sound static upper bound on the finite universe size of `s` (if `<= i32::MAX`).
pub(super) fn shape_universe_size(s: &Shape, groups: &[GroupInfo]) -> Option<u32> {
    match s {
        Shape::Bottom => Some(0),
        Shape::Bool => Some(2),
        Shape::Int(Some((lo, hi))) => u32::try_from(*hi as i128 - *lo as i128 + 1).ok().filter(|&v| v <= MAX_I32_U32),
        Shape::Str(Some(ss)) => u32::try_from(ss.len()).ok(),
        Shape::Model { groups: mask, unmoved: Some(u), .. } => {
            let mut total = u32::try_from(u.len()).ok()?;
            for (gi, g) in groups.iter().enumerate() {
                if (mask & (1u16 << gi)) != 0 {
                    total = total.checked_add(u32::try_from(g.keys.len()).ok()?).filter(|&v| v <= MAX_I32_U32)?;
                }
            }
            Some(total)
        }
        Shape::Tuple(ts) => {
            let mut prod: u32 = 1;
            for t in ts {
                prod = prod.checked_mul(shape_universe_size(t, groups)?).filter(|&v| v <= MAX_I32_U32)?;
            }
            Some(prod)
        }
        Shape::Record(fs) => {
            let mut prod: u32 = 1;
            for v in fs.values() {
                prod = prod.checked_mul(shape_universe_size(v, groups)?).filter(|&v| v <= MAX_I32_U32)?;
            }
            Some(prod)
        }
        Shape::Set { elem, .. } => {
            let u = shape_universe_size(elem, groups)?;
            (u <= 30).then(|| 1u32 << u)
        }
        Shape::Union(us) => {
            let mut sum: u32 = 0;
            for u in us {
                sum = sum.checked_add(shape_universe_size(u, groups)?).filter(|&v| v <= MAX_I32_U32)?;
            }
            Some(sum)
        }
        _ => None,
    }
}

pub(super) fn lookup_except_path(base: &Shape, path: &[ExceptKey]) -> Shape {
    let mut cur = base.clone();
    for k in path {
        cur = match (k, &cur) {
            (ExceptKey::Field(f), _) => field_of_shape(&cur, f),
            (ExceptKey::Index(ixs), Shape::Record(_)) if ixs.len() == 1 => {
                if let ExprKind::Str(f) = &*ixs[0].kind {
                    field_of_shape(&cur, f)
                } else {
                    fn_app_range(&cur)
                }
            }
            (ExceptKey::Index(ixs), Shape::Tuple(ts)) if ixs.len() == 1 => {
                if let ExprKind::Num(n) = &*ixs[0].kind {
                    if let Some(u) = usize::try_from(*n).ok().filter(|&u| (1..=ts.len()).contains(&u)) {
                        ts[u - 1].clone()
                    } else {
                        Shape::Top
                    }
                } else {
                    fn_app_range(&cur)
                }
            }
            (ExceptKey::Index(_), _) => fn_app_range(&cur),
        };
    }
    cur
}

/// Sound record/function/tuple `EXCEPT` shape update (handles `!["n"]` identically to `!.n`
/// and widens all record fields on dynamic string indices!).
pub(super) fn apply_except_shape(base: &Shape, path: &[ExceptKey], val: &Shape) -> Shape {
    if path.is_empty() {
        return val.clone();
    }
    let rest = &path[1..];
    match (&path[0], base) {
        (ExceptKey::Field(f), Shape::Record(fs)) => {
            let mut next = fs.clone();
            if let Some(old) = next.get(f).cloned() {
                let updated = apply_except_shape(&old, rest, val);
                next.insert(f.clone(), updated);
            }
            Shape::Record(next)
        }
        (ExceptKey::Index(ixs), Shape::Record(fs)) if ixs.len() == 1 => {
            let mut next = fs.clone();
            if let ExprKind::Str(f) = &*ixs[0].kind {
                if let Some(old) = next.get(f).cloned() {
                    let updated = apply_except_shape(&old, rest, val);
                    next.insert(f.clone(), updated);
                }
            } else {
                // Dynamic index on record: soundly join updated shape into EVERY field!
                for (k, old) in fs {
                    let updated = apply_except_shape(old, rest, val);
                    next.insert(k.clone(), join_shape(old, &updated));
                }
            }
            Shape::Record(next)
        }
        (ExceptKey::Index(ixs), Shape::Tuple(ts)) if ixs.len() == 1 => {
            let mut next = ts.clone();
            if let ExprKind::Num(n) = &*ixs[0].kind {
                if let Some(u) = usize::try_from(*n).ok().filter(|&u| (1..=next.len()).contains(&u)) {
                    let i = u - 1;
                    next[i] = apply_except_shape(&next[i], rest, val);
                }
            } else {
                for slot in &mut next {
                    let updated = apply_except_shape(slot, rest, val);
                    *slot = join_shape(slot, &updated);
                }
            }
            Shape::Tuple(next)
        }
        (ExceptKey::Index(_), Shape::Seq { elem, min_len, max_len }) => {
            let updated = apply_except_shape(elem, rest, val);
            Shape::Seq { elem: Box::new(join_shape(elem, &updated)), min_len: *min_len, max_len: *max_len }
        }
        (ExceptKey::Index(_), Shape::Func { dom, exact_dom, range, max_dom }) => {
            let updated = apply_except_shape(range, rest, val);
            Shape::Func { dom: dom.clone(), exact_dom: *exact_dom, range: Box::new(join_shape(range, &updated)), max_dom: *max_dom }
        }
        (_, Shape::Union(us)) => {
            let mut acc = Shape::Bottom;
            for u in us {
                let s = apply_except_shape(u, path, val);
                acc = join_shape(&acc, &s);
            }
            acc
        }
        _ => Shape::Top,
    }
}
