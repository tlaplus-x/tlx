//! Which ranks of a bitset of union elements a loop must visit: shared by the
//! JIT (`jit::stmt`) and the C generator (`cgen`), so that the two native
//! tiers iterate the same elements.
//!
//! A loop over a set of messages with a predicate that starts with tests of
//! constant fields (`m.type = "2b" /\ m.bal = 1 /\ ...`) only needs the
//! elements passing those tests; each arm of the union owns a range of ranks
//! (its elements in mixed radix), so the tests select a mask of the bitset's
//! words, and the loop visits `word & mask` instead of every element (each of
//! which would be decoded, then tested).

use tlx_layout::Shape;

use crate::ir::*;
use crate::types::Typing;

/// The mask (by word of the `n`-word bitset of `elem` elements) of the ranks
/// that can pass the leading field tests of `pred` on the element bound to
/// `bind`, if `elem` is a union and `pred` starts with such tests.
pub(crate) fn rank_mask(ty: &Typing, elem: &Shape, n: usize, bind: Temp, pred: &Expr) -> Option<Vec<u64>> {
    let Shape::Union(arm_shapes) = elem else { return None };
    let arms = crate::lower::union_radices(elem)?;
    let mut tests = Vec::new();
    field_tests(ty, pred, bind, &mut tests);
    if tests.is_empty() {
        return None;
    }
    let mut m = vec![!0u64; n];
    let mut base = 0;
    for (i, radices) in arms.iter().enumerate() {
        let card: u64 = radices.iter().product();
        if let Some(ok) = arm_ranks(&tests, i, &arm_shapes[i], radices) {
            for (q, ok) in ok.into_iter().enumerate() {
                let r = base + q as u64;
                if !ok && r < n as u64 * 64 {
                    m[(r / 64) as usize] &= !(1 << (r % 64));
                }
            }
        }
        base += card;
    }
    Some(m)
}

/// The leading conjuncts of `pred` that compare a scalar field of the union
/// element `bind` with a constant: (the field's location in each arm, the
/// constant's code). Whether all of `pred` was such.
fn field_tests<'e>(ty: &Typing, pred: &'e Expr, bind: Temp, out: &mut Vec<(&'e [Option<FieldLoc>], u64)>) -> bool {
    match &*pred.kind {
        ExprKind::And(xs) => xs.iter().all(|x| field_tests(ty, x, bind, out)),
        ExprKind::Eq(a, b) => {
            let (f, c) = if matches!(&*a.kind, ExprKind::UnionField { .. }) { (a, b) } else { (b, a) };
            let ExprKind::UnionField { base, locs } = &*f.kind else { return false };
            if !matches!(&*base.kind, ExprKind::Temp(t) if *t == bind) {
                return false;
            }
            let Ty::Enc(sid) = f.ty else { return false };
            if c.ty != f.ty || ty.words(sid) != 1 || !ty.shape(sid).is_scalar() {
                return false;
            }
            let w = match &*c.kind {
                ExprKind::ConstWords(w) if w.len() == 1 => w[0],
                ExprKind::Const(v) => {
                    let mut w = [0u64];
                    if tlx_layout::layout::encode(ty.shape(sid), v, &mut w).is_err() {
                        return false;
                    }
                    w[0]
                }
                _ => return false,
            };
            out.push((locs, w));
            true
        }
        _ => false,
    }
}

/// Which ranks of arm `i` (of `radices`) pass the field tests `tests`
/// (`field_tests`) evaluated in order, up to the first one on a field the
/// arm does not have (which fails); None if no test applies.
fn arm_ranks(tests: &[(&[Option<FieldLoc>], u64)], i: usize, arm_shape: &Shape, radices: &[u64]) -> Option<Vec<bool>> {
    let card: u64 = radices.iter().product();
    if card == 0 {
        return None;
    }
    let fl = FieldLayout::of_shape(arm_shape);
    let mut ok: Option<Vec<bool>> = None;
    for (locs, v) in tests {
        let Some(target) = locs.get(i).copied().flatten() else { break };
        let idx = match &fl {
            Some(fl) => fl.locs.iter().position(|&l| l == target),
            None => (target == FieldLoc::Words(0)).then_some(0),
        };
        let Some(o) = idx.filter(|o| *o < radices.len()) else { break };
        let weight: u64 = radices[o + 1..].iter().product();
        let ok = ok.get_or_insert_with(|| vec![true; card as usize]);
        for (q, x) in ok.iter_mut().enumerate() {
            if (q as u64 / weight) % radices[o] != *v {
                *x = false;
            }
        }
    }
    ok
}
