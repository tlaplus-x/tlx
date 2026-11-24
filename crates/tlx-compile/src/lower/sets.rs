//! Encoded sets. A set shape is encoded as a bitset over its element
//! universe when the universe is small (`bitset_universe`), else as a
//! sorted array prefixed by its length. Bitset ranks are computed for
//! scalar elements and flat products of scalars (`flat_radices`); other
//! composite elements of bitsets are not handled here.
//!
//! Iteration (`typed_iter`) yields encoded elements only when the encoded
//! order is TLC's enumeration order, unless the result cannot depend on the
//! order (`pure`).

use tlx_layout::layout::bitset_universe;
use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{self, ExprKind as H};

use super::*;

/// The largest sorted-array union shape `typed_union` widens to.
const MAX_UNION_CARD: usize = 256;

impl Lowerer<'_> {
    /// `s \subseteq t`, also membership in an already lowered powerset.
    /// Only total comparable element universes may bypass boxed membership.
    pub(super) fn native_bit_subset(&mut self, s: &Expr, t: &Expr) -> Option<Expr> {
        let shape = |x: &Expr| self.shape_of(x.ty).cloned().or_else(|| typed::const_of(x).map(|v| Shape::of(&v)));
        let (Some(Shape::Set { elem: a, .. }), Some(Shape::Set { elem: b, .. })) = (shape(s), shape(t)) else {
            return None;
        };
        if !typed::shapes_comparable(&a, &b) {
            return None;
        }
        let (s, t, sid) = self.same_bitsets(s, t).or_else(|| self.converted_bitsets(s, t, false))?;
        let outside = Expr::new(Ty::Enc(sid), ExprKind::BitSetOp(SetOp::Diff, s, t));
        Some(eq(outside, self.zero_enc(sid)))
    }

    pub(super) fn is_bitset(&self, t: Ty) -> bool {
        matches!(self.shape_of(t), Some(Shape::Set { elem, .. }) if bitset_universe(elem).is_some())
    }

    /// Element shape id, element words and max cardinality of a sorted-array set.
    pub(super) fn sorted_elem(&mut self, t: Ty) -> Option<(ShapeId, u32, u32)> {
        let Some(Shape::Set { elem, max_card }) = self.shape_of(t).cloned() else { return None };
        if bitset_universe(&elem).is_some() {
            return None;
        }
        let esid = self.sid(&elem);
        let ew = self.words_of(&elem);
        Some((esid, ew, max_card as u32))
    }

    /// `x` (a bitset) as a bitset of shape `sid` over the same element
    /// universe: the same words (bitset encodings do not depend on the
    /// maximum cardinality).
    pub(super) fn bitset_retype(&self, x: &Expr, sid: ShapeId) -> Option<Expr> {
        let (Some(Shape::Set { elem: a, .. }), Some(Shape::Set { elem: b, .. })) = (self.shape_of(x.ty), self.shape_of(Ty::Enc(sid)))
        else {
            return None;
        };
        if a != b || !self.is_bitset(x.ty) {
            return None;
        }
        Some(Expr::new(Ty::Enc(sid), ExprKind::Slice { base: x.clone(), offset: 0 }))
    }

    /// `x`, a bitset that may hold up to `bound` elements (None: any number),
    /// checked against the maximal cardinality of its set shape. A bitset
    /// can represent any subset of its universe, but one with more elements
    /// than the shape admits is not an encoding of the shape: re-encoding it
    /// (in a widened layout, through the layout functions) fails, and so
    /// would the encoding of the same value by the interpreter. As for
    /// sorted arrays (`SortedInsert`, `SortedOp`), such a value is a
    /// runtime layout miss: the evaluation falls back to the interpreter,
    /// whose state encoding reports it.
    ///
    /// Only for the shapes of the state and materialized definitions: the
    /// maximal cardinality of other shapes (of intermediate values, e.g. the
    /// parameter of a compiled function inferred from a call with a
    /// singleton) matters to no encoding, compiled code ranks a set element
    /// only when its shape admits every subset (`bit_rank`), and the
    /// interpreter never encodes such a value, so a failed check would make
    /// every evaluation that exceeds it fall back to the interpreter without
    /// a layout miss that widens the shape (TLCSailfish1 ran 10x slower).
    pub(super) fn card_checked(&mut self, x: Expr, bound: Option<u64>) -> Expr {
        let Ty::Enc(sid) = x.ty else { return x };
        if !self.typing.in_layout(sid) {
            return x;
        }
        let Some(Shape::Set { elem, max_card }) = self.shape_of(x.ty).cloned() else { return x };
        let Some(n) = bitset_universe(&elem) else { return x };
        if max_card as u64 >= n.min(bound.unwrap_or(u64::MAX)) {
            return x;
        }
        let ty = x.ty;
        let (xs, bind) = self.share(x);
        let card = Expr::new(Ty::Int, ExprKind::BitCard(xs.clone()));
        let fits = Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Le, card, int_lit(max_card as i64)));
        let fail = Expr::new(ty, ExprKind::Fail("set larger than the layout allows".into()));
        let_in(bind, Expr::new(ty, ExprKind::If(fits, xs, fail)))
    }

    /// The maximal number of elements of a bitset of the type `t`.
    pub(super) fn bitset_bound(&self, t: Ty) -> Option<u64> {
        match self.shape_of(t) {
            Some(Shape::Set { elem, max_card }) => Some(bitset_universe(elem)?.min(*max_card as u64)),
            _ => None,
        }
    }

    /// Both operands as bitsets of the same shape (encoding a constant one).
    fn same_bitsets(&self, a: &Expr, b: &Expr) -> Option<(Expr, Expr, ShapeId)> {
        match (a.ty, b.ty) {
            (Ty::Enc(x), Ty::Enc(y)) if x == y && self.is_bitset(a.ty) => Some((a.clone(), b.clone(), x)),
            (Ty::Enc(x), Ty::Enc(_)) if self.is_bitset(a.ty) => Some((a.clone(), self.bitset_retype(b, x)?, x)),
            (Ty::Enc(x), _) if self.is_bitset(a.ty) => {
                let ExprKind::Const(v) = &*b.kind else { return None };
                let c = self.const_words(v, x)?;
                Some((a.clone(), c, x))
            }
            (_, Ty::Enc(y)) if self.is_bitset(b.ty) => {
                let ExprKind::Const(v) = &*a.kind else { return None };
                let c = self.const_words(v, y)?;
                Some((c, b.clone(), y))
            }
            _ => None,
        }
    }

    /// Rank of element `x` in bitset `set` (scalar or flat product elements).
    pub(super) fn bit_rank(&mut self, set: &Expr, x: &Expr) -> Option<Expr> {
        let Some(Shape::Set { elem, .. }) = self.shape_of(set.ty).cloned() else { return None };
        bitset_universe(&elem)?;
        if elem.cardinality() == Some(0) {
            // A set over an empty element universe is always the empty set
            // (its encoding has no bits): nothing is a member. The element is
            // still evaluated, as TLC evaluates it before the set, and the
            // constant negative rank never reads a bit.
            let (xs, bind) = self.share(x.clone());
            let _ = xs;
            return Some(let_in(bind, int_lit(-1)));
        }
        if let Shape::Int { lo, .. } = *elem {
            let xi = self.as_int(x.clone()).ok()?;
            return Some(Expr::new(Ty::Int, ExprKind::IntBin(IntOp::Sub, xi, int_lit(lo))));
        }
        if let ExprKind::Const(v) = &*x.kind {
            // Constant element: rank at compile time (absent => never a member).
            let r = tlx_layout::layout::rank(&elem, v).map_or(-1, |r| r as i64);
            return Some(int_lit(r));
        }
        if let ExprKind::Convert(c) = &*x.kind {
            // A constant outside the element shape (converted at run time,
            // which fails): never a member, if comparable with all the
            // elements without a TLC error.
            if let ExprKind::Const(v) = &*c.kind {
                if tlx_layout::layout::rank(&elem, v).is_err() && v.normalize().is_ok_and(|v| typed::comparable(&elem, &v)) {
                    return Some(int_lit(-1));
                }
            }
        }
        // Sets over a small universe holding any subset: the rank is the
        // bitset itself (one word).
        if let Shape::Set { .. } = &*elem {
            if word_ranked_set(&elem) {
                let esid = self.sid(&elem);
                let x = if x.ty == Ty::Enc(esid) { x.clone() } else { self.bitset_retype(x, esid)? };
                return Some(Expr::new(Ty::Int, ExprKind::Rank(x)));
            }
            return None;
        }
        if let Some(arms) = union_radices(&elem) {
            let esid = self.sid(&elem);
            if x.ty != Ty::Enc(esid) {
                return None;
            }
            let arms: Vec<Arc<[u64]>> = arms.into_iter().map(Arc::from).collect();
            return Some(Expr::new(Ty::Int, ExprKind::RankUnion { x: x.clone(), arms: arms.into() }));
        }
        // Products and unions of those: combined from the parts' ranks.
        if !elem.is_scalar() && flat_radices(&elem).is_none() && rankable(&elem) {
            let esid = self.sid(&elem);
            if x.ty == Ty::Enc(esid) {
                let (xs, bind) = self.share(x.clone());
                let r = self.nested_rank(xs, &elem)?;
                return Some(let_in(bind, r));
            }
        }
        // Atoms and booleans are their rank; flat products combine the
        // ranks of their components.
        let radices = if elem.is_scalar() { None } else { Some(flat_radices(&elem)?) };
        let esid = self.sid(&elem);
        if x.ty == Ty::Enc(esid) {
            return Some(match radices {
                None => Expr::new(Ty::Int, ExprKind::Rank(x.clone())),
                Some(radices) => Expr::new(Ty::Int, ExprKind::RankFlat { x: x.clone(), radices: radices.into() }),
            });
        }
        if let ExprKind::Const(v) = &*x.kind {
            // Constant element: rank at compile time (absent => never a member).
            let r = tlx_layout::layout::rank(&elem, v).map_or(-1, |r| r as i64);
            return Some(int_lit(r));
        }
        None
    }

    /// Rank (as `layout::rank`) of `x`, an encoded value of the rankable
    /// shape `s` (see `rankable`): mixed radix over the parts of products,
    /// the cardinalities of the earlier arms plus the payload's rank for
    /// unions.
    fn nested_rank(&mut self, x: Expr, s: &Shape) -> Option<Expr> {
        let sid = self.sid(s);
        debug_assert_eq!(x.ty, Ty::Enc(sid));
        if s.is_scalar() || word_ranked_set(s) {
            return Some(Expr::new(Ty::Int, ExprKind::Rank(x)));
        }
        if let Some(radices) = flat_radices(s) {
            return Some(Expr::new(Ty::Int, ExprKind::RankFlat { x, radices: radices.into() }));
        }
        if let Some(arms) = union_radices(s) {
            let arms: Vec<Arc<[u64]>> = arms.into_iter().map(Arc::from).collect();
            return Some(Expr::new(Ty::Int, ExprKind::RankUnion { x, arms: arms.into() }));
        }
        match s {
            Shape::Tuple(_) | Shape::Record(_) => {
                let parts: Vec<Shape> = match s {
                    Shape::Tuple(es) => es.to_vec(),
                    Shape::Record(fs) => fs.iter().map(|(_, f)| f.clone()).collect(),
                    _ => unreachable!(),
                };
                let mut acc: Option<Expr> = None;
                let mut off = 0u32;
                for p in &parts {
                    let psid = self.sid(p);
                    let slot = Expr::new(Ty::Enc(psid), ExprKind::Slice { base: x.clone(), offset: off });
                    off += self.words(psid);
                    let r = self.nested_rank(slot, p)?;
                    let c = p.cardinality()? as i64;
                    acc = Some(match acc {
                        None => r,
                        Some(a) => Expr::new(
                            Ty::Int,
                            ExprKind::IntBin(IntOp::Add, Expr::new(Ty::Int, ExprKind::IntBin(IntOp::Mul, a, int_lit(c))), r),
                        ),
                    });
                }
                Some(acc.unwrap_or_else(|| int_lit(0)))
            }
            Shape::Union(arms) => {
                let tag = self.int_word(x.clone(), 0, arms.len() as i64 - 1);
                let mut out = Expr::new(Ty::Int, ExprKind::Fail("union arm out of range".into()));
                let mut base: i64 = arms.iter().map(|a| a.cardinality().map(|c| c as i64)).sum::<Option<i64>>()?;
                for (i, a) in arms.iter().enumerate().rev() {
                    base -= a.cardinality()? as i64;
                    let asid = self.sid(a);
                    let payload = Expr::new(Ty::Enc(asid), ExprKind::Slice { base: x.clone(), offset: 1 });
                    let r = self.nested_rank(payload, a)?;
                    let r = Expr::new(Ty::Int, ExprKind::IntBin(IntOp::Add, int_lit(base), r));
                    out = Expr::new(Ty::Int, ExprKind::If(eq(tag.clone(), int_lit(i as i64)), r, out));
                }
                Some(out)
            }
            _ => None,
        }
    }

    /// `s /= {}` for an encoded set.
    pub(super) fn nonempty(&mut self, s: Expr) -> Option<Expr> {
        let Some(Shape::Set { elem, max_card }) = self.shape_of(s.ty).cloned() else { return None };
        let card = if bitset_universe(&elem).is_some() {
            Expr::new(Ty::Int, ExprKind::BitCard(s))
        } else {
            // Sorted-array sets start with their length.
            self.int_word(s, 0, max_card as i64)
        };
        Some(Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Gt, card, int_lit(0))))
    }

    /// How to iterate over `set`: an encoded set (or a constant set that can
    /// be encoded) yields encoded elements when the encoded order is TLC's
    /// order; otherwise elements are boxed values.
    pub(super) fn typed_iter(&mut self, set: Expr) -> (Expr, Ty) {
        self.typed_iter_in(set, false)
    }

    /// `pure`: the iteration result does not depend on the order (`\E`/`\A`
    /// in expressions), so sets may be iterated in encoded order.
    pub(super) fn typed_iter_in(&mut self, set: Expr, pure: bool) -> (Expr, Ty) {
        // A stored set: its elements (normalized, so TLC's order for every
        // consumer) as handles.
        if self.is_ref(set.ty) {
            let h = set.ty;
            return (Expr::new(Ty::Val, ExprKind::RefElems(set)), h);
        }
        let set = self.set_operand(set);
        if let Some(Shape::Set { elem, .. }) = self.shape_of(set.ty).cloned() {
            if order_safe(&elem) || (pure && !is_composite_bitset_elem(&elem)) {
                let esid = self.sid(&elem);
                return (set, Ty::Enc(esid));
            }
            if !is_composite_bitset_elem(&elem) {
                let plan = self
                    .order_plans
                    .entry((*elem).clone())
                    .or_insert_with(|| {
                        crate::encoded_order::plan(&elem).map(|p| match bitset_universe(&elem) {
                            Some(n) => crate::encoded_order::with_rank_keys(p, &elem, n),
                            None => p,
                        })
                    })
                    .clone();
                if let Some(plan) = plan {
                    let esid = self.sid(&elem);
                    return (Expr::new(Ty::Val, ExprKind::OrderedSet { set, plan }), Ty::Enc(esid));
                }
            }
            return (to_val(set), Ty::Val);
        }
        if let Some(x) = self.subsets_source(&set, pure) {
            return x;
        }
        if let ExprKind::ValOp { op: B::DotDot, args } = &*set.kind {
            if !self.ip.is_builtin_overridden(B::DotDot) {
                if let (Ok(lo), Ok(hi)) = (self.as_int(args[0].clone()), self.as_int(args[1].clone())) {
                    return (Expr::new(Ty::Val, ExprKind::IntRange(lo, hi)), Ty::Int);
                }
            }
        }
        if let ExprKind::Const(v) = &*set.kind {
            if let Some(x) = self.const_iter(v) {
                return x;
            }
        }
        (to_val(set), Ty::Val)
    }

    /// `SUBSET s` of an encoded bitset `s` as an iteration source of
    /// bitsets of `s`'s shape (in TLC's order if the encoded order of the
    /// elements is TLC's order).
    fn subsets_source(&mut self, set: &Expr, pure: bool) -> Option<(Expr, Ty)> {
        let ExprKind::ValOp { op: B::Subset, args } = &*set.kind else { return None };
        if self.ip.is_builtin_overridden(B::Subset) {
            return None;
        }
        let base = match &*args[0].kind {
            ExprKind::Convert(x) => x.clone(),
            _ => args[0].clone(),
        };
        let base = self.set_operand(base);
        let Some(Shape::Set { elem, .. }) = self.shape_of(base.ty).cloned() else { return None };
        if !self.is_bitset(base.ty) || !(order_safe(&elem) || pure) {
            return None;
        }
        let ty = base.ty;
        Some((Expr::new(Ty::Val, ExprKind::Subsets(base)), ty))
    }

    /// A conservative total fragment for materializing lazy powerset filters.
    fn total_filter_predicate(&mut self, e: &Expr) -> bool {
        match &*e.kind {
            ExprKind::Const(_) | ExprKind::ConstWords(_) | ExprKind::Temp(_) | ExprKind::Var(_) | ExprKind::NextVar(_) => true,
            ExprKind::Slice { base, .. } | ExprKind::BitCard(base) | ExprKind::Not(base) => self.total_filter_predicate(base),
            ExprKind::Convert(x)
                if matches!((self.shape_of(x.ty), e.ty), (Some(Shape::Int { .. }), Ty::Int) | (Some(Shape::Bool), Ty::Bool)) =>
            {
                self.total_filter_predicate(x)
            }
            ExprKind::IntCmp(_, a, b) => self.total_filter_predicate(a) && self.total_filter_predicate(b),
            ExprKind::IntBin(IntOp::Add | IntOp::Sub | IntOp::Mul, a, b) => {
                self.int_range(e).is_some() && self.total_filter_predicate(a) && self.total_filter_predicate(b)
            }
            ExprKind::And(xs) | ExprKind::Or(xs) => xs.iter().all(|x| self.total_filter_predicate(x)),
            _ => false,
        }
    }

    /// `{x \in S : P}` over an encoded `S` (not a bitset of composites).
    pub(super) fn typed_filter(&mut self, bound: &hir::Bound, pred: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let set = self.expr(&bound.set, env, st);
        // Quorum filters over a small powerset: retain the subset's bitset
        // type, so later quantification does not box every voter. The
        // element encoding admits the full base universe (its rank is the
        // bitmask), even if the observed set cardinality was smaller.
        if let Some((_, ety)) = self.subsets_source(&set, true) {
            let Shape::Set { elem, .. } = self.shape_of(ety)?.clone() else { return None };
            let universe = bitset_universe(&elem)?;
            let subset = Shape::Set { elem, max_card: usize::try_from(universe).ok()? };
            let count = subset.cardinality()?;
            // Same inferred-universe budget as computed interval filters.
            if count > 4096 {
                return None;
            }
            let sid = self.sid(&Shape::Set { elem: Box::new(subset.clone()), max_card: count as usize });
            let mapped = self.set_filter_into(bound, pred, &subset, env, st, sid)?;
            let ExprKind::MapSet { cond: Some(cond), .. } = &*mapped.kind else { return None };
            // SUBSET filters are lazy. Materialize only a total predicate:
            // no errors or effects may appear beyond an early quantifier hit.
            return self.total_filter_predicate(cond).then_some(mapped);
        }
        if let ExprKind::Const(v) = &*set.kind {
            // A filter over a constant set: a bitset over its universe.
            let enc = self.const_bitset(v)?;
            let Ty::Enc(sid) = enc.ty else { return None };
            let Some(Shape::Set { elem, .. }) = self.shape_of(enc.ty).cloned() else { return None };
            return self.set_filter_into(bound, pred, &elem, env, st, sid);
        }
        if let ExprKind::ValOp { op: B::DotDot, args } = &*set.kind {
            // A filter over a computed interval: a bitset over the integers
            // the bounds can take.
            if self.ip.is_builtin_overridden(B::DotDot) {
                return None;
            }
            let (lo, hi) = (self.as_int(args[0].clone()).ok()?, self.as_int(args[1].clone()).ok()?);
            let (lo, hi) = (self.int_range(&lo)?.0, self.int_range(&hi)?.1);
            if hi < lo || hi - lo >= 4096 {
                return None;
            }
            let elem = Shape::Int { lo, hi };
            let sid = self.sid(&Shape::Set { elem: Box::new(elem.clone()), max_card: (hi - lo + 1) as usize });
            return self.set_filter_into(bound, pred, &elem, env, st, sid);
        }
        let Ty::Enc(sid) = set.ty else { return None };
        let Some(Shape::Set { elem, .. }) = self.shape_of(set.ty).cloned() else { return None };
        if is_composite_bitset_elem(&elem) {
            return None;
        }
        let esid = self.sid(&elem);
        let t = self.temp(Ty::Enc(esid));
        let (env2, check) = self.bind_elem(&bound.vars, &temp_ref(Ty::Enc(esid), t), env)?;
        let p = self.bool_expr(pred, &env2, st);
        Some(Expr::new(Ty::Enc(sid), ExprKind::Filter { bind: t, set, pred: binders::checked(check, p) }))
    }

    /// `A \X B` of two encoded sets whose element universes multiply to a
    /// small one: the pairs as a bitset of the product universe, the element
    /// of the product whose components are in `A` and `B`. Both operands are
    /// evaluated, and neither can fail once it is an encoded set.
    pub(super) fn typed_times(&mut self, a: &hir::Expr, b: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let x = self.expr(a, env, st);
        let y = self.expr(b, env, st);
        let (Some(Shape::Set { elem: ea, .. }), Some(Shape::Set { elem: eb, .. })) =
            (self.shape_of(x.ty).cloned(), self.shape_of(y.ty).cloned())
        else {
            return None;
        };
        if !self.is_bitset(x.ty) || !self.is_bitset(y.ty) {
            return None;
        }
        let pair = Shape::Tuple(vec![(*ea).clone(), (*eb).clone()].into());
        // `bitset_universe` already refuses a product beyond the bitset limit.
        let n = bitset_universe(&pair)?;
        let psid = self.sid(&pair);
        let rsid = self.sid(&Shape::Set { elem: Box::new(pair), max_card: n as usize });
        let (esid, fsid) = (self.sid(&ea), self.sid(&eb));
        let (nw, w) = (self.words(rsid), self.words(esid));
        let (xs, bx) = self.share(x);
        let (ys, by) = self.share(y);
        let t = self.temp(Ty::Enc(psid));
        let slot = |off: u32, sid| Expr::new(Ty::Enc(sid), ExprKind::Slice { base: temp_ref(Ty::Enc(psid), t), offset: off });
        let r0 = self.bit_rank(&xs, &slot(0, esid))?;
        let r1 = self.bit_rank(&ys, &slot(w, fsid))?;
        let m0 = Expr::new(Ty::Bool, ExprKind::BitMember { set: xs, rank: r0 });
        let m1 = Expr::new(Ty::Bool, ExprKind::BitMember { set: ys, rank: r1 });
        let mut full = vec![0u64; nw as usize];
        for r in 0..n {
            full[(r / 64) as usize] |= 1 << (r % 64);
        }
        let full = Expr::new(Ty::Enc(rsid), ExprKind::ConstWords(full.into()));
        let pred = Expr::new(Ty::Bool, ExprKind::And(vec![m0, m1]));
        let pairs = Expr::new(Ty::Enc(rsid), ExprKind::Filter { bind: t, set: full, pred });
        Some(let_in(bx, let_in(by, pairs)))
    }

    /// `S \subseteq T` for an encoded S: `\A x \in S : x \in T`.
    pub(super) fn typed_subseteq(&mut self, s: &hir::Expr, t: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        let s = self.expr(s, env, st);
        match self.subseteq_lowered(s.clone(), t, env, st) {
            Some(x) => x,
            None => {
                let t = self.expr(t, env, st);
                self.val_op(B::SubsetEq, vec![s, t])
            }
        }
    }

    /// `s \subseteq t` for a lowered, encoded `s`; None if `s` is not an
    /// iterable encoded set.
    pub(super) fn subseteq_lowered(&mut self, s: Expr, t: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let s = self.set_operand(s);
        let tset = self.expr(t, env, st);
        let tset = self.set_operand(tset);
        // A small integer set against a constant interval already has native
        // short-circuit range tests. Keep that established path: replacing it
        // with a difference adds no native coverage and can regress the whole
        // predicate even when the C compiler folds away the temporary bitset.
        // Lowered powersets still use native_bit_subset directly when they
        // have no structural interval path to retain.
        let prefer_interval = matches!(&*tset.kind, ExprKind::Const(Value::Interval(..)))
            && matches!(self.shape_of(s.ty), Some(Shape::Set { elem, .. })
                if matches!(&**elem, Shape::Int { .. }) && bitset_universe(elem).is_some_and(|n| n <= 64));
        if !prefer_interval {
            if let Some(m) = self.native_bit_subset(&s, &tset) {
                return Some(m);
            }
        }
        if !matches!(self.shape_of(s.ty), Some(Shape::Set { .. })) {
            return None;
        }
        let (s, bind_s) = self.share(s);
        let (s, ety) = self.typed_iter_in(s, true);
        if !s.is_typed_source() {
            return None;
        }
        // Construct both operands even when the left set is empty. A lazy
        // powerset/filter remains lazy; an eager finite filter must still
        // evaluate its predicate and preserve any errors or effects.
        let (tset, bind_t) = self.share(tset);
        let x = self.temp(ety);
        let m = self.member_lowered(temp_ref(ety, x), None, tset, env, st);
        let result = Expr::new(Ty::Bool, ExprKind::Forall { bind: x, set: s, body: to_bool(m) });
        Some(let_in(bind_t.into_iter().chain(bind_s), result))
    }

    /// `A \cup B` built into the sorted-array set shape `sid`: both operands
    /// in that encoding, merged up to its maximal cardinality (None: an
    /// operand does not lower into it).
    pub(super) fn sorted_union_into(&mut self, a: &hir::Expr, b: &hir::Expr, env: &LEnv, st: &St, sid: ShapeId) -> Option<Expr> {
        let (esid, ew, max_card) = self.sorted_elem(Ty::Enc(sid))?;
        let elem = self.shape_of(Ty::Enc(esid))?;
        if !typed::shapes_comparable(elem, elem) {
            return None;
        }
        let la = self.expr_into(a, env, st, sid);
        if la.ty != Ty::Enc(sid) || matches!(&*la.kind, ExprKind::Convert(_)) {
            return None;
        }
        if let H::SetEnum(es) = &*b.kind {
            let mut out = la;
            for x in es {
                let elem = self.expr_into(x, env, st, esid);
                let elem = self.coerce_enc(elem, esid);
                out = Expr::new(Ty::Enc(sid), ExprKind::SortedInsert { set: out, elem, elem_words: ew, max_card });
            }
            return Some(out);
        }
        let lb = self.expr_into(b, env, st, sid);
        if lb.ty != Ty::Enc(sid) || matches!(&*lb.kind, ExprKind::Convert(_)) {
            return None;
        }
        Some(Expr::new(Ty::Enc(sid), ExprKind::SortedOp { op: SetOp::Union, a: la, b: lb, elem_words: ew, max_card }))
    }

    /// `A \cup B`: inserting enumerated elements into a sorted-array set,
    /// or a bitset union.
    pub(super) fn typed_union(&mut self, a: &hir::Expr, b: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        let ha = a;
        let a = self.expr(a, env, st);
        // TLC's SetCupValue enumerates both operands, including duplicates,
        // when either is a lazy set. Encoding a constant lazy operand here
        // would instead turn the union into a deduplicated SetEnumValue.
        let lb = self.expr(b, env, st);
        let reducible = |x: &Expr| {
            matches!(&*x.kind, ExprKind::Const(Value::Set(_) | Value::Interval(..)))
                || matches!(self.shape_of(x.ty), Some(Shape::Set { .. }))
        };
        if !reducible(&a) || !reducible(&lb) {
            return self.val_op(B::Cup, vec![a, lb]);
        }
        // A union universe can encode values whose TLC comparisons fail
        // (e.g. an integer and a string). Word-wise union would omit
        // the merge's required comparisons, even for a subset RHS.
        if [&a, &lb].into_iter().any(|x| {
            let shape = self.shape_of(x.ty).cloned().or_else(|| match &*x.kind {
                ExprKind::Const(v) => Some(Shape::of(v)),
                _ => None,
            });
            matches!(shape, Some(Shape::Set { elem, .. }) if !typed::shapes_comparable(&elem, &elem))
        }) {
            return self.val_op(B::Cup, vec![a, lb]);
        }
        let a = self.set_operand(a);
        // A constructed sorted-array operand (e.g. `{x} \cup S`) has room
        // for its own elements only: the union is built into a shape with
        // room for both operands (otherwise it fails at run time as soon
        // as `B` adds an element).
        if let (Some((_, _, ma)), true) = (self.sorted_elem(a.ty), builds_set(ha)) {
            let mb = match &*b.kind {
                H::SetEnum(es) => Some(es.len()),
                _ => {
                    let lb = self.expr(b, env, st);
                    let lb = self.set_operand(lb);
                    match (self.shape_of(lb.ty), self.shape_of(a.ty)) {
                        (Some(Shape::Set { elem: eb, .. }), Some(Shape::Set { elem: ea, .. })) if eb == ea => self.iter_bound(&lb),
                        _ => None,
                    }
                }
            };
            if let Some(mb) = mb {
                let total = ma as usize + mb;
                if total > ma as usize && total <= MAX_UNION_CARD {
                    let Some(Shape::Set { elem, .. }) = self.shape_of(a.ty).cloned() else { unreachable!() };
                    let wsid = self.sid(&Shape::Set { elem, max_card: total });
                    if let Some(x) = self.sorted_union_into(ha, b, env, st, wsid) {
                        return x;
                    }
                }
            }
        }
        if let (Some((esid, ew, max_card)), H::SetEnum(es)) = (self.sorted_elem(a.ty), &*b.kind) {
            let ty = a.ty;
            let mut out = a;
            for x in es {
                let elem = self.expr_into(x, env, st, esid);
                out = Expr::new(ty, ExprKind::SortedInsert { set: out, elem, elem_words: ew, max_card });
            }
            return out;
        }
        if let Some((_, ew, max_card)) = self.sorted_elem(a.ty) {
            let Ty::Enc(sid) = a.ty else { unreachable!() };
            let b = if self.constructs(b, env) { self.expr_into(b, env, st, sid) } else { self.expr(b, env, st) };
            let b = if b.ty == a.ty { b } else { self.coerce_enc(b, sid) };
            let ty = a.ty;
            return Expr::new(ty, ExprKind::SortedOp { op: SetOp::Union, a, b, elem_words: ew, max_card });
        }
        let b = self.bitset_operand(b, a.ty, env, st);
        // Bitsets of different element shapes: one converted into the
        // other's universe, where every element fits; else a computed set
        // into a variable's universe, where its elements are expected to
        // fit (an element that does not is a runtime failure, as when the
        // union is stored in that variable).
        let same =
            self.same_bitsets(&a, &b).or_else(|| self.converted_bitsets(&a, &b, false)).or_else(|| self.converted_bitsets(&a, &b, true));
        match same {
            Some((a, b, sid)) => {
                let bound = self.bitset_bound(a.ty).zip(self.bitset_bound(b.ty)).map(|(x, y)| x + y);
                let u = Expr::new(Ty::Enc(sid), ExprKind::BitSetOp(SetOp::Union, a, b));
                self.card_checked(u, bound)
            }
            None => self.val_op(B::Cup, vec![a, b]),
        }
    }

    /// Two encoded sets with different element shapes as bitsets of one
    /// shape: one converted into the bitset shape of the other,
    /// if every element of its shape fits (or, with `lenient`, a computed
    /// set converted into the shape of a state variable: an element that
    /// does not fit is then a runtime failure).
    fn converted_bitsets(&mut self, a: &Expr, b: &Expr, lenient: bool) -> Option<(Expr, Expr, ShapeId)> {
        let (Ty::Enc(x), Ty::Enc(y)) = (a.ty, b.ty) else { return None };
        let (Some(Shape::Set { elem: ea, .. }), Some(Shape::Set { elem: eb, .. })) =
            (self.shape_of(a.ty).cloned(), self.shape_of(b.ty).cloned())
        else {
            return None;
        };
        if ea == eb {
            return None;
        }
        for (into, sid, from_elem, into_elem) in [(true, x, &eb, &ea), (false, y, &ea, &eb)] {
            let (other, target) = if into { (b, a) } else { (a, b) };
            let var = |e: &Expr| matches!(&*e.kind, ExprKind::Var(_) | ExprKind::NextVar(_));
            let fits = if lenient { var(target) && !var(other) } else { tlx_layout::infer::bound_covers(into_elem, from_elem) };
            if !self.is_bitset(Ty::Enc(sid)) || !fits {
                continue;
            }
            let c = self.coerce_enc(other.clone(), sid);
            if c.ty != Ty::Enc(sid) || matches!(&*c.kind, ExprKind::Convert(_)) {
                continue;
            }
            return Some(if into { (a.clone(), c, sid) } else { (c, b.clone(), sid) });
        }
        None
    }

    /// `A \cap B` / `A \ B` (`op`) as a bitset operation where possible.
    pub(super) fn typed_set_op(&mut self, op: B, a: &hir::Expr, b: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        let a = self.expr(a, env, st);
        let a = self.set_operand(a);
        if let Some((_, ew, max_card)) = self.sorted_elem(a.ty) {
            let Ty::Enc(sid) = a.ty else { unreachable!() };
            let b = if self.constructs(b, env) { self.expr_into(b, env, st, sid) } else { self.expr(b, env, st) };
            let b = if b.ty == a.ty { b } else { self.coerce_enc(b, sid) };
            let sop = if op == B::Cap { SetOp::Inter } else { SetOp::Diff };
            let ty = a.ty;
            return Expr::new(ty, ExprKind::SortedOp { op: sop, a, b, elem_words: ew, max_card });
        }
        // A constant left operand: encode it like the right operand when that
        // is a bitset, else as a bitset over a universe shared with the state.
        let (a, b) = match &*a.kind {
            ExprKind::Const(v) if a.ty == Ty::Val && self.constructs(b, env) => {
                let ac = self.const_bitset(v).unwrap_or(a.clone());
                let bl = self.bitset_operand(b, ac.ty, env, st);
                (ac, bl)
            }
            ExprKind::Const(v) if a.ty == Ty::Val => {
                let bl = self.expr(b, env, st);
                match bl.ty {
                    Ty::Enc(bsid) if self.is_bitset(bl.ty) => match self.const_words(v, bsid) {
                        Some(ac) => (ac, bl),
                        None => (self.const_bitset(v).unwrap_or(a), bl),
                    },
                    _ => (self.const_bitset(v).unwrap_or(a), bl),
                }
            }
            _ => {
                let bl = self.bitset_operand(b, a.ty, env, st);
                (a, bl)
            }
        };
        // (Converted only where every element fits: an element outside the
        // other universe would be dropped, not fail.)
        match self.same_bitsets(&a, &b).or_else(|| self.converted_bitsets(&a, &b, false)) {
            Some((a, b, sid)) => {
                let sop = if op == B::Cap { SetOp::Inter } else { SetOp::Diff };
                Expr::new(Ty::Enc(sid), ExprKind::BitSetOp(sop, a, b))
            }
            None => self.val_op(op, vec![a, b]),
        }
    }

    /// The right operand of a set operator whose left operand has type
    /// `aty`: a constructor is built directly into a bitset encoding.
    fn bitset_operand(&mut self, e: &hir::Expr, aty: Ty, env: &LEnv, st: &St) -> Expr {
        match aty {
            Ty::Enc(sid) if self.is_bitset(aty) && self.constructs(e, env) => self.expr_into(e, env, st, sid),
            _ => {
                let x = self.expr(e, env, st);
                self.set_operand(x)
            }
        }
    }

    /// `UNION S` as a bitset (see the three cases below). The listed form is
    /// tried first: it unrolls a constant domain at compile time.
    pub(super) fn typed_big_union(&mut self, arg: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        self.big_union_listed(arg, env, st)
            .or_else(|| self.big_union_mapped(arg, env, st))
            .or_else(|| self.big_union_of_bitsets(arg, env, st))
    }

    /// `UNION {f(x) : x \in S}` for a non-constant `S` whose members are
    /// bitsets of one shape: their union, accumulated over the elements of
    /// `S` in iteration order. Every element is evaluated — TLC builds the
    /// set of sets before taking its union — so an error in any member is
    /// reported, and the result is a subset of the members' element
    /// universe whatever their own capacity was.
    fn big_union_mapped(&mut self, arg: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let (p, penv) = self.peel(arg, env)?;
        let H::SetMap { expr: f, bounds } = &*p.kind else { return None };
        let [b] = &bounds[..] else { return None };
        if !binders::single_binder(b) {
            return None;
        }
        let s = self.expr(&b.set, &penv, st);
        let (src, ety) = self.typed_iter_in(s, true);
        if !src.is_typed_source() {
            return None;
        }
        let t = self.temp(ety);
        let (env2, check) = self.bind_elem(&b.vars, &temp_ref(ety, t), &penv)?;
        let x = binders::checked(check, self.expr(f, &env2, st));
        // The union of subsets of one universe: the members' own bitset
        // shape holds it whatever capacity it was inferred with (a bitset
        // represents every subset of its universe; only the shapes of the
        // state and of materialized definitions bound a value, see
        // `card_checked`). `UnionFold` ors the members' words, which is only
        // the set union for a bitset encoding: over a larger (or unbounded)
        // element universe a set is a sorted array whose words are not a set.
        let Ty::Enc(sid) = x.ty else { return None };
        if !self.is_bitset(x.ty) {
            return None;
        }
        Some(Expr::new(Ty::Enc(sid), ExprKind::UnionFold { bind: t, set: src, body: x }))
    }

    /// `UNION {f(x) : x \in S}` built directly in the destination bitset:
    /// like `big_union_mapped`, but the member is lowered as the
    /// destination's encoding, so a recursive operator's result takes it and
    /// the recursion stays encoded to its unrolling limit.
    pub(super) fn big_union_into(&mut self, arg: &hir::Expr, sid: ShapeId, env: &LEnv, st: &St) -> Option<Expr> {
        let (p, penv) = self.peel(arg, env)?;
        let H::SetMap { expr: f, bounds } = &*p.kind else { return None };
        let [b] = &bounds[..] else { return None };
        if !binders::single_binder(b) {
            return None;
        }
        let s = self.expr(&b.set, &penv, st);
        let (src, ety) = self.typed_iter_in(s, true);
        if !src.is_typed_source() {
            return None;
        }
        let t = self.temp(ety);
        let (env2, check) = self.bind_elem(&b.vars, &temp_ref(ety, t), &penv)?;
        let x = binders::checked(check, self.expr_into(f, &env2, st, sid));
        // An inlined recursive body keeps the shape its own branches gave it
        // (a singleton `{x}` bounds it): re-encode it as the destination's
        // bitset, which is free when the element shape already matches. Only a
        // bitset destination may take `UnionFold` (see `big_union_mapped`).
        if !self.is_bitset(Ty::Enc(sid)) {
            return None;
        }
        let x = self.coerce_enc(x, sid);
        if x.ty != Ty::Enc(sid) {
            return None;
        }
        Some(Expr::new(Ty::Enc(sid), ExprKind::UnionFold { bind: t, set: src, body: x }))
    }

    /// `UNION S` of an encoded set `S` of bitsets with a small element
    /// universe: the elements of the universe in some member of `S` (a
    /// bitset of the universe).
    fn big_union_of_bitsets(&mut self, arg: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        const MAX_UNIVERSE: u64 = 256;
        let s = self.expr(arg, env, st);
        let s = self.set_operand(s);
        let Some(Shape::Set { elem: inner, .. }) = self.shape_of(s.ty).cloned() else { return None };
        let Shape::Set { elem, .. } = &*inner else { return None };
        let n = bitset_universe(elem).filter(|&n| n <= MAX_UNIVERSE)?;
        let (src, ity) = self.typed_iter_in(s, true);
        if !src.is_typed_source() || ity != Ty::Enc(self.sid(&inner)) {
            return None;
        }
        let rsid = self.sid(&Shape::Set { elem: elem.clone(), max_card: n as usize });
        let esid = self.sid(elem);
        let mut full = vec![0u64; self.words(rsid) as usize];
        for r in 0..n as usize {
            full[r / 64] |= 1 << (r % 64);
        }
        let (src, bind) = self.share(src);
        let (u, x) = (self.temp(Ty::Enc(esid)), self.temp(ity));
        let rank = self.bit_rank(&temp_ref(ity, x), &temp_ref(Ty::Enc(esid), u))?;
        let member = Expr::new(Ty::Bool, ExprKind::BitMember { set: temp_ref(ity, x), rank });
        let some = Expr::new(Ty::Bool, ExprKind::Exists { bind: x, set: src, body: member });
        let full = Expr::new(Ty::Enc(rsid), ExprKind::ConstWords(full.into()));
        Some(let_in(bind, Expr::new(Ty::Enc(rsid), ExprKind::Filter { bind: u, set: full, pred: some })))
    }

    /// `UNION {f(x) : x \in S}` / `UNION {a, b, ...}` for a constant `S`
    /// whose members are bitsets of one shape: their union, unrolled (every
    /// member is evaluated, as TLC builds the set of sets first).
    fn big_union_listed(&mut self, arg: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let (p, penv) = self.peel(arg, env)?;
        let mut members = Vec::new();
        match &*p.kind {
            H::SetMap { expr: f, bounds } => {
                let [b] = &bounds[..] else { return None };
                if !binders::single_binder(b) {
                    return None;
                }
                let dom = self.const_domain(&b.set, &penv, st)?;
                let elems = tlx_value::ops::enumerate(&dom).ok()?;
                if elems.is_empty() || elems.len() > 64 {
                    return None;
                }
                for x in elems {
                    let env2 = binders::bind_const(&b.vars, &x, &penv)?;
                    let m = self.expr(f, &env2, st);
                    if m.ty == Ty::Val && !matches!(&*m.kind, ExprKind::Const(_)) {
                        return None;
                    }
                    members.push(m);
                }
            }
            H::SetEnum(es) if !es.is_empty() && es.len() <= 64 => {
                for e in es {
                    members.push(self.expr(e, &penv, st));
                }
            }
            _ => return None,
        }
        let sid = members.iter().find_map(|m| match m.ty {
            Ty::Enc(s) if self.is_bitset(m.ty) => Some(s),
            _ => None,
        })?;
        let mut acc: Option<Expr> = None;
        for m in members {
            let m = match m.ty {
                Ty::Enc(s) if s == sid => m,
                _ => self.const_words(&typed::const_of(&m)?, sid)?,
            };
            acc = Some(match acc {
                None => m,
                Some(a) => Expr::new(Ty::Enc(sid), ExprKind::BitSetOp(SetOp::Union, a, m)),
            });
        }
        Some(self.card_checked(acc?, None))
    }

    /// `{e1, ..., en}` without a target encoding: the elements in a common
    /// encoding (see `common_shape`), as a bitset when the element universe
    /// is small, else a sorted array of capacity n.
    pub(super) fn typed_set_enum(&mut self, es: &[hir::Expr], env: &LEnv, st: &St) -> Option<Expr> {
        if es.is_empty() || es.len() > 64 {
            return None;
        }
        let mut xs: Vec<Expr> = Vec::new();
        for e in es {
            let x = self.expr(e, env, st);
            if x.ty == Ty::Val && !matches!(&*x.kind, ExprKind::Const(_)) {
                return None;
            }
            xs.push(x);
        }
        let elem = self.common_shape(&mut xs)?;
        // Encoded insertion compares words; it cannot preserve a deferred
        // comparison error or membership in an unnormalized mixed set.
        if !typed::shapes_comparable(&elem, &elem) {
            return None;
        }
        let esid = self.sid(&elem);
        let xs: Vec<Expr> = xs.into_iter().map(|x| self.coerce_enc(x, esid)).collect();
        if xs.iter().any(|x| matches!(&*x.kind, ExprKind::Convert(y) if y.ty == Ty::Val)) {
            return None;
        }
        let n = es.len();
        let max_card = elem.cardinality().map_or(n, |c| (c.min(n as u64)) as usize);
        let sid = self.sid(&Shape::Set { elem: Box::new(elem.clone()), max_card });
        if self.is_bitset(Ty::Enc(sid)) {
            if is_composite_bitset_elem(&elem) {
                return None;
            }
            let probe = self.zero_enc(sid);
            let ranks = xs.iter().map(|x| self.bit_rank(&probe, x)).collect::<Option<Vec<_>>>()?;
            return Some(Expr::new(Ty::Enc(sid), ExprKind::BitSet(ranks)));
        }
        let ew = self.words(esid);
        let mut out = self.zero_enc(sid);
        for x in xs {
            out = Expr::new(Ty::Enc(sid), ExprKind::SortedInsert { set: out, elem: x, elem_words: ew, max_card: max_card as u32 });
        }
        Some(out)
    }

    /// `Cardinality(s)`.
    pub(super) fn typed_cardinality(&mut self, s: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        let s = self.expr(s, env, st);
        if self.is_ref(s.ty) {
            return self.ref_op(crate::ir::RefOp::Cardinality, vec![s]);
        }
        let s = self.set_operand(s);
        if self.is_bitset(s.ty) {
            return Expr::new(Ty::Int, ExprKind::BitCard(s));
        }
        if let Some(Shape::Set { max_card, .. }) = self.shape_of(s.ty).cloned() {
            // Sorted-array sets start with their length.
            return self.int_word(s, 0, max_card as i64);
        }
        self.val_op(B::Cardinality, vec![s])
    }

    /// `{f(x) : x \in S}` with no target encoding: the element encoding is
    /// that of `f(x)`, the capacity the number of iterations of `S`.
    pub(super) fn typed_set_map(&mut self, f: &hir::Expr, bounds: &[hir::Bound], env: &LEnv, st: &St) -> Option<Expr> {
        let [b] = bounds else { return None };
        if !binders::single_binder(b) {
            return None;
        }
        let s = self.expr(&b.set, env, st);
        let (src, ety) = self.typed_iter_in(s, true);
        if !src.is_typed_source() {
            return None;
        }
        let bound = self.iter_bound(&src)?;
        let t = self.temp(ety);
        let (env2, check) = self.bind_elem(&b.vars, &temp_ref(ety, t), env)?;
        let x = self.expr(f, &env2, st);
        let mut x = binders::checked(check, x);
        if x.ty == Ty::Int {
            // Unboxed integers: encode them in their static range.
            let (lo, hi) = self.int_range(&x)?;
            let isid = self.sid(&Shape::Int { lo, hi });
            x = self.coerce_enc(x, isid);
        }
        let Ty::Enc(esid) = x.ty else { return None };
        let elem = self.shape_of(x.ty)?.clone();
        if !typed::shapes_comparable(&elem, &elem) {
            return None;
        }
        let max_card = elem.cardinality().map_or(bound, |c| (c.min(usize::MAX as u64) as usize).min(bound)).max(1);
        let sid = self.sid(&Shape::Set { elem: Box::new(elem.clone()), max_card });
        let x = if self.is_bitset(Ty::Enc(sid)) {
            let probe = self.zero_enc(sid);
            self.bit_rank(&probe, &x)?
        } else {
            let _ = esid;
            x
        };
        Some(Expr::new(Ty::Enc(sid), ExprKind::MapSet { bind: t, set: src, elem: x, cond: None }))
    }

    /// Upper bound on the number of elements an iteration source yields.
    pub(super) fn iter_bound(&self, src: &Expr) -> Option<usize> {
        let shape = self.shape_bound(src);
        match self.card_bound(src) {
            Some(n) => Some(shape.map_or(n, |m| m.min(n))),
            None => shape,
        }
    }

    /// A bound of the number of elements of the encoded set `x` that
    /// follows from how it is computed (tighter than its shape's maximal
    /// cardinality): a map or filter has at most as many elements as its
    /// source.
    pub(super) fn card_bound(&self, x: &Expr) -> Option<usize> {
        match &*x.kind {
            ExprKind::Temp(t) => self.temp_cards.get(t).copied(),
            ExprKind::MapSet { set, .. } | ExprKind::Filter { set, .. } => self.iter_bound(set),
            ExprKind::Let { body, .. } => self.card_bound(body),
            _ => None,
        }
    }

    /// `iter_bound` from the source's kind and shape alone.
    fn shape_bound(&self, src: &Expr) -> Option<usize> {
        match &*src.kind {
            ExprKind::ConstElems { count, .. } => Some(*count as usize),
            ExprKind::OrderedSet { set, .. } => self.iter_bound(set),
            ExprKind::IntRange(lo, hi) => match (&*lo.kind, &*hi.kind) {
                (ExprKind::Const(Value::Int(a)), ExprKind::Const(Value::Int(b))) => Some((b - a + 1).max(0) as usize),
                (ExprKind::Const(Value::Int(1)), ExprKind::SeqLen(s)) => match self.shape_of(s.ty) {
                    Some(Shape::Seq { max_len, .. }) => Some(*max_len),
                    _ => None,
                },
                _ => None,
            },
            _ => match self.shape_of(src.ty) {
                Some(Shape::Set { elem, max_card }) => Some(match bitset_universe(elem) {
                    // The bitsets of the layout's shapes respect their
                    // cardinality (`card_checked`); other bitsets
                    // may hold any subset of their universe.
                    Some(n) if matches!(src.ty, Ty::Enc(sid) if self.typing.in_layout(sid)) => (n as usize).min(*max_card),
                    Some(n) => n as usize,
                    None => *max_card,
                }),
                _ => None,
            },
        }
    }

    /// `SelectSeq(s, Test)` on an encoded sequence.
    pub(super) fn typed_select_seq(&mut self, s: &hir::Expr, test: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let s = self.expr(s, env, st);
        let Some(Shape::Seq { elem, .. }) = self.shape_of(s.ty).cloned() else { return None };
        let op = self.op_arg(test, env).ok()?;
        let esid = self.sid(&elem);
        let ew = self.words_of(&elem);
        let t = self.temp(Ty::Enc(esid));
        let pred = self.apply_op_to(&op, temp_ref(Ty::Enc(esid), t), env, st)?;
        let ty = s.ty;
        Some(Expr::new(ty, ExprKind::SeqFilter { bind: t, seq: s, pred: to_bool(pred), elem_words: ew }))
    }

    /// A one-argument operator (argument) applied to a lowered value.
    fn apply_op_to(&mut self, op: &LOp, arg: Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let (params, body, base) = match op {
            LOp::Ref(OpRef::Def(d)) => {
                let (params, body, base, _) = self.def_target(*d, env)?;
                (params.to_vec(), body, base)
            }
            LOp::Lambda(params, body, lenv) => (params.to_vec(), body.clone(), lenv.clone()),
            _ => return None,
        };
        if matches!(&*body.kind, H::Num(_) | H::Str(_)) {
            return None;
        }
        let [p] = &params[..] else { return None };
        let env2 = base.bind(*p, LBind::Ir(arg));
        Some(self.expr(&body, &env2, st))
    }
}

/// Composite elements of a bitset-encoded set.
/// Bitset elements whose rank cannot be computed / inverted in compiled code
/// (neither scalars, flat products nor unions of those).
pub(super) fn is_composite_bitset_elem(elem: &Shape) -> bool {
    bitset_universe(elem).is_some() && !rankable(elem)
}

/// Shapes whose rank compiled code computes and inverts: scalars, and
/// tuples, records and unions of rankable shapes.
pub(crate) fn rankable(s: &Shape) -> bool {
    match s {
        _ if s.is_scalar() || word_ranked_set(s) => true,
        Shape::Tuple(es) | Shape::Union(es) => es.iter().all(rankable),
        Shape::Record(fs) => fs.iter().all(|(_, f)| rankable(f)),
        _ => false,
    }
}

/// Whether `s` is a set shape whose values are any subset of a universe of
/// at most 62 elements: its layout rank is its (one-word) bitset.
pub(crate) fn word_ranked_set(s: &Shape) -> bool {
    let Shape::Set { elem, max_card } = s else { return false };
    elem.cardinality().is_some_and(|n| n <= 62 && *max_card as u64 >= n) && bitset_universe(elem).is_some()
}

/// Radices of each arm of a union whose arms are scalars (one radix) or
/// flat products (see `flat_radices`).
pub(crate) fn union_radices(s: &Shape) -> Option<Vec<Vec<u64>>> {
    let Shape::Union(arms) = s else { return None };
    arms.iter()
        .map(|a| match a {
            _ if a.is_scalar() => a.cardinality().map(|c| vec![c]),
            _ => flat_radices(a),
        })
        .collect()
}

pub(crate) fn flat_radices(s: &Shape) -> Option<Vec<u64>> {
    let parts: Vec<&Shape> = match s {
        Shape::Tuple(ps) => ps.iter().collect(),
        Shape::Record(fs) => fs.iter().map(|(_, f)| f).collect(),
        _ => return None,
    };
    parts.into_iter().map(|p| if p.is_scalar() { p.cardinality() } else { None }).collect()
}

use crate::encoded_order::order_safe;

/// A set constructed syntactically, possibly joined with others by `\cup`
/// (`{x} \cup S \cup T`): `expr_into` builds it in a given encoding.
fn builds_set(e: &hir::Expr) -> bool {
    match &*e.kind {
        H::Builtin { op: B::Cup, args } => builds_set(&args[0]),
        _ => super::construct::is_constructor(e),
    }
}
