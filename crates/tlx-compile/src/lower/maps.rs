//! Encoded maps (`Shape::Map`): functions whose domain varies over subsets
//! of a finite key universe (bags, functions on `0..n` with a variable `n`).
//! A map is a presence bitset over the key universe followed by one range
//! slot per key (see `types::map_dims`); keys are addressed by their rank in
//! the universe, computed like the rank of a bitset element (`bit_rank`).
//!
//! Here: `DOMAIN m` (the bitset prefix, so membership, iteration and
//! cardinality are bitset operations), application, `EXCEPT`, construction
//! `[x \in S |-> e]` over a computed domain, `k :> v`, `f @@ g`, membership
//! in `[D -> R]`, and coercions from the other function encodings.

use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{self, DefKind, ExprKind as H};
use tlx_value::plan::Absent;
use tlx_value::Value;

use super::*;
use crate::types::{map_dims, map_domain_shape};

/// Most entries of a fixed-domain function converted entry by entry.
const MAX_COERCED_ENTRIES: usize = 64;

/// Longest sequence a native `SortSeq` sorts: the compiled insertion sort
/// recurses once per element (each level of the C call holds one frame of
/// buffers).
const SORT_MAX_LEN: usize = 256;

/// Largest set a native `SetToSeq` materializes (`lower::choose` bounds the
/// same construction the same way).
const SET_TO_SEQ_MAX_CARD: usize = 64;

/// Callee placeholders of the sort functions being built; `patch_sort_calls`
/// replaces them with the indices the functions actually get.
const PENDING_INSERT: u32 = u32::MAX - 1;
const PENDING_SORT: u32 = u32::MAX - 2;

impl Lowerer<'_> {
    /// Key and range shapes of an encoded map.
    pub(super) fn map_parts(&self, t: Ty) -> Option<(Shape, Shape)> {
        match self.shape_of(t)? {
            Shape::Map { key, range, .. } => Some(((**key).clone(), (**range).clone())),
            _ => None,
        }
    }

    /// Key, range, and witness of an encoded map.
    pub(super) fn map_info(&self, t: Ty) -> Option<(Shape, Shape, tlx_layout::FcnWitness)> {
        match self.shape_of(t)? {
            Shape::Map { key, range, witness } => Some(((**key).clone(), (**range).clone(), *witness)),
            _ => None,
        }
    }

    /// `DOMAIN m` for a map `m` with keys of shape `key`: the presence
    /// bitset at the start of its encoding.
    pub(super) fn map_domain(&mut self, m: Expr, key: &Shape) -> Expr {
        let dsid = self.sid(&map_domain_shape(key));
        Expr::new(Ty::Enc(dsid), ExprKind::Slice { base: m, loc: FieldLoc::Words(0) })
    }

    /// Rank of `x` in the universe of `key` (an integer expression; values
    /// outside the universe rank outside `0..|universe|` or fail at run
    /// time). `x` is brought into the key encoding first if necessary.
    pub(super) fn map_key_rank(&mut self, key: &Shape, x: Expr, semantic: bool) -> Option<Expr> {
        let ksid = self.sid(key);
        let dsid = self.sid(&map_domain_shape(key));
        let probe = self.zero_enc(dsid);
        let x = match x.ty {
            Ty::Enc(s) if s != ksid => self.recode(&x, ksid).or_else(|| self.union_arm_coerce(&x, ksid)).unwrap_or(x),
            // A boxed key: encoded at run time (a key outside the universe
            // is then a runtime error, and the interpreter takes over).
            Ty::Val if !matches!(&*x.kind, ExprKind::Const(_)) => self.coerce_enc(x, ksid),
            _ => x,
        };
        if let Some(r) = self.bit_rank(&probe, &x, semantic) {
            return Some(r);
        }
        let x = self.coerce_enc(x, ksid);
        self.bit_rank(&probe, &x, semantic)
    }

    /// `map_key_rank` of the key expression `e` (a constructor is built
    /// directly in the key encoding).
    pub(super) fn map_key_rank_hir(&mut self, key: &Shape, e: &hir::Expr, env: &LEnv, st: &St, semantic: bool) -> Option<Expr> {
        let x = if self.constructs(e, env) {
            let ksid = self.sid(key);
            self.expr_into(e, env, st, ksid)
        } else {
            self.expr(e, env, st)
        };
        self.map_key_rank(key, x, semantic)
    }

    /// `m[k]` for the key of rank `rank` (absent: runtime error).
    pub(super) fn map_get(&mut self, m: Expr, rank: Expr, range: &Shape) -> Expr {
        let rsid = self.sid(range);
        Expr::new(Ty::Enc(rsid), ExprKind::MapGet { base: m, rank })
    }

    /// `[m EXCEPT ![k]... = val]` on an encoded map `m` (already shared by
    /// the caller) with the first key `k` lowered: an absent key leaves
    /// `m` unchanged, except that empty maps reject non-integer keys
    /// (they decode as tuples).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn map_except(&mut self, m: Expr, k: Expr, keys: &[hir::ExceptKey], val: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        use tlx_layout::FcnWitness as W;
        let Ty::Enc(msid) = m.ty else { return None };
        let (key, range, witness) = self.map_info(m.ty)?;
        if !typed::shapes_comparable(&key, &key) {
            return None;
        }
        if let ExprKind::Const(v) = &*k.kind {
            if tlx_layout::layout::rank_semantic(&key, v).is_err() {
                if !v.normalize().is_ok_and(|n| typed::comparable(&key, &n)) {
                    return None;
                }
                // Key is comparable with the key universe and statically absent:
                // value expression is never evaluated.
                let mty = m.ty;
                let fail = || Expr::new(mty, ExprKind::Fail("Attempted to access tuple at a non integral index".into()));
                return Some(match witness {
                    W::Enumerated => m,
                    W::Interval => {
                        if matches!(v, Value::Int(_)) {
                            m
                        } else {
                            fail()
                        }
                    }
                    W::Dynamic => {
                        let admit_empty = tlx_value::plan::Witness::Tuple.key_type().admits(v);
                        let admit_nonempty = crate::types::map_canonical_witness(&key).key_type().admits(v);
                        if admit_empty && admit_nonempty {
                            m
                        } else {
                            let w_off = self.words(msid) as usize - 1;
                            let w_word = self.int_word(m.clone(), w_off, 1);
                            let is_enum = eq(w_word, int_lit(1));
                            let ok = if !admit_empty && !admit_nonempty {
                                is_enum
                            } else {
                                let dom = self.map_domain(m.clone(), &key);
                                let dsid = self.sid(&map_domain_shape(&key));
                                let non_empty = not(eq(dom, self.zero_enc(dsid)));
                                or(vec![is_enum, non_empty])
                            };
                            Expr::new(mty, ExprKind::If(ok, m, fail()))
                        }
                    }
                });
            }
        } else if let Some(ks) = self.shape_of(k.ty) {
            if !typed::shapes_comparable(&key, ks) {
                return None;
            }
        }
        let rank = self.map_key_rank(&key, k, true)?;
        let (rank, bind) = self.share(rank);
        let old = self.map_get(m.clone(), rank.clone(), &range);
        let v = self.except_path(old, &keys[1..], val, env, st)?;
        let ty = m.ty;
        let plan = self.typing.map_put_plan(ty, Absent::Unchanged, None);
        Some(let_in(bind, Expr::new(ty, ExprKind::MapPut { base: m, rank, value: v, plan })))
    }

    /// `[x \in S |-> body]` into map shape `sid`: `S` is any set that can
    /// be iterated with typed elements (typically built from `DOMAIN`s).
    pub(super) fn map_build_into(&mut self, bounds: &[hir::Bound], body: &hir::Expr, env: &LEnv, st: &St, sid: ShapeId) -> Option<Expr> {
        use tlx_layout::FcnWitness as W;
        let (key, range, map_w) = self.map_info(Ty::Enc(sid))?;
        let [b] = bounds else { return None };
        if !binders::single_binder(b) {
            return None;
        }
        let dw = self.domain_witness(&b.set, env, st)?;
        let witness = match (map_w, dw) {
            (W::Enumerated, W::Enumerated) | (W::Interval, W::Interval) => None,
            (W::Dynamic, _) => Some(u64::from(dw == W::Enumerated)),
            _ => return None,
        };
        let s = if self.constructs(&b.set, env) {
            let dsid = self.sid(&map_domain_shape(&key));
            self.expr_into(&b.set, env, st, dsid)
        } else {
            self.expr(&b.set, env, st)
        };
        // The order only matters for errors, which the interpreter reports.
        let (src, ety) = self.typed_iter_in(s, true);
        if !src.is_typed_source() {
            return None;
        }
        let t = self.temp(ety);
        let x = temp_ref(ety, t);
        let rank = self.map_key_rank(&key, x.clone(), false)?;
        let (env2, check) = self.bind_elem(&b.vars, &x, env)?;
        let rsid = self.sid(&range);
        let v = self.expr_into(body, &env2, st, rsid);
        let value = binders::checked(check, self.coerce_enc(v, rsid));
        Some(Expr::new(Ty::Enc(sid), ExprKind::MapBuild { bind: t, set: src, rank, value, witness }))
    }

    /// `DOMAIN s` of an expression `s` of sequence shape: the domain is the
    /// index range `1..Len(s)`, so its length is `Len(s)`. A sequence-shaped
    /// `[i \in DOMAIN s |-> body]` can then be built slot by slot
    /// (`construct::seq_fcn_into`, which takes this through `seq_domain_len`)
    /// instead of as a map over `s`'s key universe converted back to the
    /// sequence shape — that conversion is a host region.
    ///
    /// `Some(Len(s))` for `DOMAIN s` over a sequence (a boxed source has no
    /// shape and takes the other paths), `None` otherwise: the caller keeps
    /// the domain forms it already handles. Deciding needs `s` lowered,
    /// which has effects, so a decline leaves the frame exactly as it was
    /// (as `typed_sort_seq` does).
    pub(super) fn seq_domain_len_of_seq(&mut self, set: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        if self.ip.is_builtin_overridden(B::Domain) {
            return None;
        }
        let (p, penv) = self.peel(set, env)?;
        let H::Builtin { op: B::Domain, args } = &*p.kind else { return None };
        let [x] = &args[..] else { return None };
        let mark = self.frame.snapshot();
        let s = self.expr(x, &penv, st);
        if !matches!(self.shape_of(s.ty), Some(Shape::Seq { .. })) {
            self.frame.restore(mark);
            return None;
        }
        Some(Expr::new(Ty::Int, ExprKind::SeqLen(s)))
    }

    /// `base` with key `k` mapped to `v` (inserted if absent), for map
    /// shape `sid` (from `:>` / `@@`, so the result always has an enumerated witness).
    fn map_insert(&mut self, base: Expr, k: &hir::Expr, v: &hir::Expr, env: &LEnv, st: &St, sid: ShapeId) -> Option<Expr> {
        let (key, range, witness) = self.map_info(Ty::Enc(sid))?;
        if witness == tlx_layout::FcnWitness::Interval {
            return None;
        }
        let rank = self.map_key_rank_hir(&key, k, env, st, false)?;
        let rsid = self.sid(&range);
        let value = self.expr_into(v, env, st, rsid);
        let value = self.coerce_enc(value, rsid);
        let insert_witness = (witness == tlx_layout::FcnWitness::Dynamic).then_some(1);
        let plan = self.typing.map_put_plan(Ty::Enc(sid), Absent::Insert, insert_witness);
        Some(Expr::new(Ty::Enc(sid), ExprKind::MapPut { base, rank, value, plan }))
    }

    /// `k :> v` into map shape `sid`.
    pub(super) fn map_single_into(&mut self, k: &hir::Expr, v: &hir::Expr, env: &LEnv, st: &St, sid: ShapeId) -> Option<Expr> {
        let (_, _, witness) = self.map_info(Ty::Enc(sid))?;
        if witness == tlx_layout::FcnWitness::Interval {
            return None;
        }
        let empty = self.zero_enc(sid);
        self.map_insert(empty, k, v, env, st, sid)
    }

    /// `f @@ g` into map shape `sid` (`(k :> v) @@ g` inserts into `g`).
    pub(super) fn map_merge_into(&mut self, f: &hir::Expr, g: &hir::Expr, env: &LEnv, st: &St, sid: ShapeId) -> Option<Expr> {
        let (_, _, witness) = self.map_info(Ty::Enc(sid))?;
        if witness == tlx_layout::FcnWitness::Interval {
            return None;
        }
        if let Some((p, penv)) = self.peel(f, env) {
            if let H::Builtin { op: B::ColonGt, args } = &*p.kind {
                if !self.ip.is_builtin_overridden(B::ColonGt) {
                    let base = self.expr_into(g, env, st, sid);
                    return self.map_insert(base, &args[0], &args[1], &penv, st, sid);
                }
            }
        }
        let a = self.expr_into(f, env, st, sid);
        let b = self.expr_into(g, env, st, sid);
        Some(Expr::new(Ty::Enc(sid), ExprKind::MapMerge(a, b)))
    }

    /// An encoded function of another shape (a map over another key
    /// universe, or a fixed-domain function, tuple or record) converted to
    /// map shape `sid`; `None` if not possible statically.
    pub(super) fn map_coerce(&mut self, x: &Expr, sid: ShapeId) -> Option<Expr> {
        use tlx_layout::FcnWitness as W;
        let (key, range, dst_w) = self.map_info(Ty::Enc(sid))?;
        let src = self.shape_of(x.ty)?.clone();
        if !matches!(src, Shape::Map { .. } | Shape::Fcn { .. } | Shape::Tuple(_) | Shape::Record(_)) {
            return None;
        }
        let rsid = self.sid(&range);
        let (xs, bind) = self.share(x.clone());
        let out = if let Shape::Map { key: k2, range: r2, witness: src_w } = &src {
            let build_w = match (dst_w, src_w) {
                (W::Enumerated, W::Enumerated) | (W::Interval, W::Interval) => None,
                (W::Dynamic, W::Enumerated) => Some(1),
                (W::Dynamic, W::Interval) => Some(0),
                _ => return None,
            };
            // Entry by entry over the source's domain.
            let dom = self.map_domain(xs.clone(), k2);
            let (it, ety) = self.typed_iter_in(dom, true);
            if !it.is_typed_source() {
                return None;
            }
            let t = self.temp(ety);
            let e = temp_ref(ety, t);
            let from = self.map_key_rank(k2, e.clone(), false)?;
            let to = self.map_key_rank(&key, e, false)?;
            let v = self.map_get(xs, from, r2);
            let value = self.coerce_enc(v, rsid);
            Expr::new(Ty::Enc(sid), ExprKind::MapBuild { bind: t, set: it, rank: to, value, witness: build_w })
        } else {
            let insert_w: Option<u64> = match (&src, dst_w) {
                (Shape::Tuple(_), W::Interval) => None,
                (Shape::Tuple(_) | Shape::Record(_), W::Dynamic) => Some(0),
                (Shape::Fcn { witness: W::Enumerated, key_variants, .. }, W::Enumerated) if key_variants.is_empty() => None,
                (Shape::Fcn { witness: W::Interval, key_variants, .. }, W::Interval) if key_variants.is_empty() => None,
                (Shape::Fcn { witness: W::Enumerated, key_variants, .. }, W::Dynamic) if key_variants.is_empty() => Some(1),
                (Shape::Fcn { witness: W::Interval, key_variants, .. }, W::Dynamic) if key_variants.is_empty() => Some(0),
                _ => return None,
            };
            let slots = self.slots(&src)?;
            if slots.len() > MAX_COERCED_ENTRIES {
                return None;
            }
            let mut acc = if insert_w == Some(1) {
                let mut words = vec![0u64; self.words(sid) as usize];
                *words.last_mut().unwrap() = 1;
                Expr::new(Ty::Enc(sid), ExprKind::ConstWords(words.into()))
            } else {
                self.zero_enc(sid)
            };
            for (k, loc, sh) in slots {
                // A key outside the universe: the value never fits.
                let r = tlx_layout::layout::rank(&key, &k).ok()?;
                let ssid = self.sid(&sh);
                let slot = Expr::new(Ty::Enc(ssid), ExprKind::Slice { base: xs.clone(), loc });
                let value = self.coerce_enc(slot, rsid);
                let plan = self.typing.map_put_plan(Ty::Enc(sid), Absent::Insert, insert_w);
                acc = Expr::new(Ty::Enc(sid), ExprKind::MapPut { base: acc, rank: int_lit(r as i64), value, plan });
            }
            acc
        };
        Some(let_in(bind, out))
    }

    /// `x \in [dom -> range]` for a constant function set and an encoded
    /// map `x` (shape `shape`): the presence bitset is `dom`'s, and every
    /// slot is in `range`.
    pub(super) fn map_in_fcn_set(&mut self, x: &Expr, shape: &Shape, dom: &Value, range: &Value, depth: usize) -> Option<Expr> {
        let Shape::Map { key, range: rs, .. } = shape else { return None };
        let dims = map_dims(shape)?;
        let bw = dims.bitset_words;
        let ds = tlx_value::ops::enumerate_normalized(dom).ok()?;
        if ds.len() > MAX_COERCED_ENTRIES {
            return None;
        }
        if !ds.iter().all(|d| typed::comparable(key, d)) {
            return None;
        }
        let mut mask = vec![0u64; bw];
        let mut ranks = Vec::new();
        for d in &ds {
            // A domain element outside the universe is never in DOMAIN x.
            let Ok(r) = tlx_layout::layout::rank_semantic(key, d) else { return Some(bool_lit(false)) };
            mask[(r / 64) as usize] |= 1 << (r % 64);
            ranks.push(r as usize);
        }
        let dsid = self.sid(&map_domain_shape(key));
        let dom_x = self.map_domain(x.clone(), key);
        let mut parts = vec![eq(dom_x, Expr::new(Ty::Enc(dsid), ExprKind::ConstWords(mask.into())))];
        let rsid = self.sid(rs);
        for r in ranks {
            let slot = Expr::new(Ty::Enc(rsid), ExprKind::Slice { base: x.clone(), loc: dims.slot_loc(r) });
            parts.push(self.member_any(&slot, rsid, range, depth + 1)?);
        }
        Some(and_all(parts))
    }

    /// `x \in [d -> r]` (HIR function set with computed parts) for an
    /// encoded map `x`: `DOMAIN x = d /\ \A k \in DOMAIN x : x[k] \in r`.
    pub(super) fn map_in_fn_set_hir(&mut self, x: Expr, d: &hir::Expr, r: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let (key, range) = self.map_parts(x.ty)?;
        let dsid = self.sid(&map_domain_shape(&key));
        let dl = self.expr_into(d, env, st, dsid);
        let (xs, bx) = self.share(x);
        let dom_x = self.map_domain(xs.clone(), &key);
        let same_dom = to_bool(self.typed_eq(dl, dom_x.clone()));
        let (it, ety) = self.typed_iter_in(dom_x, true);
        if !it.is_typed_source() {
            return None;
        }
        let t = self.temp(ety);
        let rank = self.map_key_rank(&key, temp_ref(ety, t), true)?;
        let slot = self.map_get(xs, rank, &range);
        // The range is evaluated for every key (it may not depend on it).
        let m = to_bool(self.member_of(slot, r, env, st));
        let all = Expr::new(Ty::Bool, ExprKind::Forall { bind: t, set: it, body: m });
        Some(let_in(bx, and(vec![same_dom, all])))
    }

    // ------------------------------------------------------------------
    // SortSeq

    /// `SortSeq(seq, Op)` over an encoded sequence with a comparator that
    /// lowers to native code, as two compiled functions of `Typing::funcs`:
    /// the insertion sort of `tlx-eval`'s `sort_seq` — the prefix is built
    /// left to right and each element bubbles left while `Op(elem, left)`
    /// holds, so the result is stable and the comparator's errors and the
    /// order it is applied in are the interpreter's. None when the source is
    /// not an encoded sequence or the comparator cannot be compiled (the
    /// caller then falls back to the interpreter).
    pub(super) fn typed_sort_seq(&mut self, seq: &hir::Expr, cmp: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        if self.ip.is_builtin_overridden(B::SortSeq) {
            return None;
        }
        // Deciding needs the source lowered, which has effects (it may
        // materialize definitions of the enclosing predicate); a decline
        // must leave the frame exactly as it was, or the caller's fallback
        // would keep a half-lowered subexpression nobody reads.
        let mark = self.frame.snapshot();
        let out = self.sort_seq_attempt(seq, cmp, env, st);
        if out.is_none() {
            self.frame.restore(mark);
        }
        out
    }

    fn sort_seq_attempt(&mut self, seq: &hir::Expr, cmp: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let src = self.sort_source(seq, env, st)?;
        let Ty::Enc(seq_sid) = src.ty else { return None };
        let Shape::Seq { elem, max_len } = self.shape_of(Ty::Enc(seq_sid))?.clone() else { return None };
        if max_len == 0 || max_len > SORT_MAX_LEN {
            return None;
        }
        let esid = self.sid(&elem);
        let slot = SlotLayout::of(&elem);
        let (params, body, lenv) = self.sort_comparator(cmp, env)?;
        if !self.sort_no_captures(&body, &params, &lenv) {
            return None;
        }
        let sort_idx = self.build_sort_fns(seq_sid, esid, slot, max_len as u32, &params, &body, &lenv, st)?;
        let (src, bind) = self.share(src);
        let n = Expr::new(Ty::Int, ExprKind::SeqLen(src.clone()));
        let out = Expr::new(Ty::Enc(seq_sid), ExprKind::Call { func: sort_idx, args: vec![src, n] });
        Some(let_in(bind, out))
    }

    /// The sequence `SortSeq` sorts: an encoded sequence, or the `SetToSeq`
    /// of an encoded set (the interpreter builtin `enumerate_normalized`
    /// spells out).
    fn sort_source(&mut self, e: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        if let H::Builtin { op: B::SetToSeq, args } = &*e.kind {
            if !self.ip.is_builtin_overridden(B::SetToSeq) {
                if let Some(x) = self.set_to_seq(&args[0], env, st) {
                    return Some(x);
                }
            }
        }
        let x = self.expr(e, env, st);
        matches!(self.shape_of(x.ty), Some(Shape::Seq { .. })).then_some(x)
    }

    /// `SetToSeq(S)` for a set that iterates as encoded elements in TLC
    /// order: `Collect` over the set's iteration source, the sequence the
    /// interpreter's builtin returns.
    fn set_to_seq(&mut self, s: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let x = self.expr(s, env, st);
        let (src, ety) = self.typed_iter_in(x, false);
        let Ty::Enc(esid) = ety else { return None };
        if !src.is_typed_source() {
            return None;
        }
        let cap = self.iter_bound(&src)?;
        if cap == 0 || cap > SET_TO_SEQ_MAX_CARD {
            return None;
        }
        let elem = self.shape_of(ety)?.clone();
        let sid = self.sid(&Shape::Seq { elem: Box::new(elem), max_len: cap });
        let t = self.temp(Ty::Enc(esid));
        Some(Expr::new(Ty::Enc(sid), ExprKind::Collect { bind: t, set: src, elem: temp_ref(Ty::Enc(esid), t) }))
    }

    /// The comparator of a `SortSeq`: its two parameters, its body and the
    /// environment it is lowered in. A lambda, or an operator whose body is
    /// inlined (not recursive, not action-level: those are not expressions
    /// of a compiled function).
    fn sort_comparator(&self, cmp: &hir::Expr, env: &LEnv) -> Option<(Arc<[LocalId]>, hir::Expr, LEnv)> {
        let (params, body, lenv) = if let H::Lambda { params, body } = &*cmp.kind {
            let [p0, p1] = params[..] else { return None };
            (vec![p0, p1].into(), body.clone(), env.clone())
        } else {
            let H::OpArg(r) = &*cmp.kind else { return None };
            let r = match r {
                OpRef::Param(l) => match env.lookup(*l, &self.ip.prog)? {
                    LBind::Op(LOp::Lambda(ps, b, lenv)) => {
                        let [_, _] = &ps[..] else { return None };
                        if matches!(&*b.kind, H::Num(_) | H::Str(_)) {
                            return None;
                        }
                        return Some((ps, b, lenv));
                    }
                    LBind::Op(LOp::Ref(r)) => r,
                    // A call-by-name argument would be evaluated in the frame of
                    // the caller's function.
                    _ => return None,
                },
                r => *r,
            };
            let OpRef::Def(d) = r else { return None };
            if self.ip.is_action_level(d) || self.is_recursive_def(d) {
                return None;
            }
            let d = self.ip.redirect_def(d);
            let def = &self.ip.prog.defs[d.idx()];
            if def.builtin.is_some() {
                return None;
            }
            let DefKind::Op(body) = &def.kind else { return None };
            let [p0, p1] = def.params[..] else { return None };
            (vec![p0, p1].into(), body.clone(), self.def_env(d, env))
        };
        if matches!(&*body.kind, H::Num(_) | H::Str(_)) {
            return None;
        }
        Some((params, body, lenv))
    }

    /// The comparator captures nothing: its free locals are its own
    /// parameters (or constants). A captured local's value lives in the
    /// caller's frame, whose temps a compiled function cannot read, and a
    /// captured operator would have to be inlined into it.
    fn sort_no_captures(&self, body: &hir::Expr, params: &[LocalId], lenv: &LEnv) -> bool {
        let mut used = Vec::new();
        self.free_locals(body, &mut used, &mut Vec::new());
        used.iter().all(|l| {
            if params.contains(l) {
                return true;
            }
            match lenv.lookup(*l, &self.ip.prog) {
                // Bound inside the body.
                None => true,
                // A constant: it reads no frame.
                Some(LBind::Ir(x)) => free_temps(&x).is_empty(),
                _ => false,
            }
        })
    }

    /// `<<v>>` in the sequence encoding `sid`.
    fn sort_singleton(&self, sid: ShapeId, slot: SlotLayout, cap: u32, v: Expr) -> Expr {
        Expr::new(Ty::Enc(sid), ExprKind::SeqAppend { base: self.zero_enc(sid), value: v, slot, max_len: cap })
    }

    /// Register the two functions a native `SortSeq` runs — `SortSeq.insert`
    /// (`insert(p, e)`: `p` with `e` inserted, both in the sequence encoding
    /// `seq_sid`) and `SortSeq.sort` (`sort(s, n)`: s[1..n] sorted) — and
    /// return the index of the second.
    #[allow(clippy::too_many_arguments)]
    fn build_sort_fns(
        &mut self,
        seq_sid: ShapeId,
        esid: ShapeId,
        slot: SlotLayout,
        cap: u32,
        params: &[LocalId],
        body: &hir::Expr,
        lenv: &LEnv,
        st: &St,
    ) -> Option<u32> {
        let (s_ty, e_ty) = (Ty::Enc(seq_sid), Ty::Enc(esid));
        let primed = self.primed;
        let outer = self.frame.swap();
        // The comparator is evaluated in the calling context (its arguments
        // are the sequence's elements, read from the encoded source).
        self.primed = primed;

        // insert(p, e): IF len(p) = 0 THEN <<e>>
        //               ELSE IF Op(e, p[len]) THEN insert(p[1..len-1], e) \o <<p[len]>>
        //                    ELSE p \o <<e>>
        let p_t = self.temp(s_ty);
        let e_t = self.temp(e_ty);
        let p_ref = temp_ref(s_ty, p_t);
        let e_ref = temp_ref(e_ty, e_t);
        let len = Expr::new(Ty::Int, ExprKind::SeqLen(p_ref.clone()));
        let last = Expr::new(e_ty, ExprKind::SeqIndex { base: p_ref.clone(), arg: len.clone(), slot });
        let cenv = lenv.bind(params[0], LBind::Ir(e_ref.clone())).bind(params[1], LBind::Ir(last.clone()));
        let cond = self.bool_expr(body, &cenv, st);
        let typed_cond = cond.ty == Ty::Bool;
        let empty = Expr::new(Ty::Bool, ExprKind::Eq(len.clone(), int_lit(0)));
        let tail = Expr::new(
            s_ty,
            ExprKind::SeqSub {
                base: p_ref.clone(),
                lo: int_lit(1),
                hi: Expr::new(Ty::Int, ExprKind::IntBin(IntOp::Sub, len, int_lit(1))),
                slot,
            },
        );
        let rec = Expr::new(s_ty, ExprKind::Call { func: PENDING_INSERT, args: vec![tail, e_ref.clone()] });
        let recurse = Expr::new(s_ty, ExprKind::SeqConcat { a: rec, b: self.sort_singleton(seq_sid, slot, cap, last), slot, max_len: cap });
        let stop = Expr::new(
            s_ty,
            ExprKind::SeqConcat { a: p_ref, b: self.sort_singleton(seq_sid, slot, cap, e_ref.clone()), slot, max_len: cap },
        );
        let ins_body = Expr::new(
            s_ty,
            ExprKind::If(empty, self.sort_singleton(seq_sid, slot, cap, e_ref), Expr::new(s_ty, ExprKind::If(cond, recurse, stop))),
        );
        let ins_temps = std::mem::take(&mut self.frame.temps);
        let ins_ptemps = vec![p_t, e_t];

        // sort(s, n): IF n = 0 THEN <<>> ELSE insert(sort(s, n - 1), s[n])
        self.frame.swap();
        self.primed = primed;
        let s_t = self.temp(s_ty);
        let k_t = self.temp(Ty::Int);
        let s_ref = temp_ref(s_ty, s_t);
        let k_ref = temp_ref(Ty::Int, k_t);
        let done = Expr::new(Ty::Bool, ExprKind::Eq(k_ref.clone(), int_lit(0)));
        let prev = Expr::new(Ty::Int, ExprKind::IntBin(IntOp::Sub, k_ref.clone(), int_lit(1)));
        let sorted = Expr::new(s_ty, ExprKind::Call { func: PENDING_SORT, args: vec![s_ref.clone(), prev] });
        let kth = Expr::new(e_ty, ExprKind::SeqIndex { base: s_ref, arg: k_ref, slot });
        let step = Expr::new(s_ty, ExprKind::Call { func: PENDING_INSERT, args: vec![sorted, kth] });
        let sort_body = Expr::new(s_ty, ExprKind::If(done, self.zero_enc(seq_sid), step));
        let sort_temps = std::mem::take(&mut self.frame.temps);
        let sort_ptemps = vec![s_t, k_t];
        self.frame = outer;

        // Both bodies must be fully typed: a boxed node (a comparator the
        // typed lowering could not reach) or an interpreter fallback would
        // make the call a host region, slower than the interpreter alone.
        if !typed_cond || !sort_typed(&ins_body) || !sort_typed(&sort_body) {
            return None;
        }
        let ins_idx = self.typing.funcs.len() as u32;
        let sort_idx = ins_idx + 1;
        let (mut ins_body, mut sort_body) = (ins_body, sort_body);
        patch_sort_calls(&mut ins_body, ins_idx, sort_idx);
        patch_sort_calls(&mut sort_body, ins_idx, sort_idx);
        self.typing.funcs.push(FnDef {
            name: "SortSeq.insert".into(),
            params: ins_ptemps,
            temps: ins_temps,
            ret: s_ty,
            body: ins_body,
            budgeted: false,
        });
        self.typing.funcs.push(FnDef {
            name: "SortSeq.sort".into(),
            params: sort_ptemps,
            temps: sort_temps,
            ret: s_ty,
            body: sort_body,
            budgeted: false,
        });
        self.typing.funcs_changed();
        Some(sort_idx)
    }
}

/// Whether a built sort function runs entirely in native code.
fn sort_typed(e: &Expr) -> bool {
    let mut c = Coverage::default();
    c.expr(e);
    c.fully_typed()
}

/// Replace the pending callee placeholders of a sort function body.
fn patch_sort_calls(e: &mut Expr, insert: u32, sort: u32) {
    if let ExprKind::Call { func, .. } = &mut *e.kind {
        *func = match *func {
            PENDING_INSERT => insert,
            PENDING_SORT => sort,
            f => f,
        };
    }
    e.for_each_child_mut(&mut |c| patch_sort_calls(c, insert, sort));
}
