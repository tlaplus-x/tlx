//! Set membership `x \in S`. In order of preference:
//! - structurally by the syntax of `S` without building it (`member_hir`);
//! - against a constant `S`, compiled by the structure of the set and of
//!   `x`'s encoding (`member_const`): slot-wise for function, record and
//!   product sets, comparisons for intervals, rank masks for enumerations
//!   of scalars;
//! - bitset or sorted-array lookup in an encoded `S`;
//! - the boxed builtin.

use tlx_layout::layout::bitset_universe;
use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{self, BoundVars, ExprKind as H};
use tlx_value::{LazySet, Value};

use super::sets::is_composite_bitset_elem;
use super::*;

impl Lowerer<'_> {
    /// `x \in set`.
    pub(super) fn typed_in(&mut self, x: &hir::Expr, set: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        match self.member_hir(x, env, set, env, st, 0) {
            Some(m) => m,
            None => {
                let set = self.extensional_set_expr(set, env, st);
                self.member(x, env, set, st)
            }
        }
    }

    /// `x \in set` with `set` already lowered.
    fn member(&mut self, x: &hir::Expr, env: &LEnv, set: Expr, st: &St) -> Expr {
        if self.is_ref(set.ty) {
            return self.ref_member(x, set, false, env, st);
        }
        let xl = self.expr(x, env, st);
        self.member_lowered(xl, Some(x), set, env, st)
    }

    /// Membership of a lowered `x` (whose source, if given, may be lowered
    /// again into the element encoding) in a lowered set.
    pub(super) fn member_lowered(&mut self, x: Expr, src: Option<&hir::Expr>, set: Expr, env: &LEnv, st: &St) -> Expr {
        // A constant set under bindings that are only evaluated for their
        // errors (`x \in DOMAIN f[k]`, see `typed_domain`): the bindings
        // around the membership in the constant.
        if matches!(&*set.kind, ExprKind::Let { .. }) {
            let mut binds = Vec::new();
            let mut body = set.clone();
            while let ExprKind::Let { temp, value, body: b } = &*body.kind {
                binds.push((*temp, value.clone()));
                body = b.clone();
            }
            if matches!(&*body.kind, ExprKind::Const(_)) {
                binds.reverse();
                let m = self.member_lowered(x, src, body, env, st);
                return let_in(binds, m);
            }
        }
        let set = self.set_operand(set);
        if !self.ip.is_builtin_overridden(B::Subset) {
            if let ExprKind::ValOp { op: B::Subset, args } = &*set.kind {
                let base = match &*args[0].kind {
                    ExprKind::Convert(inner) if args[0].ty == Ty::Val => inner.clone(),
                    _ => args[0].clone(),
                };
                if let Some(m) = self.native_bit_subset(&x, &base) {
                    return m;
                }
            }
        }
        // A constant outside the element shape of an encoded set is in no
        // value of it (e.g. `[type |-> "Prepared", vi |-> h]` for an `h` that
        // never occurs in that field), when TLC can compare it with every
        // element (otherwise the boxed membership reports the error).
        if let (ExprKind::Const(v), Some(Shape::Set { elem, .. })) = (&*x.kind, self.shape_of(set.ty)) {
            if let Ok(n) = v.normalize() {
                if !elem.contains_semantic(&n) && typed::shapes_comparable(&Shape::of(&n), elem) {
                    let (_, bind) = self.share(set);
                    return let_in(bind, bool_lit(false));
                }
            }
        }
        // The structural tests may decide by `x`'s shape alone (e.g. a
        // tuple of another length is in no product): `x` is evaluated
        // first all the same (see `after_eval`).
        // (Repeated: only an infallible slice of a variable or temp, not
        // a computed application.)
        let (xs, bind) = if self.cannot_fail(&x) && is_slice_path(&x) { (x.clone(), None) } else { self.share(x.clone()) };
        let typed = match (xs.ty, &*set.kind) {
            (Ty::Enc(sid), ExprKind::Const(v)) => self.member_const(&xs, sid, v, 0),
            (Ty::Int, ExprKind::Const(v)) => self.member_const_int(&xs, v),
            // x \in lo..hi with computed bounds.
            (_, ExprKind::ValOp { op: B::DotDot, args }) if !self.ip.is_builtin_overridden(B::DotDot) => {
                match (self.as_int(xs.clone()), self.as_int(args[0].clone()), self.as_int(args[1].clone())) {
                    (Ok(xi), Ok(lo), Ok(hi)) => Some(and(vec![
                        Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Ge, xi.clone(), lo)),
                        Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Le, xi, hi)),
                    ])),
                    _ => None,
                }
            }
            _ => None,
        };
        if let Some(m) = typed {
            return let_in(bind, m);
        }
        let x = match (src, self.shape_of(set.ty).cloned()) {
            (Some(e), Some(Shape::Set { elem, .. }))
                if bitset_universe(&elem).is_some() && !elem.is_scalar() && rankable(&elem) && self.constructs(e, env) =>
            {
                let esid = self.sid(&elem);
                if x.ty == Ty::Enc(esid) {
                    x
                } else {
                    self.expr_into(e, env, st, esid)
                }
            }
            _ => x,
        };
        // Check the original universe before recoding into a narrower one:
        // an absent but comparable atom is false, not a conversion failure.
        // Runtime tables preserve normalized-set binary-search errors too.
        if let Some(Shape::Set { elem, .. }) = self.shape_of(set.ty) {
            let xs = match x.ty {
                Ty::Enc(_) => self.shape_of(x.ty).cloned(),
                Ty::Int => Some(Shape::Int { lo: 0, hi: 0 }),
                Ty::Bool => Some(Shape::Bool),
                _ => None,
            };
            if xs.is_some_and(|xs| !typed::shapes_comparable(&xs, elem)) {
                return self.atom_bitset_member(&x, &set).unwrap_or_else(|| self.val_op(B::In, vec![x, set]));
            }
        }
        // An encoded element of another scalar(-ish) / arm encoding: bring it
        // into the set's element encoding.
        let x = match (x.ty, self.shape_of(set.ty).cloned()) {
            (Ty::Enc(xs), Some(Shape::Set { elem, .. })) => {
                let esid = self.sid(&elem);
                if xs != esid {
                    self.recode(&x, esid).or_else(|| self.union_arm_coerce(&x, esid)).unwrap_or(x)
                } else {
                    x
                }
            }
            _ => x,
        };
        if let Some(rank) = self.bit_rank(&set, &x, true) {
            return Expr::new(Ty::Bool, ExprKind::BitMember { set, rank });
        }
        match self.sorted_elem(set.ty) {
            Some((esid, ew, _)) => {
                let elem = match src {
                    Some(e) if x.ty != Ty::Enc(esid) && self.constructs(e, env) => self.expr_into(e, env, st, esid),
                    _ => self.coerce_enc(x, esid),
                };
                Expr::new(Ty::Bool, ExprKind::SortedMember { set, elem, elem_words: ew })
            }
            None => self.val_op(B::In, vec![x, set]),
        }
    }

    /// A small runtime atom set has finitely many masks. Evaluate membership
    /// on the entire normalized set: OR-ing element equalities would change
    /// binary-search error behavior. Bound the product before enumerating it.
    fn atom_bitset_member(&mut self, x: &Expr, set: &Expr) -> Option<Expr> {
        let Shape::Atom(atoms) = self.shape_of(x.ty)? else { return None };
        let Shape::Set { elem, max_card } = self.shape_of(set.ty)? else { return None };
        let Shape::Atom(elements) = &**elem else { return None };
        if elements.len() > 12 {
            return None;
        }
        let masks = 1usize << elements.len();
        let entries = atoms.len().checked_mul(masks)?;
        if entries == 0 || entries > 4096 {
            return None;
        }
        let sets: Vec<_> = (0..masks)
            .map(|mask| {
                if mask.count_ones() as usize > *max_card {
                    return None;
                }
                Value::set_from(elements.iter().enumerate().filter(|(i, _)| mask & (1 << i) != 0).map(|(_, a)| a.clone()).collect()).ok()
            })
            .collect();
        let table = atoms
            .iter()
            .flat_map(|a| sets.iter().map(move |s| s.as_ref().and_then(|s| tlx_value::ops::member(a, s).ok()).map_or(-1, i32::from)))
            .collect();
        let atom = Expr::new(Ty::Int, ExprKind::Rank(x.clone()));
        let mask = self.int_word(set.clone(), 0, masks as i64 - 1);
        let row = Expr::new(Ty::Int, ExprKind::IntBin(IntOp::Mul, atom, int_lit(masks as i64)));
        let index = Expr::new(Ty::Int, ExprKind::IntBin(IntOp::Add, row, mask));
        Some(self.truth_error_table(index, table))
    }

    /// Structural membership `x \in set` by the syntax of `set`, without
    /// building it: `F[a]` for a function constructor `F` (lazy, like TLC's
    /// FcnLambdaValue, with the domain check), and `{f(m) : m \in S}` as a
    /// filter over `S` (every `f(m)` is evaluated, as TLC builds the set).
    fn member_hir(&mut self, x: &hir::Expr, xenv: &LEnv, set: &hir::Expr, senv: &LEnv, st: &St, depth: usize) -> Option<Expr> {
        if depth > 8 {
            return None;
        }
        let (set, senv) = self.peel_call(set, senv)?;
        match &*set.kind {
            H::FnApp { func, args } if args.len() == 1 => {
                let (f, fenv) = self.peel(func, &senv)?;
                let H::FnConstruct { bounds, body } = &*f.kind else { return None };
                let [b] = &bounds[..] else { return None };
                let BoundVars::Many(vs) = &b.vars else { return None };
                let [v] = &vs[..] else { return None };
                let a = self.expr(&args[0], &senv, st);
                let t = self.temp(a.ty);
                let ta = temp_ref(a.ty, t);
                let dom = self.expr(&b.set, &fenv, st);
                let in_dom = self.member_lowered(ta.clone(), None, dom, &fenv, st);
                if in_dom.ty != Ty::Bool {
                    return None;
                }
                let benv = fenv.bind(*v, LBind::Ir(ta));
                let inner = match self.member_hir(x, xenv, body, &benv, st, depth + 1) {
                    Some(m) => m,
                    None => {
                        let s = self.expr(body, &benv, st);
                        self.member(x, xenv, s, st)
                    }
                };
                let fail = Expr::new(Ty::Bool, ExprKind::Fail("Attempted to apply function to an argument not in its domain.".into()));
                let checked = Expr::new(Ty::Bool, ExprKind::If(in_dom, to_bool(inner), fail));
                Some(let_in([(t, a)], checked))
            }
            H::Builtin { op: B::Subset, args } if args.len() == 1 => {
                // x \in SUBSET T <=> x \subseteq T.
                let xl = self.expr(x, xenv, st);
                self.subseteq_lowered(xl, &args[0], &senv, st)
            }
            H::SetEnum(es) if !es.is_empty() && es.len() <= 8 && self.const_value(&set, &senv).is_none() => {
                // x \in {a, b, ...} <=> x = a \/ x = b \/ ... (without building the set).
                let xl = self.expr(x, xenv, st);
                if xl.ty == Ty::Val {
                    return None;
                }
                let t = self.temp(xl.ty);
                let tx = temp_ref(xl.ty, t);
                let mut binds = vec![(t, xl)];
                let mut parts = Vec::with_capacity(es.len());
                for e in es {
                    // Construct every element before membership starts, but
                    // compare only until the first match (SetEnumValue).
                    let y = self.expr(e, &senv, st);
                    let (y, bind) = self.share(y);
                    binds.extend(bind);
                    parts.push(to_bool(self.typed_eq(y, tx.clone())));
                }
                Some(let_in(binds.into_iter().rev(), or(parts)))
            }
            H::FnSet { .. } | H::Builtin { op: B::Cup, .. } if self.const_value(&set, &senv).is_none() => {
                let xl = self.expr(x, xenv, st);
                if xl.ty == Ty::Val {
                    return None;
                }
                Some(self.member_of(xl, &set, &senv, st))
            }
            H::If { cond, then, els } => {
                // x \in (IF c THEN A ELSE B): membership in the chosen set.
                let xl = self.expr(x, xenv, st);
                if xl.ty == Ty::Val {
                    return None;
                }
                let t = self.temp(xl.ty);
                let tx = temp_ref(xl.ty, t);
                let c = self.bool_expr(cond, &senv, st);
                let a = to_bool(self.member_of(tx.clone(), then, &senv, st));
                let b = to_bool(self.member_of(tx, els, &senv, st));
                Some(let_in([(t, xl)], Expr::new(Ty::Bool, ExprKind::If(c, a, b))))
            }
            H::SetFilter { bound, pred } => {
                // x \in {y \in S : P} <=> x \in S /\ P[y := x] (in that order).
                if !binders::single_binder(bound) {
                    return None;
                }
                let xl = self.expr(x, xenv, st);
                if xl.ty == Ty::Val {
                    return None;
                }
                let t = self.temp(xl.ty);
                let tx = temp_ref(xl.ty, t);
                let base = self.expr(&bound.set, &senv, st);
                // TLC constructs `{y \in S : P}` eagerly only when `S` is
                // reducible (appending each kept element, so `-maxSetSize`
                // applies). A lazy source like `SUBSET T` stays `SetPredValue`
                // and never materializes for membership.
                let lazy_base = matches!(&*base.kind, ExprKind::ValOp { op: B::Subset, .. } | ExprKind::Subsets { .. })
                    || matches!(&*base.kind, ExprKind::Const(v) if !tlx_value::ops::is_reducible(v));
                if !lazy_base && self.iter_bound(&base).is_none_or(|n| n as i64 > tlx_value::limits::growth_limit()) {
                    return None;
                }
                let in_base = self.member_lowered(tx.clone(), None, base, &senv, st);
                let (penv, check) = self.bind_elem(&bound.vars, &tx, &senv)?;
                let p = binders::checked(check, self.bool_expr(pred, &penv, st));
                Some(let_in([(t, xl)], and(vec![to_bool(in_base), p])))
            }
            H::SetMap { expr: f, bounds } => {
                let [b] = &bounds[..] else { return None };
                if !binders::single_binder(b) {
                    return None;
                }
                let s = self.expr(&b.set, &senv, st);
                // A sequence domain is a runtime integer interval, not an
                // encoded set. Count matching images without materializing
                // the mapped tuples. Unlike EXISTS, a sum evaluates every
                // image, retaining errors after an earlier match.
                if !matches!(self.shape_of(s.ty), Some(Shape::Set { .. })) {
                    let (source, ety) = self.typed_iter(s);
                    let bound = self.iter_bound(&source)?;
                    // TLC's set former appends once per iteration before
                    // deduplication: answer membership directly only when the
                    // domain cannot exceed `-maxSetSize`.
                    if !matches!(&*source.kind, ExprKind::IntRange(..)) || bound > tlx_value::limits::growth_limit() as usize {
                        return None;
                    }
                    let t = self.iter_temp(ety, &source);
                    let (menv, check) = self.bind_elem(&b.vars, &temp_ref(ety, t), &senv)?;
                    // Building the mapped set also compares its images with
                    // each other. A query (e.g. an untyped model value) can
                    // compare with every image even when the images cannot
                    // be sorted together. Keep that normalization error.
                    if !self.mapped_images_comparable(f, &menv, st) {
                        return None;
                    }
                    let (mut binds, eq) = self.eq_after_eval(x, xenv, f, &menv, st);
                    let pred = binders::checked(check, to_bool(eq));
                    let body = Expr::new(Ty::Int, ExprKind::If(pred, int_lit(1), int_lit(0)));
                    let count = Expr::new(Ty::Int, ExprKind::Fold { product: false, bind: t, set: source, body });
                    binds.reverse();
                    return Some(let_in(binds, Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Gt, count, int_lit(0)))));
                }
                if self.iter_bound(&s).is_none_or(|n| n as i64 > tlx_value::limits::growth_limit()) {
                    return None;
                }
                let Some(Shape::Set { elem, .. }) = self.shape_of(s.ty).cloned() else { unreachable!() };
                if is_composite_bitset_elem(&elem) {
                    return None;
                }
                let sty = s.ty;
                let esid = self.sid(&elem);
                let t = self.temp(Ty::Enc(esid));
                let (menv, check) = self.bind_elem(&b.vars, &temp_ref(Ty::Enc(esid), t), &senv)?;
                if !self.mapped_images_comparable(f, &menv, st) {
                    return None;
                }
                // TLC evaluates `x` before it builds `{f : y \in S}`, so an
                // erroring `x` is reported even when S has no element to
                // compare with: the filter never runs the equality.
                let (mut binds, eq) = self.eq_after_eval(x, xenv, f, &menv, st);
                let pred = binders::checked(check, to_bool(eq));
                let filtered = Expr::new(sty, ExprKind::Filter { bind: t, set: s, pred });
                binds.reverse();
                Some(let_in(binds, self.nonempty(filtered)?))
            }
            _ => None,
        }
    }

    /// Membership of a lowered `x` in `set`, structurally for unions
    /// (`x \in A \/ x \in B`, both evaluated as TLC evaluates both sets)
    /// and function sets with a map `x`, else in the lowered set.
    pub(super) fn member_of(&mut self, x: Expr, set: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        if let Some((s, senv)) = self.peel(set, env) {
            match &*s.kind {
                H::FnSet { domain, range } if self.map_parts(x.ty).is_some() => {
                    if let Some(m) = self.map_in_fn_set_hir(x.clone(), domain, range, &senv, st) {
                        return m;
                    }
                }
                H::Builtin { op: B::Cup, args } if !self.ip.is_builtin_overridden(B::Cup) && x.ty != Ty::Val => {
                    if let Some(m) = self.member_cup(x.clone(), args, &senv, st) {
                        return m;
                    }
                }
                _ => {}
            }
        }
        let s = self.expr(set, env, st);
        self.member_lowered(x, None, s, env, st)
    }

    /// `x \in (A \cup B)` without building `A \cup B`, when both operands are
    /// reducible sets whose elements are pairwise comparable with each other
    /// and with `x` (so neither merging `A \cup B` nor testing `x \in A` and
    /// `x \in B` can raise a comparability/type error).
    fn member_cup(&mut self, x: Expr, args: &[hir::Expr], senv: &LEnv, st: &St) -> Option<Expr> {
        let [a, b] = args else { return None };
        let xs = match x.ty {
            Ty::Enc(_) => self.shape_of(x.ty)?.clone(),
            Ty::Int => Shape::Int { lo: 0, hi: 0 },
            Ty::Bool => Shape::Bool,
            Ty::Val => return None,
        };
        let mark = self.frame.snapshot();
        let (tx, bind) = self.share(x);
        let la = self.expr(a, senv, st);
        let lb = self.expr(b, senv, st);
        // TLC builds the union eagerly: it appends at most `|A| + |B|` elements,
        // so a sum that may exceed `-maxSetSize` must be reported by the
        // interpreter's checked union, not by testing the operands apart.
        let limit = tlx_value::limits::growth_limit();
        let within = match (self.iter_bound(&la), self.iter_bound(&lb)) {
            (Some(na), Some(nb)) => na as i64 + nb as i64 <= limit,
            _ => false,
        };
        if !within {
            self.frame.restore(mark);
            return None;
        }
        let Some((ea, eb)) = self.set_elem_shape(&la).zip(self.set_elem_shape(&lb)) else {
            self.frame.restore(mark);
            return None;
        };
        if !typed::shapes_comparable(&ea, &eb)
            || !typed::shapes_comparable(&ea, &ea)
            || !typed::shapes_comparable(&eb, &eb)
            || !typed::shapes_comparable(&xs, &ea)
            || !typed::shapes_comparable(&xs, &eb)
        {
            self.frame.restore(mark);
            return None;
        }
        let ma = to_bool(self.member_lowered(tx.clone(), None, la, senv, st));
        let mb = to_bool(self.member_lowered(tx, None, lb, senv, st));
        let ta = self.temp(Ty::Bool);
        let tb = self.temp(Ty::Bool);
        Some(let_in([(tb, mb), (ta, ma)].into_iter().chain(bind), or(vec![temp_ref(Ty::Bool, ta), temp_ref(Ty::Bool, tb)])))
    }

    /// `a = b` for expressions in different environments, with `a` evaluated
    /// first: the returned bindings (in evaluation order) evaluate `a` (each
    /// component for literal tuples of the same length on both sides, as TLC
    /// evaluates both tuples), and the comparison uses their temps.
    fn eq_after_eval(&mut self, a: &hir::Expr, aenv: &LEnv, b: &hir::Expr, benv: &LEnv, st: &St) -> (Vec<(Temp, Expr)>, Expr) {
        if let (H::Tuple(xs), H::Tuple(ys)) = (&*a.kind, &*b.kind) {
            if xs.len() == ys.len() && !xs.is_empty() {
                let mut binds = Vec::new();
                let mut parts = Vec::new();
                for (x, y) in xs.iter().zip(ys) {
                    let (bs, p) = self.eq_after_eval(x, aenv, y, benv, st);
                    binds.extend(bs);
                    parts.push(to_bool(p));
                }
                return (binds, self.strict_and(parts));
            }
        }
        let x = self.expr(a, aenv, st);
        let (tx, bind) = self.share(x);
        let y = self.expr_as(b, tx.ty, benv, st);
        (bind.into_iter().collect(), self.typed_eq(tx, y))
    }

    /// Images of a mapped sequence domain can be normalized without a
    /// cross-element type error. Tuple images are commonly constructed
    /// without an encoding (log index/term pairs), so inspect their fields.
    fn mapped_images_comparable(&mut self, e: &hir::Expr, env: &LEnv, st: &St) -> bool {
        if let H::Tuple(parts) = &*e.kind {
            return parts.iter().all(|p| self.mapped_images_comparable(p, env, st));
        }
        let x = self.expr(e, env, st);
        match x.ty {
            Ty::Int | Ty::Bool => true,
            Ty::Enc(sid) => typed::shapes_comparable(self.typing.shape(sid), self.typing.shape(sid)),
            Ty::Val => false,
        }
    }

    /// Membership of an unboxed integer in a constant set.
    fn member_const_int(&self, x: &Expr, set: &Value) -> Option<Expr> {
        match set {
            Value::Interval(lo, hi) => Some(and(vec![
                Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Ge, x.clone(), int_lit(*lo))),
                Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Le, x.clone(), int_lit(*hi))),
            ])),
            Value::LazySet(l) if matches!(**l, LazySet::Nat) => {
                Some(Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Ge, x.clone(), int_lit(0))))
            }
            Value::LazySet(l) if matches!(**l, LazySet::Int) => Some(bool_lit(true)),
            // E.g. `Nat \ {0}` (TLC tests both operands).
            Value::LazySet(l) => match &**l {
                LazySet::Diff(a, b) => Some(and(vec![self.member_const_int(x, a)?, not(self.member_const_int(x, b)?)])),
                LazySet::Cap(a, b) => Some(and(vec![self.member_const_int(x, a)?, self.member_const_int(x, b)?])),
                LazySet::Cup(a, b) => Some(or(vec![self.member_const_int(x, a)?, self.member_const_int(x, b)?])),
                _ => None,
            },
            // A few integers: comparisons.
            Value::Set(es) if es.len() <= 16 && es.iter().all(|e| matches!(e, Value::Int(_))) => {
                Some(or_any(es.iter().map(|e| eq(x.clone(), const_expr(e.clone()))).collect()))
            }
            _ => None,
        }
    }

    /// Membership of an encoded value (shape `sid`) in a constant set,
    /// compiled structurally: function/record/product sets check each slot,
    /// intervals compare, enumerated sets of scalars test a rank bitmask,
    /// `SUBSET T` tests a mask. `None` if not applicable.
    fn member_const(&mut self, x: &Expr, sid: ShapeId, set: &Value, depth: usize) -> Option<Expr> {
        if depth > 8 {
            return None;
        }
        // Structural tests and rank masks are cheaper than semantic tables.
        // In particular, total atom universes must retain their mask lowering.
        if let Some(m) = self.member_const_structural(x, sid, set, depth) {
            return Some(m);
        }
        let Shape::Atom(atoms) = self.typing.shape(sid) else { return None };
        if atoms.len() > 256 || set.enum_elements()?.len() > 256 {
            return None;
        }
        // Do not normalize a deferred enumeration: its element order decides
        // whether membership returns before a later incomparable element.
        let table = atoms.iter().map(|a| tlx_value::ops::member(a, set).map_or(-1, i32::from)).collect();
        Some(self.truth_error_table(x.clone(), table))
    }

    fn member_const_structural(&mut self, x: &Expr, sid: ShapeId, set: &Value, depth: usize) -> Option<Expr> {
        let shape = self.typing.shape(sid).clone();
        if let Shape::Union(arms) = &shape {
            if !matches!(set, Value::Set(_)) {
                return self.member_union(x, arms, set, depth);
            }
        }
        // An untyped model value is in no set of functions, records,
        // tuples, sequences or numbers (no error), e.g. the model-value arm
        // of a union in a set of records.
        if matches!(&shape, Shape::Atom(vs) if vs.iter().all(|v| matches!(v, Value::ModelValue(m) if m.model_value_type().is_none())))
            && matches!(set, Value::LazySet(l) if matches!(**l, LazySet::FcnSet(..) | LazySet::RecordSet(_) | LazySet::Product(_) | LazySet::Seq(_) | LazySet::Nat | LazySet::Int | LazySet::StringSet))
        {
            return Some(bool_lit(false));
        }
        match set {
            Value::LazySet(l) => match &**l {
                LazySet::Union(outer) => {
                    // UNION {S1, S2, ...}: in some Si.
                    let inner = tlx_value::ops::enumerate_normalized(outer).ok()?;
                    if inner.len() > 64 {
                        return None;
                    }
                    let parts = inner.iter().map(|s| self.member_any(x, sid, s, depth + 1)).collect::<Option<Vec<_>>>()?;
                    Some(or_any(parts.into_iter().filter(|p| !is_false(p)).collect()))
                }
                LazySet::FcnSet(dom, range) if matches!(shape, Shape::Seq { .. }) => {
                    // A sequence in [1..n -> R]: length n, elements in R.
                    let Shape::Seq { elem, max_len } = &shape else { unreachable!() };
                    let n = match dom {
                        Value::Interval(1, n) => *n,
                        Value::Interval(lo, hi) if hi < lo => 0,
                        _ => return None,
                    };
                    if n < 0 || n as usize > *max_len {
                        return Some(bool_lit(false));
                    }
                    let len_ok = eq(Expr::new(Ty::Int, ExprKind::SeqLen(x.clone())), int_lit(n));
                    let esid = self.sid(elem);
                    let slot = SlotLayout::of(elem);
                    let mut parts = vec![len_ok];
                    for i in 1..=n {
                        let xi = Expr::new(Ty::Enc(esid), ExprKind::SeqIndex { base: x.clone(), arg: int_lit(i), slot });
                        parts.push(self.member_any(&xi, esid, range, depth + 1)?);
                    }
                    Some(and_all(parts))
                }
                LazySet::Seq(t) => match &shape {
                    // \A i \in 1..Len(x) : x[i] \in T
                    Shape::Seq { elem, .. } => {
                        let esid = self.sid(elem);
                        let slot = SlotLayout::of(elem);
                        let i = self.temp(Ty::Int);
                        let len = Expr::new(Ty::Int, ExprKind::SeqLen(x.clone()));
                        let range = Expr::new(Ty::Val, ExprKind::IntRange(int_lit(1), len));
                        let xi = Expr::new(Ty::Enc(esid), ExprKind::SeqIndex { base: x.clone(), arg: temp_ref(Ty::Int, i), slot });
                        let body = self.member_any(&xi, esid, t, depth + 1)?;
                        Some(Expr::new(Ty::Bool, ExprKind::Forall { bind: i, set: range, body }))
                    }
                    Shape::Tuple(_) => {
                        let slots = self.slots(&shape)?;
                        let parts = slots.iter().map(|(_, off, sh)| self.slot_member(x, *off, sh, t, depth)).collect::<Option<_>>()?;
                        Some(and_all(parts))
                    }
                    _ => None,
                },
                LazySet::FcnSet(dom, range) if matches!(shape, Shape::Map { .. }) => self.map_in_fcn_set(x, &shape, dom, range, depth),
                LazySet::FcnSet(dom, range) => {
                    let slots = self.slots(&shape)?;
                    let actual_dom = match &shape {
                        Shape::Tuple(_) => Value::Interval(1, slots.len() as i64),
                        _ => Value::set_from(slots.iter().map(|(k, _, _)| k.clone()).collect()).ok()?,
                    };
                    let dom_ok = match &shape {
                        Shape::Tuple(_) => tlx_value::order::eq_tlc(&actual_dom, dom).ok()?,
                        _ => tlx_value::order::eq_tlc(dom, &actual_dom).ok()?,
                    };
                    if !dom_ok {
                        return Some(bool_lit(false));
                    }
                    let parts = slots.iter().map(|(_, off, sh)| self.slot_member(x, *off, sh, range, depth)).collect::<Option<_>>()?;
                    Some(and_all(parts))
                }
                LazySet::RecordSet(fields) => {
                    if let Shape::Tuple(es) = &shape {
                        return es.is_empty().then(|| bool_lit(fields.is_empty()));
                    }
                    if !matches!(shape, Shape::Record(_)) {
                        return None;
                    }
                    let slots = self.slots(&shape)?;
                    if slots.len() != fields.len() {
                        return Some(bool_lit(false));
                    }
                    let mut parts = Vec::new();
                    for ((k, off, sh), (name, fset)) in slots.iter().zip(fields.iter()) {
                        if *k != Value::Str(*name) {
                            return parts.is_empty().then(|| bool_lit(false));
                        }
                        parts.push(self.slot_member(x, *off, sh, fset, depth)?);
                    }
                    Some(and_all(parts))
                }
                LazySet::Product(sets) => {
                    if !matches!(shape, Shape::Tuple(_)) {
                        return None;
                    }
                    let slots = self.slots(&shape)?;
                    if slots.len() != sets.len() {
                        return Some(bool_lit(false));
                    }
                    let parts = slots
                        .iter()
                        .zip(sets.iter())
                        .map(|((_, off, sh), s)| self.slot_member(x, *off, sh, s, depth))
                        .collect::<Option<_>>()?;
                    Some(and_all(parts))
                }
                LazySet::Subset(t) => self.member_subset(x, sid, &shape, t, depth),
                LazySet::Nat | LazySet::Int => {
                    let xi = self.as_int(x.clone()).ok()?;
                    self.member_const_int(&xi, set)
                }
                LazySet::Cup(a, b) => {
                    // (A chain of unions does not count as nesting: it is as deep as
                    // the set value, which is finite.)
                    let (p, q) = (self.member_any(x, sid, a, depth)?, self.member_any(x, sid, b, depth)?);
                    Some(match (is_false(&p), is_false(&q)) {
                        (true, _) => q,
                        (_, true) => p,
                        _ => or(vec![p, q]),
                    })
                }
                LazySet::Cap(a, b) => {
                    let (p, q) = (self.member_any(x, sid, a, depth + 1)?, self.member_any(x, sid, b, depth + 1)?);
                    Some(and_all(vec![p, q]))
                }
                LazySet::Diff(a, b) => {
                    let (p, q) = (self.member_any(x, sid, a, depth + 1)?, self.member_any(x, sid, b, depth + 1)?);
                    Some(and_all(vec![p, not(q)]))
                }
                LazySet::StringSet => match &shape {
                    Shape::Atom(u) if u.iter().all(|a| matches!(a, Value::Str(_))) => Some(bool_lit(true)),
                    _ => None,
                },
                _ => None,
            },
            // Untyped model values are in no interval (no error).
            Value::Interval(..) if matches!(&shape, Shape::Atom(vs) if vs.iter().all(|v| matches!(v, Value::ModelValue(m) if m.model_value_type().is_none()))) => {
                Some(bool_lit(false))
            }
            Value::Interval(..) => {
                let xi = self.as_int(x.clone()).ok()?;
                self.member_const_int(&xi, set)
            }
            Value::Set(elems) => self.member_enum(x, sid, &shape, elems),
            _ => None,
        }
    }

    /// `member_const` for a slot of any scalar/encoded type.
    pub(super) fn member_any(&mut self, x: &Expr, sid: ShapeId, set: &Value, depth: usize) -> Option<Expr> {
        if let Some(Shape::Int { .. }) = self.shape_of(Ty::Enc(sid)) {
            if let Ok(xi) = self.as_int(x.clone()) {
                if let Some(m) = self.member_const_int(&xi, set) {
                    return Some(m);
                }
            }
        }
        self.member_const(x, sid, set, depth)
    }

    /// A union-encoded value: dispatch on the arm index (word 0); the
    /// arm's encoding follows.
    fn member_union(&mut self, x: &Expr, arms: &[Shape], set: &Value, depth: usize) -> Option<Expr> {
        let tag = self.int_word(x.clone(), 0, arms.len() as i64 - 1);
        let mut alts = Vec::new();
        for (i, arm) in arms.iter().enumerate() {
            let asid = self.sid(arm);
            let payload = Expr::new(Ty::Enc(asid), ExprKind::Slice { base: x.clone(), loc: FieldLoc::Words(1) });
            let m = self.member_any(&payload, asid, set, depth + 1)?;
            if is_false(&m) {
                continue;
            }
            alts.push(and_all(vec![eq(tag.clone(), int_lit(i as i64)), m]));
        }
        Some(or_any(alts))
    }

    /// Slots of an encoded function/tuple/record, as (key, location, slot shape).
    pub(super) fn slots(&mut self, shape: &Shape) -> Option<Vec<(Value, FieldLoc, Shape)>> {
        let fl = FieldLayout::of_shape(shape)?;
        let mut out = Vec::with_capacity(fl.locs.len());
        match shape {
            Shape::Fcn { dom, range, .. } => {
                self.sid(range);
                for (d, &loc) in dom.iter().zip(fl.locs.iter()) {
                    out.push((d.clone(), loc, (**range).clone()));
                }
            }
            Shape::Tuple(es) => {
                for (i, (e, &loc)) in es.iter().zip(fl.locs.iter()).enumerate() {
                    self.sid(e);
                    out.push((Value::Int(i as i64 + 1), loc, e.clone()));
                }
            }
            Shape::Record(fs) => {
                for ((n, f), &loc) in fs.iter().zip(fl.locs.iter()) {
                    self.sid(f);
                    out.push((Value::Str(*n), loc, f.clone()));
                }
            }
            _ => return None,
        }
        Some(out)
    }

    /// The slot of `x` at `loc` (of shape `sh`) is in `set`.
    fn slot_member(&mut self, x: &Expr, loc: FieldLoc, sh: &Shape, set: &Value, depth: usize) -> Option<Expr> {
        let ssid = self.sid(sh);
        let slot = Expr::new(Ty::Enc(ssid), ExprKind::Slice { base: x.clone(), loc });
        self.member_any(&slot, ssid, set, depth + 1)
    }

    /// `x \in SUBSET t` for a bitset `x`: no element outside `t`'s mask.
    fn member_subset(&mut self, x: &Expr, sid: ShapeId, shape: &Shape, t: &Value, depth: usize) -> Option<Expr> {
        let Shape::Set { elem, .. } = shape else { return None };
        let Some(n) = bitset_universe(elem) else {
            // Not a bitset: every element is in `t`.
            let (src, ety) = self.typed_iter_in(x.clone(), true);
            let Ty::Enc(esid) = ety else { return None };
            if !src.is_typed_source() {
                return None;
            }
            let e = self.temp(ety);
            let m = self.member_const(&temp_ref(ety, e), esid, t, depth + 1)?;
            return Some(Expr::new(Ty::Bool, ExprKind::Forall { bind: e, set: src, body: m }));
        };
        let mut mask = vec![0u64; self.words(sid) as usize];
        for r in 0..n {
            let v = tlx_layout::layout::unrank(elem, r);
            if tlx_value::ops::member(&v, t).ok()? {
                set_bit(&mut mask, r);
            }
        }
        let m = Expr::new(Ty::Enc(sid), ExprKind::ConstWords(mask.into()));
        let outside = Expr::new(Ty::Enc(sid), ExprKind::BitSetOp(SetOp::Diff, x.clone(), m));
        Some(eq(outside, self.zero_enc(sid)))
    }

    /// `x \in {e1, ..., en}`: a rank bitmask for scalars, comparisons with
    /// the encodings of a few composite elements.
    fn member_enum(&mut self, x: &Expr, sid: ShapeId, shape: &Shape, elems: &[Value]) -> Option<Expr> {
        // Elements outside the shape count as unequal: only if comparing
        // them with `x` is no TLC error.
        if !elems.iter().all(|e| typed::comparable(shape, e)) {
            return None;
        }
        if shape.is_scalar() {
            let n = shape.cardinality()?;
            if n > 1 << 16 {
                return None;
            }
            let mut mask = vec![0u64; n.div_ceil(64).max(1) as usize];
            for e in elems {
                if let Ok(r) = tlx_layout::layout::rank(shape, e) {
                    set_bit(&mut mask, r);
                }
            }
            let ssid = self.sid(&Shape::Set { elem: Box::new(shape.clone()), max_card: n as usize });
            if self.words(ssid) as usize != mask.len() {
                return None;
            }
            let m = Expr::new(Ty::Enc(ssid), ExprKind::ConstWords(mask.into()));
            return Some(Expr::new(Ty::Bool, ExprKind::BitMember { set: m, rank: Expr::new(Ty::Int, ExprKind::Rank(x.clone())) }));
        }
        if elems.len() <= 16 {
            let consts: Vec<Expr> = elems.iter().filter_map(|e| self.const_words_semantic(e, sid)).collect();
            let parts = consts.into_iter().map(|c| self.typed_eq(x.clone(), c)).collect();
            return Some(or_any(parts));
        }
        if shape.has_dynamic_witness() {
            return None;
        }
        // Many composite elements: binary search in a constant sorted array
        // of their encodings (elements that do not fit `shape` are never
        // equal to `x`).
        let ew = self.words(sid) as usize;
        let mut encs: Vec<Vec<u64>> = elems
            .iter()
            .filter_map(|e| {
                let mut w = vec![0u64; ew];
                tlx_layout::layout::encode_semantic(shape, &e.normalize().ok()?, &mut w).ok().map(|_| w)
            })
            .collect();
        encs.sort();
        encs.dedup();
        // A plain word array (the shape only gives its size: a set shape
        // over a small universe would be a bitset).
        let n = encs.len();
        let ssid = self.sid(&Shape::Seq { elem: Box::new(Shape::Int { lo: i64::MIN, hi: i64::MAX }), max_len: (n * ew).max(1) });
        let mut words = vec![n as u64];
        words.extend(encs.into_iter().flatten());
        words.resize(self.words(ssid) as usize, 0);
        let set = Expr::new(Ty::Enc(ssid), ExprKind::ConstWords(words.into()));
        Some(Expr::new(Ty::Bool, ExprKind::SortedMember { set, elem: x.clone(), elem_words: ew as u32 }))
    }
}

fn set_bit(mask: &mut [u64], r: u64) {
    mask[(r / 64) as usize] |= 1 << (r % 64);
}

/// A constant, variable or temp, or a fixed slice of one.
fn is_slice_path(x: &Expr) -> bool {
    match &*x.kind {
        ExprKind::Slice { base, .. } => is_slice_path(base),
        ExprKind::Const(_) | ExprKind::ConstWords(_) | ExprKind::Var(_) | ExprKind::NextVar(_) | ExprKind::Temp(_) => true,
        _ => false,
    }
}
