//! CHOOSE over function sets: `CHOOSE f \in [1..n -> S] : IsInjective(f)`
//! (the usual `SetToSeq(S)`). TLC enumerates `[1..n -> S]` with the first
//! argument most significant and the elements of `S` in TLC order, so the
//! first injective function lists the `n` least elements of `S` in order
//! (none if `n` exceeds the size of `S`).

use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{self, BoundVars, DefKind, ExprKind as H, LocalId, OpRef, QuantKind};

use super::*;

const CHOOSE_NONE: &str = "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.";

impl Lowerer<'_> {
    /// `CHOOSE vars \in set : body` when it is a `SetToSeq`.
    pub(super) fn typed_choose_fn(&mut self, vars: &BoundVars, set: &hir::Expr, body: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let BoundVars::Many(ls) = vars else { return None };
        let [f] = &ls[..] else { return None };
        let (s, senv) = self.peel(set, env)?;
        let H::FnSet { domain, range } = &*s.kind else { return None };
        if !self.is_injectivity(body, *f, 0) {
            return None;
        }
        let n = self.seq_domain_len(domain, &senv, st)?;
        let r = self.expr(range, &senv, st);
        let (src, ety) = self.typed_iter_in(r, false);
        let Ty::Enc(esid) = ety else { return None };
        if !src.is_typed_source() {
            return None;
        }
        // (Not the set shape's maximal cardinality: only the bitsets of the
        // layout's shapes respect it, see `iter_bound`; a smaller buffer
        // made the evaluation fail and fall back to the interpreter.)
        let cap = self.iter_bound(&src)?;
        if cap > 64 {
            return None;
        }
        let elem = self.shape_of(ety)?.clone();
        let slot = SlotLayout::of(&elem);
        let sid = self.sid(&Shape::Seq { elem: Box::new(elem), max_len: cap });
        let t = self.temp(Ty::Enc(esid));
        let all = Expr::new(Ty::Enc(sid), ExprKind::Collect { bind: t, set: src, elem: temp_ref(Ty::Enc(esid), t) });
        let (n, bn) = self.share(n);
        let (all, ba) = self.share(all);
        let len = Expr::new(Ty::Int, ExprKind::SeqLen(all.clone()));
        let fits = Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Le, n.clone(), len));
        let prefix = Expr::new(Ty::Enc(sid), ExprKind::SeqSub { base: all, lo: int_lit(1), hi: n, slot });
        let fail = Expr::new(Ty::Enc(sid), ExprKind::Fail(CHOOSE_NONE.into()));
        Some(let_in(ba.into_iter().chain(bn), Expr::new(Ty::Enc(sid), ExprKind::If(fits, prefix, fail))))
    }

    /// Whether `e` is `\A a, b \in DOMAIN f : f[a] = f[b] => a = b` for the
    /// local `f` (also through an operator applied to `f`, like the
    /// Functions module's `IsInjective`).
    fn is_injectivity(&self, e: &hir::Expr, f: LocalId, depth: usize) -> bool {
        if depth > 4 {
            return false;
        }
        match &*e.kind {
            H::Apply { op: OpRef::Def(d), args } if args.len() == 1 && matches!(&*args[0].kind, H::Local(l) if *l == f) => {
                let d = self.ip.redirect_def(*d);
                let def = &self.ip.prog.defs[d.idx()];
                if def.builtin.is_some() || def.params.len() != 1 {
                    return false;
                }
                let DefKind::Op(body) = &def.kind else { return false };
                self.is_injectivity(body, def.params[0], depth + 1)
            }
            H::Quant { kind: QuantKind::Forall, bounds, body } => {
                let mut vars = Vec::new();
                for b in bounds {
                    let BoundVars::Many(ls) = &b.vars else { return false };
                    let H::Builtin { op: B::Domain, args } = &*b.set.kind else { return false };
                    if !matches!(&*args[0].kind, H::Local(l) if *l == f) {
                        return false;
                    }
                    vars.extend(ls.iter().copied());
                }
                let [a, b] = vars[..] else { return false };
                let H::Builtin { op: B::Implies, args } = &*body.kind else { return false };
                let app = |x: &hir::Expr| match &*x.kind {
                    H::FnApp { func, args } if args.len() == 1 && matches!(&*func.kind, H::Local(l) if *l == f) => match &*args[0].kind {
                        H::Local(v) => Some(*v),
                        _ => None,
                    },
                    _ => None,
                };
                let pair = |x: &hir::Expr| match &*x.kind {
                    H::Builtin { op: B::Eq, args } => Some((args[0].clone(), args[1].clone())),
                    _ => None,
                };
                let same = |p: (LocalId, LocalId)| p == (a, b) || p == (b, a);
                let Some((l, r)) = pair(&args[0]) else { return false };
                let Some((x, y)) = pair(&args[1]) else { return false };
                let lhs = matches!((app(&l), app(&r)), (Some(p), Some(q)) if same((p, q)));
                let rhs = matches!((&*x.kind, &*y.kind), (H::Local(p), H::Local(q)) if same((*p, *q)));
                lhs && rhs && !self.ip.is_builtin_overridden(B::Implies)
            }
            _ => false,
        }
    }

    /// `CHOOSE vars \in set : body` over an encoded set whose encoded
    /// order is not TLC's (records with sequence or set fields): the
    /// witness found in encoded order, if no other element satisfies
    /// `body` (then it is the one TLC finds, and TLC evaluates `body` on
    /// no element compiled code does not); several witnesses fail at run
    /// time (the interpreter takes over, choosing in TLC order).
    pub(super) fn verified_choose(&mut self, vars: &BoundVars, set: &Expr, body: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let (_, ety) = self.typed_iter_in(set.clone(), false);
        if ety != Ty::Val {
            return None;
        }
        let (_, ety) = self.typed_iter_in(set.clone(), true);
        if ety == Ty::Val {
            return None;
        }
        let (s, bs) = self.share(set.clone());
        let (src, ety) = self.typed_iter_in(s.clone(), true);
        let t = self.temp(ety);
        let (env2, check) = self.bind_elem(vars, &temp_ref(ety, t), env)?;
        let b = self.bool_expr(body, &env2, st);
        if b.ty != Ty::Bool {
            return None;
        }
        let w = Expr::new(ety, ExprKind::Choose { bind: t, set: src, body: binders::checked(check, b) });
        let (w, bw) = self.share(w);
        let (src2, _) = self.typed_iter_in(s, true);
        let u = self.temp(ety);
        let (env3, check) = self.bind_elem(vars, &temp_ref(ety, u), env)?;
        let b2 = self.bool_expr(body, &env3, st);
        let other = and(vec![not(eq(temp_ref(ety, u), w.clone())), binders::checked(check, b2)]);
        let several = Expr::new(Ty::Bool, ExprKind::Exists { bind: u, set: src2, body: other });
        let fail = Expr::new(ety, ExprKind::Fail("CHOOSE with several witnesses over a set not in TLC order".into()));
        Some(let_in(bw.into_iter().chain(bs), Expr::new(ety, ExprKind::If(several, fail, w))))
    }

    /// Whether `CHOOSE x \in set : body` has at most one witness whatever
    /// the order of `set`: `body` is `P(x) /\ \A y \in set : P(y) => y = x`
    /// (as in `ChooseOne(S, P)`), so the result does not depend on the
    /// order the elements are tried in. (Neither does an error: the
    /// witness evaluates `P` on every element, and without a witness every
    /// element is tried.)
    pub(super) fn unique_choice(&self, vars: &BoundVars, set: &hir::Expr, body: &hir::Expr) -> bool {
        let BoundVars::Many(ls) = vars else { return false };
        let [x] = ls[..] else { return false };
        let H::And(cs) = &*body.kind else { return false };
        let [p, all] = &cs[..] else { return false };
        let H::Quant { kind: QuantKind::Forall, bounds, body: q } = &*all.kind else { return false };
        let [hir::Bound { vars: BoundVars::Many(ys), set: set2 }] = &bounds[..] else { return false };
        let [y] = ys[..] else { return false };
        let H::Builtin { op: B::Implies, args } = &*q.kind else { return false };
        let H::Builtin { op: B::Eq, args: eq } = &*args[1].kind else { return false };
        let is = |e: &hir::Expr, l: LocalId| matches!(&*e.kind, H::Local(v) if *v == l);
        let eq_xy = (is(&eq[0], y) && is(&eq[1], x)) || (is(&eq[0], x) && is(&eq[1], y));
        !self.ip.is_builtin_overridden(B::Implies)
            && !self.ip.is_builtin_overridden(B::Eq)
            && eq_xy
            && same_hir(set, set2, None)
            && same_hir(p, &args[0], Some((x, y)))
    }
}

/// Structural equality of two expressions of a few simple kinds, where `a`
/// may use local `x` where `b` uses `y` (`rename`); false for anything else.
fn same_hir(a: &hir::Expr, b: &hir::Expr, rename: Option<(LocalId, LocalId)>) -> bool {
    let all = |xs: &[hir::Expr], ys: &[hir::Expr]| xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| same_hir(x, y, rename));
    match (&*a.kind, &*b.kind) {
        (H::Local(l), H::Local(m)) => match rename {
            Some((x, y)) if *l == x || *m == y => *l == x && *m == y,
            _ => l == m,
        },
        (H::Var(v), H::Var(w)) => v == w,
        (H::Const(c), H::Const(d)) => c == d,
        (H::Num(n), H::Num(m)) => n == m,
        (H::Str(s), H::Str(t)) => s == t,
        (H::Bool(p), H::Bool(q)) => p == q,
        (H::Apply { op, args }, H::Apply { op: op2, args: args2 }) => op == op2 && all(args, args2),
        (H::Builtin { op, args }, H::Builtin { op: op2, args: args2 }) => op == op2 && all(args, args2),
        (H::FnApp { func, args }, H::FnApp { func: f2, args: args2 }) => same_hir(func, f2, rename) && all(args, args2),
        (H::Tuple(xs), H::Tuple(ys)) | (H::And(xs), H::And(ys)) | (H::Or(xs), H::Or(ys)) | (H::SetEnum(xs), H::SetEnum(ys)) => all(xs, ys),
        (H::Field { record, field }, H::Field { record: r2, field: f2 }) => field == f2 && same_hir(record, r2, rename),
        _ => false,
    }
}
