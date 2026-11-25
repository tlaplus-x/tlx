//! Tuple binders `<<x, y, ...>> \in S` (in quantifiers, CHOOSE, set
//! constructors, function constructors and function definitions): the
//! locals are bound to the components of a typed element. The interpreter
//! requires the element to be a tuple of the binder's length (else it is an
//! error); this is static for tuple encodings and a runtime check for
//! sequence encodings.

use tlx_sema::hir::{self, BoundVars};
use tlx_value::Value;

use super::*;

/// Error of a tuple binder bound to a value of another kind / length.
pub(super) const TUPLE_BINDER: &str = "A tuple binder was bound to a value that is not a tuple of its length.";

impl Lowerer<'_> {
    /// The components of the typed element `x` (trivial, e.g. a temp) for a
    /// tuple binder of `n` locals, and the check that `x` is a tuple of
    /// length `n` (None: statically true). None if `x` has no typed
    /// components.
    pub(super) fn tuple_parts(&mut self, n: usize, x: &Expr) -> Option<(Vec<Expr>, Option<Expr>)> {
        match self.shape_of(x.ty)?.clone() {
            Shape::Tuple(parts) if parts.len() == n => {
                let fl = FieldLayout::of_shapes(parts.iter());
                let mut out = Vec::with_capacity(n);
                for (p, &loc) in parts.iter().zip(fl.locs.iter()) {
                    let psid = self.sid(p);
                    out.push(Expr::new(Ty::Enc(psid), ExprKind::Slice { base: x.clone(), loc }));
                }
                Some((out, None))
            }
            Shape::Seq { elem, max_len } if max_len >= n && n > 0 => {
                let esid = self.sid(&elem);
                let slot = SlotLayout::of(&elem);
                let out = (1..=n as i64)
                    .map(|i| Expr::new(Ty::Enc(esid), ExprKind::SeqIndex { base: x.clone(), arg: int_lit(i), slot }))
                    .collect();
                let len = Expr::new(Ty::Int, ExprKind::SeqLen(x.clone()));
                Some((out, Some(eq(len, int_lit(n as i64)))))
            }
            _ => None,
        }
    }

    /// `env` with the locals of binder `vars` bound to element `x` (a
    /// single local, or the components of a tuple binder) and the check
    /// that a tuple binder fits `x` (None: statically true). None if a tuple
    /// binder cannot be bound to `x`'s representation.
    pub(super) fn bind_elem(&mut self, vars: &BoundVars, x: &Expr, env: &LEnv) -> Option<(LEnv, Option<Expr>)> {
        match vars {
            BoundVars::Many(ls) => {
                let [l] = &ls[..] else { return None };
                Some((env.bind(*l, LBind::Ir(x.clone())), None))
            }
            BoundVars::Tuple(ls) => {
                let (parts, check) = self.tuple_parts(ls.len(), x)?;
                let env2 = ls.iter().zip(parts).fold(env.clone(), |e, (l, p)| e.bind(*l, LBind::Ir(p)));
                Some((env2, check))
            }
        }
    }
}

/// `env` with the locals of binder `vars` (a single local or a tuple
/// binder) bound to the constant `v` (None if a tuple binder does not fit
/// `v`: the interpreter reports the error).
pub(super) fn bind_const(vars: &BoundVars, v: &Value, env: &LEnv) -> Option<LEnv> {
    match vars {
        BoundVars::Many(ls) => {
            let [l] = &ls[..] else { return None };
            Some(env.bind(*l, LBind::Ir(const_expr(v.clone()))))
        }
        BoundVars::Tuple(ls) => {
            let Value::Tuple(parts) = v else { return None };
            if parts.len() != ls.len() {
                return None;
            }
            Some(ls.iter().zip(parts.iter()).fold(env.clone(), |e, (l, p)| e.bind(*l, LBind::Ir(const_expr(p.clone())))))
        }
    }
}

/// A bound with a single binder: one local or a tuple binder.
pub(super) fn single_binder(b: &hir::Bound) -> bool {
    match &b.vars {
        BoundVars::Many(ls) => ls.len() == 1,
        BoundVars::Tuple(_) => true,
    }
}

/// `body` if `check` (a tuple binder fits its element) holds, else a
/// runtime error.
pub(super) fn checked(check: Option<Expr>, body: Expr) -> Expr {
    match check {
        None => body,
        Some(c) => {
            let fail = Expr::new(body.ty, ExprKind::Fail(TUPLE_BINDER.into()));
            Expr::new(body.ty, ExprKind::If(c, body, fail))
        }
    }
}

/// Statement form of `checked`.
pub(super) fn checked_stmt(check: Option<Expr>, body: Stmt) -> Stmt {
    match check {
        None => body,
        Some(c) => if_stmt(c, body, Stmt::Error(TUPLE_BINDER.into())),
    }
}
