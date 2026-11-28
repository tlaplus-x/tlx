//! Lowering onto value store handles (`Shape::Ref` slots,
//! `TLX_VALUE_STORE`): the operations of the value contract whose principal
//! operand is a handle become `ExprKind::RefOp` nodes, which every executor
//! runs without the interpreter (docs/value-store.md §4). Arguments are
//! lowered as handles (`ref_expr`: constructors
//! built directly, other values converted), results converted back where
//! a consumer needs another representation (`as_int`, `coerce_enc`).
//! Everything else on handles keeps the boxed path (`Convert` to `Val`).

use std::sync::Arc;

use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{self, ExceptKey, ExprKind as H};
use tlx_value::{Sym, Value};

use super::*;
use crate::ir::RefOp;

impl Lowerer<'_> {
    /// Whether values of type `t` are value store handles.
    pub(super) fn is_ref(&self, t: Ty) -> bool {
        matches!(t, Ty::Enc(s) if Some(s) == self.typing.ref_sid())
    }

    fn handle_ty(&self) -> Ty {
        Ty::Enc(self.typing.ref_sid().expect("a value store shape"))
    }

    /// The node of `op` on `args` (its result type follows from `op`).
    pub(super) fn ref_op(&self, op: RefOp, args: Vec<Expr>) -> Expr {
        let ty = match &op {
            RefOp::Select | RefOp::Cardinality | RefOp::Len | RefOp::ToInt => Ty::Int,
            RefOp::Member | RefOp::InDomain | RefOp::Eq | RefOp::ToBool => Ty::Bool,
            RefOp::ToEnc(sid) => Ty::Enc(*sid),
            RefOp::DynEqInt | RefOp::DynEqBool | RefOp::DynToBool => Ty::Bool,
            RefOp::DynToInt => Ty::Int,
            _ => self.handle_ty(),
        };
        Expr::new(ty, ExprKind::RefOp { op, args })
    }

    /// `x` as a handle.
    pub(super) fn as_handle(&mut self, x: Expr) -> Expr {
        let h = self.handle_ty();
        if x.ty == h {
            return x;
        }
        if let ExprKind::Fail(m) = &*x.kind {
            return Expr::new(h, ExprKind::Fail(m.clone()));
        }
        if let ExprKind::Const(v) = &*x.kind {
            let Ty::Enc(sid) = h else { unreachable!() };
            if let Some(c) = self.const_words(v, sid) {
                return c;
            }
        }
        match x.ty {
            Ty::Int => self.ref_op(RefOp::FromInt, vec![x]),
            Ty::Bool => self.ref_op(RefOp::FromBool, vec![x]),
            Ty::Enc(sid) => match self.typing.shape(sid) {
                Shape::Int { .. } => {
                    let i = either(self.as_int(x));
                    self.ref_op(RefOp::FromInt, vec![i])
                }
                Shape::Bool => {
                    let b = either(self.as_bool(x));
                    self.ref_op(RefOp::FromBool, vec![b])
                }
                _ => self.ref_op(RefOp::FromEnc(sid), vec![x]),
            },
            // (Stored by the closure executor; native code evaluates the
            // conversion in a host region.)
            Ty::Val => Expr::new(h, ExprKind::Convert(x)),
        }
    }

    /// A handle `x` in the encoding of `sid` (integers and Booleans
    /// through their unboxed forms).
    pub(super) fn handle_into(&mut self, x: Expr, sid: ShapeId) -> Expr {
        match self.typing.shape(sid) {
            Shape::Int { .. } => Expr::new(Ty::Enc(sid), ExprKind::Convert(self.ref_op(RefOp::ToInt, vec![x]))),
            Shape::Bool => Expr::new(Ty::Enc(sid), ExprKind::Convert(self.ref_op(RefOp::ToBool, vec![x]))),
            _ => self.ref_op(RefOp::ToEnc(sid), vec![x]),
        }
    }

    /// `e` lowered as a handle: records, tuples, `:>` and `@@` (through
    /// operator calls and LETs) built directly in the store, other values
    /// lowered and converted.
    pub(super) fn ref_expr(&mut self, e: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        if self.const_value(e, env).is_none() {
            if let Some((p, penv)) = self.peel(e, env) {
                match &*p.kind {
                    H::Record(fs) if !fs.is_empty() => {
                        let names: Arc<[Sym]> = fs.iter().map(|(n, _)| Sym::new(n)).collect();
                        let args = fs.iter().map(|(_, x)| self.ref_expr(x, &penv, st)).collect();
                        return self.ref_op(RefOp::Record(names), args);
                    }
                    H::Tuple(es) => {
                        let args = es.iter().map(|x| self.ref_expr(x, &penv, st)).collect();
                        return self.ref_op(RefOp::Tuple, args);
                    }
                    H::Builtin { op: B::ColonGt, args } if !self.ip.is_builtin_overridden(B::ColonGt) => {
                        let k = self.ref_expr(&args[0], &penv, st);
                        let v = self.ref_expr(&args[1], &penv, st);
                        return self.ref_op(RefOp::Single, vec![k, v]);
                    }
                    H::Builtin { op: B::AtAt, args } if !self.ip.is_builtin_overridden(B::AtAt) => {
                        let f = self.ref_expr(&args[0], &penv, st);
                        let g = self.ref_expr(&args[1], &penv, st);
                        return self.ref_op(RefOp::Merge, vec![f, g]);
                    }
                    _ => {}
                }
            }
        }
        let x = self.expr(e, env, st);
        self.as_handle(x)
    }

    /// `[f EXCEPT !path1 = e1, ...]` for a handle `f`: the updates in
    /// order on the current function, each as the interpreter does it
    /// (`except::update` in tlx-eval): all keys of the path evaluated first, then
    /// selected one by one; a key outside the domain leaves the function
    /// unchanged without evaluating the replacement, a key the function
    /// rejects is an error; `@` is the old value.
    pub(super) fn ref_except(&mut self, f: Expr, updates: &[(Vec<ExceptKey>, hir::Expr)], env: &LEnv, st: &St) -> Expr {
        let mut binds = Vec::new();
        let (mut cur, b) = self.share(f);
        binds.extend(b);
        for (keys, val) in updates {
            let mut ks = Vec::with_capacity(keys.len());
            for k in keys {
                let x = match k {
                    ExceptKey::Field(name) => self.as_handle(val_lit(Value::Str(Sym::new(name)))),
                    ExceptKey::Index(ix) if ix.len() == 1 => self.ref_expr(&ix[0], env, st),
                    ExceptKey::Index(ix) => {
                        let args = ix.iter().map(|x| self.ref_expr(x, env, st)).collect();
                        self.ref_op(RefOp::Tuple, args)
                    }
                };
                let (x, b) = self.share(x);
                binds.extend(b);
                ks.push(x);
            }
            let next = self.ref_except_path(cur, &ks, val, env, st);
            let (n, b) = self.share(next);
            binds.extend(b);
            cur = n;
        }
        // (Bindings innermost first.)
        let_in(binds.into_iter().rev(), cur)
    }

    /// `[f EXCEPT ![k1]...[kn] = val]` with the keys evaluated (handles,
    /// shared) and `f` shared.
    fn ref_except_path(&mut self, f: Expr, keys: &[Expr], val: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        let i = self.ref_op(RefOp::Select, vec![f.clone(), keys[0].clone()]);
        let (i, bi) = self.share(i);
        // (Only where the key is present: the old value and the update.)
        let old = self.ref_op(RefOp::ValueAt, vec![f.clone(), i.clone()]);
        let set = if keys.len() == 1 {
            let saved = self.at.replace(old);
            let v = self.ref_expr(val, env, st);
            self.at = saved;
            self.ref_op(RefOp::SetAt, vec![f.clone(), i.clone(), v])
        } else {
            let (o, bo) = self.share(old);
            let inner = self.ref_except_path(o, &keys[1..], val, env, st);
            let set = self.ref_op(RefOp::SetAt, vec![f.clone(), i.clone(), inner]);
            let_in(bo, set)
        };
        let present = Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Ge, i, int_lit(0)));
        let h = self.handle_ty();
        let_in(bi, Expr::new(h, ExprKind::If(present, set, f)))
    }

    /// `x \in S` (`dom`: `S` is `DOMAIN f` with `f` the handle `s`) where
    /// the set or function is a handle.
    pub(super) fn ref_member(&mut self, x: &hir::Expr, s: Expr, dom: bool, env: &LEnv, st: &St) -> Expr {
        let k = self.ref_expr(x, env, st);
        self.ref_op(if dom { RefOp::InDomain } else { RefOp::Member }, vec![k, s])
    }
}
