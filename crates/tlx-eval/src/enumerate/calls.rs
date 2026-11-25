//! Application of an operator: a definition, an operator constant or an
//! operator parameter, and the `Local` indirection of a call-by-name
//! binding (moved out of `enumerate.rs`). A user-defined operator is
//! expanded so that the assignments inside it are recognized; anything
//! else is a test.

use crate::env::{Binding, OpVal};

use super::*;

impl<'a> Enumerator<'a> {
    /// `F(args)` for an operator constant `F` the cfg replaced by a
    /// definition: expand the definition.
    pub(super) fn apply_const(&mut self, c: &ConstId, args: &[Expr], e: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        let ip: &'a Arc<Interp> = self.ip;
        // An operator constant replaced by a definition or builtin in the cfg
        // is expanded like that operator itself.
        match ip.const_op_ref(*c) {
            Some(OpRef::Def(d)) => self.go_call(d, args, e, env, k),
            Some(OpRef::Builtin(b)) => self.go_builtin(b, args, e, env, k),
            _ => self.test(e, env, k),
        }
    }

    /// `F(args)` for an operator parameter `F`: expand the operator it
    /// is bound to.
    pub(super) fn apply_param(&mut self, l: &LocalId, args: &[Expr], e: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        let ip: &'a Arc<Interp> = self.ip;
        match env.lookup(*l) {
            Some(Binding::Op(OpVal::Ref(OpRef::Def(d)))) => self.go_call(*d, args, e, env, k),
            Some(Binding::Op(OpVal::Ref(OpRef::Builtin(b)))) => self.go_builtin(*b, args, e, env, k),
            Some(Binding::Op(OpVal::Ref(OpRef::Const(c)))) => self.apply_const(c, args, e, env, k),
            Some(Binding::Op(OpVal::Lambda { params, body, env: lenv })) => {
                let env2 = ip.bind_params(params, args, env, &self.cx(), lenv.clone(), true, false)?;
                self.go(body, &env2, k)
            }
            _ => self.test(e, env, k),
        }
    }

    /// Enumerate builtin operator `op` applied to `args` (when reached through
    /// an operator parameter or constant override) so action builtins such as
    /// `\in`, `=`, `\subseteq`, `UNCHANGED`, `=>`, and `\cdot` keep their
    /// action-enumeration semantics.
    pub(super) fn go_builtin(&mut self, op: B, args: &[Expr], e: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        let call = Expr::new(ExprKind::Builtin { op, args: args.to_vec() }, e.span);
        self.go(&call, env, k)
    }

    /// A `Local` bound to a call-by-name expression: enumerate that
    /// expression.
    pub(super) fn local_expr(&mut self, l: &LocalId, e: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        match env.lookup(*l) {
            Some(b) if b.by_name(&self.ip.prog).is_some() => {
                let (e, env) = b.by_name(&self.ip.prog).unwrap();
                self.go(e, env, k)
            }
            _ => self.test(e, env, k),
        }
    }

    /// `e`, an application of definition `d` (directly, or through an
    /// operator constant or argument) to `args`. User-defined operators are
    /// expanded (arguments by name) so that assignments inside them are
    /// recognized; anything else is a test.
    pub(super) fn go_call(&mut self, d: DefId, args: &[Expr], e: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        let ip: &'a Arc<Interp> = self.ip;
        let d = ip.redirect_def(d);
        let def = &ip.prog.defs[d.idx()];
        // A definition TLC overrides by a Java method is evaluated, with its
        // arguments, not expanded (Tool.getNextStatesAppl evaluates a
        // MethodValue).
        let expand = ip.def_defer_errors[d.idx()] || ip.def_by_name[d.idx()];
        match &def.kind {
            DefKind::Op(body) if expand && def.builtin.is_none() && !ip.def_value.contains_key(&d) && !ip.def_const[d.idx()] => {
                // (A definition on a cycle, e.g. `Next <- ReDefNext` with
                // `ReDefNext == Next /\ ...`, could expand forever.)
                let _depth = if ip.is_recursive(d) { Some(crate::depth::Guard::enter(e.span)?) } else { None };
                let env2 = ip.bind_params(&def.params, args, env, &self.cx(), ip.def_env(d, env), true, false)?;
                self.go(body, &env2, k)
            }
            _ => self.test(e, env, k),
        }
    }
}
