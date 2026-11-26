//! Action-position abstract traversal: the assignments an action can perform
//! and the definition calls, binders, and lambdas it follows.

use tlx_eval::env::{Binding, Env, OpVal};
use tlx_layout::shape::set_shape;
use tlx_layout::Shape;
use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{Bound, BoundVars, DefId, DefKind, Expr, ExprKind as H, LocalId, OpRef};

use super::expr::tuple_parts;
use super::{Abs, Analyzer, VShape, DEPTH};

impl<'a> Analyzer<'a> {
    /// Analyze the action-position expression `e`: every assignment it can
    /// perform must fit its slot.
    pub(super) fn action(&mut self, e: &Expr, env: &Env) {
        if !self.spend() {
            return;
        }
        if self.depth > DEPTH {
            self.fail("the closed-layout analysis inlining limit is exceeded");
            return;
        }
        match &*e.kind {
            H::And(es) => {
                let mark = self.refine.len();
                for c in es {
                    self.action(c, env);
                    if self.reason.is_some() {
                        self.refine.truncate(mark);
                        return;
                    }
                    self.refine_guard(c, env, true);
                }
                self.refine.truncate(mark);
            }
            H::Or(es) => {
                for c in es {
                    let mark = self.refine.len();
                    self.action(c, env);
                    self.refine.truncate(mark);
                    if self.reason.is_some() {
                        return;
                    }
                }
            }
            H::Quant { bounds, body, .. } => {
                // Always bind (using `Dyn` for unknown domains) and check the
                // body: an abstract `Dyn` domain can still be a non-empty set
                // or interval at runtime.
                let _ = self.bind_bounds(bounds, env);
                self.action(body, env);
                self.pop_scope();
            }
            H::QuantUnbounded { vars, body, .. } => {
                self.push_scope(vars.iter().map(|l| (*l, Abs::Val(VShape::Shape(Shape::Dyn)))).collect());
                self.action(body, env);
                self.pop_scope();
            }
            H::If { cond, then, els } => {
                let mark = self.refine.len();
                self.refine_guard(cond, env, true);
                self.action(then, env);
                self.refine.truncate(mark);
                self.refine_guard(cond, env, false);
                self.action(els, env);
                self.refine.truncate(mark);
            }
            H::Case { arms, other } => {
                for (g, v) in arms {
                    let mark = self.refine.len();
                    self.refine_guard(g, env, true);
                    self.action(v, env);
                    self.refine.truncate(mark);
                }
                if let Some(o) = other {
                    self.action(o, env);
                }
            }
            H::Let { body, .. } => self.action(body, env),
            H::FnApp { func, args } => self.fn_app_action(func, args, env),
            H::Apply { op, args } => self.apply_action(e, op, args, env),
            H::Local(l) => {
                if let Some((inner, benv)) = self.local_expr(*l, env) {
                    self.action(&inner, &benv);
                }
            }
            H::Builtin { op, args } => self.builtin_action(*op, args, env),
            H::BoxAction { action, .. } | H::AngleAction { action, .. } => self.action(action, env),
            _ => {}
        }
    }

    /// The action-position built-in `op` (the kinds `enumerate` dispatches).
    fn builtin_action(&mut self, op: B, args: &[Expr], env: &Env) {
        if self.base.ip.is_builtin_overridden(op) {
            self.fail(format!("builtin {} is overridden by the configuration", op.name()));
            return;
        }
        match op {
            B::Eq | B::In | B::SubsetEq => {
                self.assignment(op, args, env);
            }
            B::Implies => {
                if let [a, b] = args {
                    let mark = self.refine.len();
                    self.refine_guard(a, env, true);
                    self.action(b, env);
                    self.refine.truncate(mark);
                }
            }
            B::Unchanged => {
                // `UNCHANGED e` assigns `x' = x` for the variables of `e`
                // (their current value, which is inside the slot already), or
                // is a test. Either way it adds no value outside the slots.
            }
            B::Compose => {
                for (i, a) in args.iter().enumerate() {
                    if i == 0 {
                        let mark = self.refine.len();
                        self.action(a, env);
                        self.refine.truncate(mark);
                    } else {
                        // Later operands of `A \cdot B` read the intermediate
                        // state produced by `A`, not `s0`, so path refinements
                        // derived from `s0` guards do not apply there.
                        let saved = std::mem::take(&mut self.refine);
                        self.action(a, env);
                        self.refine = saved;
                    }
                    if self.reason.is_some() {
                        return;
                    }
                }
            }
            _ => {}
        }
    }

    /// `x = e` / `x' = e`, `x \in S` / `x' \in S`, `x \subseteq S` /
    /// `x' \subseteq S`: check the assigned values against the slot.
    fn assignment(&mut self, op: B, args: &[Expr], env: &Env) {
        let [lhs, rhs] = args else { return };
        let Some(v) = self.target(lhs, env) else { return };
        let shape = match op {
            B::Eq => self.value(rhs, env).as_shape(),
            B::In => self.value(rhs, env).elem(),
            B::SubsetEq => match self.value(rhs, env).as_set() {
                Some((elem, max_card)) => set_shape(elem, max_card),
                None => Shape::Dyn,
            },
            _ => unreachable!(),
        };
        if !self.vars[v].accepts_shape(&shape) {
            let name = &self.base.ip.prog.vars[v].name;
            self.fail(format!("a value of {name} can fall outside its layout shape"));
        }
    }

    /// The variable an assignment-shaped left-hand side denotes (`x` in Init,
    /// `x'` in an action), through by-name bindings and 0-ary definitions.
    fn target(&mut self, lhs: &Expr, env: &Env) -> Option<usize> {
        if self.follow > DEPTH {
            self.fail("the closed-layout analysis indirection limit is exceeded");
            return None;
        }
        self.follow += 1;
        let r = self.target_inner(lhs, env);
        self.follow -= 1;
        r
    }

    fn target_inner(&mut self, lhs: &Expr, env: &Env) -> Option<usize> {
        if self.init {
            return self.var_of(lhs, env);
        }
        match &*lhs.kind {
            H::Builtin { op: B::Prime, args } => args.first().and_then(|a| self.var_of(a, env)),
            H::Local(l) => {
                let (e, benv) = self.local_expr(*l, env)?;
                self.target(&e, &benv)
            }
            H::Apply { op: OpRef::Def(d), args } if args.is_empty() => {
                let (d, body) = self.plain_op_body(*d)?;
                let benv = if self.base.ip.prog.def_is_let(d) { env.clone() } else { Env::default() };
                self.target(&body, &benv)
            }
            H::Let { body, .. } => self.target(body, env),
            _ => None,
        }
    }

    /// The state variable `e` denotes (see `target`).
    pub(super) fn var_of(&mut self, e: &Expr, env: &Env) -> Option<usize> {
        if self.follow > DEPTH {
            return None;
        }
        self.follow += 1;
        let r = self.var_of_inner(e, env);
        self.follow -= 1;
        r
    }

    fn var_of_inner(&mut self, e: &Expr, env: &Env) -> Option<usize> {
        match &*e.kind {
            H::Var(v) => Some(v.idx()),
            H::Local(l) => {
                let (inner, benv) = self.local_expr(*l, env)?;
                self.var_of(&inner, &benv)
            }
            H::Apply { op: OpRef::Def(d), args } if args.is_empty() => {
                let (d, body) = self.plain_op_body(*d)?;
                let benv = if self.base.ip.prog.def_is_let(d) { env.clone() } else { Env::default() };
                self.var_of(&body, &benv)
            }
            H::Let { body, .. } => self.var_of(body, env),
            _ => None,
        }
    }

    /// The by-name binding of local `l` (the enumerator's `local_expr`).
    fn local_expr(&self, l: LocalId, env: &Env) -> Option<(Expr, Env)> {
        match self.lookup(l) {
            Some(Abs::Thunk(e, benv)) => Some((e.clone(), benv.clone())),
            Some(_) => None,
            None => env.lookup(l)?.by_name(&self.base.ip.prog).map(|(e, benv)| (e.clone(), benv.clone())),
        }
    }

    /// The body of 0-ary user definition `d` (after cfg redirection), if the
    /// interpreter evaluates it as a definition.
    fn plain_op_body(&self, orig_d: DefId) -> Option<(DefId, Expr)> {
        if self.base.ip.has_def_value(orig_d) {
            return None;
        }
        let d = self.base.ip.redirect_def(orig_d);
        if self.base.ip.has_def_value(d) {
            return None;
        }
        let def = &self.base.ip.prog.defs[d.idx()];
        match &def.kind {
            DefKind::Op(body) if def.builtin.is_none() && !self.base.ip.is_const_def(d) => Some((d, body.clone())),
            _ => None,
        }
    }

    /// `f[a]` where `f` is a lazily represented function: enumerate the body
    /// with its arguments bound (the enumerator's `fn_app`); the application
    /// is a test otherwise.
    fn fn_app_action(&mut self, func: &Expr, args: &[Expr], env: &Env) {
        let Some((bounds, body, fenv)) = self.lambda_of(func, env, true) else { return };
        if self.bind_fn_args(&bounds, args, env).is_none() {
            self.fail("a function's arguments cannot be resolved statically");
            return;
        }
        self.depth += 1;
        self.action(&body, &fenv);
        self.depth -= 1;
        self.pop_scope();
    }

    /// The function constructor `f` denotes, if it is one (the enumerator's
    /// `lambda_of`).
    pub(super) fn lambda_of(&mut self, f: &Expr, env: &Env, in_action: bool) -> Option<(Vec<Bound>, Expr, Env)> {
        if self.follow > DEPTH {
            if in_action {
                self.fail("the closed-layout analysis indirection limit is exceeded");
            }
            return None;
        }
        self.follow += 1;
        let r = self.lambda_of_inner(f, env, in_action);
        self.follow -= 1;
        r
    }

    fn lambda_of_inner(&mut self, f: &Expr, env: &Env, in_action: bool) -> Option<(Vec<Bound>, Expr, Env)> {
        match &*f.kind {
            H::FnConstruct { bounds, body } => Some((bounds.clone(), body.clone(), env.clone())),
            H::Local(l) => {
                let (inner, benv) = self.local_expr(*l, env)?;
                self.lambda_of(&inner, &benv, in_action)
            }
            H::Apply { op: OpRef::Def(orig_d), args } if args.is_empty() => {
                if self.base.ip.has_def_value(*orig_d) {
                    return None;
                }
                let d = self.base.ip.redirect_def(*orig_d);
                let def = &self.base.ip.prog.defs[d.idx()];
                if def.builtin.is_some() || self.base.ip.has_def_value(d) {
                    return None;
                }
                let base = if self.base.ip.prog.def_is_let(d) { env.clone() } else { Env::default() };
                match &def.kind {
                    DefKind::Fn { bounds, body } => Some((bounds.clone(), body.clone(), base)),
                    DefKind::Op(body) => self.lambda_of(body, &base, in_action),
                    DefKind::Pending => None,
                }
            }
            H::Let { body, .. } => self.lambda_of(body, env, in_action),
            _ => None,
        }
    }

    /// Bind a function constructor's bound variables to the caller's `args`
    /// (evaluated in caller `env`), mirroring `Interp::bind_fn_args`.
    pub(super) fn bind_fn_args(&mut self, bounds: &[Bound], args: &[Expr], env: &Env) -> Option<()> {
        if args.is_empty() || bounds.is_empty() {
            return None;
        }
        let arg = if args.len() == 1 {
            self.value(&args[0], env)
        } else {
            VShape::Shape(Shape::Tuple(args.iter().map(|a| self.value(a, env).as_shape()).collect()))
        };
        // One single-variable or tuple binder: bound directly to `arg`.
        if let [b] = bounds {
            match &b.vars {
                BoundVars::Many(ls) if ls.len() == 1 => {
                    self.push_scope(vec![(ls[0], Abs::Val(arg))]);
                    return Some(());
                }
                BoundVars::Tuple(ls) => {
                    let parts = tuple_parts(&arg.as_shape(), ls.len());
                    let entries = ls.iter().enumerate().map(|(i, l)| (*l, Abs::Val(VShape::Shape(parts[i].clone())))).collect();
                    self.push_scope(entries);
                    return Some(());
                }
                _ => {}
            }
        }
        // Multi-argument function: destructure the tuple argument across
        // each bound slot (`Many(ls)` takes `ls.len()` slots; `Tuple(_)`
        // takes one slot and destructures it).
        let slots: usize = bounds
            .iter()
            .map(|b| match &b.vars {
                BoundVars::Many(ls) => ls.len(),
                BoundVars::Tuple(_) => 1,
            })
            .sum();
        let parts = tuple_parts(&arg.as_shape(), slots);
        let mut entries = Vec::new();
        let mut idx = 0usize;
        for b in bounds {
            match &b.vars {
                BoundVars::Many(ls) => {
                    for l in ls {
                        entries.push((*l, Abs::Val(VShape::Shape(parts.get(idx).cloned().unwrap_or(Shape::Dyn)))));
                        idx += 1;
                    }
                }
                BoundVars::Tuple(ls) => {
                    let sub = tuple_parts(parts.get(idx).unwrap_or(&Shape::Dyn), ls.len());
                    entries.extend(ls.iter().enumerate().map(|(k, l)| (*l, Abs::Val(VShape::Shape(sub[k].clone())))));
                    idx += 1;
                }
            }
        }
        self.push_scope(entries);
        Some(())
    }

    /// Bind quantifier / comprehension bounds in one scope, mirroring
    /// `Interp::for_each_binding` (all domain expressions are evaluated in the
    /// outer scope; `BoundVars::Many(ls)` chooses `ls.len()` independent
    /// elements while `BoundVars::Tuple(ls)` destructures one tuple element).
    ///
    /// Always pushes a scope (binding unknown domains to `Dyn`). Returns an
    /// upper bound on the number of binding tuples when every bound has a
    /// finite set cardinality bound without overflow.
    pub(super) fn bind_bounds(&mut self, bounds: &[Bound], env: &Env) -> Option<usize> {
        let mut card: Option<usize> = Some(1);
        let mut entries = Vec::new();
        for b in bounds {
            let set = self.value(&b.set, env);
            let elem = set.elem();
            let choices = match &b.vars {
                BoundVars::Many(ls) => ls.len(),
                BoundVars::Tuple(_) => 1,
            };
            match set.as_set() {
                Some((_, max_card)) => {
                    for _ in 0..choices {
                        card = card.and_then(|c| c.checked_mul(max_card));
                    }
                }
                None => card = None,
            }
            match &b.vars {
                BoundVars::Many(ls) => {
                    entries.extend(ls.iter().map(|l| (*l, Abs::Val(VShape::Shape(elem.clone())))));
                }
                BoundVars::Tuple(ls) => {
                    let parts = tuple_parts(&elem, ls.len());
                    entries.extend(
                        ls.iter().enumerate().map(|(i, l)| (*l, Abs::Val(VShape::Shape(parts.get(i).cloned().unwrap_or(Shape::Dyn))))),
                    );
                }
            }
        }
        self.push_scope(entries);
        card
    }

    // ------------------------------------------------------------------
    // definition application in action position

    fn apply_action(&mut self, e: &Expr, op: &OpRef, args: &[Expr], env: &Env) {
        match op {
            OpRef::Const(c) => match self.base.ip.const_op_ref(*c) {
                Some(OpRef::Def(d)) => self.call_def_action(d, args, env),
                Some(OpRef::Builtin(b)) => self.builtin_action(b, args, env),
                _ => {}
            },
            OpRef::Param(l) => {
                let binding = self.lookup(*l).cloned().or_else(|| {
                    env.lookup(*l).map(|b| match b {
                        Binding::Op(o) => Abs::Op(o.clone()),
                        _ => Abs::Val(VShape::Shape(Shape::Dyn)),
                    })
                });
                match binding {
                    Some(Abs::Op(OpVal::Ref(OpRef::Def(d)))) => self.call_def_action(d, args, env),
                    Some(Abs::Op(OpVal::Ref(OpRef::Builtin(b)))) => self.builtin_action(b, args, env),
                    Some(Abs::Op(OpVal::Ref(OpRef::Const(c)))) => match self.base.ip.const_op_ref(c) {
                        Some(OpRef::Def(d)) => self.call_def_action(d, args, env),
                        Some(OpRef::Builtin(b)) => self.builtin_action(b, args, env),
                        _ => {}
                    },
                    Some(Abs::Op(OpVal::Lambda { params, body, env: lenv })) => self.lambda_action(&params, &body, &lenv, args, env),
                    // An unbound operator parameter is an evaluation error in
                    // the enumerator's `test`: it assigns nothing. A value
                    // parameter applied as an operator is not a valid call.
                    _ => {}
                }
            }
            OpRef::Def(orig_d) => {
                if self.base.ip.has_def_value(*orig_d) {
                    let _ = e;
                    return;
                }
                let d = self.base.ip.redirect_def(*orig_d);
                let def = &self.base.ip.prog.defs[d.idx()];
                let expand = self.base.ip.defers_arg_errors(d) || self.base.ip.is_action_level(d);
                if expand && def.builtin.is_none() && !self.base.ip.has_def_value(d) && !self.base.ip.is_const_def(d) {
                    self.call_def_action(d, args, env);
                } else {
                    // The enumerator evaluates this application as a test.
                    let _ = e;
                }
            }
            OpRef::Builtin(b) => self.builtin_action(*b, args, env),
        }
    }

    /// Inline `d(args)` as an action.
    fn call_def_action(&mut self, orig_d: DefId, args: &[Expr], env: &Env) {
        if self.base.ip.has_def_value(orig_d) {
            return;
        }
        let d = self.base.ip.redirect_def(orig_d);
        let def = &self.base.ip.prog.defs[d.idx()];
        if def.builtin.is_some() || self.base.ip.has_def_value(d) || self.base.ip.is_const_def(d) {
            // The enumerator evaluates this application as a test (a Java
            // override, a cfg value, or a pre-evaluated constant definition).
            return;
        }
        if self.active.contains(&d) || self.depth > DEPTH {
            self.fail(format!("recursive definition {} cannot be proven closed", self.base.ip.prog.defs[d.idx()].name));
            return;
        }
        let Some(body) = self.body_of(d) else {
            self.fail(format!("definition {} cannot be inlined", self.base.ip.prog.defs[d.idx()].name));
            return;
        };
        match self.bind_params(d, args, env) {
            Ok(base) => {
                self.active.push(d);
                self.depth += 1;
                self.action(&body, &base);
                self.depth -= 1;
                self.active.pop();
                self.pop_scope();
            }
            Err(why) => self.fail(why),
        }
    }

    /// Inline a `LAMBDA`-valued operator argument as an action.
    fn lambda_action(&mut self, params: &[LocalId], body: &Expr, lenv: &Env, args: &[Expr], env: &Env) {
        let mut entries = Vec::with_capacity(params.len());
        for (p, a) in params.iter().zip(args.iter()) {
            let arity = self.base.ip.prog.locals[p.idx()].arity;
            if arity > 0 {
                match self.op_val(a, env) {
                    Some(o) => entries.push((*p, Abs::Op(o))),
                    None => {
                        self.fail("a lambda's operator argument cannot be resolved statically");
                        return;
                    }
                }
            } else {
                entries.push((*p, Abs::Thunk(a.clone(), env.clone())));
            }
        }
        self.push_scope(entries);
        self.depth += 1;
        self.action(body, lenv);
        self.depth -= 1;
        self.pop_scope();
    }

    pub(super) fn body_of(&self, d: DefId) -> Option<Expr> {
        match &self.base.ip.prog.defs[d.idx()].kind {
            DefKind::Op(body) => Some(body.clone()),
            _ => None,
        }
    }
}
