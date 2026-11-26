//! Syntactic queries on HIR in a lowering environment: what an action
//! conjunct assigns (mirroring `tlx_eval::enumerate`), whether it may assign
//! or branch, constness, and resolving references to the expressions they
//! stand for (definitions, LET and call-by-name bindings).

use tlx_eval::env::{Binding, Env};
use tlx_eval::eval::Ctx;
use tlx_eval::Interp;
use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{self, DefKind, ExprKind as H, LocalId, OpRef, QuantKind};
use tlx_value::Value;

use super::{temp_ref, LBind, LEnv, Lowerer, St};
use crate::ir::{Expr, ExprKind, Temp};

impl Lowerer<'_> {
    /// Body of the 0-ary user operator `d` (after redirection), if it is one.
    pub(super) fn op_body(&self, d: hir::DefId) -> Option<(hir::DefId, hir::Expr)> {
        let d = self.ip.redirect_def(d);
        let def = &self.ip.prog.defs[d.idx()];
        match &def.kind {
            DefKind::Op(body) if def.builtin.is_none() => Some((d, body.clone())),
            _ => None,
        }
    }

    /// The state variable `e` denotes (through by-name arguments and 0-ary
    /// definitions).
    pub(super) fn var_of(&self, e: &hir::Expr, env: &LEnv) -> Option<usize> {
        match &*e.kind {
            H::Var(v) => Some(v.idx()),
            H::Local(l) => match env.lookup(*l, &self.ip.prog) {
                Some(LBind::Thunk(te, tenv)) => self.var_of(&te, &tenv),
                _ => None,
            },
            H::Apply { op: OpRef::Def(d), args } if args.is_empty() => {
                let (d, body) = self.op_body(*d)?;
                self.var_of(&body, &self.def_env(d, env))
            }
            _ => None,
        }
    }

    /// The variable the left side `lhs` of `=`/`\in`/`\subseteq` assigns:
    /// `x'` in Next, `x` in Init.
    fn target(&self, lhs: &hir::Expr, env: &LEnv, st: &St) -> Option<usize> {
        if st.init {
            return self.var_of(lhs, env);
        }
        match &*lhs.kind {
            H::Builtin { op: B::Prime, args } => self.var_of(&args[0], env),
            H::Local(l) => match env.lookup(*l, &self.ip.prog) {
                Some(LBind::Thunk(te, tenv)) => self.target(&te, &tenv, st),
                _ => None,
            },
            H::Apply { op: OpRef::Def(d), args } if args.is_empty() => {
                let (d, body) = self.op_body(*d)?;
                self.target(&body, &self.def_env(d, env), st)
            }
            _ => None,
        }
    }

    /// `target`, if not assigned yet on this path.
    pub(super) fn unassigned_target(&self, lhs: &hir::Expr, env: &LEnv, st: &St) -> Option<usize> {
        self.target(lhs, env, st).filter(|v| !st.assigned[*v])
    }

    /// The function constructor `f` denotes, if TLC would expand its
    /// application lazily (a constructor, or a definition whose value is
    /// not precomputed as a finite function).
    pub(super) fn lambda_of(&self, f: &hir::Expr, env: &LEnv) -> Option<(Vec<hir::Bound>, hir::Expr, LEnv)> {
        match &*f.kind {
            H::FnConstruct { bounds, body } => Some((bounds.clone(), body.clone(), env.clone())),
            H::Local(l) => match env.lookup(*l, &self.ip.prog) {
                Some(LBind::Thunk(te, tenv)) => self.lambda_of(&te, &tenv),
                _ => None,
            },
            H::Apply { op: OpRef::Def(d), args } if args.is_empty() => {
                let d = self.ip.redirect_def(*d);
                let def = &self.ip.prog.defs[d.idx()];
                if def.builtin.is_some() || self.ip.has_def_value(d) {
                    return None;
                }
                if self.ip.is_const_def(d) && !self.ip.is_recursive_fn(d) {
                    let lazy = matches!(self.ip.eval(f, &Env::default(), &Ctx::NONE), Ok(Value::LazyFcn(_)) | Err(_));
                    if !lazy {
                        return None;
                    }
                }
                let base = self.def_env(d, env);
                match &def.kind {
                    DefKind::Fn { bounds, body } => Some((bounds.clone(), body.clone(), base)),
                    DefKind::Op(body) => self.lambda_of(body, &base),
                    DefKind::Pending => None,
                }
            }
            _ => None,
        }
    }

    /// Conservative: can evaluating `e` as an action assign a variable?
    /// Only `=`/`\in`/`\subseteq` whose left side may denote a (primed, in
    /// Next) variable, UNCHANGED, action brackets, and calls/by-name
    /// arguments (whose bodies are not inspected) can.
    pub(super) fn may_assign(&self, e: &hir::Expr, env: &LEnv, st: &St) -> bool {
        may_assign_in(self.ip, e, env, st.init)
    }

    /// LET definitions that are used more than once and whose value cannot
    /// depend on the next state, computed once at the LET: the extended
    /// environment and the temp bindings (in order).
    pub(super) fn let_temps(&mut self, defs: &[hir::DefId], body: &hir::Expr, env: &LEnv, st: &St) -> (LEnv, Vec<(Temp, Expr)>) {
        let mut env2 = env.clone();
        let mut lets = Vec::new();
        if self.primed {
            return (env2, lets);
        }
        for d in defs {
            if !self.ip.is_let_cacheable(*d) {
                continue;
            }
            let mut uses = def_uses(body, *d);
            for o in defs {
                if let hir::DefKind::Op(b) = &self.ip.prog.defs[o.idx()].kind {
                    uses += def_uses(b, *d);
                }
            }
            if uses < 2 {
                continue;
            }
            let hir::DefKind::Op(b) = &self.ip.prog.defs[d.idx()].kind else { continue };
            let b = b.clone();
            let v = self.expr(&b, &env2, st);
            if matches!(&*v.kind, ExprKind::Const(_) | ExprKind::ConstWords(_)) {
                env2 = env2.bind(tlx_eval::env::let_cache_key(*d), LBind::Ir(v));
                continue;
            }
            let t = self.temp(v.ty);
            self.note_temp(t, &v);
            env2 = env2.bind(tlx_eval::env::let_cache_key(*d), LBind::Ir(temp_ref(v.ty, t)));
            lets.push((t, v));
        }
        (env2, lets)
    }

    /// Whether enumerating `e` as an action conjunct might produce several
    /// branches (so it is not equivalent to a single guard). Only statement
    /// positions matter (TLC evaluates everything else as a value).
    pub(super) fn may_branch(&self, e: &hir::Expr, env: &LEnv, depth: usize) -> bool {
        if depth > 8 {
            return true;
        }
        match &*e.kind {
            H::Or(_) | H::Quant { kind: QuantKind::Exists, .. } => true,
            H::And(es) => es.iter().any(|x| self.may_branch(x, env, depth)),
            H::Quant { kind: QuantKind::Forall, body, .. } => self.may_branch(body, env, depth),
            H::If { then, els, .. } => self.may_branch(then, env, depth) || self.may_branch(els, env, depth),
            H::Case { arms, other } => {
                arms.iter().any(|(_, v)| self.may_branch(v, env, depth)) || other.as_ref().is_some_and(|o| self.may_branch(o, env, depth))
            }
            H::Let { body, .. } => self.may_branch(body, env, depth),
            H::Builtin { op: B::Implies, args } => self.may_branch(&args[1], env, depth),
            H::Apply { op: OpRef::Def(d), .. } => match self.def_target(*d, env) {
                Some((_, body, base, _)) => {
                    let d = self.ip.redirect_def(*d);
                    !self.ip.is_const_def(d) && self.may_branch(&body, &base, depth + 1)
                }
                None => false,
            },
            H::Apply { op: OpRef::Const(_) | OpRef::Param(_), .. } => true,
            H::Local(l) => match env.lookup(*l, &self.ip.prog) {
                Some(LBind::Thunk(x, xenv)) => self.may_branch(&x, &xenv, depth + 1),
                Some(LBind::Ir(_)) => false,
                _ => true,
            },
            _ => false,
        }
    }

    /// The value of a constant boolean condition (`IF`/`CASE` guards with a
    /// constant value select their branch statically).
    pub(super) fn const_bool(&self, e: &hir::Expr, env: &LEnv) -> Option<bool> {
        match self.const_value(e, env)? {
            Value::Bool(b) => Some(b),
            _ => None,
        }
    }

    /// The arms of `CASE arms [] OTHER -> other` that can be selected,
    /// given the guards with a constant value: arms with a constant FALSE
    /// guard are dropped, and an arm with a constant TRUE guard ends the
    /// CASE (it becomes the OTHER arm).
    pub(super) fn live_case_arms<'e>(
        &self,
        arms: &'e [(hir::Expr, hir::Expr)],
        other: Option<&'e hir::Expr>,
        env: &LEnv,
    ) -> (Vec<&'e (hir::Expr, hir::Expr)>, Option<&'e hir::Expr>) {
        let mut live = Vec::new();
        for a in arms {
            match self.const_bool(&a.0, env) {
                Some(true) => return (live, Some(&a.1)),
                Some(false) => {}
                None => live.push(a),
            }
        }
        (live, other)
    }

    /// Value of `e` if it is a closed constant-level expression.
    pub(super) fn const_value(&self, e: &hir::Expr, env: &LEnv) -> Option<Value> {
        self.const_value_at(e, env, 0)
    }

    fn const_value_at(&self, e: &hir::Expr, env: &LEnv, depth: usize) -> Option<Value> {
        let key = std::sync::Arc::as_ptr(&e.kind) as *const u8 as usize;
        if let Some((_, v)) = self.const_cache.borrow().get(&key) {
            return v.clone();
        }
        let mut consts = Vec::new();
        if !self.closed_const(e, env, &mut consts, depth) {
            return None;
        }
        // Not if it may create strings: strings are ordered by creation, as
        // in TLC. (`Tail`, `SubSeq` and `\o` of sequences create
        // none.)
        if consts.is_empty() && !self.uses_env_locals(e, env) {
            // The value cannot depend on the environment: evaluate it once.
            let v = if self.strings.expr_in(e, &env.base) { None } else { self.ip.eval(e, &env.base, &Ctx::NONE).ok() };
            // A constant set over the `-maxSetSize` bound is not folded into
            // the compiled model: TLC fails on a quantifier over such a set
            // (but streams `x' \in S`), and only the interpreter decides the
            // expression's own path.
            let v = v.filter(|v| !tlx_value::ops::over_set_bound(v));
            self.const_cache.borrow_mut().insert(key, (e.kind.clone(), v.clone()));
            return v;
        }
        let mut base = env.base.clone();
        for (l, v) in consts {
            base = base.bind_val(l, v);
        }
        if self.strings.expr_in(e, &base) {
            return None;
        }
        self.ip.eval(e, &base, &Ctx::NONE).ok().filter(|v| !tlx_value::ops::over_set_bound(v))
    }

    /// Whether definition `d` (transitively) uses a nondeterministic or
    /// side-effecting builtin: its applications must be evaluated at run
    /// time, every time.
    pub(super) fn def_volatile(&self, d: hir::DefId) -> bool {
        let d = self.ip.redirect_def(d);
        // (A constant definition is evaluated once, even if it is volatile:
        // TLC caches its value at startup.)
        !self.ip.is_const_def(d) && self.ip.def_effectful(d)
    }

    /// Whether evaluating `e` may use a nondeterministic or side-effecting
    /// builtin (also through by-name arguments of `env`).
    pub(super) fn volatile_expr(&self, e: &hir::Expr, env: &LEnv) -> bool {
        if self.expr_volatile(e) {
            return true;
        }
        env.binds.iter().any(|(_, b)| matches!(b, LBind::Thunk(t, _) if self.expr_volatile(t)))
    }

    /// Whether evaluating `e` may create new strings (also through by-name
    /// arguments and operator lambdas captured in `env`): string creation
    /// order affects TLC's string order. Deduplicates shared captured
    /// environments so multi-parameter recursive inlining stays linear.
    pub(super) fn expr_makes_strings(&self, e: &hir::Expr, env: &LEnv) -> bool {
        use std::sync::Arc;
        if self.strings.expr_in(e, &env.base) {
            return true;
        }
        if env.binds.is_empty() {
            return false;
        }
        let mut seen_env = std::collections::HashSet::new();
        let mut seen_expr = std::collections::HashSet::new();
        let mut todo: Vec<&LEnv> = Vec::new();
        // `LEnv` is immutable and only copied as a whole `(binds, base)` pair,
        // so `Arc::as_ptr(&binds)` uniquely identifies the non-empty bindings
        // list and its accompanying `base`.
        if seen_env.insert(Arc::as_ptr(&env.binds) as usize) {
            todo.push(env);
        }
        while let Some(cur) = todo.pop() {
            for (_, b) in cur.binds.iter() {
                let (x, xenv) = match b {
                    LBind::Thunk(t, tenv) => (t, tenv),
                    LBind::Op(super::LOp::Lambda(_, body, lenv)) => (body, lenv),
                    _ => continue,
                };
                if seen_expr.insert((Arc::as_ptr(&x.kind) as usize, Arc::as_ptr(&xenv.binds) as usize))
                    && self.strings.expr_in(x, &xenv.base)
                {
                    return true;
                }
                if !xenv.binds.is_empty() && seen_env.insert(Arc::as_ptr(&xenv.binds) as usize) {
                    todo.push(xenv);
                }
            }
        }
        false
    }

    pub(super) fn expr_volatile(&self, e: &hir::Expr) -> bool {
        let here = match &*e.kind {
            H::Builtin { op, .. } => is_volatile_builtin(*op),
            H::Apply { op: OpRef::Def(d), .. } | H::OpArg(OpRef::Def(d)) => self.def_volatile(*d),
            H::Apply { op: OpRef::Const(c), .. } => matches!(self.ip.const_op_ref(*c), Some(OpRef::Def(d)) if self.def_volatile(d)),
            _ => false,
        };
        let mut found = here;
        if !found {
            tlx_sema::visit::children(e, &mut |c| found = found || self.expr_volatile(c));
        }
        found
    }

    /// `expr_volatile`, not counting output (Print/PrintT, see
    /// `Builtin::is_output`): through definitions whose only effect is
    /// output (`seen`: the definitions already looked at).
    pub(super) fn expr_volatile_beyond_output(&self, e: &hir::Expr, seen: &mut std::collections::HashSet<hir::DefId>) -> bool {
        let def = |d: hir::DefId, seen: &mut std::collections::HashSet<hir::DefId>| {
            let d = self.ip.redirect_def(d);
            if !self.def_volatile(d) || !seen.insert(d) {
                return false;
            }
            let def = &self.ip.prog.defs[d.idx()];
            if let Some(b) = def.builtin {
                return b.is_volatile() && !b.is_output();
            }
            match &def.kind {
                DefKind::Op(body) => self.expr_volatile_beyond_output(body, seen),
                DefKind::Fn { body, bounds } => {
                    self.expr_volatile_beyond_output(body, seen) || bounds.iter().any(|b| self.expr_volatile_beyond_output(&b.set, seen))
                }
                DefKind::Pending => true,
            }
        };
        let here = match &*e.kind {
            H::Builtin { op, .. } => is_volatile_builtin(*op) && !op.is_output(),
            H::Apply { op: OpRef::Def(d), .. } | H::OpArg(OpRef::Def(d)) => def(*d, seen),
            H::Apply { op: OpRef::Const(c), .. } => match self.ip.const_op_ref(*c) {
                Some(OpRef::Def(d)) => def(d, seen),
                _ => false,
            },
            _ => false,
        };
        let mut found = here;
        if !found {
            tlx_sema::visit::children(e, &mut |c| found = found || self.expr_volatile_beyond_output(c, seen));
        }
        found
    }

    /// Whether running the lowered statement tree `s` may evaluate a
    /// nondeterministic or side-effecting builtin other than output
    /// (Print/PrintT): a compiled run of an action that only prints can be
    /// redone by the interpreter if its output is held back until it
    /// succeeds (`Interp::hold_output`).
    pub fn stmt_volatile_beyond_output(&self, s: &crate::ir::Stmt) -> bool {
        let mut found = false;
        s.for_each_expr_deep(&mut |e| found = found || self.expression_summary(e).effects.beyond_output);
        found
    }

    /// Whether running the lowered statement tree `s` may evaluate a
    /// nondeterministic or side-effecting builtin (Print, TLCSet,
    /// RandomElement, ...), in an interpreter fallback or a boxed operation.
    /// Such a run must not be redone by the interpreter after a failure:
    /// its effects would be observed twice.
    pub fn stmt_volatile(&self, s: &crate::ir::Stmt) -> bool {
        let mut found = false;
        s.for_each_expr_deep(&mut |e| found = found || self.ir_volatile(e));
        found
    }

    /// `stmt_volatile` for an expression.
    pub fn ir_volatile(&self, e: &Expr) -> bool {
        self.expression_summary(e).effects.volatile
    }

    /// Effects local to a node; calls and children are summarized centrally.
    pub(super) fn local_volatile(&self, e: &Expr, output_ok: bool) -> bool {
        use crate::ir::{Deferred, ExprKind as K};
        let hir_volatile = |x: &hir::Expr| match output_ok {
            false => self.expr_volatile(x),
            true => self.expr_volatile_beyond_output(x, &mut std::collections::HashSet::new()),
        };
        match &*e.kind {
            K::Interp { expr, deferred, .. } => {
                hir_volatile(expr)
                    || deferred.iter().any(|d| match d {
                        Deferred::Thunk(_, x) | Deferred::Once(_, x) | Deferred::Lambda(_, _, x) => hir_volatile(x),
                        Deferred::OpRef(_, OpRef::Def(d)) => match output_ok {
                            false => self.def_volatile(*d),
                            true => self.expr_volatile_beyond_output(
                                &hir::Expr::new(H::OpArg(OpRef::Def(*d)), expr.span),
                                &mut std::collections::HashSet::new(),
                            ),
                        },
                        Deferred::OpRef(..) => false,
                    })
            }
            K::ValOp { op, .. } => is_volatile_builtin(*op) && !(output_ok && op.is_output()),
            _ => false,
        }
    }

    /// Whether `e` reads a local bound in the environment (rather than
    /// inside `e`).
    fn uses_env_locals(&self, e: &hir::Expr, env: &LEnv) -> bool {
        self.uses_env_locals_at(e, env, 0)
    }

    /// `uses_env_locals`, also through the LET definitions `e` applies
    /// (their bodies see the environment of the LET).
    fn uses_env_locals_at(&self, e: &hir::Expr, env: &LEnv, depth: usize) -> bool {
        let here = match &*e.kind {
            H::Local(l) | H::Apply { op: OpRef::Param(l), .. } | H::OpArg(OpRef::Param(l)) => {
                env.base.lookup(*l).is_some() || env.binds.iter().any(|(x, _)| x == l)
            }
            H::Apply { op: OpRef::Def(d), .. } | H::OpArg(OpRef::Def(d)) if self.ip.prog.def_is_let(self.ip.redirect_def(*d)) => {
                let d = self.ip.redirect_def(*d);
                depth >= 4
                    || match &self.ip.prog.defs[d.idx()].kind {
                        DefKind::Op(b) => self.uses_env_locals_at(b, env, depth + 1),
                        _ => true,
                    }
            }
            _ => false,
        };
        let mut found = here;
        if !found {
            tlx_sema::visit::children(e, &mut |c| found = found || self.uses_env_locals_at(c, env, depth));
        }
        found
    }

    /// Closed (no IR-bound locals, except constant ones, collected in
    /// `consts`) and constant-level (no state access): can be evaluated
    /// once, now, by the interpreter.
    fn closed_const(&self, e: &hir::Expr, env: &LEnv, consts: &mut Vec<(LocalId, Value)>, depth: usize) -> bool {
        let here = match &*e.kind {
            H::Var(_) | H::At => false,
            // LET definitions are checked where they are applied.
            H::Let { .. } => true,
            H::Builtin { op: B::Prime | B::Unchanged | B::Enabled, .. } => false,
            H::Builtin { op, .. } if is_volatile_builtin(*op) => false,
            // Locals bound inside `e` are not in `env`; locals of the action
            // instance are constants; IR-bound, by-name and operator locals are not.
            H::Local(l) => match env.binds.iter().rev().find(|(x, _)| x == l) {
                // IR-bound locals with a constant value / constant by-name
                // arguments.
                Some((_, b)) => {
                    if consts.iter().any(|(x, _)| x == l) {
                        return true;
                    }
                    let v = match b {
                        LBind::Ir(x) => super::typed::const_of(x),
                        LBind::Thunk(te, tenv) if depth < 4 => self.const_value_at(te, tenv, depth + 1),
                        _ => None,
                    };
                    match v {
                        Some(v) => {
                            consts.push((*l, v));
                            true
                        }
                        None => false,
                    }
                }
                None => !matches!(env.base.lookup(*l), Some(Binding::Thunk(_) | Binding::Name(..) | Binding::Op(_))),
            },
            H::Apply { op: OpRef::Def(d), .. } | H::OpArg(OpRef::Def(d)) => {
                let d = self.ip.redirect_def(*d);
                if self.ip.prog.def_is_let(d) {
                    // A LET definition: constant if its body is.
                    depth < 4
                        && (self.ip.is_pure_def(d) || self.ip.is_let_cacheable(d))
                        && match &self.ip.prog.defs[d.idx()].kind {
                            DefKind::Op(b) => self.closed_const(b, env, consts, depth + 1),
                            _ => false,
                        }
                } else {
                    // (A constant definition is evaluated once.)
                    self.ip.is_const_def(d) || self.ip.is_pure_def(d) && !self.def_volatile(d)
                }
            }
            H::Apply { op: OpRef::Param(_), .. } | H::OpArg(OpRef::Param(_)) => false,
            H::Apply { op: OpRef::Const(c), .. } => self.ip.const_op_ref(*c).is_none_or(|r| match r {
                OpRef::Def(d) => self.ip.is_pure_def(d) && !self.def_volatile(d),
                _ => true,
            }),
            H::BoxAction { .. } | H::AngleAction { .. } | H::Fairness { .. } => false,
            _ => true,
        };
        if !here {
            return false;
        }
        let mut ok = true;
        tlx_sema::visit::children(e, &mut |c| ok = ok && self.closed_const(c, env, consts, depth));
        ok
    }

    /// Parameters, body and base environment of an inlinable definition
    /// (and the definition itself, after redirection).
    pub(super) fn def_target(&self, d: hir::DefId, env: &LEnv) -> Option<(Vec<LocalId>, hir::Expr, LEnv, Option<hir::DefId>)> {
        let d = self.ip.redirect_def(d);
        let def = &self.ip.prog.defs[d.idx()];
        if def.builtin.is_some() || self.ip.has_def_value(d) {
            return None;
        }
        let DefKind::Op(body) = &def.kind else { return None };
        Some((def.params.clone(), body.clone(), self.def_env(d, env), Some(d)))
    }

    /// Resolve references to zero-arity operators and LET/call-by-name
    /// bindings to the expression they stand for.
    /// Whether `e` is (behind definitions / by-name arguments) a value
    /// constructor that `expr_into` can build in a given encoding.
    pub(super) fn constructs(&self, e: &hir::Expr, env: &LEnv) -> bool {
        use super::construct::is_constructor;
        if is_constructor(e) || self.peel(e, env).is_some_and(|(p, _)| is_constructor(&p)) {
            return true;
        }
        // An operator call whose body is a constructor (e.g. a record).
        match &*e.kind {
            H::Apply { op: OpRef::Def(d), args } if !args.is_empty() => self.def_target(*d, env).is_some_and(|(_, body, base, _)| {
                is_constructor(&body) || self.peel(&body, &base).is_some_and(|(p, _)| is_constructor(&p))
            }),
            _ => false,
        }
    }

    /// `constructs`, also through up to `depth` operator calls and LETs
    /// (`WriteToFile(f, o, d) == LET ... IN MkArray(n, g)`).
    pub(super) fn builds(&self, e: &hir::Expr, env: &LEnv, depth: usize) -> bool {
        if self.constructs(e, env) {
            return true;
        }
        if depth == 0 {
            return false;
        }
        match &*e.kind {
            H::Let { body, .. } => self.builds(body, env, depth - 1),
            H::Apply { op: OpRef::Def(d), args } if !args.is_empty() => {
                // (The arguments are not bound: only the body's form matters.)
                self.def_target(*d, env).is_some_and(|(_, body, base, _)| self.builds(&body, &base, depth - 1))
            }
            _ => false,
        }
    }

    /// `peel`, also through applications of operators whose body is a
    /// value constructor (parameters bound by name).
    pub(super) fn peel_call(&self, e: &hir::Expr, env: &LEnv) -> Option<(hir::Expr, LEnv)> {
        let (mut e, mut env) = self.peel(e, env)?;
        for _ in 0..8 {
            let H::Apply { op: OpRef::Def(d), args } = &*e.kind else { break };
            if args.is_empty() {
                break;
            }
            let (params, body, base, def) = self.def_target(*d, &env)?;
            if params.len() != args.len() || params.iter().any(|p| self.ip.prog.locals[p.idx()].arity > 0) {
                return None;
            }
            // Arguments evaluated eagerly: no component may be
            // selected without evaluating the others.
            if !self.defers_arg_errors(def, &body) {
                return None;
            }
            let mut env2 = base;
            for (p, a) in params.iter().zip(args) {
                env2 = env2.bind(*p, LBind::Thunk(a.clone(), env.clone()));
            }
            (e, env) = self.peel(&body, &env2)?;
        }
        Some((e, env))
    }

    pub(super) fn peel(&self, e: &hir::Expr, env: &LEnv) -> Option<(hir::Expr, LEnv)> {
        let (mut e, mut env) = (e.clone(), env.clone());
        for _ in 0..16 {
            match &*e.kind {
                H::Apply { op: OpRef::Def(d), args } if args.is_empty() => {
                    // A LET definition computed once at its LET (see
                    // `let_temps`): not re-evaluated where it is used.
                    if !self.primed && matches!(env.lookup(tlx_eval::env::let_cache_key(*d), &self.ip.prog), Some(LBind::Ir(_))) {
                        return Some((e, env));
                    }
                    let (params, body, base, def) = self.def_target(*d, &env)?;
                    if !params.is_empty() || def.is_some_and(|d| self.inline_stack.contains(&d)) {
                        return None;
                    }
                    (e, env) = (body, base);
                }
                H::Local(l) => match env.lookup(*l, &self.ip.prog) {
                    Some(LBind::Thunk(x, xenv)) => (e, env) = (x, xenv),
                    _ => return Some((e, env)),
                },
                _ => return Some((e, env)),
            }
        }
        None
    }
}

/// See `Lowerer::may_assign`.
fn may_assign_in(ip: &Interp, e: &hir::Expr, env: &LEnv, init: bool) -> bool {
    // Only statement positions can assign (as in TLC's enumeration): the
    // left side of `=`/`\in`/`\subseteq`, conjunctions, disjunctions,
    // quantifier/IF/CASE/LET bodies, the consequent of `=>` and operator
    // bodies. Everything else (function applications, right-hand sides,
    // comparisons, ...) is evaluated as a value.
    let rec = |x: &hir::Expr| may_assign_in(ip, x, env, init);
    match &*e.kind {
        H::Builtin { op: B::Eq | B::In | B::SubsetEq, args } => lhs_may_target(ip, &args[0], env, init),
        H::Builtin { op: B::Unchanged, .. } | H::BoxAction { .. } | H::AngleAction { .. } => true,
        H::Builtin { op: B::Implies, args } => rec(&args[1]),
        H::And(es) | H::Or(es) => es.iter().any(rec),
        H::Quant { body, .. } => rec(body),
        H::If { then, els, .. } => rec(then) || rec(els),
        H::Case { arms, other } => arms.iter().any(|(_, v)| rec(v)) || other.as_ref().is_some_and(rec),
        H::Let { body, .. } => rec(body),
        // In Next only action-level definitions can assign (they may
        // contain primes); in Init any definition might.
        H::Apply { op: OpRef::Def(d), .. } => init || ip.is_action_level(ip.redirect_def(*d)),
        H::Apply { op: OpRef::Const(_) | OpRef::Param(_), .. } => true,
        H::Local(x) => match env.lookup(*x, &ip.prog) {
            Some(LBind::Thunk(t, tenv)) => may_assign_in(ip, &t, &tenv, init),
            _ => false,
        },
        _ => false,
    }
}

/// Whether the left side of `=`/`\in`/`\subseteq` may denote a variable to
/// assign (primed in Next, unprimed in Init).
fn lhs_may_target(ip: &Interp, l: &hir::Expr, env: &LEnv, init: bool) -> bool {
    match &*l.kind {
        H::Builtin { op: B::Prime, .. } => !init,
        H::Var(_) => init,
        // A by-name parameter targets what its argument does; quantified
        // variables (unbound during this analysis) are values.
        H::Local(x) => match env.lookup(*x, &ip.prog) {
            Some(LBind::Thunk(t, tenv)) => lhs_may_target(ip, &t, &tenv, init),
            _ => false,
        },
        H::Apply { args, .. } => args.is_empty(),
        _ => false,
    }
}

/// Number of references to 0-ary definition `d` in `e`.
fn def_uses(e: &hir::Expr, d: hir::DefId) -> usize {
    let here = matches!(&*e.kind, H::Apply { op: OpRef::Def(x), args } if *x == d && args.is_empty()) as usize;
    let mut n = here;
    tlx_sema::visit::children(e, &mut |c| n += def_uses(c, d));
    n
}

/// Builtins whose value is nondeterministic or that have side effects:
/// never evaluated at compile time.
pub(super) fn is_volatile_builtin(op: B) -> bool {
    op.is_volatile()
}
