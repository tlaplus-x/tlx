//! Operator applications: plain and instance-qualified names, and the
//! substitution of instantiated modules' declarations.

use std::sync::Arc;

use tlx_front::ast::{self, Span};

use super::{CtxId, DefSrc, DefState, DefUnit, Env, LocalBinding, ModIdx, Program, Sym, ROOT_CTX};
use crate::builtins::Builtin;
use crate::hir::*;

/// Whether `e` contains any `ExprKind::Let` (whose inner `DefId`s may capture
/// enclosing locals and therefore cannot be beta-reduced by `subst_locals`).
fn contains_let(e: &Expr) -> bool {
    if matches!(&*e.kind, ExprKind::Let { .. }) {
        return true;
    }
    let mut found = false;
    crate::visit::children(e, &mut |c| found = found || contains_let(c));
    found
}

impl Program {
    /// What an unqualified `name` denotes in `env`: a local binding (`Ok`) or a
    /// module-scope symbol (`Err`).
    fn lookup(&mut self, env: &Env, name: &str) -> Option<Result<LocalBinding, Sym>> {
        if let Some(b) = env.local(name) {
            return Some(Ok(b.clone()));
        }
        let sc = self.scope(env.ctx, env.module);
        self.scopes[sc].names.get(name).map(|s| Err(*s))
    }

    /// Resolve `prefix!name(args)` followed by subexpression selectors `path`.
    #[allow(clippy::too_many_arguments)] // the argument set of the hot-path/dispatch signature; a bundling struct would only rename them
    pub(super) fn op_appl(
        &mut self,
        env: &mut Env,
        prefix: &[ast::NamePrefix],
        name: &ast::Ident,
        args: &[ast::Expr],
        path: &[ast::Selector],
        op_arg: bool,
        span: Span,
    ) -> Result<Expr, ()> {
        if !prefix.is_empty() {
            return self.qualified_appl(env, prefix, name, args, path, op_arg, span);
        }
        // `ENABLED A` in an instance: A's primed variables of the
        // instantiated module are not substituted (see `enabled_ctx`).
        let found = self.lookup(env, &name.name);
        let fresh = match &*name.name {
            "ENABLED" if found.is_none() => self.enabled_ctx(env.ctx),
            _ => None,
        };
        let param_arities = match &found {
            Some(Ok(LocalBinding::LetDef(d))) | Some(Err(Sym::Def(d))) => self.def_param_arities(*d),
            _ => Vec::new(),
        };
        let args_r = match fresh {
            Some(c) => {
                let outer = std::mem::replace(&mut env.ctx, c);
                let r = self.arg_exprs_for(env, args, &param_arities);
                env.ctx = outer;
                r
            }
            None => self.arg_exprs_for(env, args, &param_arities),
        };
        if !path.is_empty() {
            // `D!sel`: select a subexpression of definition D.
            let d = match found {
                Some(Ok(LocalBinding::LetDef(d))) | Some(Err(Sym::Def(d))) => d,
                _ => return self.fail(span, format!("`{}` is not a definition (in a subexpression reference)", name.name)),
            };
            let mut args = args_r?;
            let (sd, extra) = self.select(env, d, path, op_arg && args.is_empty(), span)?;
            let sd_arities = self.def_param_arities(sd);
            let extra_arities = sd_arities.get(args.len()..).unwrap_or(&[]);
            args.extend(self.arg_exprs_for(env, &extra, extra_arities)?);
            return self.apply_def(env, sd, args, span);
        }
        match found {
            Some(Ok(LocalBinding::Local(l, arity))) => {
                let args = args_r?;
                if arity == 0 {
                    if !args.is_empty() {
                        return self.fail(span, format!("{} takes no arguments", name.name));
                    }
                    Ok(Expr::new(ExprKind::Local(l), span))
                } else {
                    if !args.is_empty() && args.len() != arity {
                        return self.fail(span, format!("`{}` expects {arity} argument(s), got {}", name.name, args.len()));
                    }
                    Ok(apply_op(OpRef::Param(l), args, span))
                }
            }
            Some(Ok(LocalBinding::LetDef(d))) => {
                let args = args_r?;
                self.apply_def(env, d, args, span)
            }
            Some(Ok(LocalBinding::Instance(_))) => self.fail(span, format!("instance `{}` used as an expression", name.name)),
            Some(Ok(LocalBinding::Value(v))) => {
                if !args_r?.is_empty() {
                    return self.fail(span, format!("{} takes no arguments", name.name));
                }
                Ok(v)
            }
            Some(Ok(LocalBinding::Op(op, arity))) => {
                let args = args_r?;
                self.apply_op_expr(op, &name.name, arity, args, env.ctx, env.module, span)
            }
            Some(Err(sym)) => {
                let args = args_r?;
                self.apply_sym(env, sym, &name.name, args, span)
            }
            None => {
                let args = args_r?;
                match Builtin::core(&name.name) {
                    Some(b) => self.apply_builtin(b, args, span),
                    None if matches!(&*name.name, "/\\" | "\\/") => {
                        // `/\` / `\/` as an operator (argument).
                        let is_and = &*name.name == "/\\";
                        let junction = |es| if is_and { ExprKind::And(es) } else { ExprKind::Or(es) };
                        if !args.is_empty() {
                            return Ok(Expr::new(junction(args), span));
                        }
                        let params: Vec<LocalId> = ["a", "b"].iter().map(|n| self.new_local((*n).into(), 0, span)).collect();
                        let refs = params.iter().map(|&l| Expr::new(ExprKind::Local(l), span)).collect();
                        let body = Expr::new(junction(refs), span);
                        Ok(Expr::new(ExprKind::Lambda { params, body }, span))
                    }
                    None => self.fail(span, format!("unknown identifier `{}`", name.name)),
                }
            }
        }
    }

    pub(super) fn apply_builtin(&mut self, b: Builtin, args: Vec<Expr>, span: Span) -> Result<Expr, ()> {
        let ar = b.arity();
        if args.is_empty() && ar > 0 {
            return Ok(Expr::new(ExprKind::OpArg(OpRef::Builtin(b)), span));
        }
        if ar >= 0 && args.len() != ar as usize {
            return self.fail(span, format!("`{}` expects {} argument(s), got {}", b.name(), ar, args.len()));
        }
        Ok(Expr::new(ExprKind::Builtin { op: b, args }, span))
    }

    /// Apply definition `d` from within `env` (passing on `env`'s instance params).
    fn apply_def(&mut self, env: &Env, d: DefId, args: Vec<Expr>, span: Span) -> Result<Expr, ()> {
        if let Some(b) = self.defs[d.idx()].builtin {
            if args.is_empty() && self.def_arity(d) > 0 {
                return Ok(Expr::new(ExprKind::OpArg(OpRef::Builtin(b)), span));
            }
            return self.apply_builtin(b, args, span);
        }
        let inst_args = env.inst_args.clone();
        self.apply_user_def(d, inst_args, args, span)
    }

    /// Apply definition `d` (or subexpression `path` of it) reached through an
    /// instance path; `inst_args` are the arguments of the innermost instance
    /// context's params.
    #[allow(clippy::too_many_arguments)] // the argument set of the hot-path/dispatch signature; a bundling struct would only rename them
    fn apply_qualified_def(
        &mut self,
        env: &mut Env,
        d: DefId,
        inst_args: Vec<Expr>,
        args: Vec<Expr>,
        path: &[ast::Selector],
        op_arg: bool,
        span: Span,
    ) -> Result<Expr, ()> {
        let (d, extra) = self.select(env, d, path, op_arg && args.is_empty(), span)?;
        let mut args = args;
        let sd_arities = self.def_param_arities(d);
        let extra_arities = sd_arities.get(args.len()..).unwrap_or(&[]);
        args.extend(self.arg_exprs_for(env, &extra, extra_arities)?);
        if let Some(b) = self.defs[d.idx()].builtin {
            return self.apply_builtin(b, args, span);
        }
        self.apply_user_def(d, inst_args, args, span)
    }

    /// Apply a non-builtin definition. `inst_args` start with the values of
    /// `d`'s instance params (extra trailing ones are dropped).
    fn apply_user_def(&mut self, d: DefId, mut inst_args: Vec<Expr>, args: Vec<Expr>, span: Span) -> Result<Expr, ()> {
        self.enqueue(d);
        let arity = self.def_arity(d);
        let n = self.def_inst[d.idx()];
        if args.is_empty() && arity > 0 {
            if n > 0 {
                // `I(x)!Op` as an argument: `LAMBDA p1, ..., pk : I(x)!Op(p1, ..., pk)`.
                let arities = self.def_param_arities(d);
                let params: Vec<LocalId> =
                    arities.iter().enumerate().map(|(i, &a)| self.new_local(format!("p{}", i + 1).into(), a, span)).collect();
                inst_args.truncate(n);
                inst_args.extend(params.iter().map(|&l| self.local_ref(l, span)));
                let body = Expr::new(ExprKind::Apply { op: OpRef::Def(d), args: inst_args }, span);
                return Ok(Expr::new(ExprKind::Lambda { params, body }, span));
            }
            return Ok(Expr::new(ExprKind::OpArg(OpRef::Def(d)), span));
        }
        if args.len() != arity {
            let name = self.defs[d.idx()].name.clone();
            return self.fail(span, format!("`{name}` expects {arity} argument(s), got {}", args.len()));
        }
        let own_arities = self.def_param_arities(d);
        let dname = self.defs[d.idx()].name.clone();
        for (i, (&param_arity, arg)) in own_arities.iter().zip(&args).enumerate() {
            self.check_param_arg(&dname, i + 1, param_arity, arg)?;
        }
        debug_assert!(inst_args.len() >= n, "missing instance arguments for `{}`", self.defs[d.idx()].name);
        inst_args.truncate(n);
        inst_args.extend(args);
        Ok(Expr::new(ExprKind::Apply { op: OpRef::Def(d), args: inst_args }, span))
    }

    fn apply_sym(&mut self, env: &mut Env, sym: Sym, name: &str, args: Vec<Expr>, span: Span) -> Result<Expr, ()> {
        match sym {
            Sym::Var(v) => {
                if !args.is_empty() {
                    return self.fail(span, format!("variable `{name}` applied to arguments"));
                }
                Ok(Expr::new(ExprKind::Var(v), span))
            }
            Sym::Const(c) => {
                if self.consts[c.idx()].arity == 0 {
                    if !args.is_empty() {
                        return self.fail(span, format!("constant `{name}` applied to arguments"));
                    }
                    Ok(Expr::new(ExprKind::Const(c), span))
                } else {
                    Ok(apply_op(OpRef::Const(c), args, span))
                }
            }
            Sym::Def(d) => self.apply_def(env, d, args, span),
            Sym::Decl { ctx, arity, var } => {
                let n = self.ctxs[ctx].inst_params.len();
                if env.inst_args.len() < n {
                    return self.fail(span, "internal: instance parameter mismatch");
                }
                let vals = env.inst_args[..n].to_vec();
                let subst = self.substitute(ctx, &vals, name, arity, var, args, span)?;
                if var && self.ctxs[ctx].copy_of.is_some() {
                    let slot = self.inst_var_slot(ctx, name, span);
                    return Ok(Expr::new(ExprKind::InstVar { slot, subst }, span));
                }
                Ok(subst)
            }
            Sym::Instance(_) => self.fail(span, format!("instance `{name}` used as an expression")),
        }
    }

    /// Replace a reference to declaration `name` of instance context `ctx` by
    /// its substitution, resolved in the instantiating module.
    /// `inst_vals` are the values of all of `ctx`'s instance params as seen
    /// from the reference site.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn substitute(
        &mut self,
        ctx: CtxId,
        inst_vals: &[Expr],
        name: &str,
        arity: usize,
        var: bool,
        args: Vec<Expr>,
        span: Span,
    ) -> Result<Expr, ()> {
        let (outer_ctx, outer_mod, outer_inst, target, sub, captured) = {
            let s = self.ctxs[ctx].subst.as_ref().expect("Decl only exists in instance contexts");
            (s.outer_ctx, s.outer_mod, s.outer_inst, s.target, s.explicit.get(name).cloned(), s.captured.clone())
        };
        if inst_vals.len() != self.ctxs[ctx].inst_params.len() {
            return self.fail(span, "internal: instance parameter mismatch");
        }
        let max_level = if var {
            Some(1)
        } else if !self.is_constant_module(target, &mut Vec::new()) {
            Some(0)
        } else {
            None
        };
        // The substitution sees the outer context's instance params (resolved
        // expressions: locals, operator params, or concrete arguments)...
        let mut senv = Env::new(outer_ctx, outer_mod);
        // ... the names bound around a LET INSTANCE ...
        if let Some(cap) = &captured {
            senv.names = cap.to_vec();
            senv.captured = senv.names.len();
        }
        senv.inst_args = inst_vals[..outer_inst].to_vec();
        // ... and the instance's own params by name.
        let own_params: Vec<(Arc<str>, usize)> = self.ctxs[ctx].inst_params[outer_inst..].to_vec();
        for ((n, a), v) in own_params.into_iter().zip(&inst_vals[outer_inst..]) {
            let b = match &*v.kind {
                ExprKind::Local(l) if a == 0 => LocalBinding::Local(*l, 0),
                ExprKind::OpArg(OpRef::Param(l)) if a > 0 => LocalBinding::Local(*l, a),
                _ if a == 0 => LocalBinding::Value(v.clone()),
                ExprKind::OpArg(_) | ExprKind::Lambda { .. } => LocalBinding::Op(v.clone(), a),
                _ => return self.fail(span, format!("An operator of arity {a} is required.")),
            };
            senv.names.push((n, b));
        }
        // Without an explicit `WITH name <- e`, the substitution is `name <- name`.
        let sub = sub.unwrap_or_else(|| ast::Expr {
            kind: Box::new(ast::ExprKind::OpAppl { prefix: Vec::new(), name: ast::Ident { name: name.into(), span }, args: Vec::new() }),
            span,
        });
        if arity == 0 {
            if !args.is_empty() {
                return self.fail(span, format!("`{name}` applied to arguments"));
            }
            let r = self.expr(&mut senv, &sub);
            if senv.used_capture.get() {
                self.ctxs[ctx].uses_capture = true;
            }
            if let (Ok(e), Some(max), Some(&d)) = (&r, max_level, self.resolving_def.last()) {
                self.def_subst_bounds[d.idx()].push((e.clone(), max));
            }
            return r;
        }
        // Operator declaration: the substitution must denote an operator.
        senv.in_arg = true;
        let op = self.expr(&mut senv, &sub);
        if senv.used_capture.get() {
            self.ctxs[ctx].uses_capture = true;
        }
        let op = op?;
        if let (Some(max), Some(&d)) = (max_level, self.resolving_def.last()) {
            self.def_subst_bounds[d.idx()].push((op.clone(), max));
        }
        self.apply_op_expr(op, name, arity, args, outer_ctx, outer_mod, span)
    }

    /// Arity of an `OpRef`, or `None` for variadic built-ins.
    fn op_ref_arity(&self, r: OpRef) -> Option<usize> {
        match r {
            OpRef::Def(d) => Some(self.def_inst[d.idx()] + self.def_arity(d)),
            OpRef::Const(c) => Some(self.consts[c.idx()].arity),
            OpRef::Param(l) => Some(self.locals[l.idx()].arity),
            OpRef::Builtin(b) => usize::try_from(b.arity()).ok(),
        }
    }

    /// Whether definition `d` declares any higher-order operator parameter
    /// (among its instance parameters or its own parameters).
    fn def_has_op_param(&self, d: DefId) -> bool {
        let ctx = self.def_src[d.idx()].ctx;
        let inst_ho = self.def_inst[d.idx()] > 0 && self.ctxs[ctx].inst_params.iter().any(|(_, a)| *a > 0);
        let own_ho = match &self.def_src[d.idx()].unit {
            DefUnit::Op(o) => o.params.iter().any(|p| p.arity > 0),
            DefUnit::Fn(_) => false,
        };
        inst_ho || own_ho
    }

    /// Check that resolved argument `arg` matches the declared arity of an
    /// operator or instance parameter (`0` for a value expression, `> 0` for an operator).
    fn check_param_arg(&mut self, op_name: &str, pos: usize, expected_arity: usize, arg: &Expr) -> Result<(), ()> {
        if expected_arity == 0 {
            return match &*arg.kind {
                ExprKind::Lambda { .. } => self.fail(arg.span, "LAMBDA expression used where an expression is required."),
                ExprKind::OpArg(_) => self.fail(arg.span, format!("An expression is required for argument {pos} of `{op_name}`.")),
                _ => Ok(()),
            };
        }
        match &*arg.kind {
            ExprKind::Lambda { params, .. } => {
                if params.len() != expected_arity {
                    return self.fail(arg.span, format!("Expected arity {expected_arity} but found operator of arity {}.", params.len()));
                }
                if params.iter().any(|l| self.locals[l.idx()].arity > 0) {
                    return self.fail(
                        arg.span,
                        format!("Argument number {pos} to operator '{op_name}' \nshould be a {expected_arity}-parameter operator."),
                    );
                }
                Ok(())
            }
            ExprKind::OpArg(r) => {
                if let Some(actual) = self.op_ref_arity(*r) {
                    if actual != expected_arity {
                        return self.fail(arg.span, format!("Expected arity {expected_arity} but found operator of arity {actual}."));
                    }
                }
                if let OpRef::Def(d) = *r {
                    if self.def_has_op_param(d) {
                        return self.fail(
                            arg.span,
                            format!("Argument number {pos} to operator '{op_name}' \nshould be a {expected_arity}-parameter operator."),
                        );
                    }
                }
                Ok(())
            }
            _ => self.fail(arg.span, format!("An operator of arity {expected_arity} is required.")),
        }
    }

    /// Apply a resolved operator expression (`OpArg` or `Lambda`) to `args`,
    /// or return it as an operator argument when `args` is empty.
    #[allow(clippy::too_many_arguments)]
    fn apply_op_expr(
        &mut self,
        op: Expr,
        name: &str,
        expected_arity: usize,
        args: Vec<Expr>,
        ctx: CtxId,
        module: ModIdx,
        span: Span,
    ) -> Result<Expr, ()> {
        match (*op.kind).clone() {
            ExprKind::OpArg(r) => {
                if expected_arity > 0 {
                    if let Some(actual) = self.op_ref_arity(r) {
                        if actual != expected_arity {
                            return self.fail(span, format!("Expected arity {expected_arity} but found operator of arity {actual}."));
                        }
                    }
                }
                if args.is_empty() {
                    return Ok(Expr::new(ExprKind::OpArg(r), span));
                }
                if expected_arity > 0 && args.len() != expected_arity {
                    return self.fail(span, format!("`{name}` expects {expected_arity} argument(s), got {}", args.len()));
                }
                match r {
                    OpRef::Builtin(b) => self.apply_builtin(b, args, span),
                    _ => Ok(Expr::new(ExprKind::Apply { op: r, args }, span)),
                }
            }
            ExprKind::Lambda { params, mut body } => {
                if expected_arity > 0 && params.len() != expected_arity {
                    return self.fail(span, format!("Expected arity {expected_arity} but found operator of arity {}.", params.len()));
                }
                if args.is_empty() {
                    return Ok(Expr::new(ExprKind::Lambda { params, body }, span));
                }
                if args.len() != params.len() {
                    return self.fail(span, format!("`{name}` expects {} argument(s), got {}", params.len(), args.len()));
                }
                if contains_let(&body) {
                    // Inner LET definitions may reference `params`, so bind
                    // them via a local synthetic definition rather than
                    // beta-reducing past the LET boundary.
                    let ast_params = params
                        .iter()
                        .map(|&l| ast::OpDecl {
                            name: ast::Ident { name: self.locals[l.idx()].name.clone(), span },
                            arity: self.locals[l.idx()].arity,
                        })
                        .collect();
                    let unit = DefUnit::Op(ast::OpDef {
                        name: ast::Ident { name: Arc::from("$lambda"), span },
                        params: ast_params,
                        body: ast::Expr { kind: Box::new(ast::ExprKind::Bool(false)), span },
                        local: true,
                        span,
                    });
                    let src = DefSrc { ctx, module, unit, state: DefState::Local };
                    let d = self.new_def(Arc::from("$lambda"), None, span, src);
                    self.defs[d.idx()].params = params;
                    self.defs[d.idx()].kind = DefKind::Op(body);
                    let call = Expr::new(ExprKind::Apply { op: OpRef::Def(d), args }, span);
                    return Ok(Expr::new(ExprKind::Let { defs: vec![d], body: call }, span));
                }
                // Beta-reduce.
                let map = params.into_iter().zip(args).collect();
                crate::visit::subst_locals(&mut body, &map);
                Ok(body)
            }
            _ => self.fail(span, format!("substitution for operator `{name}` is not an operator")),
        }
    }

    /// Declared parameter arities of definition `d` (excluding instance params).
    fn def_param_arities(&self, d: DefId) -> Vec<usize> {
        match &self.def_src[d.idx()].unit {
            DefUnit::Op(o) => o.params.iter().map(|p| p.arity).collect(),
            DefUnit::Fn(_) => Vec::new(),
        }
    }

    /// Lower a bare qualified operator argument (such as `S!Read`, `S!Pair`, or
    /// `S!Read!HERE`) using the full public signature collected from the
    /// instance prefix (`path_locals`) followed by `d`'s own parameters.
    /// `inst_args` already holds the runtime instance arguments for `d`'s
    /// context (referencing `path_locals` for unapplied prefix parameters, plus
    /// any outer enclosing instance arguments).
    fn bare_qualified_op(&mut self, d: DefId, mut inst_args: Vec<Expr>, path_locals: Vec<LocalId>, span: Span) -> Result<Expr, ()> {
        let own_arities = self.def_param_arities(d);
        if path_locals.is_empty() && own_arities.is_empty() {
            if let Some(b) = self.defs[d.idx()].builtin {
                return self.apply_builtin(b, Vec::new(), span);
            }
            return self.apply_user_def(d, inst_args, Vec::new(), span);
        }
        if let Some(b) = self.defs[d.idx()].builtin {
            if path_locals.is_empty() {
                return self.apply_builtin(b, Vec::new(), span);
            }
            let own_params: Vec<LocalId> = own_arities
                .iter()
                .enumerate()
                .map(|(i, &a)| self.new_local(format!("p{}", path_locals.len() + i + 1).into(), a, span))
                .collect();
            let own_refs: Vec<Expr> = own_params.iter().map(|&l| self.local_ref(l, span)).collect();
            let mut params = path_locals;
            params.extend(own_params);
            let body = self.apply_builtin(b, own_refs, span)?;
            return Ok(Expr::new(ExprKind::Lambda { params, body }, span));
        }
        self.enqueue(d);
        let n = self.def_inst[d.idx()];
        // Fast path: when `d`'s runtime instance arguments match `path_locals`
        // 1-to-1 (no outer captured args, no dropped prefix params),
        // `OpArg(Def(d))` already has the exact public signature.
        let direct = n == path_locals.len()
            && inst_args.len() >= n
            && inst_args[..n].iter().zip(&path_locals).all(|(a, &l)| match &*a.kind {
                ExprKind::Local(id) | ExprKind::OpArg(OpRef::Param(id)) => *id == l,
                _ => false,
            });
        if direct {
            return Ok(Expr::new(ExprKind::OpArg(OpRef::Def(d)), span));
        }
        // Otherwise emit a lambda over the full public signature (`path_locals`
        // followed by `d`'s own parameters) and forward only the leading
        // instance arguments `d` actually consumes (e.g. 0 for a definition
        // inherited from a declaration-free extended module in `ROOT_CTX`, or
        // only the inner prefix's parameters when an outer prefix was in
        // `ROOT_CTX`).
        let own_params: Vec<LocalId> = own_arities
            .iter()
            .enumerate()
            .map(|(i, &a)| self.new_local(format!("p{}", path_locals.len() + i + 1).into(), a, span))
            .collect();
        let own_refs: Vec<Expr> = own_params.iter().map(|&l| self.local_ref(l, span)).collect();
        debug_assert!(inst_args.len() >= n, "missing instance arguments for `{}`", self.defs[d.idx()].name);
        inst_args.truncate(n);
        inst_args.extend(own_refs);
        let mut params = path_locals;
        params.extend(own_params);
        let body = Expr::new(ExprKind::Apply { op: OpRef::Def(d), args: inst_args }, span);
        Ok(Expr::new(ExprKind::Lambda { params, body }, span))
    }

    /// Resolve `I1(a1)!...!In(an)!name(args)` (plus selectors `path`).
    #[allow(clippy::too_many_arguments)] // the argument set of the hot-path/dispatch signature; a bundling struct would only rename them
    fn qualified_appl(
        &mut self,
        env: &mut Env,
        prefix: &[ast::NamePrefix],
        name: &ast::Ident,
        args: &[ast::Expr],
        path: &[ast::Selector],
        op_arg: bool,
        span: Span,
    ) -> Result<Expr, ()> {
        let path_has_args = path.iter().any(|s| matches!(s, ast::Selector::Args(a) | ast::Selector::Label(_, a) if !a.is_empty()));
        let bare_op_arg = op_arg && args.is_empty() && !path_has_args && prefix.iter().all(|p| p.args.is_empty());
        // Walk the instance path, collecting instance arguments (or, for a bare
        // qualified operator argument such as `S!Read`, `S!Pair`, or
        // `S!Read!HERE`, binding fresh locals for the unapplied prefix formals
        // in order and routing them through the exact same context transitions).
        let mut inst_args = env.inst_args.clone();
        let mut path_locals: Vec<LocalId> = Vec::new();
        let (mut ctx, mut module) = (env.ctx, env.module);
        for (pi, p) in prefix.iter().enumerate() {
            // Only the first component can be a LET-bound name.
            let local = if pi == 0 { env.local(&p.name.name).cloned() } else { None };
            let found = match local {
                Some(LocalBinding::Instance(iid)) => Ok(iid),
                Some(LocalBinding::LetDef(d)) => Err(Some(d)),
                Some(_) => Err(None),
                None => {
                    let sc = self.scope(ctx, module);
                    match self.scopes[sc].names.get(&p.name.name).copied() {
                        Some(Sym::Instance(iid)) => Ok(iid),
                        Some(Sym::Def(d)) => Err(Some(d)),
                        _ => Err(None),
                    }
                }
            };
            let iid = match found {
                Ok(iid) => iid,
                Err(Some(d)) => {
                    // `D(a)!lab1!lab2...`: the remaining names are labels in D.
                    let last = ast::NamePrefix { name: name.clone(), args: args.to_vec() };
                    let mut sels: Vec<ast::Selector> = Vec::new();
                    for q in prefix[pi + 1..].iter().chain(std::iter::once(&last)) {
                        sels.push(ast::Selector::Label(q.name.clone(), q.args.clone()));
                    }
                    sels.extend(path.iter().cloned());
                    let d = if pi > 0 { self.qualified_def(d) } else { d };
                    if bare_op_arg {
                        let (sd, _) = self.select(env, d, &sels, true, span)?;
                        return self.bare_qualified_op(sd, inst_args, path_locals, span);
                    }
                    let d_arities = self.def_param_arities(d);
                    let a = self.arg_exprs_for(env, &p.args, &d_arities)?;
                    if a.is_empty() && sels.iter().all(|s| matches!(s, ast::Selector::Label(_, sa) if sa.is_empty())) {
                        if let Some(sel) = prefix[..pi].iter().find(|q| !q.args.is_empty()) {
                            let (sd, _) = self.select(env, d, &sels, op_arg, span)?;
                            if self.def_arity(sd) > 0 {
                                return self.fail(sel.name.span, format!("Selector `{}' should not have argument(s).", sel.name.name));
                            }
                        }
                    }
                    return self.apply_qualified_def(env, d, inst_args, a, &sels, op_arg, span);
                }
                Err(None) => return self.fail(p.name.span, format!("`{}` is not a module instance", p.name.name)),
            };
            let Some((c, m)) = self.named_instance(iid) else { return Err(()) };
            let params: Vec<usize> = self.insts[iid.0].ast.params.iter().map(|pr| pr.arity).collect();
            let keep = self.ctxs[self.insts[iid.0].ctx].inst_params.len();
            let a = if bare_op_arg {
                let locals: Vec<LocalId> = params
                    .iter()
                    .map(|&arity| {
                        let idx = path_locals.len() + 1;
                        let l = self.new_local(format!("p{idx}").into(), arity, span);
                        path_locals.push(l);
                        l
                    })
                    .collect();
                locals.into_iter().map(|l| self.local_ref(l, span)).collect()
            } else {
                if p.args.len() != params.len() {
                    return self.fail(p.name.span, format!("instance `{}` expects {} argument(s)", p.name.name, params.len()));
                }
                let a = self.arg_exprs_for(env, &p.args, &params)?;
                for (i, (&arity, arg)) in params.iter().zip(&a).enumerate() {
                    self.check_param_arg(&p.name.name, i + 1, arity, arg)?;
                }
                a
            };
            // Arguments for the new context: those of the context the instance was declared in, plus `a`.
            inst_args.truncate(keep);
            inst_args.extend(a);
            if c == ROOT_CTX {
                inst_args.clear();
            }
            ctx = c;
            module = m;
        }
        let sc = self.scope(ctx, module);
        let Some(sym) = self.scopes[sc].names.get(&name.name).copied() else {
            return self.fail(name.span, format!("unknown identifier `{}` in instance", name.name));
        };
        if !path.is_empty() && !matches!(sym, Sym::Def(_)) {
            return self.fail(name.span, format!("`{}` is not a definition (in a subexpression reference)", name.name));
        }
        let arg_arities = match sym {
            Sym::Def(d) => self.def_param_arities(d),
            _ => Vec::new(),
        };
        let args = self.arg_exprs_for(env, args, &arg_arities)?;
        match sym {
            Sym::Def(d) => {
                let d = self.qualified_def(d);
                if bare_op_arg {
                    let (sd, _) = self.select(env, d, path, true, span)?;
                    return self.bare_qualified_op(sd, inst_args, path_locals, span);
                }
                // SANY rejects selector arguments on a qualified operator name
                // used without its own arguments (e.g. `S(1)!Pair` as an operator).
                if path.is_empty() && args.is_empty() && self.def_arity(d) > 0 {
                    if let Some(sel) = prefix.iter().find(|p| !p.args.is_empty()) {
                        return self.fail(sel.name.span, format!("Selector `{}' should not have argument(s).", sel.name.name));
                    }
                }
                self.apply_qualified_def(env, d, inst_args, args, path, op_arg, span)
            }
            Sym::Decl { .. } => {
                // `I!x`: INSTANCE does not import the declarations (SANY).
                let mut full: Vec<&str> = prefix.iter().map(|p| &*p.name.name).collect();
                full.push(&name.name);
                self.fail(span, format!("Unknown operator: `{}'.", full.join("!")))
            }
            other => self.apply_sym(env, other, &name.name, args, span),
        }
    }
}

/// Application of an operator-valued callee; an operator argument if `args`
/// is empty.
fn apply_op(op: OpRef, args: Vec<Expr>, span: Span) -> Expr {
    if args.is_empty() {
        Expr::new(ExprKind::OpArg(op), span)
    } else {
        Expr::new(ExprKind::Apply { op, args }, span)
    }
}
