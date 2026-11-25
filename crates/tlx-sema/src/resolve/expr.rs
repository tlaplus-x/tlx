//! Resolution of expressions, binders and LET.
//!
//! Resolution keeps going after an error where possible (so that all errors
//! of an expression are reported); `Err(())` means at least one error was
//! recorded in `Program::errors`.

use tlx_front::ast::{self, Span};

use super::{err, DefSrc, DefState, DefUnit, Env, InstId, InstInfo, LocalBinding, Program};
use crate::hir::*;

/// The operands of conjunction (`is_and`) / disjunction `e`, with nested
/// conjunctions (disjunctions) spliced in.
fn flatten_junction(e: &ast::Expr, is_and: bool, out: &mut Vec<ast::Expr>) {
    match &*e.kind {
        ast::ExprKind::And(es) if is_and => es.iter().for_each(|x| flatten_junction(x, is_and, out)),
        ast::ExprKind::Or(es) if !is_and => es.iter().for_each(|x| flatten_junction(x, is_and, out)),
        _ => out.push(e.clone()),
    }
}

impl Program {
    /// Run `f` with the names it binds in `env` removed afterwards.
    pub(super) fn scoped<T>(&mut self, env: &mut Env, f: impl FnOnce(&mut Self, &mut Env) -> T) -> T {
        let mark = env.names.len();
        let r = f(self, env);
        env.names.truncate(mark);
        r
    }

    /// Resolve quantifier bounds and bind their variables. Sets are resolved in
    /// the outer scope; then all variables are bound.
    pub(super) fn bounds(&mut self, env: &mut Env, bs: &[ast::Bound]) -> Result<Vec<Bound>, ()> {
        let sets: Vec<_> = bs.iter().map(|b| self.expr(env, &b.set)).collect();
        let mut out = Vec::new();
        for (b, set) in bs.iter().zip(sets) {
            let vars = self.bind_vars(env, &b.vars);
            out.push(Bound { vars, set: set? });
        }
        Ok(out)
    }

    fn bind_vars(&mut self, env: &mut Env, vars: &ast::BoundVars) -> BoundVars {
        match vars {
            ast::BoundVars::Many(v) => BoundVars::Many(self.bind_names(env, v)),
            ast::BoundVars::Tuple(v) => BoundVars::Tuple(self.bind_names(env, v)),
        }
    }

    fn bind_names(&mut self, env: &mut Env, ids: &[ast::Ident]) -> Vec<LocalId> {
        ids.iter().map(|i| self.bind_name(env, i)).collect()
    }

    fn bind_name(&mut self, env: &mut Env, i: &ast::Ident) -> LocalId {
        let l = self.new_local(i.name.clone(), 0, i.span);
        env.names.push((i.name.clone(), LocalBinding::Local(l, 0)));
        l
    }

    /// Resolve the arguments `es` of an operator or instance application,
    /// marking position `i` as an operator-argument position (`env.in_arg`)
    /// only when its expected parameter arity `param_arities[i] > 0`.
    pub(super) fn arg_exprs_for(&mut self, env: &mut Env, es: &[ast::Expr], param_arities: &[usize]) -> Result<Vec<Expr>, ()> {
        let mut out = Vec::with_capacity(es.len());
        let mut ok = true;
        for (i, e) in es.iter().enumerate() {
            env.in_arg = param_arities.get(i).copied().unwrap_or(0) > 0;
            match self.expr(env, e) {
                Ok(x) => out.push(x),
                Err(()) => ok = false,
            }
        }
        env.in_arg = false;
        if ok {
            Ok(out)
        } else {
            Err(())
        }
    }

    /// Resolve all of `es` (reporting every error).
    pub(super) fn exprs(&mut self, env: &mut Env, es: &[ast::Expr]) -> Result<Vec<Expr>, ()> {
        let rs: Vec<_> = es.iter().map(|e| self.expr(env, e)).collect();
        rs.into_iter().collect()
    }

    pub(super) fn expr(&mut self, env: &mut Env, e: &ast::Expr) -> Result<Expr, ()> {
        use ast::ExprKind as A;
        let span = e.span;
        let in_arg = std::mem::replace(&mut env.in_arg, false);
        let k = match &*e.kind {
            A::Num(n) => ExprKind::Num(*n),
            A::Decimal(d) => ExprKind::Decimal(d.clone()),
            A::Str(s) => ExprKind::Str(s.clone()),
            A::Bool(b) => ExprKind::Bool(*b),
            A::OpAppl { prefix, name, args } => return self.op_appl(env, prefix, name, args, &[], in_arg, span),
            A::Subexpr { base, path } => {
                let A::OpAppl { prefix, name, args } = &*base.kind else {
                    return self.fail(base.span, "subexpression selector without a definition name");
                };
                return self.op_appl(env, prefix, name, args, path, in_arg, span);
            }
            // Labels have no meaning for evaluation.
            A::Label { body, .. } => return self.expr(env, body),
            A::Lambda { params, body } => {
                let (params, body) = self.scoped(env, |p, env| (p.bind_names(env, params), p.expr(env, body)));
                ExprKind::Lambda { params, body: body? }
            }
            // Nested conjunctions (disjunctions) are flattened.
            A::And(_) | A::Or(_) => {
                let is_and = matches!(&*e.kind, A::And(_));
                let mut flat = Vec::new();
                flatten_junction(e, is_and, &mut flat);
                let es = self.exprs(env, &flat)?;
                if is_and {
                    ExprKind::And(es)
                } else {
                    ExprKind::Or(es)
                }
            }
            A::Quant { kind, bounds, body } => self.scoped(env, |p, env| {
                let bounds = p.bounds(env, bounds)?;
                let body = p.expr(env, body)?;
                Ok(ExprKind::Quant { kind: *kind, bounds, body })
            })?,
            A::QuantUnbounded { kind, vars, body } => {
                let (vars, body) = self.scoped(env, |p, env| (p.bind_names(env, vars), p.expr(env, body)));
                ExprKind::QuantUnbounded { kind: *kind, vars, body: body? }
            }
            A::TemporalQuant { kind, vars, body } => {
                let (vars, body) = self.scoped(env, |p, env| (p.bind_names(env, vars), p.expr(env, body)));
                ExprKind::TemporalQuant { kind: *kind, vars, body: body? }
            }
            A::Choose { vars, set, body } => {
                let set = set.as_ref().map(|s| self.expr(env, s)).transpose()?;
                let (vars, body) = self.scoped(env, |p, env| (p.bind_vars(env, vars), p.expr(env, body)));
                ExprKind::Choose { vars, set, body: body? }
            }
            A::If { cond, then, els } => {
                let c = self.expr(env, cond);
                let t = self.expr(env, then);
                let el = self.expr(env, els);
                ExprKind::If { cond: c?, then: t?, els: el? }
            }
            A::Case { arms, other } => {
                let arms: Vec<_> = arms.iter().map(|(g, v)| (self.expr(env, g), self.expr(env, v))).collect();
                let other = other.as_ref().map(|o| self.expr(env, o)).transpose()?;
                let arms = arms.into_iter().map(|(g, v)| Ok((g?, v?))).collect::<Result<_, ()>>()?;
                ExprKind::Case { arms, other }
            }
            A::Let { defs, body } => return self.let_in(env, defs, body, span),
            A::SetEnum(es) => ExprKind::SetEnum(self.exprs(env, es)?),
            A::SetFilter { bound, pred } => self.scoped(env, |p, env| {
                let mut bs = p.bounds(env, std::slice::from_ref(bound))?;
                let pred = p.expr(env, pred)?;
                Ok(ExprKind::SetFilter { bound: bs.pop().unwrap(), pred })
            })?,
            A::SetMap { expr, bounds } => self.scoped(env, |p, env| {
                let bounds = p.bounds(env, bounds)?;
                let expr = p.expr(env, expr)?;
                Ok(ExprKind::SetMap { expr, bounds })
            })?,
            A::Tuple(es) => ExprKind::Tuple(self.exprs(env, es)?),
            A::FnConstruct { bounds, body } => self.scoped(env, |p, env| {
                let bounds = p.bounds(env, bounds)?;
                let body = p.expr(env, body)?;
                Ok(ExprKind::FnConstruct { bounds, body })
            })?,
            A::FnApp { func, args } => {
                let f = self.expr(env, func);
                let a = self.exprs(env, args);
                ExprKind::FnApp { func: f?, args: a? }
            }
            A::FnSet { domain, range } => {
                let d = self.expr(env, domain);
                let r = self.expr(env, range);
                ExprKind::FnSet { domain: d?, range: r? }
            }
            A::Record(fs) => ExprKind::Record(self.fields(env, fs)?),
            A::RecordSet(fs) => ExprKind::RecordSet(self.fields(env, fs)?),
            A::Field { record, field } => ExprKind::Field { record: self.expr(env, record)?, field: field.name.clone() },
            A::Except { base, updates } => return self.except(env, base, updates, span),
            A::At => {
                if !env.in_except {
                    return self.fail(span, "`@` used outside of an EXCEPT update");
                }
                ExprKind::At
            }
            A::BoxAction { action, sub } => {
                let a = self.expr(env, action);
                let s = self.expr(env, sub);
                ExprKind::BoxAction { action: a?, sub: s? }
            }
            A::AngleAction { action, sub } => {
                let a = self.expr(env, action);
                let s = self.expr(env, sub);
                ExprKind::AngleAction { action: a?, sub: s? }
            }
            A::Fairness { kind, sub, action } => {
                let s = self.expr(env, sub);
                let a = self.expr(env, action);
                // WF/SF are defined with ENABLED <<A>>_v: within an
                // instance, its primed variables are not substituted.
                let enabled = match self.enabled_ctx(env.ctx) {
                    Some(c) => {
                        let outer = std::mem::replace(&mut env.ctx, c);
                        let (a2, s2) = (self.expr(env, action), self.expr(env, sub));
                        env.ctx = outer;
                        Some(Expr::new(ExprKind::AngleAction { action: a2?, sub: s2? }, span))
                    }
                    None => None,
                };
                ExprKind::Fairness { kind: *kind, sub: s?, action: a?, enabled }
            }
        };
        Ok(Expr::new(k, span))
    }

    /// Record fields `[f |-> e, ...]` / `[f : S, ...]`.
    fn fields(&mut self, env: &mut Env, fs: &[(ast::Ident, ast::Expr)]) -> Result<Vec<(std::sync::Arc<str>, Expr)>, ()> {
        let rs: Vec<_> = fs.iter().map(|(n, v)| self.expr(env, v).map(|v| (n.name.clone(), v))).collect();
        rs.into_iter().collect()
    }

    fn except(&mut self, env: &mut Env, base: &ast::Expr, updates: &[(Vec<ast::ExceptKey>, ast::Expr)], span: Span) -> Result<Expr, ()> {
        let base = self.expr(env, base);
        let mut ups = Vec::new();
        let mut ok = true;
        for (path, val) in updates {
            let mut keys = Vec::new();
            for k in path {
                match k {
                    ast::ExceptKey::Field(f) => keys.push(ExceptKey::Field(f.name.clone())),
                    ast::ExceptKey::Index(ix) => match self.exprs(env, ix) {
                        Ok(ix) => keys.push(ExceptKey::Index(ix)),
                        Err(()) => ok = false,
                    },
                }
            }
            let saved = std::mem::replace(&mut env.in_except, true);
            let v = self.expr(env, val);
            env.in_except = saved;
            match v {
                Ok(v) => ups.push((keys, v)),
                Err(()) => ok = false,
            }
        }
        if !ok {
            return Err(());
        }
        Ok(Expr::new(ExprKind::Except { base: base?, updates: ups }, span))
    }

    fn let_in(&mut self, env: &mut Env, defs: &[ast::Unit], body: &ast::Expr, span: Span) -> Result<Expr, ()> {
        let mark = env.names.len();
        // Allocate all LET definitions first (they may be mutually recursive).
        let mut ids = Vec::new();
        for u in defs {
            let (name, dspan, unit) = match u {
                ast::Unit::OpDef(od) => (&od.name, od.span, DefUnit::Op(od.clone())),
                ast::Unit::FnDef(fd) => (&fd.name, fd.span, DefUnit::Fn(fd.clone())),
                ast::Unit::Recursive(_) => continue,
                ast::Unit::Instance(inst @ ast::Instance { name: Some(name), .. }) => {
                    // The substitutions can refer to the names bound around
                    // the LET (and to earlier LET definitions).
                    let id = InstId(self.insts.len());
                    let captured = Some(std::sync::Arc::new(env.names.clone()));
                    self.insts.push(InstInfo { ctx: env.ctx, module: env.module, ast: inst.clone(), target: None, captured });
                    env.names.push((name.name.clone(), LocalBinding::Instance(id)));
                    continue;
                }
                _ => {
                    self.errors.push(err(span, "unsupported definition kind in LET"));
                    continue;
                }
            };
            let src = DefSrc { ctx: env.ctx, module: env.module, unit, state: DefState::Local };
            let d = self.new_def(name.name.clone(), None, dspan, src);
            env.names.push((name.name.clone(), LocalBinding::LetDef(d)));
            ids.push(d);
        }
        let mut ok = true;
        for &d in &ids {
            let unit = self.def_src[d.idx()].unit.clone();
            ok &= self.fill_def(env, d, &unit, Vec::new()).is_ok();
        }
        let body = self.expr(env, body);
        env.names.truncate(mark);
        if !ok {
            return Err(());
        }
        Ok(Expr::new(ExprKind::Let { defs: ids, body: body? }, span))
    }
}
