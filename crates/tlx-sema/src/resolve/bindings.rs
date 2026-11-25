//! Scoped binding-form handlers for name resolution and level inference.
//!
//! `names::Checker` (SANY's scoping/arity pass over the surface AST) and
//! `level::Checker` (SANY's level inference over the resolved HIR) both
//! dispatch `expr` over the same family of constructs that bind variables in
//! a nested scope: labels, `LAMBDA`, the quantifiers, `CHOOSE`, set filter and
//! set map, the function constructor and `LET`. The `expr` matches stay in
//! their own modules and call a handler here for each such form, so every arm
//! is still selected at the same position in the same order and every error is
//! still reported from the same point; only the handler body moved.
//!
//! The primitives the handlers share with the rest of their module
//! (`bind_param`, `bounds`, `def_body`, `label`, `binder`, ...) stay there, so
//! this file holds no state of its own.

use std::sync::Arc;

use tlx_front::ast;

use crate::hir::*;

use super::level::{Info, ACTION, TEMPORAL};
use super::names::{bound_vars, fn_def_entry, instance_entry, op_def_entry, pos, simple_entry, Entry, Kind, NameScope, Origin};

impl super::names::Checker<'_> {
    /// `label(params):: body`: the parameters of labels inside are the
    /// identifiers bound inside this one.
    pub(super) fn label_form(&mut self, sc: &mut NameScope, name: &ast::Ident, params: &[ast::Ident], body: &ast::Expr) {
        self.label(sc, name, params);
        let saved = std::mem::replace(&mut self.label_mark, sc.locals.len());
        self.label_levels.push(Vec::new());
        self.expr(sc, body);
        self.label_levels.pop();
        self.label_mark = saved;
    }

    /// `LAMBDA params: body`: the parameters are bound in the body.
    pub(super) fn lambda_form(&mut self, sc: &mut NameScope, params: &[ast::Ident], body: &ast::Expr) {
        for p in params {
            self.bind_param(sc, p, 0);
        }
        let m = sc.locals.len();
        self.def_body(sc, body, m);
    }

    /// Bound-variable forms that share `[x \in S, y \in T]` bounds:
    /// `\A x \in S : P`, `\E x \in S : P` and `[x \in S |-> e]`.
    pub(super) fn bounded_form(&mut self, sc: &mut NameScope, bounds: &[ast::Bound], body: &ast::Expr) {
        self.bounds(sc, bounds);
        self.expr(sc, body);
    }

    /// Unbounded quantifiers `\A x : P` / `\E x : P`, and their temporal
    /// `\AA x : P` / `\EE x : P` forms.
    pub(super) fn unbounded_form(&mut self, sc: &mut NameScope, vars: &[ast::Ident], body: &ast::Expr) {
        for v in vars {
            self.bind_param(sc, v, 0);
        }
        self.expr(sc, body);
    }

    /// `CHOOSE x \in S : P` (unbounded when `set` is `None`): the set is an
    /// outer expression, the bound variables are in scope only in the body.
    pub(super) fn choose_form(&mut self, sc: &mut NameScope, vars: &ast::BoundVars, set: &Option<ast::Expr>, body: &ast::Expr) {
        if let Some(s) = set {
            self.expr(sc, s);
        }
        for v in bound_vars(vars) {
            self.bind_param(sc, v, 0);
        }
        self.expr(sc, body);
    }

    /// `LET defs IN body`: the definitions are bound before the body and see
    /// one another SANY's way (RECURSIVE declarations, LET instances).
    pub(super) fn let_form(&mut self, sc: &mut NameScope, defs: &[ast::Unit], body: &ast::Expr) {
        let mname = self.mod_name(self.cur_mod);
        let mut pending: Vec<(Arc<str>, Span)> = Vec::new();
        for (k, d) in defs.iter().enumerate() {
            match d {
                ast::Unit::Recursive(ds) => {
                    for d in ds {
                        let e = Entry {
                            origin: Origin::Recursive(self.cur_mod, usize::MAX, k),
                            ..simple_entry(Kind::Op, d.arity, d.name.span, Origin::Local, &mname)
                        };
                        self.bind_own(sc, &d.name.name, e, true);
                        pending.push((d.name.name.clone(), d.name.span));
                    }
                }
                ast::Unit::OpDef(od) => {
                    self.op_def(sc, od);
                    self.bind_own(sc, &od.name.name, op_def_entry(od, Origin::Local, &mname), true);
                    pending.retain(|(n, _)| *n != od.name.name);
                }
                ast::Unit::FnDef(fd) => {
                    self.bind_own(sc, &fd.name.name, fn_def_entry(fd, Origin::Local, &mname), true);
                    pending.retain(|(n, _)| *n != fd.name.name);
                    self.fn_def(sc, fd);
                }
                ast::Unit::Instance(inst) => {
                    let m = self.cur_mod;
                    // SANY quirk: instantiating a nested module in a LET
                    // registers the module a second time.
                    if let Some(t) = self.instance_target(m, inst).filter(|&t| self.p.mods[t].parent.is_some()) {
                        let at = self.p.mods[t].ast.span;
                        let msg = format!(
                            "Multiply-defined module '{}': this definition or declaration conflicts \nwith the one at {}.",
                            inst.module.name,
                            pos(at, &self.p.mods[t].name)
                        );
                        self.error(inst.module.span, msg);
                    }
                    self.instance(sc, m, inst);
                    if let Some(n) = &inst.name {
                        let e = instance_entry(inst, n.span, Origin::Local, &mname);
                        self.bind_own(sc, &n.name, e, true);
                    }
                }
                _ => {}
            }
        }
        for (n, span) in pending {
            self.error(span, format!("Symbol {n} declared in RECURSIVE statement but not defined."));
        }
        self.expr(sc, body);
    }

    /// `{x \in S : P}`.
    pub(super) fn set_filter_form(&mut self, sc: &mut NameScope, bound: &ast::Bound, pred: &ast::Expr) {
        self.bounds(sc, std::slice::from_ref(bound));
        self.expr(sc, pred);
    }

    /// `{e : x \in S, y \in T}`.
    pub(super) fn set_map_form(&mut self, sc: &mut NameScope, expr: &ast::Expr, bounds: &[ast::Bound]) {
        self.bounds(sc, bounds);
        self.expr(sc, expr);
    }
}

impl super::level::Checker<'_> {
    /// `\A x \in S : P` / `\E x \in S : P`.
    pub(super) fn bounded_quant_level(&mut self, kind: QuantKind, bounds: &[Bound], body: &Expr, span: Span) -> Info {
        let name = if kind == QuantKind::Exists { "$BoundedExists" } else { "$BoundedForall" };
        self.binder(name, bounds, body, TEMPORAL, false, span)
    }

    /// `\AA x : P` / `\EE x : P`: temporal, and its body's constraints carry.
    pub(super) fn temporal_quant_level(&mut self, body: &Expr) -> Info {
        let bi = self.expr(body);
        let mut out = Info::at(TEMPORAL);
        out.constraints(&bi);
        out
    }

    /// `CHOOSE x \in S : P` / `CHOOSE x : P`.
    pub(super) fn choose_level(&mut self, vars: &BoundVars, set: &Option<Expr>, body: &Expr, span: Span) -> Info {
        match set {
            Some(s) => {
                let b = Bound { vars: vars.clone(), set: s.clone() };
                self.binder("$BoundedChoose", std::slice::from_ref(&b), body, ACTION, true, span)
            }
            None => self.binder("$UnboundedChoose", &[], body, ACTION, true, span),
        }
    }

    /// `{x \in S : P}`.
    pub(super) fn set_filter_level(&mut self, bound: &Bound, pred: &Expr, span: Span) -> Info {
        self.binder("$SubsetOf", std::slice::from_ref(bound), pred, ACTION, true, span)
    }

    /// `{e : x \in S, y \in T}`.
    pub(super) fn set_map_level(&mut self, expr: &Expr, bounds: &[Bound], span: Span) -> Info {
        self.binder("$SetOfAll", bounds, expr, ACTION, true, span)
    }

    /// `[x \in S |-> e]`.
    pub(super) fn fn_construct_level(&mut self, bounds: &[Bound], body: &Expr, span: Span) -> Info {
        self.binder("$FcnConstructor", bounds, body, TEMPORAL, true, span)
    }

    /// `LET defs IN body`: every definition is summarized, then the body.
    pub(super) fn let_level(&mut self, defs: &[DefId], body: &Expr) -> Info {
        for d in defs {
            self.summary(*d);
        }
        self.expr(body)
    }
}
