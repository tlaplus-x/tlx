//! Module scopes (computed per (context, module)) and instance contexts.

use std::collections::HashMap;
use std::sync::Arc;

use tlx_front::ast::{self, Span};

use super::{Ctx, CtxId, DefSrc, DefState, DefUnit, InstId, InstInfo, ModIdx, Program, Scope, ScopeId, SubstInfo, Sym, ROOT_CTX};
use crate::builtins::Builtin;
use crate::hir::*;

/// A scope under construction.
#[derive(Default)]
struct ScopeBuilder {
    names: HashMap<Arc<str>, Sym>,
    exports: HashMap<Arc<str>, Sym>,
}

impl ScopeBuilder {
    /// Bind `name` in the scope, and also export it unless `local`.
    fn bind(&mut self, name: &Arc<str>, sym: Sym, local: bool) {
        self.names.insert(name.clone(), sym);
        if !local {
            self.exports.insert(name.clone(), sym);
        }
    }

    /// Bind an imported name (EXTENDS, anonymous INSTANCE): of conflicting
    /// imports the first one is kept (as in SANY, which warns).
    fn import(&mut self, name: &Arc<str>, sym: Sym, local: bool) {
        if !self.names.contains_key(name) {
            self.bind(name, sym, local);
        }
    }
}

impl Program {
    /// The scope of module `m` in context `ctx`, building it on first use.
    pub(super) fn scope(&mut self, ctx: CtxId, m: ModIdx) -> ScopeId {
        if let Some(&s) = self.scope_of.get(&(ctx, m)) {
            return s;
        }
        // Register the (empty) scope first so that cyclic lookups terminate.
        let sid = self.scopes.len();
        self.scopes.push(Scope { names: HashMap::new(), exports: HashMap::new() });
        self.scope_of.insert((ctx, m), sid);

        let ast = self.mods[m].ast.clone();
        let mut sb = ScopeBuilder::default();

        // A nested module sees everything defined in its enclosing module, in
        // the context the enclosing module was instantiated in.
        if let Some(parent) = self.mods[m].parent {
            // The context of the INSTANCE (possibly several levels out, when
            // the nested module is instantiated by a sibling) that appears
            // in the parent module.
            let mut pctx = ctx;
            let mut c = ctx;
            while let Some(s) = &self.ctxs[c].subst {
                if s.outer_mod == parent {
                    pctx = s.outer_ctx;
                    break;
                }
                c = s.outer_ctx;
                if c == ROOT_CTX {
                    pctx = ROOT_CTX;
                }
            }
            // It sees the names bound before it, recorded while the parent's
            // scope was built (which may still be in progress, when the
            // parent instantiates the nested module itself).
            let ps = self.scope(pctx, parent);
            match self.nested_prefix.get(&(pctx, m)) {
                Some(names) => sb.names.extend(names.clone()),
                None => sb.names.extend(self.scopes[ps].names.clone()),
            }
        }

        for e in &ast.extends {
            let Some(em) = self.find_module(e) else { continue };
            // A module extended from an instance context shares that context,
            // unless it declares nothing (then use the root context).
            let ectx = if ctx != ROOT_CTX && !self.has_decls(em, &mut Vec::new()) { ROOT_CTX } else { ctx };
            let es = self.scope(ectx, em);
            for (n, s) in self.scopes[es].exports.clone() {
                sb.import(&n, s, false);
            }
        }

        for (ui, u) in ast.units.iter().enumerate() {
            self.declare_unit(&mut sb, ctx, m, ui, u);
        }
        self.scopes[sid] = Scope { names: sb.names, exports: sb.exports };
        sid
    }

    /// Add the names introduced by module unit `u` (the `ui`-th unit of `m`).
    fn declare_unit(&mut self, sb: &mut ScopeBuilder, ctx: CtxId, m: ModIdx, ui: usize, u: &ast::Unit) {
        match u {
            ast::Unit::Constants(decls) => {
                for d in decls {
                    let s = if ctx == ROOT_CTX {
                        let id = ConstId(self.consts.len() as u32);
                        self.consts.push(ConstInfo { name: d.name.name.clone(), arity: d.arity, span: d.name.span });
                        Sym::Const(id)
                    } else {
                        Sym::Decl { ctx, arity: d.arity, var: false }
                    };
                    sb.bind(&d.name.name, s, false);
                }
            }
            ast::Unit::Variables(vs) => {
                for v in vs {
                    let s = if ctx == ROOT_CTX {
                        let id = VarId(self.vars.len() as u32);
                        self.vars.push(VarInfo { name: v.name.clone(), span: v.span });
                        Sym::Var(id)
                    } else {
                        Sym::Decl { ctx, arity: 0, var: true }
                    };
                    sb.bind(&v.name, s, false);
                }
            }
            ast::Unit::OpDef(od) => {
                // Natives apply to standard modules and, like TLC's overrides,
                // by name to a few community modules. Definitions TLC
                // implements in Java and tlx does not support are recognized
                // in every module (TLC's override exists regardless of the
                // module whitelist) and fail when applied.
                let native_module = self.mods[m].std || crate::builtins::COMMUNITY_NATIVE_MODULES.contains(&&*self.mods[m].name);
                let builtin = Builtin::java_only(&self.mods[m].name, &od.name.name)
                    .or_else(|| native_module.then(|| Builtin::std(&self.mods[m].name, &od.name.name)).flatten());
                let d = self.new_module_def(ctx, m, &od.name.name, builtin, od.span, DefUnit::Op(od.clone()));
                sb.bind(&od.name.name, Sym::Def(d), od.local);
            }
            ast::Unit::FnDef(fd) => {
                let d = self.new_module_def(ctx, m, &fd.name.name, None, fd.span, DefUnit::Fn(fd.clone()));
                sb.bind(&fd.name.name, Sym::Def(d), fd.local);
            }
            ast::Unit::Instance(inst) => {
                if let Some(n) = &inst.name {
                    let id = InstId(self.insts.len());
                    self.insts.push(InstInfo { ctx, module: m, ast: inst.clone(), target: None, captured: None });
                    sb.bind(&n.name, Sym::Instance(id), inst.local);
                } else if let Some((ictx, im)) = self.anon_instance(ctx, m, ui, inst) {
                    let is = self.scope(ictx, im);
                    for (n, s) in self.scopes[is].exports.clone() {
                        // INSTANCE imports definitions only; the instantiated
                        // module's declarations are substituted away.
                        if matches!(s, Sym::Decl { ctx: c, .. } if c == ictx) {
                            continue;
                        }
                        // A definition of a module with parameters becomes a
                        // node of its own (`Program::entry_def`); those of
                        // modules that declare nothing (root context) are
                        // shared, except under a LOCAL INSTANCE (SANY's
                        // Generator.generateInstance), which matters only
                        // for the names the cfg binds: the root module's.
                        let own = |p: &Program, d: DefId| {
                            p.def_src[d.idx()].ctx != ROOT_CTX || (inst.local && ctx == ROOT_CTX && m == p.root_mod)
                        };
                        let s = match s {
                            Sym::Def(d) if !sb.names.contains_key(&n) && own(self, d) => Sym::Def(self.entry_def(d)),
                            s => s,
                        };
                        sb.import(&n, s, inst.local);
                    }
                }
            }
            ast::Unit::Assume { name: Some(name), body, span } | ast::Unit::Theorem { name, body, span } => {
                // Named assumptions and theorems can be referenced like definitions.
                let od = ast::OpDef { name: name.clone(), params: Vec::new(), body: body.clone(), local: false, span: *span };
                let d = self.new_module_def(ctx, m, &name.name, None, *span, DefUnit::Op(od));
                sb.bind(&name.name, Sym::Def(d), false);
            }
            ast::Unit::Module(nested) => {
                let n = (0..self.mods.len()).find(|&i| self.mods[i].parent == Some(m) && self.mods[i].name == nested.name.name);
                if let Some(n) = n {
                    self.nested_prefix.insert((ctx, n), sb.names.clone());
                }
            }
            ast::Unit::Recursive(_) | ast::Unit::Assume { name: None, .. } => {}
        }
    }

    /// A (lazily resolved) module-level definition in context `ctx`.
    fn new_module_def(
        &mut self,
        ctx: CtxId,
        module: ModIdx,
        name: &Arc<str>,
        builtin: Option<Builtin>,
        span: Span,
        unit: DefUnit,
    ) -> DefId {
        self.new_def(name.clone(), builtin, span, DefSrc { ctx, module, unit, state: DefState::Unresolved })
    }

    /// Create the context for an INSTANCE of module `inst.module` appearing in
    /// (ctx, m) with the given extra params. Instances of modules without
    /// declarations (and parameters) share the root context.
    fn instance_ctx(&mut self, ctx: CtxId, m: ModIdx, inst: &ast::Instance, captured: Option<super::Captured>) -> Option<(CtxId, ModIdx)> {
        let target = self.find_instance_module(m, &inst.module)?;
        if inst.params.is_empty() && !self.has_decls(target, &mut Vec::new()) && (ctx == ROOT_CTX || self.mods[target].parent.is_none()) {
            return Some((ROOT_CTX, target));
        }
        let outer_inst = self.ctxs[ctx].inst_params.len();
        let mut inst_params = self.ctxs[ctx].inst_params.clone();
        inst_params.extend(inst.params.iter().map(|p| (p.name.name.clone(), p.arity)));
        let explicit = inst.substs.iter().map(|(n, e)| (n.name.clone(), e.clone())).collect();
        let id = self.ctxs.len();
        let subst = SubstInfo { outer_ctx: ctx, outer_mod: m, outer_inst, explicit, target, span: inst.span, captured };
        self.ctxs.push(Ctx { inst_params, subst: Some(subst), uses_capture: false, fresh: None, copy_of: None });
        Some((id, target))
    }

    /// The context to resolve the argument of an `ENABLED` in, when it
    /// appears in instance context `ctx`: a copy of `ctx` whose VARIABLEs are
    /// `ExprKind::InstVar`s (the primed variables of the instantiated module
    /// are the ENABLED's own, not their substitutions). None where that
    /// makes no difference: outside instances, in a copy already, and when
    /// every instance on the way substitutes distinct variables for the
    /// variables (a renaming).
    pub(super) fn enabled_ctx(&mut self, ctx: CtxId) -> Option<CtxId> {
        if ctx == ROOT_CTX || self.ctxs[ctx].copy_of.is_some() || self.vars_renamed(ctx) {
            return None;
        }
        if let Some(c) = self.ctxs[ctx].fresh {
            return Some(c);
        }
        let mut subst = self.ctxs[ctx].subst.clone();
        if let Some(s) = &mut subst {
            if let Some(fresh_outer) = self.enabled_ctx(s.outer_ctx) {
                s.outer_ctx = fresh_outer;
            }
        }
        let copy = Ctx { inst_params: self.ctxs[ctx].inst_params.clone(), subst, uses_capture: false, fresh: None, copy_of: Some(ctx) };
        let id = self.ctxs.len();
        self.ctxs.push(copy);
        self.ctxs[ctx].fresh = Some(id);
        Some(id)
    }

    /// The context `ctx` copies for ENABLED (see `enabled_ctx`), or `ctx`.
    pub(super) fn unfresh(&self, ctx: CtxId) -> CtxId {
        self.ctxs[ctx].copy_of.unwrap_or(ctx)
    }

    /// Whether instance context `ctx` and those it is nested in substitute
    /// distinct variables of the instantiating module for the VARIABLEs of
    /// the instantiated one.
    fn vars_renamed(&mut self, ctx: CtxId) -> bool {
        let Some(s) = self.ctxs[ctx].subst.clone() else { return true };
        if s.captured.is_some() {
            return false;
        }
        let sc = self.scope(ctx, s.target);
        let mut vars: Vec<Arc<str>> = self.scopes[sc]
            .names
            .iter()
            .filter(|(_, sym)| matches!(sym, Sym::Decl { ctx: c, var: true, .. } if *c == ctx))
            .map(|(n, _)| n.clone())
            .collect();
        vars.sort();
        let outer = self.scope(s.outer_ctx, s.outer_mod);
        let mut targets: Vec<(CtxId, Arc<str>)> = Vec::new();
        for v in vars {
            let name = match s.explicit.get(&v).map(|e| &*e.kind) {
                None => v.clone(),
                Some(ast::ExprKind::OpAppl { prefix, name, args }) if prefix.is_empty() && args.is_empty() => name.name.clone(),
                Some(_) => return false,
            };
            let target = match self.scopes[outer].names.get(&name) {
                Some(Sym::Var(id)) => (ROOT_CTX, self.vars[id.idx()].name.clone()),
                Some(Sym::Decl { ctx: c, var: true, .. }) => (*c, name.clone()),
                _ => return false,
            };
            if targets.contains(&target) {
                return false;
            }
            targets.push(target);
        }
        self.vars_renamed(s.outer_ctx)
    }

    /// The `InstVar` slot of VARIABLE `name` of the context copy `ctx`.
    pub(super) fn inst_var_slot(&mut self, ctx: CtxId, name: &str, span: Span) -> u32 {
        let key = (ctx, Arc::<str>::from(name));
        if let Some(&s) = self.inst_var_slot.get(&key) {
            return s;
        }
        let shown: Arc<str> = match self.ctx_prefix(ctx) {
            Some(p) => format!("{p}!{name}").into(),
            None => name.into(),
        };
        let slot = self.inst_vars.len() as u32;
        self.inst_vars.push(VarInfo { name: shown, span });
        self.inst_var_slot.insert(key, slot);
        slot
    }

    /// Context of the anonymous `INSTANCE` that is unit `ui` of (ctx, m).
    fn anon_instance(&mut self, ctx: CtxId, m: ModIdx, ui: usize, inst: &ast::Instance) -> Option<(CtxId, ModIdx)> {
        if let Some(&c) = self.anon_inst_ctx.get(&(ctx, m, ui)) {
            let target = self.find_instance_module(m, &inst.module)?;
            return Some((c, target));
        }
        let (c, t) = self.instance_ctx(ctx, m, inst, None)?;
        self.anon_inst_ctx.insert((ctx, m, ui), c);
        Some((c, t))
    }

    /// Context of a named instance `I == INSTANCE ...` (created on first use).
    pub(super) fn named_instance(&mut self, id: InstId) -> Option<(CtxId, ModIdx)> {
        if let Some(t) = self.insts[id.0].target {
            return Some(t);
        }
        let info = &self.insts[id.0];
        let (ctx, m, ast, captured) = (info.ctx, info.module, info.ast.clone(), info.captured.clone());
        let t = self.instance_ctx(ctx, m, &ast, captured)?;
        self.insts[id.0].target = Some(t);
        Some(t)
    }
}
