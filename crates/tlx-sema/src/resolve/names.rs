//! SANY's scoping and arity rules, checked on the surface AST of every loaded
//! module (SANY's `Generator` / `SymbolTable`):
//! - a name can only be used after its definition or declaration (or a
//!   RECURSIVE declaration, whose definition must follow at the same level);
//! - a module cannot define a name twice, redefine a built-in, or define a
//!   name it imports; a parameter, bound variable or LET definition cannot
//!   shadow a name in scope ("Multiply-defined symbol"). Conflicting imports
//!   of the same kind and arity are only a warning in SANY: the first one
//!   is kept (and the resolver does the same);
//! - operators are applied to the right number of arguments, operator
//!   arguments are operators of the right arity, and only declared
//!   CONSTANTs/VARIABLEs are substituted (each once) by INSTANCE ... WITH;
//! - no record constructor repeats a field; no module depends on itself.
//!
//! The resolver proper (`scope`, `expr`, `apply`) sees all module-level names
//! at once and allows shadowing; this pass rejects the specs SANY rejects.

use std::collections::HashMap;
use std::sync::Arc;

use tlx_front::ast::{self, Span};

mod proofs;

use super::{err, ModIdx, Program};
use crate::builtins::Builtin;

/// The identity of a module-level symbol: the same definition imported
/// along several paths (e.g. Naturals through two EXTENDS) is no conflict.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Origin {
    /// The `k`-th name introduced by unit `u` of module `m`.
    Unit(ModIdx, usize, usize),
    /// A `RECURSIVE` declaration (the definition follows later).
    Recursive(ModIdx, usize, usize),
    /// A name bound inside an expression.
    Local,
}

/// SANY's symbol kinds (two symbols of different kinds or arities always
/// conflict).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Kind {
    Constant,
    Variable,
    /// User-defined operator (including LET definitions).
    Op,
    /// Function definition `f[x \in S, ...] == ...` with this many bound
    /// variables.
    Fn(usize),
    Instance,
    Theorem,
    /// Parameter, bound variable (also NEW, TAKE, PICK).
    Param,
    /// A named proof step; for steps that are not assertions, what they are
    /// (they cannot be used as expressions).
    Step(Option<&'static str>),
    Builtin,
}

#[derive(Clone)]
pub(super) struct Entry {
    pub(super) origin: Origin,
    pub(super) kind: Kind,
    /// Number of arguments; `None` for variadic built-ins.
    pub(super) arity: Option<usize>,
    /// Arities of the parameters (> 0 for operator parameters).
    pub(super) params: Arc<[usize]>,
    pub(super) span: Span,
    pub(super) module: Arc<str>,
}

impl Entry {
    fn same_shape(&self, o: &Entry) -> bool {
        let kind = |k: Kind| if let Kind::Fn(_) = k { Kind::Op } else { k };
        kind(self.kind) == kind(o.kind) && self.arity == o.arity
    }
}

#[derive(Clone, Default)]
pub(super) struct NameScope {
    module: HashMap<Arc<str>, Entry>,
    /// Names bound inside an expression, innermost last.
    pub(super) locals: Vec<(Arc<str>, Entry)>,
}

pub(super) struct Checker<'p> {
    pub(super) p: &'p mut Program,
    exports: HashMap<ModIdx, Arc<Vec<(Arc<str>, Entry)>>>,
    /// Module whose units are being checked (for error messages).
    pub(super) cur_mod: ModIdx,
    /// Labels: the bound identifiers of the current definition body are
    /// `NameScope::locals[label_mark..]`; the label names used at each
    /// nesting level; why labels are not allowed here, if they are not.
    pub(super) label_mark: usize,
    pub(super) label_levels: Vec<Vec<Arc<str>>>,
    label_ban: Option<&'static str>,
}

const NOT_IN_DEF: &str = "Label not in definition or proof step.";

/// Names that are TLA+ built-ins (and so cannot be defined).
fn is_builtin_name(name: &str) -> bool {
    Builtin::core(name).is_some() || matches!(name, "TRUE" | "FALSE" | "/\\" | "\\/")
}

fn builtin_entry(name: &str) -> Option<Entry> {
    let arity = match name {
        "/\\" | "\\/" => Some(2),
        _ => usize::try_from(Builtin::core(name)?.arity()).ok(),
    };
    Some(Entry {
        origin: Origin::Local,
        kind: Kind::Builtin,
        arity,
        params: vec![0; arity.unwrap_or(0)].into(),
        span: Span::default(),
        module: "--TLA+ BUILTINS--".into(),
    })
}

pub(super) fn op_def_entry(od: &ast::OpDef, origin: Origin, module: &Arc<str>) -> Entry {
    Entry {
        origin,
        kind: Kind::Op,
        arity: Some(od.params.len()),
        params: od.params.iter().map(|p| p.arity).collect(),
        span: od.name.span,
        module: module.clone(),
    }
}

pub(super) fn fn_def_entry(fd: &ast::FnDef, origin: Origin, module: &Arc<str>) -> Entry {
    // A tuple `<<x, y>> \in S` is one parameter.
    let nvars = fd
        .bounds
        .iter()
        .map(|b| match &b.vars {
            ast::BoundVars::Many(v) => v.len(),
            ast::BoundVars::Tuple(_) => 1,
        })
        .sum();
    Entry { origin, kind: Kind::Fn(nvars), arity: Some(0), params: Arc::new([]), span: fd.name.span, module: module.clone() }
}

/// The origin of the name of `Module::proofs[j]` of module `m`.
fn proof_origin(m: ModIdx, j: usize) -> Origin {
    Origin::Unit(m, usize::MAX / 2 + j, 0)
}

pub(super) fn simple_entry(kind: Kind, arity: usize, span: Span, origin: Origin, module: &Arc<str>) -> Entry {
    Entry { origin, kind, arity: Some(arity), params: vec![0; arity].into(), span, module: module.clone() }
}

pub(super) fn instance_entry(inst: &ast::Instance, span: Span, origin: Origin, module: &Arc<str>) -> Entry {
    Entry {
        origin,
        kind: Kind::Instance,
        arity: Some(inst.params.len()),
        params: inst.params.iter().map(|p| p.arity).collect(),
        span,
        module: module.clone(),
    }
}

pub(super) fn bound_vars(v: &ast::BoundVars) -> &[ast::Ident] {
    match v {
        ast::BoundVars::Many(v) | ast::BoundVars::Tuple(v) => v,
    }
}

/// Arity of an operator argument that is not known here.
const ANY: usize = usize::MAX;

pub(super) fn pos(span: Span, module: &str) -> String {
    crate::source::begin_text(span, module)
}

impl Program {
    /// Check SANY's scoping rules on every loaded module (loading the modules
    /// they depend on). Errors go to `self.errors`.
    pub(super) fn check_names(&mut self) {
        let mut c =
            Checker { p: self, exports: HashMap::new(), cur_mod: 0, label_mark: 0, label_levels: Vec::new(), label_ban: Some(NOT_IN_DEF) };
        c.check_cycles();
        if !c.p.errors.is_empty() {
            return;
        }
        let mut m = 0;
        while m < c.p.mods.len() {
            if c.p.mods[m].parent.is_none() {
                c.module(m, NameScope::default());
            }
            m += 1;
        }
    }
}

impl Checker<'_> {
    pub(super) fn error(&mut self, span: Span, msg: String) {
        self.p.errors.push(err(span, msg));
    }

    pub(super) fn mod_name(&self, m: ModIdx) -> Arc<str> {
        self.p.mods[m].name.clone()
    }

    /// The nested module named `name` of `m`.
    fn nested(&self, m: ModIdx, name: &str) -> Option<ModIdx> {
        (0..self.p.mods.len()).find(|&i| self.p.mods[i].parent == Some(m) && &*self.p.mods[i].name == name)
    }

    fn find(&mut self, name: &ast::Ident) -> Option<ModIdx> {
        self.p.find_module(name)
    }

    /// The module instantiated by `inst` (appearing in module `m`): a nested
    /// module of `m` (or of its ancestors) or a top-level module.
    pub(super) fn instance_target(&mut self, m: ModIdx, inst: &ast::Instance) -> Option<ModIdx> {
        let mut cur = Some(m);
        while let Some(c) = cur {
            if let Some(n) = self.nested(c, &inst.module.name) {
                return Some(n);
            }
            cur = self.p.mods[c].parent;
        }
        self.find(&inst.module)
    }

    /// The modules `m` depends on (EXTENDS and INSTANCE, also from its nested
    /// modules), as (module, file) pairs.
    fn deps(&mut self, m: ModIdx) -> Vec<ModIdx> {
        fn walk(md: &ast::Module, out: &mut Vec<ast::Ident>, nested: &mut Vec<Arc<str>>) {
            out.extend(md.extends.iter().cloned());
            for u in &md.units {
                match u {
                    ast::Unit::Instance(i) => out.push(i.module.clone()),
                    ast::Unit::Module(inner) => {
                        nested.push(inner.name.name.clone());
                        walk(inner, out, nested);
                    }
                    _ => {}
                }
            }
        }
        let ast = self.p.mods[m].ast.clone();
        let (mut names, mut nested) = (Vec::new(), Vec::new());
        walk(&ast, &mut names, &mut nested);
        let mut out = Vec::new();
        for n in names {
            if nested.contains(&n.name) {
                continue;
            }
            if let Some(d) = self.find(&n) {
                if !out.contains(&d) {
                    out.push(d);
                }
            }
        }
        out
    }

    /// SANY: "Circular dependency among .tla files".
    fn check_cycles(&mut self) {
        let mut state: HashMap<ModIdx, u8> = HashMap::new(); // 1 = on stack, 2 = done
        let mut stack = Vec::new();
        let root = self.p.root_mod;
        self.dfs(root, &mut state, &mut stack);
    }

    fn dfs(&mut self, m: ModIdx, state: &mut HashMap<ModIdx, u8>, stack: &mut Vec<ModIdx>) {
        match state.get(&m) {
            Some(2) => return,
            Some(1) => {
                let i = stack.iter().position(|&x| x == m).unwrap_or(0);
                let mut cycle: Vec<String> = stack[i..].iter().map(|&x| format!("{}.tla", self.p.mods[x].name)).collect();
                cycle.push(format!("{}.tla", self.p.mods[m].name));
                let span = self.p.mods[m].ast.name.span;
                self.error(span, format!("Circular dependency among .tla files; dependency cycle is:\n\n  {}", cycle.join(" --> ")));
                return;
            }
            _ => {}
        }
        state.insert(m, 1);
        stack.push(m);
        for d in self.deps(m) {
            if self.p.errors.is_empty() {
                self.dfs(d, state, stack);
            }
        }
        stack.pop();
        state.insert(m, 2);
    }

    // ------------------------------------------------------------------
    // exports

    /// The names module `m` exports to a module extending it, in order.
    fn exports_of(&mut self, m: ModIdx) -> Arc<Vec<(Arc<str>, Entry)>> {
        if let Some(e) = self.exports.get(&m) {
            return e.clone();
        }
        self.exports.insert(m, Arc::new(Vec::new()));
        let ast = self.p.mods[m].ast.clone();
        let mname = self.mod_name(m);
        let mut out: Vec<(Arc<str>, Entry)> = Vec::new();
        let push = |out: &mut Vec<(Arc<str>, Entry)>, n: &Arc<str>, e: Entry| {
            // The first of conflicting imports is kept.
            if !out.iter().any(|(x, _)| x == n) {
                out.push((n.clone(), e));
            }
        };
        for e in &ast.extends {
            if let Some(em) = self.find(e) {
                for (n, x) in self.exports_of(em).iter() {
                    push(&mut out, n, x.clone());
                }
            }
        }
        for (ui, u) in ast.units.iter().enumerate() {
            let o = |k| Origin::Unit(m, ui, k);
            match u {
                ast::Unit::Constants(ds) => {
                    for (k, d) in ds.iter().enumerate() {
                        push(&mut out, &d.name.name, simple_entry(Kind::Constant, d.arity, d.name.span, o(k), &mname));
                    }
                }
                ast::Unit::Variables(vs) => {
                    for (k, v) in vs.iter().enumerate() {
                        push(&mut out, &v.name, simple_entry(Kind::Variable, 0, v.span, o(k), &mname));
                    }
                }
                ast::Unit::OpDef(od) if !od.local => push(&mut out, &od.name.name, op_def_entry(od, o(0), &mname)),
                ast::Unit::FnDef(fd) if !fd.local => push(&mut out, &fd.name.name, fn_def_entry(fd, o(0), &mname)),
                ast::Unit::Instance(inst) if !inst.local => match &inst.name {
                    Some(n) => push(&mut out, &n.name, instance_entry(inst, n.span, o(0), &mname)),
                    None => {
                        if let Some(t) = self.instance_target(m, inst) {
                            for (n, x) in self.exports_of(t).iter() {
                                if !matches!(x.kind, Kind::Constant | Kind::Variable) {
                                    push(&mut out, n, x.clone());
                                }
                            }
                        }
                    }
                },
                ast::Unit::Assume { name: Some(n), .. } | ast::Unit::Theorem { name: n, .. } => {
                    push(&mut out, &n.name, simple_entry(Kind::Theorem, 0, n.span, o(0), &mname))
                }
                _ => {}
            }
        }
        for (j, (_, pu)) in ast.proofs.iter().enumerate() {
            if let ast::ProofUnit::Theorem { name: Some(n), stmt: ast::Stmt::AssumeProve(_), .. } = pu {
                push(&mut out, &n.name, simple_entry(Kind::Theorem, 0, n.span, proof_origin(m, j), &mname))
            }
        }
        let out = Arc::new(out);
        self.exports.insert(m, out.clone());
        out
    }

    // ------------------------------------------------------------------
    // binding

    fn lookup<'s>(&self, sc: &'s NameScope, name: &str) -> Option<&'s Entry> {
        sc.locals.iter().rev().find(|(n, _)| &**n == name).map(|(_, e)| e).or_else(|| sc.module.get(name))
    }

    fn conflict(&mut self, name: &str, old: &Entry, new: &Entry) {
        let msg = if old.kind == Kind::Builtin {
            format!("Symbol {name} is a built-in operator, and cannot be redefined.")
        } else if !old.same_shape(new) || matches!(new.kind, Kind::Param) {
            format!(
                "Multiply-defined symbol '{name}': this definition or declaration conflicts \nwith the one at {}.",
                pos(old.span, &old.module)
            )
        } else {
            format!("Multiple declarations or definitions for symbol {name}.  \nThis duplicates the one at {}.", pos(old.span, &old.module))
        };
        self.error(new.span, msg);
    }

    /// Bind a name defined or declared by the current module (or a LET).
    pub(super) fn bind_own(&mut self, sc: &mut NameScope, name: &Arc<str>, e: Entry, local: bool) {
        if is_builtin_name(name) {
            let old = builtin_entry(name).unwrap_or(Entry { kind: Kind::Builtin, ..e.clone() });
            self.conflict(name, &old, &e);
            return;
        }
        if let Some(old) = self.lookup(sc, name).cloned() {
            let completes = match (old.origin, e.origin) {
                (Origin::Recursive(m1, ..), Origin::Unit(m2, ..)) => m1 == m2,
                (Origin::Recursive(..), Origin::Local) => local,
                _ => false,
            };
            if completes {
                if matches!(e.kind, Kind::Fn(_)) && old.arity != Some(0) {
                    self.error(e.span, format!("Function {name} has operator arguments in its RECURSIVE declaration."));
                } else {
                    // A RECURSIVE declaration gives only the number of
                    // parameters; operator parameters are allowed in any
                    // position (CommunityModules' Folds and Apalache define
                    // recursive operators with an operator first). SANY
                    // also rejects an operator as the *last* parameter (its
                    // paramsMatch loop assigns instead of conjoining); tlx
                    // does not copy that (compat.md D-17).
                    let params_match = old.params.len() == e.params.len();
                    if !params_match {
                        self.error(e.span, format!("Definition of {name} has different arity than its RECURSIVE declaration."));
                    }
                }
            } else if local || old.origin != e.origin {
                self.conflict(name, &old, &e);
                return;
            }
        }
        if local {
            if let Some(i) = sc.locals.iter().rposition(|(n, x)| n == name && matches!(x.origin, Origin::Recursive(..))) {
                sc.locals[i] = (name.clone(), e);
                return;
            }
            sc.locals.push((name.clone(), e));
        } else {
            sc.module.insert(name.clone(), e);
        }
    }

    /// Bind a name imported by EXTENDS or an anonymous INSTANCE: a conflict
    /// with a symbol of the same kind and arity is only a warning in SANY
    /// (the first one is kept).
    fn bind_import(&mut self, sc: &mut NameScope, name: &Arc<str>, e: Entry) {
        if let Some(old) = sc.module.get(name).cloned() {
            if old.origin != e.origin && !old.same_shape(&e) {
                self.conflict(name, &old, &e);
            }
            return;
        }
        sc.module.insert(name.clone(), e);
    }

    /// Bind a parameter or bound variable.
    pub(super) fn bind_param(&mut self, sc: &mut NameScope, id: &ast::Ident, arity: usize) {
        let e = simple_entry(Kind::Param, arity, id.span, Origin::Local, &self.mod_name(self.cur_mod));
        if let Some(old) = self.lookup(sc, &id.name).cloned() {
            self.conflict(&id.name, &old, &e);
        }
        sc.locals.push((id.name.clone(), e));
    }

    // ------------------------------------------------------------------
    // modules

    /// Check module `m` whose scope starts as `sc` (the enclosing module's
    /// scope for a nested module).
    fn module(&mut self, m: ModIdx, mut sc: NameScope) {
        let saved = self.cur_mod;
        self.cur_mod = m;
        let ast = self.p.mods[m].ast.clone();
        let mname = self.mod_name(m);
        for e in &ast.extends {
            let Some(em) = self.find(e) else { continue };
            for (n, entry) in self.exports_of(em).iter() {
                self.bind_import(&mut sc, n, entry.clone());
            }
        }
        // RECURSIVE declarations not yet defined.
        let mut pending: Vec<(Arc<str>, Span)> = Vec::new();
        let mut next_proof = 0;
        for (ui, u) in ast.units.iter().enumerate() {
            while next_proof < ast.proofs.len() && ast.proofs[next_proof].0 <= ui {
                self.proof_unit(&mut sc, m, next_proof, &ast.proofs[next_proof].1, &pending);
                next_proof += 1;
            }
            let o = |k| Origin::Unit(m, ui, k);
            let section = |c: &mut Self, span: Span, what: &str, pending: &[(Arc<str>, Span)]| {
                if !pending.is_empty() {
                    c.error(span, format!("{what} may not appear within a recursive definition section."));
                }
            };
            match u {
                ast::Unit::Constants(ds) => {
                    if let Some(d) = ds.first() {
                        section(self, d.name.span, "A declaration", &pending);
                    }
                    for (k, d) in ds.iter().enumerate() {
                        self.bind_own(&mut sc, &d.name.name, simple_entry(Kind::Constant, d.arity, d.name.span, o(k), &mname), false);
                    }
                }
                ast::Unit::Variables(vs) => {
                    if let Some(v) = vs.first() {
                        section(self, v.span, "A VARIABLE declaration", &pending);
                    }
                    for (k, v) in vs.iter().enumerate() {
                        self.bind_own(&mut sc, &v.name, simple_entry(Kind::Variable, 0, v.span, o(k), &mname), false);
                    }
                }
                ast::Unit::Recursive(ds) => {
                    for (k, d) in ds.iter().enumerate() {
                        let e = Entry { origin: Origin::Recursive(m, ui, k), ..simple_entry(Kind::Op, d.arity, d.name.span, o(k), &mname) };
                        self.bind_own(&mut sc, &d.name.name, e, false);
                        pending.push((d.name.name.clone(), d.name.span));
                    }
                }
                ast::Unit::OpDef(od) => {
                    self.op_def(&mut sc, od);
                    self.bind_own(&mut sc, &od.name.name, op_def_entry(od, o(0), &mname), false);
                    pending.retain(|(n, _)| *n != od.name.name);
                }
                ast::Unit::FnDef(fd) => {
                    // A function definition may be recursive.
                    self.bind_own(&mut sc, &fd.name.name, fn_def_entry(fd, o(0), &mname), false);
                    pending.retain(|(n, _)| *n != fd.name.name);
                    self.fn_def(&mut sc, fd);
                }
                ast::Unit::Instance(inst) => {
                    self.instance(&mut sc, m, inst);
                    match &inst.name {
                        Some(n) => {
                            let e = instance_entry(inst, n.span, o(0), &mname);
                            self.bind_own(&mut sc, &n.name, e, false);
                        }
                        None => {
                            if let Some(t) = self.instance_target(m, inst) {
                                for (n, e) in self.exports_of(t).iter() {
                                    if !matches!(e.kind, Kind::Constant | Kind::Variable) {
                                        self.bind_import(&mut sc, n, e.clone());
                                    }
                                }
                            }
                        }
                    }
                }
                ast::Unit::Assume { name, body, span } => {
                    section(self, *span, "An ASSUME", &pending);
                    // A named assumption is a definition (labels allowed).
                    if name.is_some() {
                        let m = sc.locals.len();
                        self.def_body(&mut sc, body, m);
                    } else {
                        self.expr(&mut sc, body);
                    }
                    if let Some(n) = name {
                        self.bind_own(&mut sc, &n.name, simple_entry(Kind::Theorem, 0, n.span, o(0), &mname), false);
                    }
                }
                ast::Unit::Theorem { name, body, span } => {
                    section(self, *span, "A THEOREM", &pending);
                    let m = sc.locals.len();
                    self.def_body(&mut sc, body, m);
                    self.bind_own(&mut sc, &name.name, simple_entry(Kind::Theorem, 0, name.span, o(0), &mname), false);
                }
                ast::Unit::Module(inner) => {
                    section(self, inner.name.span, "A MODULE ", &pending);
                    if ast.extends.iter().any(|e| e.name == inner.name.name) {
                        let msg = format!(
                            "Multiply-defined module '{}': this definition or declaration conflicts \nwith the one in EXTENDS.",
                            inner.name.name
                        );
                        self.error(inner.name.span, msg);
                    }
                    if let Some(im) = self.nested(m, &inner.name.name) {
                        self.module(im, sc.clone());
                    }
                }
            }
        }
        for (j, (_, pu)) in ast.proofs.iter().enumerate().skip(next_proof) {
            self.proof_unit(&mut sc, m, j, pu, &pending);
        }
        for (n, span) in pending {
            self.error(span, format!("Symbol {n} declared in RECURSIVE statement but not defined."));
        }
        self.cur_mod = saved;
    }

    pub(super) fn op_def(&mut self, sc: &mut NameScope, od: &ast::OpDef) {
        let mark = sc.locals.len();
        for p in &od.params {
            self.bind_param(sc, &p.name, p.arity);
        }
        let body_mark = sc.locals.len();
        self.def_body(sc, &od.body, body_mark);
        sc.locals.truncate(mark);
    }

    pub(super) fn fn_def(&mut self, sc: &mut NameScope, fd: &ast::FnDef) {
        let mark = sc.locals.len();
        self.bounds(sc, &fd.bounds);
        self.def_body(sc, &fd.body, mark);
        sc.locals.truncate(mark);
    }

    /// The body of a definition, in which labels may appear: their
    /// parameters are the identifiers bound by `locals[mark..]`.
    pub(super) fn def_body(&mut self, sc: &mut NameScope, body: &ast::Expr, mark: usize) {
        let saved = (self.label_mark, self.label_ban);
        self.label_mark = mark;
        self.label_ban = None;
        self.label_levels.push(Vec::new());
        self.expr(sc, body);
        self.label_levels.pop();
        (self.label_mark, self.label_ban) = saved;
    }

    /// SANY's rules for `name(params):: body`.
    pub(super) fn label(&mut self, sc: &NameScope, name: &ast::Ident, params: &[ast::Ident]) {
        if let Some(msg) = self.label_ban {
            self.error(name.span, msg.into());
            return;
        }
        if let Some(level) = self.label_levels.last_mut() {
            if level.contains(&name.name) {
                let msg = format!("Duplicate label `{}'.", name.name);
                self.error(name.span, msg);
            } else {
                level.push(name.name.clone());
            }
        }
        let bound: Vec<&Arc<str>> =
            sc.locals[self.label_mark.min(sc.locals.len())..].iter().filter(|(_, e)| e.kind == Kind::Param).map(|(n, _)| n).collect();
        for (i, p) in params.iter().enumerate() {
            if params[..i].iter().any(|q| q.name == p.name) {
                self.error(p.span, format!("Repeated formal parameter {} \nin label `{}'.", p.name, name.name));
            } else if !bound.contains(&&p.name) {
                self.error(p.span, format!("Label {} declares extra parameter(s)  {}", name.name, p.name));
            }
        }
        for b in bound {
            if !params.iter().any(|p| p.name == *b) {
                self.error(name.span, format!("Label {} must contain formal parameter `{b}'.", name.name));
            }
        }
    }

    /// `[I(params) ==] INSTANCE M WITH subst`: the substitutions (of declared
    /// constants and variables of M, each at most once), and an implicit
    /// `c <- c` for every declaration of M without one.
    pub(super) fn instance(&mut self, sc: &mut NameScope, m: ModIdx, inst: &ast::Instance) {
        let mark = sc.locals.len();
        for p in &inst.params {
            self.bind_param(sc, &p.name, p.arity);
        }
        let target = self.instance_target(m, inst);
        let decls: Vec<(Arc<str>, Entry)> = match target {
            Some(t) => self.exports_of(t).iter().filter(|(_, e)| matches!(e.kind, Kind::Constant | Kind::Variable)).cloned().collect(),
            None => Vec::new(),
        };
        for (i, (target_name, e)) in inst.substs.iter().enumerate() {
            if inst.substs[..i].iter().any(|(t, _)| t.name == target_name.name) {
                self.error(target_name.span, format!("Multiple substitutions for symbol '{}' in substitution.", target_name.name));
            }
            match decls.iter().find(|(n, _)| *n == target_name.name) {
                Some((_, d)) => {
                    let arity = d.arity.unwrap_or(0);
                    self.operand(sc, e, arity, None);
                }
                None if target.is_some() => {
                    self.error(
                        target_name.span,
                        format!(
                            "Identifier '{}' is not a legal target of a substitution. \nA legal target must be a declared CONSTANT or VARIABLE in the module being instantiated.",
                            target_name.name
                        ),
                    );
                    self.expr(sc, e);
                }
                None => self.expr(sc, e),
            }
        }
        for (n, d) in decls {
            if inst.substs.iter().any(|(s, _)| s.name == n) {
                continue;
            }
            if let Some(found) = self.lookup(sc, &n).cloned().or_else(|| builtin_entry(&n)) {
                let arity = d.arity.unwrap_or(0);
                if found.arity.is_some_and(|a| a != arity) {
                    let msg = if arity > 0 {
                        format!("An operator must be substituted for symbol '{n}', and it must have arity {arity}.")
                    } else {
                        format!("An expression must be substituted for symbol '{n}'.")
                    };
                    self.error(inst.span, msg);
                }
                continue;
            }
            let msg = format!(
                "Substitution missing for symbol {n} declared at {}\nand instantiated in module {}.",
                pos(d.span, &d.module),
                self.mod_name(self.cur_mod)
            );
            self.error(inst.span, msg);
        }
        sc.locals.truncate(mark);
    }

    // ------------------------------------------------------------------
    // expressions

    pub(super) fn bounds(&mut self, sc: &mut NameScope, bs: &[ast::Bound]) {
        for b in bs {
            self.expr(sc, &b.set);
        }
        for b in bs {
            for v in bound_vars(&b.vars) {
                self.bind_param(sc, v, 0);
            }
        }
    }

    /// The arguments of the components of an instance / subexpression path
    /// (`Op(Foo, 9)!lab`: operator arguments of a definition are allowed).
    fn prefix_args(&mut self, sc: &mut NameScope, prefix: &[ast::NamePrefix]) {
        for (k, p) in prefix.iter().enumerate() {
            let op = if k == 0 && !p.args.is_empty() {
                self.lookup(sc, &p.name.name)
                    .filter(|e| matches!(e.kind, Kind::Op | Kind::Instance) && !matches!(e.origin, Origin::Recursive(..)))
                    .map(|e| e.params.clone())
            } else {
                None
            };
            for (i, a) in p.args.iter().enumerate() {
                match &op {
                    Some(params) => {
                        let ar = params.get(i).copied().unwrap_or(0);
                        self.operand(sc, a, ar, Some((&p.name.name, i + 1)))
                    }
                    // Arities unknown here (e.g. `I!Op(Foo)!lab`).
                    None => self.operand(sc, a, ANY, None),
                }
            }
        }
    }

    /// The symbol named by the first component of an operator application.
    fn use_name(&mut self, sc: &NameScope, id: &ast::Ident) -> Option<Entry> {
        if let Some(e) = self.lookup(sc, &id.name) {
            return Some(e.clone());
        }
        if let Some(e) = builtin_entry(&id.name) {
            return Some(e);
        }
        if !id.name.starts_with('<') {
            self.error(id.span, format!("Unknown operator: `{}'.", id.name));
        }
        None
    }

    /// An argument (or substitution) in a position where an operator of
    /// arity `arity` (0: an expression; `ANY`: unknown) is expected; `ctx` is
    /// the applied operator and the argument position, for messages.
    fn operand(&mut self, sc: &mut NameScope, e: &ast::Expr, arity: usize, ctx: Option<(&str, usize)>) {
        use ast::ExprKind as A;
        if arity == ANY {
            match &*e.kind {
                A::Lambda { params, body } => {
                    let mark = sc.locals.len();
                    for p in params {
                        self.bind_param(sc, p, 0);
                    }
                    self.expr(sc, body);
                    sc.locals.truncate(mark);
                }
                A::OpAppl { prefix, name, args } if args.is_empty() => {
                    self.prefix_args(sc, prefix);
                    self.use_name(sc, prefix.first().map_or(name, |p| &p.name));
                }
                _ => self.expr(sc, e),
            }
            return;
        }
        if arity == 0 {
            if let A::Lambda { .. } = &*e.kind {
                self.error(e.span, "LAMBDA expression used where an expression is required.".into());
            }
            self.expr(sc, e);
            return;
        }
        match &*e.kind {
            A::Lambda { params, body } => {
                if params.len() != arity {
                    let msg = match ctx {
                        Some((op, i)) => format!(
                            "Lambda expression with arity {} used as argument {i} of operator `{op}', \nbut an operator of arity {arity} is required.",
                            params.len()
                        ),
                        None => format!("Expected arity {arity} but found operator of arity {}.", params.len()),
                    };
                    self.error(e.span, msg);
                }
                let mark = sc.locals.len();
                for p in params {
                    self.bind_param(sc, p, 0);
                }
                self.expr(sc, body);
                sc.locals.truncate(mark);
            }
            A::OpAppl { prefix, name, args } if args.is_empty() => {
                self.prefix_args(sc, prefix);
                let first = prefix.first().map_or(name, |p| &p.name);
                let found = self.use_name(sc, first);
                if prefix.is_empty() {
                    if let Some(Entry { arity: Some(a), params, kind, .. }) = found {
                        if a != arity {
                            self.error(e.span, format!("Expected arity {arity} but found operator of arity {a}."));
                        } else if kind == Kind::Op && params.iter().any(|&p| p > 0) {
                            // An operator argument cannot take operator arguments.
                            if let Some((op, i)) = ctx {
                                let msg = format!("Argument number {i} to operator '{op}' \nshould be a {arity}-parameter operator.");
                                self.error(e.span, msg);
                            }
                        }
                    }
                }
            }
            // A subexpression reference can name an operator (`D!1!Op`).
            A::Subexpr { .. } => self.expr(sc, e),
            _ => {
                let msg = match ctx {
                    Some((op, i)) => format!(
                        "An expression appears as argument number {i} (counting from 1) to operator '{op}', in a position an operator is required."
                    ),
                    None => format!("An operator of arity {arity} is required."),
                };
                self.error(e.span, msg);
                self.expr(sc, e);
            }
        }
    }

    pub(super) fn expr(&mut self, sc: &mut NameScope, e: &ast::Expr) {
        use ast::ExprKind as A;
        let mark = sc.locals.len();
        match &*e.kind {
            A::Num(_) | A::Decimal(_) | A::Str(_) | A::Bool(_) | A::At => {}
            A::OpAppl { prefix, name, args } => {
                self.prefix_args(sc, prefix);
                let first = prefix.first().map_or(name, |p| &p.name);
                let found = self.use_name(sc, first);
                match found {
                    Some(op) if prefix.is_empty() => {
                        if let Kind::Step(Some(what)) = op.kind {
                            self.error(e.span, format!("{what} proof step selected instead of expression."));
                        }
                        if let Some(a) = op.arity {
                            if a != args.len() && op.kind != Kind::Instance {
                                self.error(e.span, format!("The operator {} requires {a} arguments.", name.name));
                            }
                        }
                        // Only user-defined operators take operator arguments
                        // (unknown before the definition of a RECURSIVE one).
                        let recursive = matches!(op.origin, Origin::Recursive(..));
                        let takes_ops = matches!(op.kind, Kind::Op);
                        for (i, a) in args.iter().enumerate() {
                            let ar = if recursive {
                                ANY
                            } else if takes_ops {
                                op.params.get(i).copied().unwrap_or(0)
                            } else {
                                0
                            };
                            self.operand(sc, a, ar, Some((&name.name, i + 1)));
                        }
                    }
                    _ => {
                        // Instance-qualified (or unknown): arities unknown here.
                        for a in args {
                            self.operand(sc, a, ANY, None);
                        }
                    }
                }
            }
            A::Subexpr { base, path } => {
                for s in path {
                    if let ast::Selector::Args(es) | ast::Selector::Label(_, es) = s {
                        for x in es {
                            // Arguments of a selected LET operator may be operators.
                            self.operand(sc, x, ANY, None);
                        }
                    }
                }
                if let A::OpAppl { prefix, name, args } = &*base.kind {
                    self.prefix_args(sc, prefix);
                    let found = self.use_name(sc, prefix.first().map_or(name, |p| &p.name));
                    for (i, a) in args.iter().enumerate() {
                        let ar = match &found {
                            Some(op) if prefix.is_empty() && op.kind == Kind::Op && !matches!(op.origin, Origin::Recursive(..)) => {
                                op.params.get(i).copied().unwrap_or(0)
                            }
                            _ => ANY,
                        };
                        self.operand(sc, a, ar, Some((&name.name, i + 1)));
                    }
                } else {
                    self.expr(sc, base);
                }
            }
            A::Label { name, params, body } => self.label_form(sc, name, params, body),
            A::Lambda { params, body } => self.lambda_form(sc, params, body),
            A::And(es) | A::Or(es) | A::SetEnum(es) | A::Tuple(es) => {
                for x in es {
                    self.expr(sc, x);
                }
            }
            A::Quant { bounds, body, .. } | A::FnConstruct { bounds, body } => self.bounded_form(sc, bounds, body),
            A::QuantUnbounded { vars, body, .. } | A::TemporalQuant { vars, body, .. } => self.unbounded_form(sc, vars, body),
            A::Choose { vars, set, body } => self.choose_form(sc, vars, set, body),
            A::If { cond, then, els } => {
                self.expr(sc, cond);
                self.expr(sc, then);
                self.expr(sc, els);
            }
            A::Case { arms, other } => {
                for (g, v) in arms {
                    self.expr(sc, g);
                    self.expr(sc, v);
                }
                if let Some(o) = other {
                    self.expr(sc, o);
                }
            }
            A::Let { defs, body } => self.let_form(sc, defs, body),
            A::SetFilter { bound, pred } => self.set_filter_form(sc, bound, pred),
            A::SetMap { expr, bounds } => self.set_map_form(sc, expr, bounds),
            A::FnApp { func, args } => {
                if args.len() >= 2 {
                    if let A::OpAppl { prefix, name, args: fa } = &*func.kind {
                        if prefix.is_empty() && fa.is_empty() {
                            if let Some(Entry { kind: Kind::Fn(n), .. }) = self.lookup(sc, &name.name) {
                                if *n != args.len() {
                                    let msg = format!(
                                        "Function '{}' is defined with {n} parameters, but is applied to {} arguments.",
                                        name.name,
                                        args.len()
                                    );
                                    self.error(e.span, msg);
                                }
                            }
                        }
                    }
                }
                self.expr(sc, func);
                for a in args {
                    self.expr(sc, a);
                }
            }
            A::FnSet { domain, range } => {
                self.expr(sc, domain);
                self.expr(sc, range);
            }
            A::Record(fs) | A::RecordSet(fs) => {
                for (i, (f, v)) in fs.iter().enumerate() {
                    if fs[..i].iter().any(|(g, _)| g.name == f.name) {
                        self.error(f.span, "Non-unique fields in constructor.".into());
                    }
                    self.expr(sc, v);
                }
            }
            A::Field { record, .. } => self.expr(sc, record),
            A::Except { base, updates } => {
                self.expr(sc, base);
                for (keys, v) in updates {
                    for k in keys {
                        if let ast::ExceptKey::Index(ix) = k {
                            for x in ix {
                                self.expr(sc, x);
                            }
                        }
                    }
                    let saved = self.label_ban;
                    self.label_ban = Some("Labels inside EXCEPT clauses are not yet implemented.");
                    self.expr(sc, v);
                    self.label_ban = saved;
                }
            }
            A::BoxAction { action, sub } | A::AngleAction { action, sub } => {
                self.expr(sc, action);
                self.expr(sc, sub);
            }
            A::Fairness { sub, action, .. } => {
                self.expr(sc, sub);
                self.expr(sc, action);
            }
        }
        sc.locals.truncate(mark);
    }
}
