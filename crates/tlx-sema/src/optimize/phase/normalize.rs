//! Bounded, analysis-only expansion. Executable definitions remain untouched.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use tlx_front::cfg::Config;

use super::ConstSubstTarget;
use crate::{
    builtins::{Builtin as B, Effect},
    hir::*,
    visit, Program,
};

pub(super) struct Normalizer<'a> {
    program: &'a Program,
    cfg: &'a Config,
    stack: Vec<DefId>,
    const_stack: Vec<ConstId>,
    expanded_substs: BTreeMap<ConstId, String>,
    /// `.cfg` definition and builtin overrides the runtime would apply; `None`
    /// when the configuration has an override this analysis cannot certify, in
    /// which case lowering any operator definition fails closed.
    redirect: Option<super::CfgRedirects>,
    /// Definition and parameterized-constant overrides actually lowered, with
    /// the argument tuple each use site applied.
    expanded_overrides: Vec<super::AppliedOverride>,
    override_keys: HashSet<(String, Vec<String>)>,
    /// Syntactic HIR of each normalized formula once an override was applied;
    /// the override connection theorems are stated against these formulas.
    model_hirs: Vec<String>,
    saw_override: bool,
    remaining: usize,
    local: u32,
    at_stack: Vec<(Expr, bool)>,
    let_at: HashMap<DefId, Option<usize>>,
    allow_opaque_recursive: bool,
    expand_inst_var: bool,
    in_enabled: bool,
    recursive_cache: HashMap<DefId, bool>,
    opaque_vars_cache: HashMap<DefId, Option<BTreeSet<VarId>>>,
}

impl<'a> Normalizer<'a> {
    pub fn with_config(program: &'a Program, cfg: &'a Config) -> Self {
        Self {
            program,
            cfg,
            stack: Vec::new(),
            const_stack: Vec::new(),
            expanded_substs: BTreeMap::new(),
            redirect: super::cfg_def_redirects(program, cfg),
            expanded_overrides: Vec::new(),
            override_keys: HashSet::new(),
            model_hirs: Vec::new(),
            saw_override: false,
            remaining: 100_000,
            local: program.locals.len() as u32,
            at_stack: Vec::new(),
            let_at: HashMap::new(),
            allow_opaque_recursive: false,
            expand_inst_var: false,
            in_enabled: false,
            recursive_cache: HashMap::new(),
            opaque_vars_cache: HashMap::new(),
        }
    }

    pub fn with_config_threshold(program: &'a Program, cfg: &'a Config) -> Self {
        Self { allow_opaque_recursive: true, expand_inst_var: true, ..Self::with_config(program, cfg) }
    }

    pub fn opaque_vars_cache_mut(&mut self) -> &mut HashMap<DefId, Option<BTreeSet<VarId>>> {
        &mut self.opaque_vars_cache
    }

    fn builtin_override(&self, op: B) -> Option<(DefId, DefId)> {
        self.redirect.as_ref()?.builtins.get(&op).copied()
    }

    fn is_recursive_def(&mut self, target: DefId) -> bool {
        if let Some(&cached) = self.recursive_cache.get(&target) {
            return cached;
        }
        let mut visited = std::collections::HashSet::new();
        let mut stack = vec![target];
        let mut reaches_target = false;
        while let Some(id) = stack.pop() {
            if let Some(body) = Self::def_body(&self.program.defs[id.idx()]) {
                collect_def_callees(&body, &mut |callee| {
                    if callee == target {
                        reaches_target = true;
                    } else if visited.insert(callee) {
                        stack.push(callee);
                    }
                });
                if reaches_target {
                    break;
                }
            }
        }
        self.recursive_cache.insert(target, reaches_target);
        reaches_target
    }

    fn def_body(d: &Def) -> Option<Expr> {
        match &d.kind {
            DefKind::Op(body) => Some(body.clone()),
            DefKind::Fn { bounds, body } => Some(Expr::new(ExprKind::FnConstruct { bounds: bounds.clone(), body: body.clone() }, d.span)),
            DefKind::Pending => None,
        }
    }

    pub fn attach_const_subst(&self, cert: super::OpenCert) -> Option<String> {
        super::attach_const_subst_obligation(
            self.program,
            self.cfg,
            &self.expanded_substs,
            &super::OverrideObligations { applied: &self.expanded_overrides, model_hirs: &self.model_hirs },
            |cid| Self::expand_declared_const_subst(self.program, self.cfg, cid),
            |name, args| Self::expand_declared_override(self.program, self.cfg, name, args),
            cert,
        )
    }

    /// Re-derive a `.cfg` definition override from the configuration alone: the
    /// configured replacement body applied to `args`, canonicalized the same way
    /// the lowering records it.
    fn expand_declared_override(program: &'a Program, cfg: &'a Config, name: &str, args: &[Expr]) -> Option<String> {
        let target = cfg.last_constant_subst(name)?;
        let super::ConstSubstTarget::Def(target) = super::resolve_override_name(program, target)? else { return None };
        let mut fresh = Self::with_config(program, cfg);
        let expanded = fresh.apply_def(target, args, &HashMap::new(), 1)?;
        super::canonical_expr_repr(program, &expanded)
    }

    pub fn expand_declared_const_subst(program: &'a Program, cfg: &'a Config, c: ConstId) -> Option<String> {
        let (seen, terminal) = super::resolve_const_subst_chain(program, cfg, c)?;
        let resolved = match terminal {
            ConstSubstTarget::PureBuiltin(op, span) => {
                let mut fresh = Self::with_config(program, cfg);
                match fresh.builtin_override(op) {
                    Some((_, target)) => fresh.apply_def(target, &[], &HashMap::new(), 1)?,
                    None => Expr::new(ExprKind::Builtin { op, args: vec![] }, span),
                }
            }
            ConstSubstTarget::Const(other) => Expr::new(ExprKind::Const(other), Span::default()),
            ConstSubstTarget::Def(id) => {
                let body = Self::def_body(&program.defs[id.idx()])?;
                let mut fresh = Self::with_config(program, cfg);
                fresh.const_stack.extend_from_slice(&seen);
                fresh.stack.push(id);
                fresh.expand(&body, &HashMap::new(), None, 1)?
            }
        };
        super::canonical_expr_repr(program, &resolved)
    }

    fn record_const_subst(&mut self, c: ConstId, res: &Expr) -> bool {
        let Some(repr) = super::canonical_expr_repr(self.program, res) else {
            return false;
        };
        match self.expanded_substs.get(&c) {
            Some(prev) => prev == &repr,
            None => {
                self.expanded_substs.insert(c, repr);
                true
            }
        }
    }

    pub fn root(&mut self, e: &Expr) -> Option<Expr> {
        let result = self.expand(e, &HashMap::new(), None, 0)?;
        if self.saw_override {
            self.model_hirs.push(super::syntactic_expr_repr(self.program, &result)?);
        }
        Some(result)
    }

    fn bind(&mut self, vars: &BoundVars, env: &mut HashMap<LocalId, Expr>, span: Span) -> BoundVars {
        let ids = vars
            .locals()
            .iter()
            .map(|old| {
                let id = LocalId(self.local);
                self.local += 1;
                env.insert(*old, Expr::new(ExprKind::Local(id), span));
                id
            })
            .collect();
        match vars {
            BoundVars::Many(_) => BoundVars::Many(ids),
            BoundVars::Tuple(_) => BoundVars::Tuple(ids),
        }
    }

    fn bounds(&mut self, bounds: &[Bound], env: &mut HashMap<LocalId, Expr>, lex_at: Option<usize>, depth: usize) -> Option<Vec<Bound>> {
        bounds
            .iter()
            .map(|b| {
                let set = self.expand(&b.set, env, lex_at, depth)?;
                let vars = self.bind(&b.vars, env, b.set.span);
                Some(Bound { vars, set })
            })
            .collect()
    }

    fn expand_const(&mut self, c: ConstId, span: Span, env: &HashMap<LocalId, Expr>, lex_at: Option<usize>, depth: usize) -> Option<Expr> {
        if self.program.consts[c.idx()].arity != 0 || self.cfg.last_constant_subst(&self.program.consts[c.idx()].name).is_none() {
            return Some(Expr::new(ExprKind::Const(c), span));
        }
        if self.const_stack.contains(&c) {
            return None;
        }
        let res = match super::resolve_const_subst_target(self.program, self.cfg, c)? {
            ConstSubstTarget::PureBuiltin(op, span) => match self.builtin_override(op) {
                Some((_, target)) => self.apply_def(target, &[], env, depth + 1)?,
                None => Expr::new(ExprKind::Builtin { op, args: vec![] }, span),
            },
            ConstSubstTarget::Def(id) => {
                if self.stack.contains(&id) {
                    return None;
                }
                let body = Self::def_body(&self.program.defs[id.idx()])?;
                self.const_stack.push(c);
                self.stack.push(id);
                let res = self.expand(&body, &HashMap::new(), None, depth + 1);
                self.stack.pop();
                self.const_stack.pop();
                res?
            }
            ConstSubstTarget::Const(other) => {
                self.const_stack.push(c);
                let res = self.expand(&Expr::new(ExprKind::Const(other), span), env, lex_at, depth + 1);
                self.const_stack.pop();
                res?
            }
        };
        self.record_const_subst(c, &res).then_some(res)
    }

    /// Lower a call of `id` after applying the `.cfg` definition overrides the
    /// runtime applies. A redirected call is expanded from the configured
    /// replacement body and recorded for the certificate's override obligation;
    /// a configuration with an uncertifiable override fails closed.
    fn apply_def(&mut self, id: DefId, args: &[Expr], env: &HashMap<LocalId, Expr>, depth: usize) -> Option<Expr> {
        let redirect = self.redirect.as_ref()?;
        let target = *redirect.defs.get(&id).unwrap_or(&id);
        let d = &self.program.defs[target.idx()];
        if let Some(op) = d.builtin {
            // A builtin operator replaced through this definition: the
            // replacement body runs at every use of the operator.
            if let Some((_, replacement)) = self.builtin_override(op) {
                return self.apply_def(replacement, args, env, depth);
            }
            return Some(Expr::new(ExprKind::Builtin { op, args: args.to_vec() }, d.span));
        }
        if d.params.len() != args.len() {
            return None;
        }
        if self.allow_opaque_recursive && self.is_recursive_def(target) {
            // Only keep a recursive call opaque when `id` and every
            // transitively reachable definition are pure and lexically closed
            // (no free enclosing locals or `@` captures).
            opaque_recursive_def_vars(self.program, self.cfg, target, &mut self.opaque_vars_cache)?;
            return Some(Expr::new(ExprKind::Apply { op: OpRef::Def(target), args: args.to_vec() }, d.span));
        }
        if self.stack.contains(&target) {
            return None;
        }
        if self.program.is_strict_call_def(target) && !strict_call_preserves_args(self.program, d) {
            return None;
        }
        // TLA+ parameters are by name. Substitution keeps each actual read in
        // the callee's control context; expansion above still refuses effectful
        // actuals.
        let mut scope = env.clone();
        scope.extend(d.params.iter().copied().zip(args.iter().cloned()));
        let body = Self::def_body(d)?;
        let def_at = self.let_at.get(&target).copied().unwrap_or(None);
        self.stack.push(target);
        let result = self.expand(&body, &scope, def_at, depth + 1);
        self.stack.pop();
        let result = result?;
        if target != id {
            let name = self.program.defs[id.idx()].name.to_string();
            let target_name = self.program.defs[target.idx()].name.to_string();
            self.record_override(name, target_name, args, &result)?;
        }
        Some(result)
    }

    /// Record one applied override use site, deduplicated by the replaced name
    /// and canonical argument tuple.
    fn record_override(&mut self, name: String, target: String, args: &[Expr], result: &Expr) -> Option<()> {
        let key = (name.clone(), args.iter().map(|a| super::canonical_expr_repr(self.program, a)).collect::<Option<Vec<_>>>()?);
        if self.override_keys.insert(key) {
            let applied = super::canonical_expr_repr(self.program, result)?;
            let applied_syntax = super::syntactic_expr_repr(self.program, result)?;
            self.expanded_overrides.push(super::AppliedOverride { name, target, args: args.to_vec(), applied, applied_syntax });
        }
        self.saw_override = true;
        Some(())
    }

    fn expand(&mut self, e: &Expr, env: &HashMap<LocalId, Expr>, lex_at: Option<usize>, depth: usize) -> Option<Expr> {
        if depth >= 128 || self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        let kind = match &*e.kind {
            ExprKind::Local(l) => return Some(env.get(l).unwrap_or(e).clone()),
            ExprKind::Const(c) => return self.expand_const(*c, e.span, env, lex_at, depth),
            ExprKind::At => {
                let idx = lex_at?;
                let (expr, used) = self.at_stack.get_mut(idx)?;
                *used = true;
                return Some(expr.clone());
            }
            ExprKind::Let { defs, body } => {
                let prev: Vec<_> = defs.iter().map(|&d| (d, self.let_at.insert(d, lex_at))).collect();
                let res = self.expand(body, env, lex_at, depth + 1);
                for (d, old) in prev {
                    match old {
                        Some(v) => {
                            self.let_at.insert(d, v);
                        }
                        None => {
                            self.let_at.remove(&d);
                        }
                    }
                }
                return res;
            }
            ExprKind::Apply { op, args } => {
                let expanded: Vec<_> = args.iter().map(|a| self.expand(a, env, lex_at, depth + 1)).collect::<Option<_>>()?;
                match op {
                    OpRef::Builtin(op) => {
                        if let Some((lhs, target)) = self.builtin_override(*op) {
                            let result = self.apply_def(target, &expanded, env, depth + 1)?;
                            let name = self.program.defs[lhs.idx()].name.to_string();
                            let target_name = self.program.defs[target.idx()].name.to_string();
                            self.record_override(name, target_name, &expanded, &result)?;
                            return Some(result);
                        }
                        ExprKind::Builtin { op: *op, args: expanded }
                    }
                    OpRef::Def(id) => return self.apply_def(*id, &expanded, env, depth + 1),
                    OpRef::Const(c) => {
                        let arity = self.program.consts[c.idx()].arity;
                        let name = self.program.consts[c.idx()].name.to_string();
                        let target = self.cfg.last_constant_subst(&name)?;
                        let super::ConstSubstTarget::Def(target) = super::resolve_override_name(self.program, target)? else {
                            return None;
                        };
                        if self.program.defs[target.idx()].params.len() != arity {
                            return None;
                        }
                        let result = self.apply_def(target, &expanded, env, depth + 1)?;
                        let target_name = self.program.defs[target.idx()].name.to_string();
                        self.record_override(name, target_name, &expanded, &result)?;
                        return Some(result);
                    }
                    OpRef::Param(_) => return None,
                }
            }
            ExprKind::InstVar { subst, .. } if self.expand_inst_var && !self.in_enabled => {
                return self.expand(subst, env, lex_at, depth + 1);
            }
            ExprKind::Builtin { op, args } if self.builtin_override(*op).is_some() => {
                let expanded: Vec<_> = args.iter().map(|a| self.expand(a, env, lex_at, depth + 1)).collect::<Option<_>>()?;
                let (lhs, target) = self.builtin_override(*op)?;
                let result = self.apply_def(target, &expanded, env, depth + 1)?;
                let name = self.program.defs[lhs.idx()].name.to_string();
                let target_name = self.program.defs[target.idx()].name.to_string();
                self.record_override(name, target_name, &expanded, &result)?;
                return Some(result);
            }
            ExprKind::Builtin { op: crate::builtins::Builtin::Enabled, args } if self.expand_inst_var => {
                let prev = self.in_enabled;
                self.in_enabled = true;
                let expanded = args.iter().map(|a| self.expand(a, env, lex_at, depth + 1)).collect::<Option<Vec<_>>>();
                self.in_enabled = prev;
                ExprKind::Builtin { op: crate::builtins::Builtin::Enabled, args: expanded? }
            }
            ExprKind::OpArg(_) | ExprKind::Lambda { .. } | ExprKind::InstVar { .. } => return None,
            ExprKind::Quant { kind, bounds, body } => {
                let mut scope = env.clone();
                let bounds = self.bounds(bounds, &mut scope, lex_at, depth + 1)?;
                ExprKind::Quant { kind: *kind, bounds, body: self.expand(body, &scope, lex_at, depth + 1)? }
            }
            ExprKind::FnConstruct { bounds, body } => {
                let mut scope = env.clone();
                let bounds = self.bounds(bounds, &mut scope, lex_at, depth + 1)?;
                ExprKind::FnConstruct { bounds, body: self.expand(body, &scope, lex_at, depth + 1)? }
            }
            ExprKind::SetMap { expr, bounds } => {
                let mut scope = env.clone();
                let bounds = self.bounds(bounds, &mut scope, lex_at, depth + 1)?;
                ExprKind::SetMap { expr: self.expand(expr, &scope, lex_at, depth + 1)?, bounds }
            }
            ExprKind::SetFilter { bound, pred } => {
                let mut scope = env.clone();
                let mut bounds = self.bounds(std::slice::from_ref(bound), &mut scope, lex_at, depth + 1)?;
                ExprKind::SetFilter { bound: bounds.remove(0), pred: self.expand(pred, &scope, lex_at, depth + 1)? }
            }
            ExprKind::Choose { vars, set, body } => {
                let set = match set {
                    Some(s) => Some(self.expand(s, env, lex_at, depth + 1)?),
                    None => None,
                };
                let mut scope = env.clone();
                let vars = self.bind(vars, &mut scope, e.span);
                ExprKind::Choose { vars, set, body: self.expand(body, &scope, lex_at, depth + 1)? }
            }
            ExprKind::Except { base, updates } => {
                let mut cur_base = self.expand(base, env, lex_at, depth + 1)?;
                let mut expanded: Vec<(Vec<ExceptKey>, Expr)> = Vec::new();
                for (path, rhs) in updates {
                    let mut keys = Vec::new();
                    for key in path {
                        let key = match key {
                            ExceptKey::Field(field) => ExceptKey::Field(field.clone()),
                            ExceptKey::Index(args) => {
                                ExceptKey::Index(args.iter().map(|e| self.expand(e, env, lex_at, depth + 1)).collect::<Option<_>>()?)
                            }
                        };
                        keys.push(key);
                    }
                    let build_old = |from: &Expr, ks: &[ExceptKey]| -> Expr {
                        let mut old = from.clone();
                        for key in ks {
                            old = Expr::new(
                                match key {
                                    ExceptKey::Field(field) => ExprKind::Field { record: old, field: field.clone() },
                                    ExceptKey::Index(args) => ExprKind::FnApp { func: old, args: args.clone() },
                                },
                                e.span,
                            );
                        }
                        old
                    };
                    let old = build_old(&cur_base, &keys);
                    let at_idx = self.at_stack.len();
                    self.at_stack.push((old, false));
                    let rhs_exp = self.expand(rhs, env, Some(at_idx), depth + 1);
                    let (_, at_used) = self.at_stack.pop().unwrap();
                    // EXCEPT updates are sequential. Using the original base
                    // for @ is valid only when preceding writes cannot touch
                    // this point. Check after expansion to include LET helpers.
                    if at_used && expanded.iter().any(|(prior, _)| !disjoint(prior, &keys)) {
                        if !self.expand_inst_var {
                            return None;
                        }
                        cur_base = Expr::new(ExprKind::Except { base: cur_base, updates: std::mem::take(&mut expanded) }, e.span);
                        let seq_old = build_old(&cur_base, &keys);
                        let at_idx = self.at_stack.len();
                        self.at_stack.push((seq_old, false));
                        let seq_rhs = self.expand(rhs, env, Some(at_idx), depth + 1);
                        self.at_stack.pop().unwrap();
                        expanded.push((keys, seq_rhs?));
                    } else {
                        expanded.push((keys, rhs_exp?));
                    }
                }
                ExprKind::Except { base: cur_base, updates: expanded }
            }
            ExprKind::QuantUnbounded { .. } | ExprKind::TemporalQuant { .. } => return None,
            _ => {
                let mut out = Expr::new((*e.kind).clone(), e.span);
                let mut valid = true;
                visit::children_mut(&mut out, &mut |c| match self.expand(c, env, lex_at, depth + 1) {
                    Some(x) => *c = x,
                    None => valid = false,
                });
                if !valid {
                    return None;
                }
                (*out.kind).clone()
            }
        };
        if matches!(&kind, ExprKind::Builtin { op, .. } if op.metadata().effect != Effect::Pure) {
            return None;
        }
        Some(Expr::new(kind, e.span))
    }
}

fn collect_def_callees(e: &Expr, f: &mut impl FnMut(DefId)) {
    if let ExprKind::Apply { op: OpRef::Def(id), .. } = &*e.kind {
        f(*id);
    }
    visit::children(e, &mut |c| collect_def_callees(c, f));
}

/// Transitively prove that `root` is pure, state-level, and lexically closed
/// (references no `LocalId` or `@` bound outside `root` itself, including
/// through transitively called definitions and `.cfg` constant substitutions),
/// returning the exact set of state `VarId`s it may read.
///
/// Returns `None` if any reachable expression captures an enclosing local or
/// `@`, uses `Prime`/`Unchanged`/`Enabled`/temporal/unbounded/higher-order/
/// `InstVar`/`Pending`/non-pure constructs, or exceeds the traversal budget.
pub(in crate::optimize::phase) fn opaque_recursive_def_vars(
    program: &Program,
    cfg: &Config,
    root: DefId,
    cache: &mut HashMap<DefId, Option<BTreeSet<VarId>>>,
) -> Option<BTreeSet<VarId>> {
    if let Some(cached) = cache.get(&root) {
        return cached.clone();
    }
    // A `.cfg` override changes the body that runs at a use site, so the
    // dependency walk must see the replacement's reads; otherwise an opaque
    // recursive helper can hide a live variable from the reduction rules.
    let redirect = super::cfg_def_redirects(program, cfg)?;

    struct Ctx<'a> {
        program: &'a Program,
        cfg: &'a Config,
        redirect: &'a super::CfgRedirects,
        visited_defs: HashSet<DefId>,
        visited_consts: HashSet<ConstId>,
        let_scopes: HashMap<DefId, (HashSet<LocalId>, bool)>,
        stack: Vec<(DefId, HashSet<LocalId>, bool)>,
        vars: BTreeSet<VarId>,
        budget: usize,
    }

    impl Ctx<'_> {
        fn is_allowed_builtin(b: B) -> bool {
            !matches!(b, B::Prime | B::Unchanged | B::Enabled) && b.metadata().effect == Effect::Pure
        }

        fn walk_bounds(&mut self, bounds: &[Bound], scope: &mut HashSet<LocalId>, in_except: bool) -> bool {
            for b in bounds {
                if !self.walk(&b.set, scope, in_except) {
                    return false;
                }
                scope.extend(b.vars.locals().iter().copied());
            }
            true
        }

        fn enqueue_def(&mut self, id: DefId) -> bool {
            let id = *self.redirect.defs.get(&id).unwrap_or(&id);
            let d = &self.program.defs[id.idx()];
            if let Some(b) = d.builtin {
                if let Some((_, replacement)) = self.redirect.builtins.get(&b) {
                    return self.enqueue_def(*replacement);
                }
                return Self::is_allowed_builtin(b);
            }
            if self.visited_defs.insert(id) {
                let (base_scope, base_except) = self.let_scopes.get(&id).cloned().unwrap_or_default();
                self.stack.push((id, base_scope, base_except));
            }
            true
        }

        fn walk(&mut self, e: &Expr, scope: &HashSet<LocalId>, in_except: bool) -> bool {
            if self.budget == 0 {
                return false;
            }
            self.budget -= 1;
            match &*e.kind {
                ExprKind::Var(v) => {
                    self.vars.insert(*v);
                    true
                }
                ExprKind::Local(l) => scope.contains(l),
                ExprKind::At => in_except,
                ExprKind::Const(c) => {
                    if self.cfg.last_constant_subst(&self.program.consts[c.idx()].name).is_some() {
                        if self.program.consts[c.idx()].arity != 0 {
                            return false;
                        }
                        if self.visited_consts.insert(*c) {
                            let Some((_, terminal)) = super::resolve_const_subst_chain(self.program, self.cfg, *c) else {
                                return false;
                            };
                            match terminal {
                                ConstSubstTarget::PureBuiltin(b, _) => {
                                    if !Self::is_allowed_builtin(b) {
                                        return false;
                                    }
                                }
                                ConstSubstTarget::Const(_) => {}
                                ConstSubstTarget::Def(did) => {
                                    let d = &self.program.defs[did.idx()];
                                    if let Some(b) = d.builtin {
                                        if let Some((_, replacement)) = self.redirect.builtins.get(&b) {
                                            if !self.enqueue_def(*replacement) {
                                                return false;
                                            }
                                        } else if !Self::is_allowed_builtin(b) {
                                            return false;
                                        }
                                    } else if !self.enqueue_def(did) {
                                        return false;
                                    }
                                }
                            }
                        }
                    }
                    true
                }
                ExprKind::InstVar { .. }
                | ExprKind::OpArg(_)
                | ExprKind::Lambda { .. }
                | ExprKind::QuantUnbounded { .. }
                | ExprKind::TemporalQuant { .. }
                | ExprKind::BoxAction { .. }
                | ExprKind::AngleAction { .. }
                | ExprKind::Fairness { .. } => false,
                ExprKind::Builtin { op, args } => {
                    let ok = match self.redirect.builtins.get(op) {
                        Some((_, replacement)) => self.enqueue_def(*replacement),
                        None => Self::is_allowed_builtin(*op),
                    };
                    ok && args.iter().all(|a| self.walk(a, scope, in_except))
                }
                ExprKind::Apply { op, args } => {
                    let ok = match op {
                        OpRef::Def(id) => self.enqueue_def(*id),
                        OpRef::Builtin(b) => match self.redirect.builtins.get(b) {
                            Some((_, replacement)) => self.enqueue_def(*replacement),
                            None => Self::is_allowed_builtin(*b),
                        },
                        OpRef::Const(_) | OpRef::Param(_) => false,
                    };
                    ok && args.iter().all(|a| self.walk(a, scope, in_except))
                }
                ExprKind::Let { defs, body } => {
                    for &d in defs {
                        self.let_scopes.insert(d, (scope.clone(), in_except));
                    }
                    self.walk(body, scope, in_except)
                }
                ExprKind::Quant { bounds, body, .. } | ExprKind::FnConstruct { bounds, body } => {
                    let mut inner = scope.clone();
                    self.walk_bounds(bounds, &mut inner, in_except) && self.walk(body, &inner, in_except)
                }
                ExprKind::SetMap { expr, bounds } => {
                    let mut inner = scope.clone();
                    self.walk_bounds(bounds, &mut inner, in_except) && self.walk(expr, &inner, in_except)
                }
                ExprKind::SetFilter { bound, pred } => {
                    if !self.walk(&bound.set, scope, in_except) {
                        return false;
                    }
                    let mut inner = scope.clone();
                    inner.extend(bound.vars.locals().iter().copied());
                    self.walk(pred, &inner, in_except)
                }
                ExprKind::Choose { vars, set, body } => {
                    if let Some(s) = set {
                        if !self.walk(s, scope, in_except) {
                            return false;
                        }
                    }
                    let mut inner = scope.clone();
                    inner.extend(vars.locals().iter().copied());
                    self.walk(body, &inner, in_except)
                }
                ExprKind::Except { base, updates } => {
                    if !self.walk(base, scope, in_except) {
                        return false;
                    }
                    for (path, rhs) in updates {
                        for key in path {
                            if let ExceptKey::Index(args) = key {
                                if !args.iter().all(|a| self.walk(a, scope, in_except)) {
                                    return false;
                                }
                            }
                        }
                        if !self.walk(rhs, scope, true) {
                            return false;
                        }
                    }
                    true
                }
                _ => {
                    let mut ok = true;
                    visit::children(e, &mut |c| {
                        if ok {
                            ok &= self.walk(c, scope, in_except);
                        }
                    });
                    ok
                }
            }
        }
    }

    let mut ctx = Ctx {
        program,
        cfg,
        redirect: &redirect,
        visited_defs: HashSet::from([root]),
        visited_consts: HashSet::new(),
        let_scopes: HashMap::new(),
        stack: vec![(root, HashSet::new(), false)],
        vars: BTreeSet::new(),
        budget: 2048,
    };

    while let Some((id, mut scope, in_except)) = ctx.stack.pop() {
        if ctx.visited_defs.len() > 64 {
            cache.insert(root, None);
            return None;
        }
        let d = &program.defs[id.idx()];
        if let Some(b) = d.builtin {
            if !Ctx::is_allowed_builtin(b) {
                cache.insert(root, None);
                return None;
            }
            continue;
        }
        scope.extend(d.params.iter().copied());
        let ok = match &d.kind {
            DefKind::Op(body) => ctx.walk(body, &scope, in_except),
            DefKind::Fn { bounds, body } => ctx.walk_bounds(bounds, &mut scope, in_except) && ctx.walk(body, &scope, in_except),
            DefKind::Pending => false,
        };
        if !ok {
            cache.insert(root, None);
            return None;
        }
    }

    cache.insert(root, Some(ctx.vars.clone()));
    Some(ctx.vars)
}

fn disjoint(a: &[ExceptKey], b: &[ExceptKey]) -> bool {
    // Different field names at the same path depth cannot alias, regardless
    // of whether earlier indices select the same entry. Prefixes may alias.
    a.iter().zip(b).any(|(a, b)| matches!((a, b), (ExceptKey::Field(a), ExceptKey::Field(b)) if a != b))
}

/// Whether call-by-name inlining of a strict call-by-value definition
/// (`Program::is_strict_call_def`) is guaranteed to evaluate every value
/// argument unconditionally, so partial or asymmetric arguments (such as
/// `1 \div 0` or `CHOOSE`) are never erased before totality or dependency
/// analysis.
pub(in crate::optimize::phase) fn strict_call_preserves_args(program: &Program, d: &Def) -> bool {
    let DefKind::Op(body) = &d.kind else {
        return false;
    };
    d.params.iter().all(|&p| program.locals[p.idx()].arity > 0 || param_evaluated_unconditionally(program, body, p))
}

fn param_evaluated_unconditionally(program: &Program, e: &Expr, param: LocalId) -> bool {
    use crate::builtins::Builtin as B;
    match &*e.kind {
        ExprKind::Local(l) => *l == param,
        ExprKind::And(es) | ExprKind::Or(es) => es.first().is_some_and(|a| param_evaluated_unconditionally(program, a, param)),
        ExprKind::If { cond, then, els } => {
            param_evaluated_unconditionally(program, cond, param)
                || (param_evaluated_unconditionally(program, then, param) && param_evaluated_unconditionally(program, els, param))
        }
        ExprKind::Quant { bounds, .. } | ExprKind::FnConstruct { bounds, .. } | ExprKind::SetMap { bounds, .. } => {
            bounds.first().is_some_and(|b| param_evaluated_unconditionally(program, &b.set, param))
        }
        ExprKind::SetFilter { bound, .. } => param_evaluated_unconditionally(program, &bound.set, param),
        ExprKind::Choose { set: Some(s), .. } => param_evaluated_unconditionally(program, s, param),
        ExprKind::Builtin { op, args } => match op {
            B::Implies | B::Not => args.first().is_some_and(|a| param_evaluated_unconditionally(program, a, param)),
            _ if op.is_strict_value_op() => args.iter().any(|a| param_evaluated_unconditionally(program, a, param)),
            _ => false,
        },
        ExprKind::Apply { op, args } => match op {
            OpRef::Builtin(b) => match b {
                B::Implies | B::Not => args.first().is_some_and(|a| param_evaluated_unconditionally(program, a, param)),
                _ if b.is_strict_value_op() => args.iter().any(|a| param_evaluated_unconditionally(program, a, param)),
                _ => false,
            },
            OpRef::Def(id) => {
                let d = &program.defs[id.idx()];
                if d.builtin.is_some_and(B::is_strict_value_op) || program.is_strict_call_def(*id) {
                    args.iter().any(|a| param_evaluated_unconditionally(program, a, param))
                } else {
                    false
                }
            }
            OpRef::Const(_) | OpRef::Param(_) => false,
        },
        ExprKind::Tuple(es) | ExprKind::SetEnum(es) => es.iter().any(|a| param_evaluated_unconditionally(program, a, param)),
        ExprKind::Record(fs) | ExprKind::RecordSet(fs) => fs.iter().any(|(_, a)| param_evaluated_unconditionally(program, a, param)),
        ExprKind::FnApp { func, args } => {
            param_evaluated_unconditionally(program, func, param) || args.iter().any(|a| param_evaluated_unconditionally(program, a, param))
        }
        ExprKind::Field { record, .. } => param_evaluated_unconditionally(program, record, param),
        ExprKind::Except { base, .. } => param_evaluated_unconditionally(program, base, param),
        ExprKind::FnSet { domain, range } => {
            param_evaluated_unconditionally(program, domain, param) || param_evaluated_unconditionally(program, range, param)
        }
        ExprKind::Let { body, .. } => param_evaluated_unconditionally(program, body, param),
        _ => false,
    }
}
