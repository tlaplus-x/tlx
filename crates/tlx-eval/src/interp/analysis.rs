//! Static classification of definitions over the call graph: constant-level,
//! action-level (observes the next state), effectful, state-cacheable and
//! recursive function definitions; closed constant domains of bound variables.

use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::{Arc, OnceLock};

use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::*;

use super::{ConstVal, Interp};

/// Built-ins whose result is nondeterministic or that have side effects.
fn is_effectful_builtin(b: B) -> bool {
    b.is_volatile()
}

/// Whether an application of `b` is constant-level (TLC level 0) when its
/// arguments are: no prime, UNCHANGED, ENABLED or temporal operator, and
/// deterministic without effects (the builtin metadata's effect).
pub(crate) fn constant_level_builtin(b: B) -> bool {
    !(matches!(b, B::Prime | B::Unchanged | B::Enabled | B::Always | B::Eventually | B::LeadsTo) || is_effectful_builtin(b))
}

/// Mark definition `i` with `to` whenever one of its dependencies (in any of
/// the dependency lists) is marked `to`, until nothing changes.
fn propagate(flags: &mut [bool], deps: &[&[Vec<DefId>]], to: bool) {
    loop {
        let mut changed = false;
        for i in 0..flags.len() {
            if flags[i] != to && deps.iter().any(|ds| ds[i].iter().any(|d| flags[d.idx()] == to)) {
                flags[i] = to;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
}

impl Interp {
    /// Whether an operator defined in `file` (named `name`, if a module-level
    /// definition) takes its arguments lazily in TLC: everything but the
    /// definitions of bundled standard and community modules with Java
    /// overrides (`Program::is_strict_call_def`), which evaluate their
    /// arguments eagerly.
    pub(crate) fn lazy_args_in(&self, _file: tlx_front::ast::FileId, _name: Option<&str>) -> bool {
        true
    }

    /// `scan_action(body)` of an operator value's body, cached per arena
    /// expression (a body outside the arena is scanned every time).
    pub(crate) fn lambda_is_action(&self, body: &Expr) -> bool {
        let compute = || {
            let mut deps = Vec::new();
            scan_action(&self.consts, body, &mut deps) || deps.iter().any(|d| self.def_by_name[d.idx()])
        };
        let Some(slot) = self.prog.expr_id(body).and_then(|id| self.lambda_action.get(id.index())) else {
            return compute();
        };
        match slot.load(Ordering::Relaxed) {
            0 => {
                let r = compute();
                slot.store(1 + r as u8, Ordering::Relaxed);
                r
            }
            v => v == 2,
        }
    }

    /// `lazy_args_in(file, None)` for a LAMBDA written in `file`, from the
    /// table filled by `analyze_defs`.
    pub(crate) fn lambda_lazy_args(&self, file: tlx_front::ast::FileId) -> bool {
        match self.file_lazy_args.get(file.0 as usize) {
            Some(&b) => b,
            None => self.lazy_args_in(file, None),
        }
    }

    /// Fill the per-definition classification tables.
    pub(super) fn analyze_defs(&mut self) {
        let n = self.prog.defs.len();
        let (is_const, const_deps) = self.constness(false);
        let (act, act_deps) = self.action_levels(true);
        // TLC evaluates the 0-ary constant-level module definitions once, at
        // startup (SpecProcessor.processConstantDefns), even when they make
        // random choices (e.g. a random graph), print or read files.
        let (const_level, _) = self.constness(true);
        self.def_const =
            (0..n).map(|i| const_level[i] && self.prog.defs[i].params.is_empty() && !self.prog.def_is_let(DefId(i as u32))).collect();
        let eff = self.effects(&const_deps, &act_deps, true);
        // The same, not counting applications of operator parameters: the
        // operator a 0-ary module-level definition ends up applying is a
        // LAMBDA in it or in a definition it calls (scanned there) or a
        // definition it passes (a dependency), so a call of a higher-order
        // definition (MapSeq(s, LAMBDA x : 2 * x)) does not make it
        // action-level or effectful. Only for state caching: a
        // LET definition or an argument passed by name can apply an
        // operator bound to anything.
        let (act_ho, act_deps_ho) = self.action_levels(false);
        let eff_ho = self.effects(&const_deps, &act_deps_ho, false);
        self.def_memo = (0..n)
            .map(|i| {
                let def = &self.prog.defs[i];
                is_const[i]
                    && !def.params.is_empty()
                    && def.params.iter().all(|p| self.prog.locals[p.idx()].arity == 0)
                    && matches!(def.kind, DefKind::Op(_))
                    && def.builtin.is_none()
                    && !self.prog.def_is_let(DefId(i as u32))
                    && !self.def_value.contains_key(&DefId(i as u32))
                    && !self.def_redirect.contains_key(&DefId(i as u32))
            })
            .collect();
        self.uses_trace = self.prog.defs.iter().any(|def| match &def.kind {
            DefKind::Op(e) => mentions_trace(e),
            DefKind::Fn { body, bounds } => mentions_trace(body) || bounds.iter().any(|b| mentions_trace(&b.set)),
            DefKind::Pending => false,
        });
        self.def_pure = is_const;
        self.def_effectful = eff_ho.clone();
        self.def_effectful_strict = self.strict_effects(&const_deps, &act_deps);
        self.const_cache = (0..n).map(|_| OnceLock::new()).collect();
        self.def_state_cacheable = (0..n)
            .map(|i| {
                let d = DefId(i as u32);
                let def = &self.prog.defs[i];
                !eff_ho[i]
                    && !act_ho[i]
                    && !self.def_const[i]
                    && def.params.is_empty()
                    && def.builtin.is_none()
                    && !self.prog.def_is_let(d)
                    && !self.def_value.contains_key(&d)
                    && !self.def_redirect.contains_key(&d)
                    && matches!(def.kind, DefKind::Op(_))
            })
            .collect();
        self.def_recursive_fn = (0..n)
            .map(|i| match &self.prog.defs[i].kind {
                DefKind::Fn { body, .. } => mentions_def(body, DefId(i as u32)),
                _ => false,
            })
            .collect();
        // LET definitions whose value can be kept for one evaluation of the
        // LET (TLC's LazyValue caching): 0-ary, deterministic, no next-state
        // access. A recursive function definition is included: TLC binds its
        // name to the function value itself (FcnLambdaValue.makeRecursive),
        // so the recursive applications in its body use one memoized
        // RecursiveFcn instead of building a new one (with an empty memo)
        // at every reference (Relation!TransitiveClosure).
        self.let_cacheable = (0..n)
            .map(|i| {
                let def = &self.prog.defs[i];
                !eff[i]
                    && !act[i]
                    && def.params.is_empty()
                    && self.prog.def_is_let(DefId(i as u32))
                    && (matches!(def.kind, DefKind::Op(_)) || self.def_recursive_fn[i])
            })
            .collect();
        self.def_by_name = act;
        self.def_defer_errors = (0..n).map(|i| !self.prog.is_strict_call_def(DefId(i as u32))).collect();
        self.file_lazy_args = (0..self.prog.files.len()).map(|f| self.lazy_args_in(tlx_front::ast::FileId(f as u32), None)).collect();
        self.lambda_action = (0..self.prog.arena_len()).map(|_| AtomicU8::new(0)).collect();
        // Definitions on a cycle of the call graph: only these can recurse
        // forever, so only they pay for the depth guard.
        let call_deps: Vec<Vec<DefId>> = (0..n)
            .map(|i| {
                let mut ds = Vec::new();
                match &self.prog.defs[i].kind {
                    DefKind::Op(e) => collect_def_refs(&self.consts, e, &mut ds),
                    DefKind::Fn { bounds, body } => {
                        collect_def_refs(&self.consts, body, &mut ds);
                        for b in bounds {
                            collect_def_refs(&self.consts, &b.set, &mut ds);
                        }
                    }
                    DefKind::Pending => {}
                }
                if let Some(&t) = self.def_redirect.get(&DefId(i as u32)) {
                    ds.push(t);
                }
                ds
            })
            .collect();
        self.def_recursive = recursive_defs(&call_deps);
        self.def_read_vars = self.compute_def_read_vars();
        self.closed_bounds = self.find_closed_bounds();
    }

    /// The domains of bound variables of quantifiers (also `\E` in actions)
    /// and set maps `{e : x \in S}` in the program that are closed constant
    /// expressions, numbered (see `closed_bounds`; these bindings are
    /// enumerated by `for_each_binding`).
    fn find_closed_bounds(&self) -> super::local::AddrMap<u32> {
        fn walk(ip: &Interp, e: &Expr, out: &mut super::local::AddrMap<u32>) {
            let mut add = |b: &Bound| {
                let key = Arc::as_ptr(&b.set.kind) as usize;
                if !out.contains_key(&key) && ip.is_closed_constant(&b.set) {
                    let n = out.len() as u32;
                    out.insert(key, n);
                }
            };
            match &*e.kind {
                ExprKind::Quant { bounds, .. } | ExprKind::SetMap { bounds, .. } => bounds.iter().for_each(&mut add),
                _ => {}
            }
            tlx_sema::visit::children(e, &mut |c| walk(ip, c, out));
        }
        let mut out = super::local::AddrMap::default();
        for def in &self.prog.defs {
            match &def.kind {
                DefKind::Op(e) => walk(self, e, &mut out),
                DefKind::Fn { bounds, body } => {
                    for b in bounds {
                        walk(self, &b.set, &mut out);
                    }
                    walk(self, body, &mut out);
                }
                DefKind::Pending => {}
            }
        }
        for e in &self.prog.assumes {
            walk(self, e, &mut out);
        }
        out
    }

    /// Whether `e` has the same value wherever it is evaluated: constant-level
    /// and deterministic (`is_constant_in`), and it mentions no bound
    /// variable or operator parameter, directly or through a LET definition
    /// (whose body may refer to the bound variables around it).
    pub(crate) fn is_closed_constant(&self, e: &Expr) -> bool {
        fn closed(ip: &Interp, e: &Expr) -> bool {
            let here = match &*e.kind {
                ExprKind::Local(_) | ExprKind::At | ExprKind::Var(_) | ExprKind::Let { .. } | ExprKind::Lambda { .. } => false,
                ExprKind::Apply { op: OpRef::Param(_), .. } | ExprKind::OpArg(OpRef::Param(_)) => false,
                ExprKind::Apply { op: OpRef::Def(d), .. } | ExprKind::OpArg(OpRef::Def(d)) => !ip.prog.def_is_let(*d),
                _ => true,
            };
            let mut ok = here;
            tlx_sema::visit::children(e, &mut |c| ok = ok && closed(ip, c));
            ok
        }
        closed(self, e) && self.is_constant_in(e, &crate::env::Env::default())
    }

    /// Constant-level definitions (any arity): the body is locally constant
    /// and so is every definition it uses (`startup`: see `scan_const`).
    /// Also returns, per definition, the definitions it uses.
    fn constness(&self, startup: bool) -> (Vec<bool>, Vec<Vec<DefId>>) {
        let n = self.prog.defs.len();
        let mut is_const = vec![true; n];
        let mut deps: Vec<Vec<DefId>> = vec![Vec::new(); n];
        for i in 0..n {
            let d = DefId(i as u32);
            if self.def_value.contains_key(&d) {
                continue;
            }
            if let Some(&t) = self.def_redirect.get(&d) {
                deps[i].push(t);
                continue;
            }
            let ds = &mut deps[i];
            is_const[i] = match &self.prog.defs[i].kind {
                DefKind::Pending => true,
                DefKind::Op(e) => self.scan_const(e, ds, startup),
                DefKind::Fn { bounds, body } => {
                    let mut ok = self.scan_const(body, ds, startup);
                    for b in bounds {
                        ok &= self.scan_const(&b.set, ds, startup);
                    }
                    ok
                }
            };
        }
        propagate(&mut is_const, &[&deps], false);
        (is_const, deps)
    }

    /// Action-level definitions (can observe the next state). Also returns
    /// the dependency lists. `params`: an application of an operator
    /// parameter counts as action-level.
    fn action_levels(&self, params: bool) -> (Vec<bool>, Vec<Vec<DefId>>) {
        let n = self.prog.defs.len();
        let mut act = vec![false; n];
        let mut deps: Vec<Vec<DefId>> = vec![Vec::new(); n];
        for i in 0..n {
            let ds = &mut deps[i];
            act[i] = match &self.prog.defs[i].kind {
                DefKind::Op(e) => scan_action_in(&self.consts, e, ds, params),
                DefKind::Fn { body, bounds } => {
                    let mut found = scan_action_in(&self.consts, body, ds, params);
                    for b in bounds {
                        found |= scan_action_in(&self.consts, &b.set, ds, params);
                    }
                    found
                }
                DefKind::Pending => false,
            };
            if let Some(&t) = self.def_redirect.get(&DefId(i as u32)) {
                ds.push(t);
            }
        }
        propagate(&mut act, &[&deps], true);
        (act, deps)
    }

    /// Nondeterministic / effectful definitions (TLCGet, RandomElement, ...),
    /// propagated along both dependency relations. `params`: an
    /// application of an operator parameter counts as effectful.
    fn effects(&self, const_deps: &[Vec<DefId>], act_deps: &[Vec<DefId>], params: bool) -> Vec<bool> {
        let mut eff: Vec<bool> = self
            .prog
            .defs
            .iter()
            .map(|def| {
                let local = match &def.kind {
                    DefKind::Op(e) => scan_effects(e, params),
                    DefKind::Fn { body, bounds } => scan_effects(body, params) || bounds.iter().any(|b| scan_effects(&b.set, params)),
                    DefKind::Pending => true,
                };
                local || def.builtin.is_some_and(is_effectful_builtin)
            })
            .collect();
        // A definition evaluated once at startup (`def_const`) has its
        // effects then: those that use it only read its value (a trace
        // validation's log, read from a file, makes no action effectful).
        let once = |deps: &[Vec<DefId>]| -> Vec<Vec<DefId>> {
            deps.iter().map(|ds| ds.iter().copied().filter(|d| !self.def_const[d.idx()]).collect()).collect()
        };
        propagate(&mut eff, &[&once(const_deps), &once(act_deps)], true);
        eff
    }

    /// Strict effect classification: unlike `effects`, does not exclude
    /// `def_const` dependencies (a cached constant may hold a `LazyFcn` or
    /// `FilterSet` whose body contains a volatile builtin) and also follows
    /// cfg builtin overrides (`builtin_override`) and operator parameters.
    fn strict_effects(&self, const_deps: &[Vec<DefId>], act_deps: &[Vec<DefId>]) -> Vec<bool> {
        let n = self.prog.defs.len();
        let mut eff: Vec<bool> = Vec::with_capacity(n);
        let mut override_deps: Vec<Vec<DefId>> = vec![Vec::new(); n];
        for (i, ov_deps) in override_deps.iter_mut().enumerate() {
            let d = DefId(i as u32);
            if self.def_value.contains_key(&d) || self.def_redirect.contains_key(&d) {
                eff.push(false);
                continue;
            }
            let def = &self.prog.defs[i];
            let local = match &def.kind {
                DefKind::Op(e) => self.scan_strict_effects(e, ov_deps),
                DefKind::Fn { body, bounds } => {
                    let mut found = self.scan_strict_effects(body, ov_deps);
                    for b in bounds {
                        found |= self.scan_strict_effects(&b.set, ov_deps);
                    }
                    found
                }
                DefKind::Pending => true,
            };
            let builtin_eff = match def.builtin {
                Some(b) => match self.builtin_override(b) {
                    Some(ov) if ov != d => {
                        ov_deps.push(ov);
                        false
                    }
                    _ => is_effectful_builtin(b),
                },
                None => false,
            };
            eff.push(local || builtin_eff);
        }
        propagate(&mut eff, &[const_deps, act_deps, &override_deps], true);
        eff
    }

    fn scan_strict_effects(&self, e: &Expr, deps: &mut Vec<DefId>) -> bool {
        let here = match &*e.kind {
            ExprKind::Builtin { op, .. } | ExprKind::Apply { op: OpRef::Builtin(op), .. } | ExprKind::OpArg(OpRef::Builtin(op)) => {
                if let Some(ov) = self.builtin_override(*op) {
                    deps.push(ov);
                    false
                } else {
                    is_effectful_builtin(*op)
                }
            }
            ExprKind::Apply { op: OpRef::Param(_), .. } | ExprKind::OpArg(OpRef::Param(_)) => true,
            ExprKind::Const(c) | ExprKind::Apply { op: OpRef::Const(c), .. } | ExprKind::OpArg(OpRef::Const(c)) => {
                match &self.consts[c.idx()] {
                    Some(ConstVal::Op(OpRef::Builtin(op))) => {
                        if let Some(ov) = self.builtin_override(*op) {
                            deps.push(ov);
                            false
                        } else {
                            is_effectful_builtin(*op)
                        }
                    }
                    Some(ConstVal::Op(OpRef::Param(_)) | ConstVal::Table(_)) => true,
                    _ => false,
                }
            }
            _ => false,
        };
        let mut found = here;
        tlx_sema::visit::children(e, &mut |c| found |= self.scan_strict_effects(c, deps));
        found
    }

    /// Compute the sorted, deduplicated set of state variables transitively
    /// read by each strictly effect-free, non-recursive `def_state_cacheable`
    /// definition (`None` if ineligible or variable reads are not statically
    /// closed over `VarId`).
    fn compute_def_read_vars(&self) -> Vec<Option<Box<[VarId]>>> {
        let n = self.prog.defs.len();
        let mut vars: Vec<Vec<VarId>> = vec![Vec::new(); n];
        let mut deps: Vec<Vec<DefId>> = vec![Vec::new(); n];
        let mut closed_ok = vec![true; n];
        for i in 0..n {
            let d = DefId(i as u32);
            if self.def_value.contains_key(&d) {
                continue;
            }
            if let Some(&t) = self.def_redirect.get(&d) {
                deps[i].push(t);
                continue;
            }
            if let Some(b) = self.prog.defs[i].builtin {
                if let Some(ov) = self.builtin_override(b) {
                    if ov != d {
                        deps[i].push(ov);
                    }
                } else if !constant_level_builtin(b) {
                    closed_ok[i] = false;
                }
                continue;
            }
            closed_ok[i] = match &self.prog.defs[i].kind {
                DefKind::Op(e) => self.scan_read_vars(e, &mut vars[i], &mut deps[i]),
                DefKind::Fn { bounds, body } => {
                    let mut ok = self.scan_read_vars(body, &mut vars[i], &mut deps[i]);
                    for b in bounds {
                        ok &= self.scan_read_vars(&b.set, &mut vars[i], &mut deps[i]);
                    }
                    ok
                }
                DefKind::Pending => false,
            };
            vars[i].sort_unstable();
            vars[i].dedup();
        }
        propagate(&mut closed_ok, &[&deps], false);
        loop {
            let mut changed = false;
            for i in 0..n {
                if !closed_ok[i] || self.def_effectful_strict[i] {
                    continue;
                }
                let mut cur = std::mem::take(&mut vars[i]);
                let before = cur.len();
                for &dep in &deps[i] {
                    cur.extend_from_slice(&vars[dep.idx()]);
                }
                if cur.len() > before {
                    cur.sort_unstable();
                    cur.dedup();
                    if cur.len() > before {
                        changed = true;
                    }
                }
                vars[i] = cur;
            }
            if !changed {
                break;
            }
        }
        (0..n)
            .map(|i| {
                if self.def_state_cacheable[i]
                    && !self.def_effectful_strict[i]
                    && !self.def_recursive[i]
                    && closed_ok[i]
                    && !vars[i].is_empty()
                {
                    Some(vars[i].clone().into_boxed_slice())
                } else {
                    None
                }
            })
            .collect()
    }

    fn scan_read_vars(&self, e: &Expr, vars: &mut Vec<VarId>, deps: &mut Vec<DefId>) -> bool {
        let here = match &*e.kind {
            ExprKind::Var(v) => {
                vars.push(*v);
                true
            }
            ExprKind::InstVar { .. }
            | ExprKind::Apply { op: OpRef::Param(_), .. }
            | ExprKind::OpArg(OpRef::Param(_))
            | ExprKind::BoxAction { .. }
            | ExprKind::AngleAction { .. }
            | ExprKind::Fairness { .. }
            | ExprKind::TemporalQuant { .. } => false,
            ExprKind::Apply { op: OpRef::Def(d), .. } | ExprKind::OpArg(OpRef::Def(d)) => {
                if self.def_value.contains_key(d) {
                    true
                } else {
                    let t = self.redirect_def(*d);
                    if self.def_value.contains_key(&t) {
                        true
                    } else if let Some(b) = self.prog.defs[t.idx()].builtin {
                        if let Some(ov) = self.builtin_override(b) {
                            deps.push(ov);
                            true
                        } else {
                            constant_level_builtin(b)
                        }
                    } else {
                        deps.push(t);
                        true
                    }
                }
            }
            ExprKind::Const(c) | ExprKind::Apply { op: OpRef::Const(c), .. } | ExprKind::OpArg(OpRef::Const(c)) => {
                match &self.consts[c.idx()] {
                    Some(ConstVal::Value(_)) => true,
                    Some(ConstVal::Def(d) | ConstVal::Op(OpRef::Def(d))) => {
                        let t = self.redirect_def(*d);
                        if !self.def_value.contains_key(&t) {
                            deps.push(t);
                        }
                        true
                    }
                    Some(ConstVal::Op(OpRef::Builtin(op))) => {
                        if let Some(ov) = self.builtin_override(*op) {
                            deps.push(ov);
                            true
                        } else {
                            constant_level_builtin(*op)
                        }
                    }
                    _ => false,
                }
            }
            ExprKind::Let { defs, .. } => {
                deps.extend(defs.iter().copied());
                true
            }
            ExprKind::Builtin { op, .. } | ExprKind::Apply { op: OpRef::Builtin(op), .. } | ExprKind::OpArg(OpRef::Builtin(op)) => {
                if let Some(ov) = self.builtin_override(*op) {
                    deps.push(ov);
                    true
                } else {
                    constant_level_builtin(*op)
                }
            }
            _ => true,
        };
        let mut ok = here;
        tlx_sema::visit::children(e, &mut |c| ok = ok && self.scan_read_vars(c, vars, deps));
        ok
    }

    /// Whether `e`, in `env`, is constant-level (TLC: level 0): it mentions
    /// no variable, prime, ENABLED, action or temporal operator and nothing
    /// nondeterministic or effectful, neither directly nor through
    /// definitions or by-name arguments bound in `env`.
    pub(crate) fn is_constant_in(&self, e: &Expr, env: &crate::env::Env) -> bool {
        let def = |d: DefId| self.def_value.contains_key(&d) || self.def_pure[self.redirect_def(d).idx()];
        let here = match &*e.kind {
            ExprKind::Apply { op: OpRef::Def(d), .. } | ExprKind::OpArg(OpRef::Def(d)) => def(*d),
            ExprKind::Const(c) | ExprKind::Apply { op: OpRef::Const(c), .. } | ExprKind::OpArg(OpRef::Const(c)) => {
                match &self.consts[c.idx()] {
                    Some(ConstVal::Def(d) | ConstVal::Op(OpRef::Def(d))) => def(*d),
                    Some(ConstVal::Op(OpRef::Builtin(op))) => constant_level_builtin(*op),
                    _ => true,
                }
            }
            ExprKind::Let { defs, .. } => defs.iter().all(|d| def(*d)),
            ExprKind::Local(id) => match env.lookup(*id) {
                None | Some(crate::env::Binding::Val(_)) => true,
                Some(b) => match b.by_name(&self.prog) {
                    Some((a, aenv)) => self.is_constant_in(a, aenv),
                    None => false,
                },
            },
            ExprKind::Apply { op: OpRef::Param(_), .. } => false,
            ExprKind::Var(_)
            | ExprKind::BoxAction { .. }
            | ExprKind::AngleAction { .. }
            | ExprKind::Fairness { .. }
            | ExprKind::TemporalQuant { .. } => false,
            ExprKind::Builtin { op, .. } => constant_level_builtin(*op),
            _ => true,
        };
        let mut ok = here;
        tlx_sema::visit::children(e, &mut |c| ok = ok && self.is_constant_in(c, env));
        ok
    }

    /// Whether `e`, in `env`, is deterministic and free of side effects,
    /// higher-order operator parameters, and action/temporal constructs.
    /// Unlike `is_constant_in`, state variables are permitted (for a fixed
    /// evaluation snapshot `Ctx`).
    pub(crate) fn is_effect_free_in(&self, e: &Expr, env: &crate::env::Env) -> bool {
        // Only inspect calls whose implementation is known here. User
        // operators and LET bodies can force captured lazy values, including
        // cached constants, or invoke higher-order parameters.
        let builtin = |op| self.builtin_override(op).is_none() && constant_level_builtin(op);
        let here = match &*e.kind {
            ExprKind::Apply { op: OpRef::Def(d), .. } | ExprKind::OpArg(OpRef::Def(d)) => {
                !self.has_def_value(*d) && self.redirect_def(*d) == *d && self.prog.defs[d.idx()].builtin.is_some_and(builtin)
            }
            ExprKind::Const(c) => matches!(self.consts[c.idx()], Some(ConstVal::Value(_))),
            ExprKind::Apply { op: OpRef::Const(_), .. } | ExprKind::OpArg(OpRef::Const(_)) | ExprKind::Let { .. } => false,
            ExprKind::Local(id) => match env.lookup(*id) {
                None | Some(crate::env::Binding::Val(_)) => true,
                Some(b) => match b.by_name(&self.prog) {
                    Some((a, aenv)) => self.is_effect_free_in(a, aenv),
                    None => false,
                },
            },
            ExprKind::Apply { op: OpRef::Param(_), .. }
            | ExprKind::OpArg(OpRef::Param(_))
            | ExprKind::BoxAction { .. }
            | ExprKind::AngleAction { .. }
            | ExprKind::Fairness { .. }
            | ExprKind::TemporalQuant { .. } => false,
            ExprKind::Builtin { op, .. } | ExprKind::Apply { op: OpRef::Builtin(op), .. } | ExprKind::OpArg(OpRef::Builtin(op)) => {
                builtin(*op)
            }
            _ => true,
        };
        let mut ok = here;
        tlx_sema::visit::children(e, &mut |c| ok = ok && self.is_effect_free_in(c, env));
        ok
    }

    /// Whether `e`, in `env`, is strictly deterministic and effect-free across
    /// user-defined operators (via `def_effectful_strict`, which also tracks
    /// volatile builtins inside `def_const` and `builtin_override`s). Permits
    /// state variables for a fixed evaluation snapshot `Ctx`, while rejecting
    /// higher-order operator parameters, action/temporal constructs, and
    /// `InstVar`. Callers that memoize or stream across values must also rule
    /// out lazy callables captured in runtime values (`value_has_lazy_callable`).
    pub(crate) fn is_strictly_effect_free_in(&self, e: &Expr, env: &crate::env::Env) -> bool {
        fn check(ip: &Interp, e: &Expr, env: &crate::env::Env, depth: usize) -> bool {
            if depth > 16 {
                return false;
            }
            let check_def = |d: DefId| {
                if ip.def_value.contains_key(&d) {
                    return true;
                }
                let t = ip.redirect_def(d);
                if ip.def_value.contains_key(&t) {
                    return true;
                }
                if let Some(b) = ip.prog.defs[t.idx()].builtin {
                    match ip.builtin_override(b) {
                        Some(ov) => !ip.def_effectful_strict[ov.idx()] && !ip.def_by_name[ov.idx()],
                        None => constant_level_builtin(b),
                    }
                } else {
                    !ip.def_effectful_strict[t.idx()] && !ip.def_by_name[t.idx()]
                }
            };
            let here = match &*e.kind {
                ExprKind::Apply { op: OpRef::Def(d), .. } | ExprKind::OpArg(OpRef::Def(d)) => check_def(*d),
                ExprKind::Const(c) | ExprKind::Apply { op: OpRef::Const(c), .. } | ExprKind::OpArg(OpRef::Const(c)) => {
                    match &ip.consts[c.idx()] {
                        Some(ConstVal::Value(_)) => true,
                        Some(ConstVal::Def(d) | ConstVal::Op(OpRef::Def(d))) => check_def(*d),
                        Some(ConstVal::Op(OpRef::Builtin(op))) => match ip.builtin_override(*op) {
                            Some(ov) => !ip.def_effectful_strict[ov.idx()] && !ip.def_by_name[ov.idx()],
                            None => constant_level_builtin(*op),
                        },
                        _ => false,
                    }
                }
                ExprKind::Let { defs, .. } => defs.iter().all(|d| check_def(*d)),
                ExprKind::Local(id) => match env.lookup(*id) {
                    None | Some(crate::env::Binding::Val(_)) => true,
                    Some(b) => match b.by_name(&ip.prog) {
                        Some((a, aenv)) => check(ip, a, aenv, depth + 1),
                        None => false,
                    },
                },
                ExprKind::InstVar { .. }
                | ExprKind::Apply { op: OpRef::Param(_), .. }
                | ExprKind::OpArg(OpRef::Param(_))
                | ExprKind::BoxAction { .. }
                | ExprKind::AngleAction { .. }
                | ExprKind::Fairness { .. }
                | ExprKind::TemporalQuant { .. } => false,
                ExprKind::Builtin { op, .. } | ExprKind::Apply { op: OpRef::Builtin(op), .. } | ExprKind::OpArg(OpRef::Builtin(op)) => {
                    match ip.builtin_override(*op) {
                        Some(ov) => !ip.def_effectful_strict[ov.idx()] && !ip.def_by_name[ov.idx()],
                        None => constant_level_builtin(*op),
                    }
                }
                _ => true,
            };
            if !here {
                return false;
            }
            let mut ok = true;
            tlx_sema::visit::children(e, &mut |c| ok = ok && check(ip, c, env, depth));
            ok
        }
        check(self, e, env, 0)
    }

    /// A deterministic state argument can retain its unprimed value while
    /// keeping its expression for a later prime. Be conservative about
    /// higher-order calls and LET definitions with captured bindings.
    pub(crate) fn state_argument_in(&self, e: &Expr, env: &crate::env::Env) -> bool {
        use crate::env::Binding;
        let def = |d: DefId| {
            let d = self.redirect_def(d);
            self.def_value.contains_key(&d) || (!self.def_by_name[d.idx()] && !self.def_effectful[d.idx()] && !self.prog.def_is_let(d))
        };
        let here = match &*e.kind {
            ExprKind::Apply { op: OpRef::Def(d), .. } => def(*d),
            ExprKind::Const(c) | ExprKind::Apply { op: OpRef::Const(c), .. } => match &self.consts[c.idx()] {
                Some(ConstVal::Def(d) | ConstVal::Op(OpRef::Def(d))) => def(*d),
                Some(ConstVal::Op(_)) => false,
                _ => true,
            },
            ExprKind::Local(id) => match env.lookup(*id) {
                Some(Binding::Val(v)) => !matches!(v, tlx_value::Value::LazyFcn(_) | tlx_value::Value::LazySet(_)),
                Some(Binding::Thunk(t)) if t.memo.is_some() => true,
                Some(b) => b.by_name(&self.prog).is_some_and(|(a, aenv)| self.state_argument_in(a, aenv)),
                None => false,
            },
            ExprKind::Apply { op: OpRef::Param(_), .. }
            | ExprKind::Lambda { .. }
            | ExprKind::OpArg(_)
            | ExprKind::Let { .. }
            | ExprKind::BoxAction { .. }
            | ExprKind::AngleAction { .. }
            | ExprKind::Fairness { .. }
            | ExprKind::TemporalQuant { .. } => false,
            ExprKind::Builtin { op, .. } | ExprKind::Apply { op: OpRef::Builtin(op), .. } => constant_level_builtin(*op),
            _ => true,
        };
        let mut ok = here;
        tlx_sema::visit::children(e, &mut |c| ok = ok && self.state_argument_in(c, env));
        ok
    }

    /// Whether `e` is locally constant-level; collects the definitions it uses.
    /// `startup`: volatile builtins that TLC evaluates in startup-cached
    /// definitions (`Builtin::cached_at_startup`) count as constant-level.
    fn scan_const(&self, e: &Expr, deps: &mut Vec<DefId>, startup: bool) -> bool {
        let here = match &*e.kind {
            ExprKind::Var(_) => false,
            ExprKind::Builtin { op, .. } => {
                !(matches!(op, B::Prime | B::Unchanged | B::Enabled) || (is_effectful_builtin(*op) && !(startup && op.cached_at_startup())))
            }
            ExprKind::Apply { op: OpRef::Def(d), .. } | ExprKind::OpArg(OpRef::Def(d)) => {
                deps.push(*d);
                true
            }
            ExprKind::Const(c) | ExprKind::Apply { op: OpRef::Const(c), .. } | ExprKind::OpArg(OpRef::Const(c)) => {
                match &self.consts[c.idx()] {
                    Some(ConstVal::Def(d) | ConstVal::Op(OpRef::Def(d))) => {
                        deps.push(*d);
                        true
                    }
                    Some(ConstVal::Op(OpRef::Builtin(op))) => {
                        !(matches!(op, B::Prime | B::Unchanged | B::Enabled)
                            || (is_effectful_builtin(*op) && !(startup && op.cached_at_startup())))
                    }
                    _ => true,
                }
            }
            ExprKind::Let { defs, .. } => {
                deps.extend(defs.iter().copied());
                true
            }
            ExprKind::BoxAction { .. } | ExprKind::AngleAction { .. } | ExprKind::Fairness { .. } => false,
            _ => true,
        };
        let mut ok = here;
        tlx_sema::visit::children(e, &mut |c| ok &= self.scan_const(c, deps, startup));
        ok
    }
}

/// Whether `e` (not counting called definitions) applies `TLCExt!Trace`.
fn mentions_trace(e: &Expr) -> bool {
    let here = matches!(
        &*e.kind,
        ExprKind::Builtin { op: B::Trace, .. }
            | ExprKind::OpArg(OpRef::Builtin(B::Trace))
            | ExprKind::Apply { op: OpRef::Builtin(B::Trace), .. }
    );
    let mut found = here;
    tlx_sema::visit::children(e, &mut |c| found |= mentions_trace(c));
    found
}

/// Whether `e` (not counting called definitions) is nondeterministic or has
/// effects, or (`params`) applies an operator argument.
fn scan_effects(e: &Expr, params: bool) -> bool {
    let here = match &*e.kind {
        ExprKind::Builtin { op, .. } => is_effectful_builtin(*op),
        ExprKind::Apply { op: OpRef::Param(_), .. } => params,
        _ => false,
    };
    let mut found = here;
    tlx_sema::visit::children(e, &mut |c| found |= scan_effects(c, params));
    found
}

/// Whether `e` itself can observe the next state; collects called definitions.
fn scan_action(consts: &[Option<ConstVal>], e: &Expr, deps: &mut Vec<DefId>) -> bool {
    scan_action_in(consts, e, deps, true)
}

/// `scan_action`; `params`: an application of an operator parameter counts
/// (the operator argument may be action-level).
fn scan_action_in(consts: &[Option<ConstVal>], e: &Expr, deps: &mut Vec<DefId>, params: bool) -> bool {
    let here = match &*e.kind {
        ExprKind::Builtin { op: B::Prime | B::Unchanged | B::Enabled, .. } | ExprKind::BoxAction { .. } | ExprKind::AngleAction { .. } => {
            true
        }
        // Higher-order application: the operator argument may be action-level.
        ExprKind::Apply { op: OpRef::Param(_), .. } => params,
        ExprKind::Apply { op: OpRef::Def(d), .. } | ExprKind::OpArg(OpRef::Def(d)) => {
            deps.push(*d);
            false
        }
        ExprKind::Const(c) | ExprKind::Apply { op: OpRef::Const(c), .. } | ExprKind::OpArg(OpRef::Const(c)) => match &consts[c.idx()] {
            Some(ConstVal::Def(d) | ConstVal::Op(OpRef::Def(d))) => {
                deps.push(*d);
                false
            }
            Some(ConstVal::Op(OpRef::Builtin(B::Prime | B::Unchanged | B::Enabled))) => true,
            _ => false,
        },
        ExprKind::Let { defs, .. } => {
            deps.extend(defs.iter().copied());
            false
        }
        _ => false,
    };
    let mut found = here;
    tlx_sema::visit::children(e, &mut |c| found |= scan_action_in(consts, c, deps, params));
    found
}

/// Whether `e` refers to definition `d` (directly).
fn mentions_def(e: &Expr, d: DefId) -> bool {
    if matches!(&*e.kind, ExprKind::Apply { op: OpRef::Def(x), .. } | ExprKind::OpArg(OpRef::Def(x)) if *x == d) {
        return true;
    }
    let mut found = false;
    tlx_sema::visit::children(e, &mut |c| found = found || mentions_def(c, d));
    found
}

/// The definitions `e` refers to (statically called, or a LET's local defs).
fn collect_def_refs(consts: &[Option<ConstVal>], e: &Expr, deps: &mut Vec<DefId>) {
    match &*e.kind {
        ExprKind::Apply { op: OpRef::Def(d), .. } | ExprKind::OpArg(OpRef::Def(d)) => deps.push(*d),
        ExprKind::Const(c) | ExprKind::Apply { op: OpRef::Const(c), .. } | ExprKind::OpArg(OpRef::Const(c)) => {
            if let Some(ConstVal::Def(d) | ConstVal::Op(OpRef::Def(d))) = &consts[c.idx()] {
                deps.push(*d);
            }
        }
        ExprKind::Let { defs, .. } => deps.extend(defs.iter().copied()),
        _ => {}
    }
    tlx_sema::visit::children(e, &mut |c| collect_def_refs(consts, c, deps));
}

/// The definitions that lie on a cycle of the static call graph `deps` --
/// i.e. that can call themselves (a recursive operator, or a mutually
/// recursive group). Only these can recurse forever, so only they need the
/// interpreter's recursion-depth guard. Higher-order cycles (through an
/// operator argument or LAMBDA) are not visible here and are covered by the
/// guard on operator-argument application; self-referential function
/// definitions are covered where they are applied.
fn recursive_defs(deps: &[Vec<DefId>]) -> Vec<bool> {
    let n = deps.len();
    let adj: Vec<Vec<usize>> = deps.iter().map(|ds| ds.iter().map(|d| d.idx()).filter(|&j| j < n).collect()).collect();
    let mut radj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (i, ds) in adj.iter().enumerate() {
        for &j in ds {
            radj[j].push(i);
        }
    }
    // Kosaraju: finishing order, then components of the reverse graph.
    let mut seen = vec![false; n];
    let mut order = Vec::with_capacity(n);
    for s in 0..n {
        if seen[s] {
            continue;
        }
        seen[s] = true;
        let mut stack = vec![(s, 0usize)];
        while let Some((v, k)) = stack.pop() {
            if k < adj[v].len() {
                stack.push((v, k + 1));
                let w = adj[v][k];
                if !seen[w] {
                    seen[w] = true;
                    stack.push((w, 0));
                }
            } else {
                order.push(v);
            }
        }
    }
    let mut comp = vec![usize::MAX; n];
    let mut sizes: Vec<usize> = Vec::new();
    for &s in order.iter().rev() {
        if comp[s] != usize::MAX {
            continue;
        }
        let cid = sizes.len();
        comp[s] = cid;
        let mut size = 0;
        let mut stack = vec![s];
        while let Some(v) = stack.pop() {
            size += 1;
            for &w in &radj[v] {
                if comp[w] == usize::MAX {
                    comp[w] = cid;
                    stack.push(w);
                }
            }
        }
        sizes.push(size);
    }
    (0..n).map(|i| sizes[comp[i]] > 1 || adj[i].contains(&i)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn defs(deps: &[&[usize]]) -> Vec<bool> {
        let d: Vec<Vec<DefId>> = deps.iter().map(|ds| ds.iter().map(|&i| DefId(i as u32)).collect()).collect();
        recursive_defs(&d)
    }

    #[test]
    fn recursive_defs_on_cycles() {
        assert_eq!(defs(&[&[], &[], &[]]), [false, false, false]);
        assert_eq!(defs(&[&[0]]), [true]); // self-recursive operator
        assert_eq!(defs(&[&[1], &[0]]), [true, true]); // mutually recursive
        assert_eq!(defs(&[&[1], &[]]), [false, false]); // acyclic call
        assert_eq!(defs(&[&[1], &[2], &[1]]), [false, true, true]); // chain into a cycle
        assert_eq!(defs(&[&[9]]), [false]); // out-of-range edge is ignored
    }
}
