//! RECURSIVE operators and recursive function definitions as compiled
//! functions (`ExprKind::Call`): an application whose arguments are typed
//! lowers the operator body once per combination of argument
//! representations (and lowering context) into a function of
//! `Typing::funcs`; recursive applications inside it call it.
//!
//! A recursive function definition `f[x \in S] == body` compiles to a
//! function of `x` that checks `x \in S` and evaluates `body`: applying it
//! point by point is how TLC evaluates a recursive function (lazily; it
//! caches the computed points, which only saves time). The locals the
//! definition captures (the parameters of the operators around a LET) are
//! extra parameters of the function; operator arguments it uses are part of
//! the specialization.
//!
//! The result representation is the destination encoding when there is one;
//! otherwise it is inferred: the body is first lowered with the recursive
//! calls failing (a failing branch takes the representation of the other
//! branch), then again with calls of that representation, and the body is
//! converted to it (a value not fitting it is a runtime error, handled by
//! the interpreter). Applications whose arguments are all constants are
//! unrolled instead (their conditions fold).

use std::collections::HashMap;

use tlx_sema::hir::{self, BoundVars, DefKind, ExprKind as H, LocalId, OpRef};

use super::*;

/// What a compiled function is specialized on.
#[derive(Clone, PartialEq, Eq, Hash)]
pub(super) struct FnKey {
    def: hir::DefId,
    params: Vec<Ty>,
    primed: bool,
    init: bool,
    assigned: Vec<bool>,
    into: Option<ShapeId>,
    /// Captured locals (function definitions in a LET), in parameter order
    /// after the arguments.
    caps: Vec<CapKey>,
}

/// A captured local of a function definition, as specialized on.
#[derive(Clone, PartialEq, Eq, Hash)]
enum CapKey {
    /// A value: a parameter (of the next parameter representation).
    Val,
    /// A named operator argument.
    Op(String),
    /// A LAMBDA argument (by body identity) followed by its `n` captures.
    Lambda(usize, usize),
}

/// How a captured local is bound in a function's frame.
#[derive(Clone)]
enum Cap {
    Val(LocalId),
    Op(LocalId, OpRef),
    Lambda(LocalId, Arc<[LocalId]>, hir::Expr, Vec<Cap>),
}

/// The source of a compiled function: its parameters (operator parameters
/// or function binders) bound over `base`, then its captures; with
/// `domains`, a function definition whose binders are checked to be in them.
struct FnSrc {
    params: Vec<LocalId>,
    body: hir::Expr,
    base: LEnv,
    domains: Option<Vec<hir::Expr>>,
    caps: Vec<Cap>,
}

/// A function being lowered.
pub(super) struct InProgress {
    key: FnKey,
    id: u32,
    /// Result representation assumed by recursive calls (None: they fail).
    ret: Option<Ty>,
    /// A recursive call could not be typed: give up.
    poisoned: bool,
}

/// Compiled-function state of a lowerer.
#[derive(Default)]
pub(super) struct Calls {
    done: HashMap<FnKey, (u32, Ty)>,
    progress: Vec<InProgress>,
    recursive: std::cell::RefCell<HashMap<hir::DefId, bool>>,
    /// Functions that could not be compiled (outside any other one).
    failed: std::collections::HashSet<FnKey>,
    /// Syntactic call-site counts per definition across `prog.defs` (computed lazily once).
    def_refs: std::cell::OnceCell<HashMap<hir::DefId, usize>>,
    /// Non-recursive helper definitions seen at least once during lowering
    /// (so a 1-call-site helper shared across multiple split action instances
    /// is outlined from its second encounter onward).
    seen_helpers: std::collections::HashSet<hir::DefId>,
}

/// Most attempts at inferring a result representation.
const ATTEMPTS: usize = 4;
/// Minimum HIR nodes to outline a pure non-recursive operator into a shared
/// compiled function (lower when the body contains a quantifier/comprehension).
const HELPER_MIN_HIR: usize = 24;
const HELPER_LOOP_MIN_HIR: usize = 10;
/// Minimum lowered IR nodes to keep an outlined non-recursive helper.
const HELPER_MIN_IR: usize = 16;

impl Lowerer<'_> {
    /// Source definition when a function body is still a lowering placeholder.
    pub(super) fn pending_fn(&self, func: u32) -> Option<hir::DefId> {
        self.calls.progress.iter().find(|p| p.id == func).map(|p| p.key.def)
    }

    /// `d(args)` as a call of a compiled function, if `d` is a recursive
    /// module-level operator applied (outside actions) to typed arguments.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn recursive_call(
        &mut self,
        d: hir::DefId,
        params: &[LocalId],
        body: &hir::Expr,
        base: &LEnv,
        args: &[hir::Expr],
        env: &LEnv,
        st: &St,
        into: Option<ShapeId>,
    ) -> Option<Expr> {
        if !self.is_recursive_def(d) || self.ip.prog.def_is_let(d) || self.ip.is_action_level(d) {
            return None;
        }
        if params.iter().any(|p| self.ip.prog.locals[p.idx()].arity > 0) {
            return None;
        }
        // Which next-state variables are assigned only matters where
        // variables may read the next state (Init, primed expressions;
        // non-action operators contain no primes).
        let assigned = if st.init || self.primed { st.assigned.clone() } else { Vec::new() };
        let in_progress = self
            .calls
            .progress
            .iter()
            .rposition(|p| p.key.def == d && p.key.primed == self.primed && p.key.init == st.init && p.key.assigned == assigned);
        if in_progress.is_none() && self.const_driven_call(args, env) {
            return None;
        }
        // The arguments, by value (constants encoded).
        let mut vals = Vec::new();
        for a in args {
            let x = self.expr(a, env, st);
            match self.typed_arg(x) {
                Some(x) => vals.push(x),
                None => {
                    if let Some(i) = in_progress {
                        self.calls.progress[i].poisoned = true;
                    }
                    return None;
                }
            }
        }
        if let Some(i) = in_progress {
            return Some(self.call_in_progress(i, vals));
        }
        let key = FnKey {
            def: d,
            params: vals.iter().map(|x| x.ty).collect(),
            primed: self.primed,
            init: st.init,
            assigned,
            into,
            caps: Vec::new(),
        };
        let src = FnSrc { params: params.to_vec(), body: body.clone(), base: base.clone(), domains: None, caps: Vec::new() };
        self.call_fn(key, &src, vals, st)
    }

    /// `d(args)` as a call of a shared compiled helper when `d` is a
    /// substantial, pure, non-recursive, state-level module operator applied
    /// to typed arguments (so repeated call sites share one IR/C/JIT body
    /// instead of duplicating it across every action and branch).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn helper_call(
        &mut self,
        d: hir::DefId,
        params: &[LocalId],
        body: &hir::Expr,
        base: &LEnv,
        args: &[hir::Expr],
        env: &LEnv,
        st: &St,
        into: Option<ShapeId>,
    ) -> Option<Expr> {
        if self.ip.prog.def_is_let(d)
            || self.is_recursive_def(d)
            || self.ip.is_action_level(d)
            || self.def_volatile(d)
            || self.inline_stack.contains(&d)
            || self.calls.progress.iter().any(|p| p.key.def == d)
        {
            return None;
        }
        if params.iter().any(|p| self.ip.prog.locals[p.idx()].arity > 0) {
            return None;
        }
        if !worth_outlining(body) {
            return None;
        }
        if self.def_ref_count(d) < 2 && self.calls.seen_helpers.insert(d) {
            return None;
        }
        if !args.is_empty() && self.const_driven_call(args, env) {
            return None;
        }
        if self.expr_makes_strings(body, base) {
            return None;
        }
        let defer = self.defers_arg_errors(Some(d), body);
        for (p, a) in params.iter().zip(args) {
            if self.is_product_literal(a, env) || self.is_lazy_fn_ref(a, env) {
                return None;
            }
            if defer {
                let uses = super::expr::local_uses(&self.ip.prog, body, *p);
                if st.init && uses == 0 {
                    return None;
                }
                if !st.init && self.const_value(a, env).is_none() && self.constructs(a, env) && uses <= 1 {
                    return None;
                }
            }
        }
        let mark = self.frame.snapshot();
        let mut vals = Vec::with_capacity(args.len());
        for a in args {
            let x = self.expr(a, env, st);
            match self.typed_arg(x) {
                Some(x) => vals.push(x),
                None => {
                    self.frame.restore(mark);
                    return None;
                }
            }
        }
        let assigned = if st.init || self.primed { st.assigned.clone() } else { Vec::new() };
        let key = FnKey {
            def: d,
            params: vals.iter().map(|x| x.ty).collect(),
            primed: self.primed,
            init: st.init,
            assigned,
            into,
            caps: Vec::new(),
        };
        if let Some(&(id, ret)) = self.calls.done.get(&key) {
            return Some(Expr::new(ret, ExprKind::Call { func: id, args: vals }));
        }
        if self.calls.failed.contains(&key) {
            self.frame.restore(mark);
            return None;
        }
        let start = self.typing.funcs.len();
        let src = FnSrc { params: params.to_vec(), body: body.clone(), base: base.clone(), domains: None, caps: Vec::new() };
        let (out, temps, ptemps) = self.lower_fn_body(&key, &src, st);
        let mut cov = crate::ir::Coverage::default();
        cov.expr(&out);
        let ok =
            out.ty != Ty::Val && cov.fully_typed() && helper_ir_native(&out) && (expr_nodes(&out) >= HELPER_MIN_IR || expr_has_loop(&out));
        if !ok {
            self.rollback_fns(start);
            if self.calls.progress.is_empty() {
                self.calls.failed.insert(key);
            }
            self.frame.restore(mark);
            return None;
        }
        let id = self.typing.funcs.len() as u32;
        let ret = out.ty;
        let name: Arc<str> = self.ip.prog.defs[d.idx()].name.clone();
        self.typing.funcs.push(FnDef { name, params: ptemps, temps, ret, body: out, budgeted: false });
        self.typing.funcs_changed();
        self.calls.done.insert(key, (id, ret));
        Some(Expr::new(ret, ExprKind::Call { func: id, args: vals }))
    }

    /// `f[args]` as a call of a compiled function, if `f` is a recursive
    /// function definition `f[x \in S, ...] == body` (one local per binder;
    /// `env` is the environment of its use) applied to typed arguments
    /// (each in its environment) and its captured locals are typed values
    /// or operator arguments. `calls` is the number of applications of `f`
    /// in its body; with `into`, the function returns that encoding.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn recursive_fn_call(
        &mut self,
        d: hir::DefId,
        vars: &[(BoundVars, hir::Expr)],
        body: &hir::Expr,
        args: &[(hir::Expr, LEnv)],
        env: &LEnv,
        calls: usize,
        into: Option<ShapeId>,
        st: &St,
    ) -> Option<Expr> {
        let mut params = Vec::new();
        for (v, _) in vars {
            match v {
                BoundVars::Many(ls) if ls.len() == 1 => params.push(ls[0]),
                _ => return None,
            }
        }
        // The interpreter keeps the points of a constant-level definition
        // computed in any state: better than recomputing a branching
        // recursion.
        if calls > 1 && self.ip.is_const_def(d) {
            return None;
        }
        let assigned = if st.init || self.primed { st.assigned.clone() } else { Vec::new() };
        // Linear recursion applied to constants is unrolled instead (its
        // conditions fold).
        if calls == 1
            && !self.calls.progress.iter().any(|p| p.key.def == d)
            && args.iter().all(|(a, aenv)| self.const_value(a, aenv).is_some())
        {
            return None;
        }
        // The captured locals, then the arguments.
        let domains: Vec<hir::Expr> = vars.iter().map(|(_, s)| s.clone()).collect();
        let mut exprs = domains.clone();
        exprs.push(body.clone());
        let mut keys = Vec::new();
        let (caps, cvals) = self.captures(&exprs, &params, env, &mut keys, st)?;
        // A definition classified action-level (e.g. through an operator
        // argument) is compiled if it does not access the next state.
        if self.ip.is_action_level(d) && !(exprs.iter().all(|e| self.state_level(e, &mut Vec::new())) && self.caps_state_level(&caps)) {
            return None;
        }
        let i = self.calls.progress.iter().rposition(|p| {
            p.key.def == d && p.key.primed == self.primed && p.key.init == st.init && p.key.assigned == assigned && p.key.caps == keys
        });
        let mut vals = Vec::new();
        for (a, aenv) in args {
            let x = self.expr(a, aenv, st);
            match self.typed_arg(x) {
                Some(x) => vals.push(x),
                None => {
                    if let Some(i) = i {
                        self.calls.progress[i].poisoned = true;
                    }
                    return None;
                }
            }
        }
        vals.extend(cvals);
        if let Some(i) = i {
            return Some(self.call_in_progress(i, vals));
        }
        let key =
            FnKey { def: d, params: vals.iter().map(|x| x.ty).collect(), primed: self.primed, init: st.init, assigned, into, caps: keys };
        let src = FnSrc { params, body: body.clone(), base: LEnv::new(Env::default()), domains: Some(domains), caps };
        self.call_fn(key, &src, vals, st)
    }

    /// The captured locals of `exprs` (bound in `env`, other than `params`):
    /// how to bind them in a function's frame and their values (appending
    /// their keys to `keys`). None if one cannot be passed.
    fn captures(
        &mut self,
        exprs: &[hir::Expr],
        params: &[LocalId],
        env: &LEnv,
        keys: &mut Vec<CapKey>,
        st: &St,
    ) -> Option<(Vec<Cap>, Vec<Expr>)> {
        let mut used = Vec::new();
        let mut seen = Vec::new();
        for e in exprs {
            self.free_locals(e, &mut used, &mut seen);
        }
        let mut caps = Vec::new();
        let mut vals = Vec::new();
        for l in used {
            if params.contains(&l) {
                continue;
            }
            match env.lookup(l, &self.ip.prog) {
                None => {} // bound inside
                Some(LBind::Ir(x)) => {
                    vals.push(self.typed_arg(x)?);
                    caps.push(Cap::Val(l));
                    keys.push(CapKey::Val);
                }
                // Evaluated eagerly: an error it raises is a runtime
                // failure (the interpreter then evaluates it lazily).
                Some(LBind::Thunk(e, tenv)) => {
                    let x = self.expr(&e, &tenv, st);
                    vals.push(self.typed_arg(x)?);
                    caps.push(Cap::Val(l));
                    keys.push(CapKey::Val);
                }
                Some(LBind::Op(LOp::Ref(r))) => {
                    if matches!(r, OpRef::Param(_)) {
                        return None;
                    }
                    caps.push(Cap::Op(l, r));
                    keys.push(CapKey::Op(format!("{r:?}")));
                }
                Some(LBind::Op(LOp::Lambda(ps, b, lenv))) => {
                    let at = keys.len();
                    let id = Arc::as_ptr(&b.kind) as usize;
                    keys.push(CapKey::Lambda(id, 0));
                    let (sub, subvals) = self.captures(std::slice::from_ref(&b), &ps, &lenv, keys, st)?;
                    keys[at] = CapKey::Lambda(id, keys.len() - at - 1);
                    vals.extend(subvals);
                    caps.push(Cap::Lambda(l, ps, b, sub));
                }
            }
        }
        Some((caps, vals))
    }

    /// `e` does not access the next state (no prime, UNCHANGED, ENABLED or
    /// action composition, also in the definitions it applies; applications
    /// of operator parameters are checked by the caller).
    fn state_level(&self, e: &hir::Expr, seen: &mut Vec<hir::DefId>) -> bool {
        use tlx_sema::builtins::Builtin as B;
        match &*e.kind {
            H::Builtin { op: B::Prime | B::Unchanged | B::Enabled | B::Compose, .. }
            | H::OpArg(OpRef::Builtin(B::Prime | B::Unchanged | B::Enabled | B::Compose)) => return false,
            H::Apply { op: OpRef::Def(x), .. } | H::OpArg(OpRef::Def(x)) => {
                let x = self.ip.redirect_def(*x);
                if self.ip.is_action_level(x) && !seen.contains(&x) {
                    seen.push(x);
                    let ok = match &self.ip.prog.defs[x.idx()].kind {
                        DefKind::Op(b) => self.state_level(b, seen),
                        DefKind::Fn { bounds, body } => {
                            bounds.iter().all(|b| self.state_level(&b.set, seen)) && self.state_level(body, seen)
                        }
                        DefKind::Pending => false,
                    };
                    if !ok {
                        return false;
                    }
                }
            }
            _ => {}
        }
        let mut ok = true;
        tlx_sema::visit::children(e, &mut |c| ok = ok && self.state_level(c, seen));
        ok
    }

    /// The operator arguments among `caps` do not access the next state.
    fn caps_state_level(&self, caps: &[Cap]) -> bool {
        caps.iter().all(|c| match c {
            Cap::Val(_) => true,
            Cap::Op(_, r) => {
                let e = hir::Expr::new(H::OpArg(*r), tlx_sema::hir::Span::default());
                self.state_level(&e, &mut Vec::new())
            }
            Cap::Lambda(_, _, b, sub) => self.state_level(b, &mut Vec::new()) && self.caps_state_level(sub),
        })
    }

    /// Call the function for `key` (compiled from `src` if needed).
    fn call_fn(&mut self, key: FnKey, src: &FnSrc, vals: Vec<Expr>, st: &St) -> Option<Expr> {
        let (id, ret) = match self.calls.done.get(&key) {
            Some(x) => *x,
            None if self.calls.failed.contains(&key) => return None,
            None => {
                let top = self.calls.progress.is_empty();
                let r = self.compile_fn(key.clone(), src, st);
                if r.is_none() && top {
                    self.calls.failed.insert(key);
                }
                r?
            }
        };
        Some(Expr::new(ret, ExprKind::Call { func: id, args: vals }))
    }

    /// A recursive call inside the function being lowered: its arguments
    /// converted to its parameter representations.
    fn call_in_progress(&mut self, i: usize, vals: Vec<Expr>) -> Expr {
        let (id, ret, tys) = {
            let p = &self.calls.progress[i];
            (p.id, p.ret, p.key.params.clone())
        };
        let Some(ret) = ret else {
            return Expr::new(Ty::Val, ExprKind::Fail("recursive call while inferring the result".into()));
        };
        let mut args = Vec::new();
        for (x, t) in vals.into_iter().zip(tys) {
            match self.to_repr(x, t) {
                Some(x) => args.push(x),
                None => {
                    self.calls.progress[i].poisoned = true;
                    return Expr::new(ret, ExprKind::Fail("argument of another representation".into()));
                }
            }
        }
        Expr::new(ret, ExprKind::Call { func: id, args })
    }

    /// Lower the function for `key` (`d`'s body with its parameters bound
    /// to the function's parameter temps); None if it cannot be typed.
    fn compile_fn(&mut self, key: FnKey, src: &FnSrc, st: &St) -> Option<(u32, Ty)> {
        let start = self.typing.funcs.len();
        let name: Arc<str> = self.ip.prog.defs[key.def.idx()].name.clone();
        let budgeted = src.domains.is_some();
        let placeholder = FnDef {
            name: name.clone(),
            params: Vec::new(),
            temps: Vec::new(),
            ret: Ty::Val,
            body: Expr::new(Ty::Val, ExprKind::Fail("function being compiled".into())),
            budgeted: false,
        };
        // Candidate result representations: the destination, else the one
        // the body produces with failing recursive calls, then those of the
        // parameters (e.g. a function returning a value like its argument).
        let mut candidates: Vec<Ty> = Vec::new();
        match key.into {
            Some(sid) => candidates.push(Ty::Enc(sid)),
            None => {
                let (out, _, poisoned) = self.lower_attempt(&key, start, &placeholder, None, src, st);
                if !poisoned && out.ty != Ty::Val && !matches!(&*out.kind, ExprKind::Fail(_)) {
                    candidates.push(out.ty);
                }
                // A boxed result whose branches are scalars (`IF cur > n
                // THEN cur ELSE Min({cur, F(cur + 1)})`): the scalar.
                if !poisoned && out.ty == Ty::Val {
                    let mut leaves = Vec::new();
                    branch_types(&out, &mut leaves);
                    for t in leaves {
                        if matches!(t, Ty::Int | Ty::Bool) && !candidates.contains(&t) {
                            candidates.push(t);
                        }
                    }
                }
                for t in &key.params {
                    if matches!(t, Ty::Enc(_)) && !candidates.contains(t) {
                        candidates.push(*t);
                    }
                }
                // The points of a function definition are often scalars.
                if src.domains.is_some() {
                    for t in [Ty::Int, Ty::Bool] {
                        if !candidates.contains(&t) {
                            candidates.push(t);
                        }
                    }
                }
            }
        }
        // The first candidate giving a fully typed body (else the first
        // one that converts at all).
        let mut fallback: Option<FnDef> = None;
        let mut tried = 0;
        while tried < candidates.len() && tried < ATTEMPTS {
            let r = candidates[tried];
            tried += 1;
            let (out, rest, poisoned) = self.lower_attempt(&key, start, &placeholder, Some(r), src, st);
            if poisoned {
                continue;
            }
            let (mut temps, ptemps) = rest;
            let out_ty = out.ty;
            // Conversions may need temps of the function's frame.
            let saved = std::mem::replace(&mut self.temps, std::mem::take(&mut temps));
            let out = self.to_repr(out, r);
            let temps = std::mem::replace(&mut self.temps, saved);
            let Some(out) = out else {
                // Try the representation the body produced.
                if key.into.is_none() && out_ty != Ty::Val && !candidates.contains(&out_ty) {
                    candidates.push(out_ty);
                }
                continue;
            };
            let f = FnDef { name: name.clone(), params: ptemps, temps, ret: r, body: out, budgeted };
            let cov = {
                let mut c = crate::ir::Coverage::default();
                c.expr(&f.body);
                c
            };
            if cov.fully_typed() {
                return self.finish_fn(start, key, f);
            }
            if fallback.is_none() {
                fallback = Some(f);
            }
        }
        if let Some(f) = fallback {
            // Lower it again so that the functions it calls are its own.
            let r = f.ret;
            let (out, (temps, ptemps), poisoned) = self.lower_attempt(&key, start, &placeholder, Some(r), src, st);
            if !poisoned {
                let mut temps = temps;
                let saved = std::mem::replace(&mut self.temps, std::mem::take(&mut temps));
                let out = self.to_repr(out, r);
                let temps = std::mem::replace(&mut self.temps, saved);
                if let Some(out) = out {
                    return self.finish_fn(start, key, FnDef { name, params: ptemps, temps, ret: r, body: out, budgeted });
                }
            }
        }
        self.rollback_fns(start);
        None
    }

    /// Record function `f` (being compiled at index `start`).
    fn finish_fn(&mut self, start: usize, key: FnKey, f: FnDef) -> Option<(u32, Ty)> {
        let r = f.ret;
        self.typing.funcs[start] = f;
        self.typing.funcs_changed();
        self.calls.done.insert(key, (start as u32, r));
        Some((start as u32, r))
    }

    /// One attempt at lowering the function at index `start` with result
    /// representation `ret` (None: recursive calls fail): the body, the
    /// frame's temps and parameter temps, and whether it was poisoned.
    #[allow(clippy::too_many_arguments)]
    fn lower_attempt(
        &mut self,
        key: &FnKey,
        start: usize,
        placeholder: &FnDef,
        ret: Option<Ty>,
        src: &FnSrc,
        st: &St,
    ) -> (Expr, (Vec<Ty>, Vec<Temp>), bool) {
        self.rollback_fns(start);
        self.typing.funcs.push(placeholder.clone());
        self.typing.funcs_changed();
        self.calls.progress.push(InProgress { key: key.clone(), id: start as u32, ret, poisoned: false });
        let (out, temps, ptemps) = self.lower_fn_body(key, src, st);
        self.typing.invalidate();
        let poisoned = self.calls.progress.pop().is_none_or(|p| p.poisoned);
        (out, (temps, ptemps), poisoned)
    }

    /// Forget the functions from `start` on (an attempt is redone).
    fn rollback_fns(&mut self, start: usize) {
        self.typing.funcs.truncate(start);
        self.typing.funcs_changed();
        self.calls.done.retain(|_, (id, _)| (*id as usize) < start);
    }

    /// `d`'s body in a fresh frame (the caller's frame is swapped out and
    /// restored): the result, the frame's temps and the parameter temps.
    fn lower_fn_body(&mut self, key: &FnKey, src: &FnSrc, st: &St) -> (Expr, Vec<Ty>, Vec<Temp>) {
        let outer = self.frame.swap();
        // The body of `key.def` runs with `key.def` on the inline stack (to
        // stop at its own recursion) and in the primed-ness of the call site.
        self.inline_stack.push(key.def);
        self.primed = key.primed;
        let mut env = src.base.clone();
        let mut ptemps = Vec::new();
        let mut tys = key.params.iter().copied();
        for p in &src.params {
            let t = tys.next().unwrap_or(Ty::Val);
            let tmp = self.temp(t);
            ptemps.push(tmp);
            env = env.bind(*p, LBind::Ir(temp_ref(t, tmp)));
        }
        env = self.bind_caps(&src.caps, env, &mut tys, &mut ptemps);
        let mut out = match key.into {
            Some(sid) => {
                let x = self.expr_into(&src.body, &env, st, sid);
                self.coerce_enc(x, sid)
            }
            None => self.expr(&src.body, &env, st),
        };
        if let Some(domains) = &src.domains {
            // Applying a function to an argument outside its domain is an
            // error (checked before the body is evaluated).
            let mut checks = Vec::new();
            for (p, set) in src.params.iter().zip(domains) {
                let x = hir::Expr::new(H::Local(*p), set.span);
                let c = self.typed_in(&x, set, &env, st);
                if c.ty != Ty::Bool {
                    if let Some(p) = self.calls.progress.last_mut() {
                        p.poisoned = true;
                    }
                }
                checks.push(c);
            }
            let in_dom = if checks.len() == 1 { checks.swap_remove(0) } else { and(checks) };
            let fail = Expr::new(out.ty, ExprKind::Fail("Attempted to apply function to an argument not in its domain.".into()));
            out = Expr::new(out.ty, ExprKind::If(in_dom, out, fail));
        }
        self.hoist_typed(&mut out);
        self.share_ranks(&mut out);
        let temps = std::mem::take(&mut self.frame.temps);
        self.frame = outer;
        (out, temps, ptemps)
    }

    /// Bind captures `caps` over `env`, the values to parameters of the
    /// next representations of `tys`.
    fn bind_caps(&mut self, caps: &[Cap], mut env: LEnv, tys: &mut impl Iterator<Item = Ty>, ptemps: &mut Vec<Temp>) -> LEnv {
        for c in caps {
            match c {
                Cap::Val(l) => {
                    let t = tys.next().unwrap_or(Ty::Val);
                    let tmp = self.temp(t);
                    ptemps.push(tmp);
                    env = env.bind(*l, LBind::Ir(temp_ref(t, tmp)));
                }
                Cap::Op(l, r) => env = env.bind(*l, LBind::Op(LOp::Ref(*r))),
                Cap::Lambda(l, ps, b, sub) => {
                    let lenv = self.bind_caps(sub, LEnv::new(Env::default()), tys, ptemps);
                    env = env.bind(*l, LBind::Op(LOp::Lambda(ps.clone(), b.clone(), lenv)));
                }
            }
        }
        env
    }

    /// `x` as an argument of a compiled function: typed, or a constant
    /// encoded in a shape holding it.
    fn typed_arg(&mut self, x: Expr) -> Option<Expr> {
        match x.ty {
            Ty::Bool | Ty::Int | Ty::Enc(_) => Some(x),
            Ty::Val => {
                let ExprKind::Const(v) = &*x.kind else { return None };
                let v = v.clone();
                match v {
                    Value::Bool(_) | Value::Int(_) => Some(const_expr(v)),
                    _ => {
                        let s = self.fit_shape(std::slice::from_ref(&v))?;
                        let sid = self.sid(&s);
                        self.const_words(&v, sid)
                    }
                }
            }
        }
    }

    /// `x` in representation `t` (None if not natively convertible).
    #[allow(clippy::wrong_self_convention)] // converts `x`, not self; needs &mut self
    fn to_repr(&mut self, x: Expr, t: Ty) -> Option<Expr> {
        if x.ty == t {
            return Some(x);
        }
        if let ExprKind::Fail(m) = &*x.kind {
            return Some(Expr::new(t, ExprKind::Fail(m.clone())));
        }
        match t {
            Ty::Int => self.as_int(x).ok(),
            Ty::Bool => self.as_bool(x).ok(),
            Ty::Enc(sid) => {
                let y = self.coerce_enc(x, sid);
                (!matches!(&*y.kind, ExprKind::Convert(z) if matches!(z.ty, Ty::Val | Ty::Enc(_)))).then_some(y)
            }
            Ty::Val => None,
        }
    }

    /// All arguments are compile-time constants: unrolling folds.
    fn const_driven_call(&self, args: &[hir::Expr], env: &LEnv) -> bool {
        args.iter().all(|a| self.const_value(a, env).is_some())
    }

    /// Number of syntactic references to definition `d` across all definitions
    /// in the program (cached once per lowerer).
    fn def_ref_count(&self, d: hir::DefId) -> usize {
        let counts = self.calls.def_refs.get_or_init(|| {
            let mut map = HashMap::new();
            let mut callees = Vec::new();
            for def in &self.ip.prog.defs {
                callees.clear();
                match &def.kind {
                    DefKind::Op(b) => collect_callees(b, &mut callees),
                    DefKind::Fn { bounds, body } => {
                        for b in bounds {
                            collect_callees(&b.set, &mut callees);
                        }
                        collect_callees(body, &mut callees);
                    }
                    DefKind::Pending => {}
                }
                for c in &callees {
                    *map.entry(self.ip.redirect_def(*c)).or_insert(0) += 1;
                }
            }
            map
        });
        counts.get(&d).copied().unwrap_or(0)
    }

    /// Whether operator `d` can reach an application of itself (through
    /// the operators its body applies).
    pub(super) fn is_recursive_def(&self, d: hir::DefId) -> bool {
        if let Some(r) = self.calls.recursive.borrow().get(&d) {
            return *r;
        }
        let mut seen = std::collections::HashSet::new();
        let mut stack = vec![d];
        let mut found = false;
        while let Some(x) = stack.pop() {
            let DefKind::Op(b) = &self.ip.prog.defs[x.idx()].kind else { continue };
            let mut callees = Vec::new();
            collect_callees(b, &mut callees);
            for c in callees {
                let c = self.ip.redirect_def(c);
                if c == d {
                    found = true;
                    break;
                }
                if seen.insert(c) && self.ip.prog.defs[c.idx()].builtin.is_none() {
                    stack.push(c);
                }
            }
            if found {
                break;
            }
        }
        self.calls.recursive.borrow_mut().insert(d, found);
        found
    }
}

/// The definitions applied (or passed as operators) in `e`.
fn collect_callees(e: &hir::Expr, out: &mut Vec<hir::DefId>) {
    if let H::Apply { op: OpRef::Def(d), .. } | H::OpArg(OpRef::Def(d)) = &*e.kind {
        out.push(*d);
    }
    tlx_sema::visit::children(e, &mut |c| collect_callees(c, out));
}

/// The representations of the values `e` can take, looking through
/// conditionals and LETs (before conversion to a common one).
fn branch_types(e: &Expr, out: &mut Vec<Ty>) {
    match &*e.kind {
        ExprKind::If(_, t, f) => {
            branch_types(t, out);
            branch_types(f, out);
        }
        ExprKind::Let { body, .. } => branch_types(body, out),
        ExprKind::Convert(x) if e.ty == Ty::Val => branch_types(x, out),
        ExprKind::Fail(_) => {}
        _ => out.push(e.ty),
    }
}

/// Whether `body` is large enough (or contains a quantifier/comprehension) to
/// justify outlining into a shared compiled helper.
fn worth_outlining(body: &hir::Expr) -> bool {
    fn walk(e: &hir::Expr, nodes: &mut usize, has_loop: &mut bool) {
        if *nodes >= HELPER_MIN_HIR {
            return;
        }
        *nodes += 1;
        if matches!(&*e.kind, H::Quant { .. } | H::Choose { .. } | H::SetFilter { .. } | H::SetMap { .. } | H::FnConstruct { .. }) {
            *has_loop = true;
        }
        tlx_sema::visit::children(e, &mut |c| walk(c, nodes, has_loop));
    }
    let (mut nodes, mut has_loop) = (0, false);
    walk(body, &mut nodes, &mut has_loop);
    nodes >= HELPER_MIN_HIR || (has_loop && nodes >= HELPER_LOOP_MIN_HIR)
}

/// Whether `e` contains only IR constructs that a compiled `FnDef` (which has
/// no host `h`/`cx` pointers) can execute natively.
fn helper_ir_native(e: &Expr) -> bool {
    match &*e.kind {
        ExprKind::Enabled(_) | ExprKind::RefOp { .. } | ExprKind::RefElems(_) => return false,
        ExprKind::Const(_) if e.ty == Ty::Val => return false,
        _ => {}
    }
    let mut ok = true;
    e.for_each_child(&mut |c| ok = ok && helper_ir_native(c));
    ok
}

fn expr_nodes(e: &Expr) -> usize {
    let mut n = 1;
    e.for_each_child(&mut |c| n += expr_nodes(c));
    n
}

fn expr_has_loop(e: &Expr) -> bool {
    let here = matches!(
        &*e.kind,
        ExprKind::Exists { .. }
            | ExprKind::Forall { .. }
            | ExprKind::Choose { .. }
            | ExprKind::Filter { .. }
            | ExprKind::SeqFilter { .. }
            | ExprKind::Fold { .. }
            | ExprKind::UnionFold { .. }
            | ExprKind::Collect { .. }
            | ExprKind::MapBuild { .. }
            | ExprKind::MapSet { .. }
    );
    let mut found = here;
    if !found {
        e.for_each_child(&mut |c| found = found || expr_has_loop(c));
    }
    found
}
