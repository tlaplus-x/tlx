//! The mechanics the three environment-aware HIR walks share.
//!
//! `lower::summary_hir` (fallback read sets), `lower::materialize`
//! (definition reachability) and `exec::memo` (memo purity and read sets)
//! all follow the same HIR shapes to the same places. An operator reference
//! in `Apply`/`OpArg` resolves — after the cfg's `Def <- Def` redirections —
//! to a definition, a constant, a builtin, or an operator parameter or a
//! local, which is followed to what the environment binds it to: a thunk's
//! expression, a `LAMBDA`'s body, another operator reference, or a by-name
//! argument. A definition body is walked in its own scope (it refers to no
//! local of its caller's environment: its parameters are bound at its call
//! sites), and `Let` definitions are walked where the `Let` names them, in
//! the environment current there.
//!
//! Only those mechanics live here; what a reached node *means* is the
//! policy's (`Policy`): a read set, a reachability test, a purity verdict.
//! So is the [`Scope`] the walk keeps (the single current environment,
//! replaced when the walk enters a closure or a definition body, or every
//! environment reached; [`State::new`] takes it), whether the walk counts
//! structural depth, whether
//! `'e`/`UNCHANGED` priming is tracked, what a constant resolves to in value
//! position and in operator position, and how a definition visit is
//! memoized. `State` owns the mechanics, `Policy` the differences.
//!
//! The simpler definition-stack walks in `enc::speculate` are deliberately
//! not expressed here: their roots and policies differ, and folding them in
//! is a separate question (`CODE-08`, `CODE-23`).

use std::sync::Arc;

use tlx_eval::env::{Binding, Env, OpVal, Thunk};
use tlx_eval::Interp;
use tlx_sema::builtins::Builtin;
use tlx_sema::hir::{self, ConstId, DefId, DefKind, ExprKind as H, LocalId, OpRef};
use tlx_sema::visit;

use crate::ir::Deferred;

/// How the walk continues at an expression node.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Flow {
    /// Walk the node's children; the driver resolves `Const`, `Local`,
    /// `Apply`/`OpArg` and `Let` itself (see [`State::walk`]).
    Children,
    /// Walk no children: the node was handled, or the walk is over.
    Done,
    /// Walk the builtin's arguments primed (`'e`).
    PrimedArgs,
    /// Walk the builtin's arguments unprimed and then primed (`UNCHANGED e`).
    BothArgs,
}

/// How the walk's environment scope grows.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Scope {
    /// One current environment: entering a closure replaces it, and a
    /// definition body replaces it with the empty environment, so a free
    /// local resolves in that one environment only. `lower::summary_hir`
    /// and `lower::materialize` walk this way.
    Single,
    /// Every environment reached stays in scope, so a free local resolves in
    /// any enclosing closure that bound it; a definition body keeps the
    /// environments current at its call site. `exec::memo` walks this way.
    Shared,
}

/// The shared traversal state: the interpreter, the environments a free local
/// resolves in, and the primed flag (`'e`).
pub(crate) struct State<'a> {
    /// The interpreter being walked (its program, cfg overrides and
    /// redirections).
    pub(crate) ip: &'a Interp,
    /// The environments in scope, outermost first.
    scope: Vec<Env>,
    /// The environments a `Single` scope has replaced (a stack, so nested
    /// closures and definition bodies restore in order).
    saved: Vec<Env>,
    scope_kind: Scope,
    /// `'e` is in effect: the walk is reading the next state.
    primed: bool,
}

impl<'a> State<'a> {
    pub(crate) fn new(ip: &'a Interp, scope_kind: Scope, env: Env) -> State<'a> {
        State { ip, scope: vec![env], saved: Vec::new(), scope_kind, primed: false }
    }

    /// Whether reads are next-state reads (inside `'e` or `UNCHANGED e`).
    pub(crate) fn primed(&self) -> bool {
        self.primed
    }

    /// Walk `e` at `depth`: the node policy, the generic resolution of
    /// `Const`, `Local`, `Apply`/`OpArg` and `Let`, then the children in the
    /// policy's child depth.
    pub(crate) fn walk<P: Policy>(&mut self, p: &mut P, e: &hir::Expr, depth: usize) {
        if p.node(self, e, depth) == Flow::Done {
            return;
        }
        match &*e.kind {
            H::Builtin { op, args } => match p.builtin(self, *op, args, depth) {
                Flow::Done => return,
                Flow::PrimedArgs => return self.walk_args(p, args, depth, true),
                Flow::BothArgs => {
                    // Every argument unprimed and then primed: the order the
                    // read sets were built in before this driver.
                    for a in args {
                        self.walk_args(p, std::slice::from_ref(a), depth, false);
                        self.walk_args(p, std::slice::from_ref(a), depth, true);
                    }
                    return;
                }
                Flow::Children => {}
            },
            H::Const(c) => p.constant(self, *c, depth),
            H::Local(l) => self.local(p, *l, depth),
            H::Apply { op, .. } | H::OpArg(op) => p.op(self, *op, depth),
            H::Let { defs, .. } => defs.iter().for_each(|d| self.def(p, *d)),
            _ => {}
        }
        visit::children(e, &mut |c| self.walk(p, c, p.child_depth(depth)));
    }

    /// Walk a builtin's arguments with the primed flag set (`'e`,
    /// `UNCHANGED e`).
    fn walk_args<P: Policy>(&mut self, p: &mut P, args: &[hir::Expr], depth: usize, primed: bool) {
        let saved = self.primed;
        self.primed = primed;
        for a in args {
            self.walk(p, a, p.child_depth(depth));
        }
        self.primed = saved;
    }

    /// Walk the deferred arguments of an interpreter fallback node:
    /// `Deferred::Thunk`/`Once`/`Lambda` carry an expression of the node,
    /// `OpRef` an operator argument.
    pub(crate) fn walk_deferred<P: Policy>(&mut self, p: &mut P, deferred: &[Deferred], depth: usize) {
        for d in deferred {
            match d {
                Deferred::Thunk(_, x) | Deferred::Once(_, x) | Deferred::Lambda(_, _, x) => self.walk(p, x, depth),
                Deferred::OpRef(_, r) => p.op(self, *r, depth),
            }
        }
    }

    /// Walk definition `d` (after the cfg's redirections), in a definition
    /// scope (or in the enclosing scope for a `LET`-local definition), if the
    /// policy admits it.
    pub(crate) fn def<P: Policy>(&mut self, p: &mut P, d: DefId) {
        let d = self.ip.redirect_def(d);
        if !p.def(self, d) {
            return;
        }
        // The body belongs to the interpreter's program, not to `self`, so
        // holding it across the mutable walk is fine.
        let ip = self.ip;
        let is_let = ip.prog.def_is_let(d);
        if !is_let {
            self.enter_def_scope();
        }
        match &ip.prog.defs[d.idx()].kind {
            DefKind::Op(body) => self.walk(p, body, 0),
            DefKind::Fn { bounds, body } => {
                for b in bounds {
                    self.walk(p, &b.set, 0);
                }
                self.walk(p, body, 0);
            }
            DefKind::Pending => p.pending_def(self, d),
        }
        if !is_let {
            self.leave_def_scope();
        }
        p.def_done(self, d);
    }

    /// Resolve local (or operator parameter) `l`: what the environment binds
    /// it to, followed in that binding's environment.
    pub(crate) fn local<P: Policy>(&mut self, p: &mut P, l: LocalId, depth: usize) {
        if !p.local(self, l, depth) {
            return;
        }
        let Some(binding) = self.scope.iter().find_map(|e| e.lookup(l).cloned()) else {
            return;
        };
        match binding {
            Binding::Val(_) | Binding::LetCache(_) => {}
            Binding::Thunk(t) => {
                let env = t.env.clone();
                self.enter_local_scope(env);
                self.walk(p, &t.expr, depth + 1);
                self.leave_local_scope();
            }
            Binding::Name(x, env) => {
                let ip = self.ip;
                let e = ip.prog.arena_expr(x);
                self.enter_local_scope(env);
                self.walk(p, e, depth + 1);
                self.leave_local_scope();
            }
            Binding::Op(OpVal::Lambda { body, env, .. }) => {
                p.bound_operator(self, l);
                self.enter_local_scope(env);
                self.walk(p, &body, depth + 1);
                self.leave_local_scope();
            }
            Binding::Op(OpVal::Ref(r)) => {
                p.bound_operator(self, l);
                p.op(self, r, depth + 1);
            }
        }
    }

    /// Enter the environment of a closure body.
    fn enter_local_scope(&mut self, env: Env) {
        match self.scope_kind {
            Scope::Single => self.saved.push(std::mem::replace(&mut self.scope[0], env)),
            Scope::Shared => self.scope.push(env),
        }
    }

    fn leave_local_scope(&mut self) {
        // A shared scope keeps every environment reached: a local id is
        // unique per binding site, so an environment outside the current
        // nesting can only add bindings.
        if let Scope::Single = self.scope_kind {
            self.scope[0] = self.saved.pop().expect("scope enter/leave are balanced");
        }
    }

    /// Enter the scope of a definition body: no local of the caller's
    /// environment is in scope (its parameters are bound at its call sites).
    fn enter_def_scope(&mut self) {
        if let Scope::Single = self.scope_kind {
            self.saved.push(std::mem::take(&mut self.scope[0]));
        }
    }

    fn leave_def_scope(&mut self) {
        if let Scope::Single = self.scope_kind {
            self.scope[0] = self.saved.pop().expect("scope enter/leave are balanced");
        }
    }
}

/// What one walk makes of the nodes the shared driver reaches. The driver
/// owns the mechanics (see the module documentation); a policy supplies what
/// each reached node means to it.
pub(crate) trait Policy: Sized {
    /// What the policy makes of expression node `e` at `depth`. `Flow::Done`
    /// ends the walk here (the policy records why); `Flow::Children` leaves
    /// the generic resolution and the children to the driver.
    fn node(&mut self, s: &mut State<'_>, e: &hir::Expr, depth: usize) -> Flow;

    /// What the policy makes of builtin `op` with `args`, when `node`
    /// returned `Flow::Children`. `Flow::Children` walks the arguments as
    /// usual; `Flow::PrimedArgs`/`Flow::BothArgs` walk them primed.
    fn builtin(&mut self, s: &mut State<'_>, op: Builtin, args: &[hir::Expr], depth: usize) -> Flow {
        let _ = (s, op, args, depth);
        Flow::Children
    }

    /// The recursion depth of a node's children: walks that count structural
    /// depth add one, the others keep the node's depth.
    fn child_depth(&self, depth: usize) -> usize {
        depth
    }

    /// Whether to walk redirected definition `d` (its body then follows).
    /// `false` stops before its body (the policy records why).
    fn def(&mut self, s: &mut State<'_>, d: DefId) -> bool;

    /// Definition `d`, admitted by `def`, had its body walked.
    fn def_done(&mut self, s: &mut State<'_>, d: DefId) {
        let _ = (s, d);
    }

    /// Definition `d`, admitted by `def`, has no body yet (`Pending`).
    fn pending_def(&mut self, s: &mut State<'_>, d: DefId) {
        let _ = (s, d);
    }

    /// Whether to resolve local (or operator parameter) `l` in the
    /// environments in scope. `false` stops here: the policy followed the
    /// local itself, saw it already, or recorded the walk as over.
    fn local(&mut self, s: &mut State<'_>, l: LocalId, depth: usize) -> bool {
        let _ = (s, l, depth);
        true
    }

    /// Local `l` resolved to an operator the environment bound it to (a
    /// `LAMBDA` body or an operator reference) rather than to an expression.
    fn bound_operator(&mut self, s: &mut State<'_>, l: LocalId) {
        let _ = (s, l);
    }

    /// What the policy makes of constant `c` in value position (`H::Const`):
    /// the definition the cfg binds it to (`C <- Def`), when the walk follows
    /// one.
    fn constant(&mut self, s: &mut State<'_>, c: ConstId, depth: usize);

    /// What the policy makes of constant `c` in operator position
    /// (`OpRef::Const`). The two positions differ (`C <- Def` binds a value
    /// constant; `C <- Op` an operator), so this is a separate hook; the
    /// default follows the value-position policy.
    fn op_const(&mut self, s: &mut State<'_>, c: ConstId, depth: usize) {
        self.constant(s, c, depth)
    }

    /// Operator reference `r` reached by an application, passed as an
    /// argument, or bound in an environment: the shared resolution of a
    /// reference to its target.
    fn op(&mut self, s: &mut State<'_>, r: OpRef, depth: usize) {
        match r {
            OpRef::Def(d) => s.def(self, d),
            OpRef::Const(c) => self.op_const(s, c, depth),
            OpRef::Param(l) => s.local(self, l, depth),
            OpRef::Builtin(b) => self.op_builtin(s, b),
        }
    }

    /// Builtin `b` reached as an operator reference (not as a node).
    fn op_builtin(&mut self, s: &mut State<'_>, b: Builtin) {
        let _ = (s, b);
    }
}

/// The local a deferred argument binds (`Deferred::Thunk`/`Once`/`Lambda`
/// bind their expression, `OpRef` its operator reference).
pub(crate) fn deferred_local(d: &Deferred) -> LocalId {
    match d {
        Deferred::Thunk(l, _) | Deferred::Once(l, _) | Deferred::Lambda(l, _, _) | Deferred::OpRef(l, _) => *l,
    }
}

/// Bind `deferred` arguments onto `base` in order, matching
/// `InterpNode::eval_with`, so walks that resolve locals inside primed
/// contexts see deferred bindings in their exact lexical environments.
pub(crate) fn bind_deferred(ip: &Interp, base: &Env, deferred: &[Deferred]) -> Env {
    let mut env = base.clone();
    for d in deferred {
        env = match d {
            Deferred::Thunk(l, e) => {
                let t = Thunk { expr: e.clone(), env: env.clone(), memo: None };
                env.bind(*l, Binding::Thunk(Arc::new(t)))
            }
            Deferred::Once(l, e) => {
                let t = Thunk { expr: e.clone(), env: env.clone(), memo: Some(Default::default()) };
                env.bind(*l, Binding::Thunk(Arc::new(t)))
            }
            Deferred::Lambda(l, params, body) => {
                let o = OpVal::Lambda { params: params.clone(), body: body.clone(), env: env.clone() };
                env.bind(*l, Binding::Op(o))
            }
            Deferred::OpRef(l, OpRef::Def(def)) if ip.prog.def_is_let(*def) => match &ip.prog.defs[def.idx()].kind {
                DefKind::Op(body) => {
                    let o = OpVal::Lambda { params: ip.prog.defs[def.idx()].params.clone().into(), body: body.clone(), env: env.clone() };
                    env.bind(*l, Binding::Op(o))
                }
                _ => env.bind(*l, Binding::Op(OpVal::Ref(OpRef::Def(*def)))),
            },
            Deferred::OpRef(l, r) => env.bind(*l, Binding::Op(OpVal::Ref(*r))),
        };
    }
    env
}
