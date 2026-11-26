//! Whether the compiled tier's layout can ever miss: a conservative static
//! closure analysis of `Init`, `Next` and the materialized definitions
//! (design.md §6.5.3, scale.md §6).
//!
//! The driver keeps the layout-miss archive only while a later value can fail
//! `Layout::encode_state`. When this analysis proves that every value an
//! assignment can produce fits its slot, and so does every materialized
//! definition, the archive is pure overhead and is elided.
//!
//! The analysis is an abstract interpretation over HIR whose value domain is
//! [`Shape`]: a state variable's abstract value is its layout slot (an
//! over-approximation of the values reachable states hold, the induction
//! hypothesis), a constant's is `Shape::of` its value, and any construct this
//! analysis does not understand becomes `Shape::Dyn` (top). For each
//! assignment `x = e` (Init) or `x' = e` (Next) the shape of `e` must be
//! accepted by `x`'s slot ([`Shape::accepts_shape`]); `x' \in S` and
//! `x' \subseteq S` are checked against `S`'s element and subset shapes.
//! Anything that leaves a value unproven — an unsupported operator, a
//! recursive definition, a `Dyn` operand — keeps the archive.
//!
//! [`VShape`] additionally tracks `lo..hi` interval *values*
//! (`Value::Interval`): such a value can only live in a `Dyn`/`Ref` slot, so
//! it must not be conflated with `Shape::Set` (shape inference maps it to
//! `Dyn`), while its integer elements and set view are still exact and useful
//! for `\in`/`\subseteq` assignments and function domains.
//!
//! The traversal mirrors `tlx_eval::enumerate`: only the positions that can
//! assign a state variable are followed as actions (`\land`, `\lor`, `=>`'s
//! consequent, `\E`/`\A` bodies, `IF`/`CASE` branches, `LET` bodies, expanded
//! definition calls, `UNCHANGED`, `\cdot` and the action operators), and the
//! interpreter's expansion rules decide whether a definition is followed or
//! evaluated as a test (a test cannot assign). Analyzing every branch
//! (rather than only a condition's chosen one) is sound: a successor that is
//! not generated is also not missed.
//!
//! A proof failure is always safe: it only restores the archive. The
//! `TLX_PARANOID` assertion in the driver checks a proof against the running
//! search.

use std::sync::Arc;

use tlx_eval::env::{Binding, Env, OpVal};
use tlx_eval::eval::Ctx;
use tlx_eval::model::InterpModel;
use tlx_layout::shape::{join_all, set_shape};
use tlx_layout::{FcnWitness, Shape};
use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{Bound, BoundVars, ConstId, DefId, DefKind, ExceptKey, Expr, ExprKind as H, LocalId, OpRef};
use tlx_value::{Sym, Value};

/// Whether a run with this layout can never raise a layout miss.
///
/// `Err` names the first construct that could not be proven closed (the run
/// then keeps its archive). `vars` are the layout slots in variable order and
/// `defs` the materialized definitions with their layout shapes: the shapes
/// the encoded model actually uses (`Speculation::layout_shapes`).
pub(super) fn layout_is_closed(base: &InterpModel, vars: &[Shape], defs: &[(DefId, Shape)]) -> Result<(), String> {
    // Fast path: when every variable and materialized definition slot is
    // unbounded (`Dyn` / `Ref`), no assignment or definition can raise a layout
    // miss regardless of the expressions in `Init` or `Next`.
    if vars.iter().all(Shape::is_unbounded) && defs.iter().all(|(_, s)| s.is_unbounded()) {
        return Ok(());
    }
    let mut a = Analyzer::new(base, vars.to_vec(), defs.to_vec());
    a.check_init();
    if a.reason.is_none() {
        a.check_actions();
    }
    if a.reason.is_none() {
        a.check_defs();
    }
    match a.reason {
        Some(why) => Err(why),
        None => Ok(()),
    }
}

/// Most finite keys a function-constructor domain may have before the analysis
/// treats it as a map instead of enumerating its keys.
const MAX_EXACT_DOMAIN: i64 = 4096;
/// Maximum expression nodes one analysis may visit. The traversal is linear in
/// the (inlined) model; this only bounds pathological nesting, where it
/// forfeits the proof (the archive is kept).
const BUDGET: usize = 500_000;
/// Maximum inlining depth (definitions, binders, function constructors).
const DEPTH: usize = 96;

/// An abstract value: a value shape, or an integer-interval value
/// (`Value::Interval`, which only a `Dyn`/`Ref` slot can hold).
#[derive(Clone)]
enum VShape {
    Shape(Shape),
    Interval { lo: i64, hi: i64 },
}

impl VShape {
    fn as_shape(&self) -> Shape {
        match self {
            VShape::Shape(s) => s.clone(),
            VShape::Interval { .. } => Shape::Dyn,
        }
    }

    /// The shape its elements take, when the value is a set or an interval.
    fn elem(&self) -> Shape {
        match self {
            VShape::Shape(Shape::Set { elem, .. }) => (**elem).clone(),
            VShape::Shape(Shape::Never) => Shape::Never,
            VShape::Interval { lo, hi } => {
                if lo <= hi {
                    Shape::Int { lo: *lo, hi: *hi }
                } else {
                    Shape::Never
                }
            }
            _ => Shape::Dyn,
        }
    }

    /// The set view `(element shape, max cardinality)`, when the value is a
    /// set or an interval.
    fn as_set(&self) -> Option<(Shape, usize)> {
        match self {
            VShape::Shape(Shape::Set { elem, max_card }) => Some(((**elem).clone(), *max_card)),
            VShape::Interval { lo, hi } => {
                if hi < lo {
                    return Some((Shape::Never, 0));
                }
                let card = usize::try_from((*hi as i128) - (*lo as i128) + 1).ok()?;
                Some((Shape::Int { lo: *lo, hi: *hi }, card))
            }
            _ => None,
        }
    }

    fn join(&self, other: &VShape) -> VShape {
        match (self, other) {
            (VShape::Shape(Shape::Never), x) | (x, VShape::Shape(Shape::Never)) => x.clone(),
            (VShape::Shape(a), VShape::Shape(b)) => VShape::Shape(a.join(b)),
            // Two interval values are both intervals at runtime, but no `Shape`
            // describes interval values; any other mix is beyond the domain.
            _ => VShape::Shape(Shape::Dyn),
        }
    }
}

impl From<Shape> for VShape {
    fn from(s: Shape) -> VShape {
        VShape::Shape(s)
    }
}

/// An abstract local binding: a value shape, a call-by-name argument (its
/// expression may still assign when used in action position), or an operator
/// value.
#[derive(Clone)]
enum Abs {
    Val(VShape),
    Thunk(Expr, Env),
    Op(OpVal),
}

struct Analyzer<'a> {
    base: &'a InterpModel,
    /// The abstract value of each state variable: its layout slot (an
    /// over-approximation by induction over the reachable states).
    vars: Vec<Shape>,
    /// Materialized definitions and their layout slots.
    defs: Vec<(DefId, Shape)>,
    /// Analyzing `Init` (assignments are unprimed) instead of an action.
    init: bool,
    /// The value of `@` inside the update of an `EXCEPT`.
    at: Option<Shape>,
    /// Abstract bindings, innermost scope last.
    scopes: Vec<Vec<(LocalId, Abs)>>,
    /// Definitions currently being inlined (recursion).
    active: Vec<DefId>,
    /// Remaining expression nodes this analysis may visit.
    budget: usize,
    /// Inlining depth.
    depth: usize,
    /// Definition/local-following depth (0-ary definition chains, by-name
    /// bindings, function-constructor resolution).
    follow: usize,
    /// Path refinements from already-tested guards (`x < 10` narrows `x` for
    /// the conjuncts to its right and for the branches the guard selects).
    refine: Vec<Refine>,
    /// The first construct that cannot be proven closed.
    reason: Option<String>,
}

/// A guard-derived narrowing of one variable's values on the current path.
#[derive(Clone)]
struct Refine {
    var: usize,
    /// The guard reads the variable primed (`x'`).
    primed: bool,
    shape: Shape,
}

impl<'a> Analyzer<'a> {
    fn new(base: &'a InterpModel, vars: Vec<Shape>, defs: Vec<(DefId, Shape)>) -> Analyzer<'a> {
        Analyzer {
            base,
            vars,
            defs,
            init: false,
            at: None,
            scopes: Vec::new(),
            active: Vec::new(),
            refine: Vec::new(),
            budget: BUDGET,
            depth: 0,
            follow: 0,
            reason: None,
        }
    }

    // ------------------------------------------------------------------
    // proof driver

    fn fail(&mut self, why: impl Into<String>) {
        if self.reason.is_none() {
            self.reason = Some(why.into());
        }
    }

    /// Charge one expression node; false (and a failure) when the budget is
    /// exhausted or the proof already failed.
    fn spend(&mut self) -> bool {
        if self.reason.is_some() {
            return false;
        }
        if self.budget == 0 {
            self.reason = Some("the closed-layout analysis budget is exhausted".into());
            return false;
        }
        self.budget -= 1;
        true
    }

    fn check_init(&mut self) {
        let init = self.base.init_expr().clone();
        self.init = true;
        self.action(&init, &Env::default());
        self.init = false;
    }

    fn check_actions(&mut self) {
        let actions = self.base.actions().iter().map(|a| (a.name.to_string(), a.expr.clone(), a.env.clone())).collect::<Vec<_>>();
        for (i, (name, expr, env)) in actions.into_iter().enumerate() {
            if self.reason.is_some() {
                return;
            }
            self.init = false;
            self.action(&expr, &env);
            if let Some(why) = self.reason.take() {
                self.reason = Some(format!("action {} (#{i}): {why}", name));
            }
        }
    }

    fn check_defs(&mut self) {
        let defs = self.defs.clone();
        for (orig_d, slot) in defs {
            if self.reason.is_some() {
                return;
            }
            if slot.is_unbounded() {
                continue;
            }
            let d = self.base.ip.redirect_def(orig_d);
            let def = &self.base.ip.prog.defs[d.idx()];
            if def.builtin.is_some() || self.base.ip.has_def_value(orig_d) || self.base.ip.has_def_value(d) {
                self.fail(format!("definition {} is evaluated from the configuration", def.name));
                continue;
            }
            let body = match &def.kind {
                DefKind::Op(body) if def.params.is_empty() => body.clone(),
                _ => {
                    self.fail(format!("definition {} cannot be analyzed as a 0-ary operator", def.name));
                    continue;
                }
            };
            let shape = self.value(&body, &Env::default()).as_shape();
            if !slot.accepts_shape(&shape) {
                self.fail(format!("materialized definition {} can produce a value outside its shape", def.name));
            }
        }
    }

    // ------------------------------------------------------------------
    // abstract environments

    fn push_scope(&mut self, entries: Vec<(LocalId, Abs)>) {
        self.scopes.push(entries);
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn lookup(&self, l: LocalId) -> Option<&Abs> {
        self.scopes.iter().rev().find_map(|s| s.iter().rev().find(|(id, _)| *id == l).map(|(_, b)| b))
    }

    /// The shape of a local bound to a value (a call-by-name argument is
    /// evaluated).
    fn local_value(&mut self, l: LocalId, env: &Env) -> VShape {
        match self.lookup(l).cloned() {
            Some(Abs::Val(s)) => s,
            Some(Abs::Thunk(e, benv)) => {
                if self.follow > DEPTH {
                    return VShape::Shape(Shape::Dyn);
                }
                self.follow += 1;
                let s = self.value(&e, &benv);
                self.follow -= 1;
                s
            }
            Some(Abs::Op(_)) => VShape::Shape(Shape::Dyn),
            None => match env.lookup(l) {
                Some(Binding::Val(v)) => shape_of_value(v),
                Some(b @ (Binding::Name(..) | Binding::Thunk(_))) => {
                    let (e, benv) = b.by_name(&self.base.ip.prog).expect("by-name binding");
                    let (e, benv) = (e.clone(), benv.clone());
                    if self.follow > DEPTH {
                        return VShape::Shape(Shape::Dyn);
                    }
                    self.follow += 1;
                    let s = self.value(&e, &benv);
                    self.follow -= 1;
                    s
                }
                _ => VShape::Shape(Shape::Dyn),
            },
        }
    }

    /// The current abstract value of variable `v`, with the narrowings from
    /// guards already tested on this path.
    fn refined_value(&self, v: usize, primed: bool) -> Shape {
        match self.refine.iter().rev().find(|r| r.var == v && r.primed == primed) {
            Some(r) => r.shape.clone(),
            None => self.vars.get(v).cloned().unwrap_or(Shape::Dyn),
        }
    }

    /// Narrow `v`'s values on this path to the values of `shape` (the guard
    /// held). An empty intersection is `Never`: the path is infeasible and
    /// generates nothing. Each narrowing is pushed onto the stack so
    /// length-based rollback (`refine.truncate(mark)`) always restores the
    /// enclosing branch's bound.
    fn narrow(&mut self, v: usize, primed: bool, shape: Shape) {
        if matches!(shape, Shape::Dyn) {
            return;
        }
        let old = self.refined_value(v, primed);
        let new = intersect(&old, &shape);
        self.refine.push(Refine { var: v, primed, shape: new });
    }

    /// Refine the values read on this path from `guard` being `truth`.
    ///
    /// Only conditions that hold *as a necessary consequence* are used: the
    /// conjuncts of a true conjunction, the disjuncts of a false disjunction
    /// and a negated condition. Every other form leaves the shapes alone
    /// (still a sound over-approximation).
    fn refine_guard(&mut self, guard: &Expr, env: &Env, truth: bool) {
        if self.reason.is_some() || !self.spend() {
            return;
        }
        match &*guard.kind {
            H::And(es) if truth => {
                for e in es {
                    self.refine_guard(e, env, true);
                }
            }
            H::Or(es) if !truth => {
                for e in es {
                    self.refine_guard(e, env, false);
                }
            }
            H::Builtin { op, args } if !self.base.ip.is_builtin_overridden(*op) => match (*op, args.as_slice()) {
                (B::Not, [a]) => self.refine_guard(a, env, !truth),
                (op, [a, b]) => self.refine_comparison(op, a, b, env, truth),
                _ => {}
            },
            H::Let { body, .. } => self.refine_guard(body, env, truth),
            _ => {}
        }
    }

    /// Refine from `a <op> b`, when one side is a variable and the other a
    /// constant or interval.
    fn refine_comparison(&mut self, op: B, a: &Expr, b: &Expr, env: &Env, truth: bool) {
        if let Some(v) = self.var_of(a, env) {
            let primed = is_primed(a);
            let other = self.value(b, env);
            self.refine_bound(op, v, primed, &other, truth);
            return;
        }
        let Some(v) = self.var_of(b, env) else { return };
        if !truth {
            // `a < x` false means `x <= a`; the complemented relation.
            let op = match op {
                B::Lt => B::Le,
                B::Le => B::Lt,
                B::Gt => B::Ge,
                B::Ge => B::Gt,
                _ => return,
            };
            let other = self.value(a, env);
            return self.refine_bound(op, v, is_primed(b), &other, true);
        }
        // `a < x` means `x > a`.
        let op = match op {
            B::Lt => B::Gt,
            B::Le => B::Ge,
            B::Gt => B::Lt,
            B::Ge => B::Le,
            B::Eq => B::Eq,
            _ => return,
        };
        let other = self.value(a, env);
        self.refine_bound(op, v, is_primed(b), &other, true);
    }

    fn refine_bound(&mut self, op: B, v: usize, primed: bool, other: &VShape, truth: bool) {
        let old = self.refined_value(v, primed);
        let shape = match (&old, other, op, truth) {
            // `x < b`: with b at most b.hi, x is at most b.hi - 1.
            (Shape::Int { lo, hi }, VShape::Shape(Shape::Int { hi: bhi, .. }), B::Lt, true) => {
                Shape::Int { lo: *lo, hi: (*hi).min(bhi.saturating_sub(1)) }
            }
            (Shape::Int { lo, hi }, VShape::Shape(Shape::Int { hi: bhi, .. }), B::Le, true) => Shape::Int { lo: *lo, hi: (*hi).min(*bhi) },
            // `not (x < b)`: x >= b >= b.lo.
            (Shape::Int { lo, hi }, VShape::Shape(Shape::Int { lo: blo, .. }), B::Lt, false) => Shape::Int { lo: (*lo).max(*blo), hi: *hi },
            (Shape::Int { lo, hi }, VShape::Shape(Shape::Int { lo: blo, .. }), B::Le, false) => {
                Shape::Int { lo: (*lo).max(blo.saturating_add(1)), hi: *hi }
            }
            // `x > b`: x >= b.lo + 1.
            (Shape::Int { lo, hi }, VShape::Shape(Shape::Int { lo: blo, .. }), B::Gt, true) => {
                Shape::Int { lo: (*lo).max(blo.saturating_add(1)), hi: *hi }
            }
            (Shape::Int { lo, hi }, VShape::Shape(Shape::Int { lo: blo, .. }), B::Ge, true) => Shape::Int { lo: (*lo).max(*blo), hi: *hi },
            // `not (x > b)`: x <= b <= b.hi.
            (Shape::Int { lo, hi }, VShape::Shape(Shape::Int { hi: bhi, .. }), B::Gt, false) => Shape::Int { lo: *lo, hi: (*hi).min(*bhi) },
            (Shape::Int { lo, hi }, VShape::Shape(Shape::Int { hi: bhi, .. }), B::Ge, false) => {
                Shape::Int { lo: *lo, hi: (*hi).min(bhi.saturating_sub(1)) }
            }
            // `x = b`: x is one of b's values.
            (Shape::Int { lo, hi }, VShape::Shape(Shape::Int { lo: blo, hi: bhi }), B::Eq, true) => {
                Shape::Int { lo: (*lo).max(*blo), hi: (*hi).min(*bhi) }
            }
            (Shape::Bool, VShape::Shape(Shape::Bool), B::Eq, true) => Shape::Bool,
            // `x \in S`: x is one of S's elements.
            (s, VShape::Interval { lo, hi }, B::In, true) => {
                let elem = if lo <= hi { Shape::Int { lo: *lo, hi: *hi } } else { Shape::Never };
                intersect(s, &elem)
            }
            (s, VShape::Shape(Shape::Set { elem, .. }), B::In, true) => intersect(s, elem),
            _ => return,
        };
        self.narrow(v, primed, shape);
    }

    /// The operator `arg` is passed as, if it can be resolved.
    fn op_val(&mut self, arg: &Expr, env: &Env) -> Option<OpVal> {
        match &*arg.kind {
            H::OpArg(r) => match r {
                OpRef::Param(l) => match self.lookup(*l).cloned().or_else(|| {
                    env.lookup(*l).map(|b| match b {
                        Binding::Op(o) => Abs::Op(o.clone()),
                        _ => Abs::Val(VShape::Shape(Shape::Dyn)),
                    })
                }) {
                    Some(Abs::Op(o)) => Some(o),
                    _ => None,
                },
                OpRef::Def(d) if self.base.ip.prog.def_is_let(*d) => match &self.base.ip.prog.defs[d.idx()].kind {
                    DefKind::Op(body) => Some(OpVal::Lambda {
                        params: self.base.ip.prog.defs[d.idx()].params.clone().into(),
                        body: body.clone(),
                        env: env.clone(),
                    }),
                    _ => Some(OpVal::Ref(*r)),
                },
                r => Some(OpVal::Ref(*r)),
            },
            H::Lambda { params, body } => Some(OpVal::Lambda { params: params.clone().into(), body: body.clone(), env: env.clone() }),
            _ => None,
        }
    }

    /// The base environment for `def`'s body and the bindings for the call's
    /// arguments (pushed as a scope).
    fn bind_params(&mut self, def: DefId, args: &[Expr], env: &Env) -> Result<Env, String> {
        let d = self.base.ip.redirect_def(def);
        let decl = &self.base.ip.prog.defs[d.idx()];
        let base = if self.base.ip.prog.def_is_let(d) { env.clone() } else { Env::default() };
        let mut entries = Vec::with_capacity(decl.params.len());
        for (p, a) in decl.params.iter().zip(args.iter()) {
            let arity = self.base.ip.prog.locals[p.idx()].arity;
            if arity > 0 {
                match self.op_val(a, env) {
                    Some(o) => entries.push((*p, Abs::Op(o))),
                    None => {
                        return Err(format!(
                            "the operator argument of {} cannot be resolved statically",
                            self.base.ip.prog.defs[d.idx()].name
                        ));
                    }
                }
            } else {
                entries.push((*p, Abs::Thunk(a.clone(), env.clone())));
            }
        }
        self.push_scope(entries);
        Ok(base)
    }

    // ------------------------------------------------------------------
    // action-position traversal (mirrors tlx_eval::enumerate)

    /// Analyze the action-position expression `e`: every assignment it can
    /// perform must fit its slot.
    fn action(&mut self, e: &Expr, env: &Env) {
        if !self.spend() {
            return;
        }
        if self.depth > DEPTH {
            self.fail("the closed-layout analysis inlining limit is exceeded");
            return;
        }
        match &*e.kind {
            H::And(es) => {
                let mark = self.refine.len();
                for c in es {
                    self.action(c, env);
                    if self.reason.is_some() {
                        self.refine.truncate(mark);
                        return;
                    }
                    self.refine_guard(c, env, true);
                }
                self.refine.truncate(mark);
            }
            H::Or(es) => {
                for c in es {
                    let mark = self.refine.len();
                    self.action(c, env);
                    self.refine.truncate(mark);
                    if self.reason.is_some() {
                        return;
                    }
                }
            }
            H::Quant { bounds, body, .. } => {
                // Always bind (using `Dyn` for unknown domains) and check the
                // body: an abstract `Dyn` domain can still be a non-empty set
                // or interval at runtime.
                let _ = self.bind_bounds(bounds, env);
                self.action(body, env);
                self.pop_scope();
            }
            H::QuantUnbounded { vars, body, .. } => {
                self.push_scope(vars.iter().map(|l| (*l, Abs::Val(VShape::Shape(Shape::Dyn)))).collect());
                self.action(body, env);
                self.pop_scope();
            }
            H::If { cond, then, els } => {
                let mark = self.refine.len();
                self.refine_guard(cond, env, true);
                self.action(then, env);
                self.refine.truncate(mark);
                self.refine_guard(cond, env, false);
                self.action(els, env);
                self.refine.truncate(mark);
            }
            H::Case { arms, other } => {
                for (g, v) in arms {
                    let mark = self.refine.len();
                    self.refine_guard(g, env, true);
                    self.action(v, env);
                    self.refine.truncate(mark);
                }
                if let Some(o) = other {
                    self.action(o, env);
                }
            }
            H::Let { body, .. } => self.action(body, env),
            H::FnApp { func, args } => self.fn_app_action(func, args, env),
            H::Apply { op, args } => self.apply_action(e, op, args, env),
            H::Local(l) => {
                if let Some((inner, benv)) = self.local_expr(*l, env) {
                    self.action(&inner, &benv);
                }
            }
            H::Builtin { op, args } => self.builtin_action(*op, args, env),
            H::BoxAction { action, .. } | H::AngleAction { action, .. } => self.action(action, env),
            _ => {}
        }
    }

    /// The action-position built-in `op` (the kinds `enumerate` dispatches).
    fn builtin_action(&mut self, op: B, args: &[Expr], env: &Env) {
        if self.base.ip.is_builtin_overridden(op) {
            self.fail(format!("builtin {} is overridden by the configuration", op.name()));
            return;
        }
        match op {
            B::Eq | B::In | B::SubsetEq => {
                self.assignment(op, args, env);
            }
            B::Implies => {
                if let [a, b] = args {
                    let mark = self.refine.len();
                    self.refine_guard(a, env, true);
                    self.action(b, env);
                    self.refine.truncate(mark);
                }
            }
            B::Unchanged => {
                // `UNCHANGED e` assigns `x' = x` for the variables of `e`
                // (their current value, which is inside the slot already), or
                // is a test. Either way it adds no value outside the slots.
            }
            B::Compose => {
                for (i, a) in args.iter().enumerate() {
                    if i == 0 {
                        let mark = self.refine.len();
                        self.action(a, env);
                        self.refine.truncate(mark);
                    } else {
                        // Later operands of `A \cdot B` read the intermediate
                        // state produced by `A`, not `s0`, so path refinements
                        // derived from `s0` guards do not apply there.
                        let saved = std::mem::take(&mut self.refine);
                        self.action(a, env);
                        self.refine = saved;
                    }
                    if self.reason.is_some() {
                        return;
                    }
                }
            }
            _ => {}
        }
    }

    /// `x = e` / `x' = e`, `x \in S` / `x' \in S`, `x \subseteq S` /
    /// `x' \subseteq S`: check the assigned values against the slot.
    fn assignment(&mut self, op: B, args: &[Expr], env: &Env) {
        let [lhs, rhs] = args else { return };
        let Some(v) = self.target(lhs, env) else { return };
        let shape = match op {
            B::Eq => self.value(rhs, env).as_shape(),
            B::In => self.value(rhs, env).elem(),
            B::SubsetEq => match self.value(rhs, env).as_set() {
                Some((elem, max_card)) => set_shape(elem, max_card),
                None => Shape::Dyn,
            },
            _ => unreachable!(),
        };
        if !self.vars[v].accepts_shape(&shape) {
            let name = &self.base.ip.prog.vars[v].name;
            self.fail(format!("a value of {name} can fall outside its layout shape"));
        }
    }

    /// The variable an assignment-shaped left-hand side denotes (`x` in Init,
    /// `x'` in an action), through by-name bindings and 0-ary definitions.
    fn target(&mut self, lhs: &Expr, env: &Env) -> Option<usize> {
        if self.follow > DEPTH {
            self.fail("the closed-layout analysis indirection limit is exceeded");
            return None;
        }
        self.follow += 1;
        let r = self.target_inner(lhs, env);
        self.follow -= 1;
        r
    }

    fn target_inner(&mut self, lhs: &Expr, env: &Env) -> Option<usize> {
        if self.init {
            return self.var_of(lhs, env);
        }
        match &*lhs.kind {
            H::Builtin { op: B::Prime, args } => args.first().and_then(|a| self.var_of(a, env)),
            H::Local(l) => {
                let (e, benv) = self.local_expr(*l, env)?;
                self.target(&e, &benv)
            }
            H::Apply { op: OpRef::Def(d), args } if args.is_empty() => {
                let (d, body) = self.plain_op_body(*d)?;
                let benv = if self.base.ip.prog.def_is_let(d) { env.clone() } else { Env::default() };
                self.target(&body, &benv)
            }
            H::Let { body, .. } => self.target(body, env),
            _ => None,
        }
    }

    /// The state variable `e` denotes (see `target`).
    fn var_of(&mut self, e: &Expr, env: &Env) -> Option<usize> {
        if self.follow > DEPTH {
            return None;
        }
        self.follow += 1;
        let r = self.var_of_inner(e, env);
        self.follow -= 1;
        r
    }

    fn var_of_inner(&mut self, e: &Expr, env: &Env) -> Option<usize> {
        match &*e.kind {
            H::Var(v) => Some(v.idx()),
            H::Local(l) => {
                let (inner, benv) = self.local_expr(*l, env)?;
                self.var_of(&inner, &benv)
            }
            H::Apply { op: OpRef::Def(d), args } if args.is_empty() => {
                let (d, body) = self.plain_op_body(*d)?;
                let benv = if self.base.ip.prog.def_is_let(d) { env.clone() } else { Env::default() };
                self.var_of(&body, &benv)
            }
            H::Let { body, .. } => self.var_of(body, env),
            _ => None,
        }
    }

    /// The by-name binding of local `l` (the enumerator's `local_expr`).
    fn local_expr(&self, l: LocalId, env: &Env) -> Option<(Expr, Env)> {
        match self.lookup(l) {
            Some(Abs::Thunk(e, benv)) => Some((e.clone(), benv.clone())),
            Some(_) => None,
            None => env.lookup(l)?.by_name(&self.base.ip.prog).map(|(e, benv)| (e.clone(), benv.clone())),
        }
    }

    /// The body of 0-ary user definition `d` (after cfg redirection), if the
    /// interpreter evaluates it as a definition.
    fn plain_op_body(&self, orig_d: DefId) -> Option<(DefId, Expr)> {
        if self.base.ip.has_def_value(orig_d) {
            return None;
        }
        let d = self.base.ip.redirect_def(orig_d);
        if self.base.ip.has_def_value(d) {
            return None;
        }
        let def = &self.base.ip.prog.defs[d.idx()];
        match &def.kind {
            DefKind::Op(body) if def.builtin.is_none() && !self.base.ip.is_const_def(d) => Some((d, body.clone())),
            _ => None,
        }
    }

    /// `f[a]` where `f` is a lazily represented function: enumerate the body
    /// with its arguments bound (the enumerator's `fn_app`); the application
    /// is a test otherwise.
    fn fn_app_action(&mut self, func: &Expr, args: &[Expr], env: &Env) {
        let Some((bounds, body, fenv)) = self.lambda_of(func, env, true) else { return };
        if self.bind_fn_args(&bounds, args, env).is_none() {
            self.fail("a function's arguments cannot be resolved statically");
            return;
        }
        self.depth += 1;
        self.action(&body, &fenv);
        self.depth -= 1;
        self.pop_scope();
    }

    /// The function constructor `f` denotes, if it is one (the enumerator's
    /// `lambda_of`).
    fn lambda_of(&mut self, f: &Expr, env: &Env, in_action: bool) -> Option<(Vec<Bound>, Expr, Env)> {
        if self.follow > DEPTH {
            if in_action {
                self.fail("the closed-layout analysis indirection limit is exceeded");
            }
            return None;
        }
        self.follow += 1;
        let r = self.lambda_of_inner(f, env, in_action);
        self.follow -= 1;
        r
    }

    fn lambda_of_inner(&mut self, f: &Expr, env: &Env, in_action: bool) -> Option<(Vec<Bound>, Expr, Env)> {
        match &*f.kind {
            H::FnConstruct { bounds, body } => Some((bounds.clone(), body.clone(), env.clone())),
            H::Local(l) => {
                let (inner, benv) = self.local_expr(*l, env)?;
                self.lambda_of(&inner, &benv, in_action)
            }
            H::Apply { op: OpRef::Def(orig_d), args } if args.is_empty() => {
                if self.base.ip.has_def_value(*orig_d) {
                    return None;
                }
                let d = self.base.ip.redirect_def(*orig_d);
                let def = &self.base.ip.prog.defs[d.idx()];
                if def.builtin.is_some() || self.base.ip.has_def_value(d) {
                    return None;
                }
                let base = if self.base.ip.prog.def_is_let(d) { env.clone() } else { Env::default() };
                match &def.kind {
                    DefKind::Fn { bounds, body } => Some((bounds.clone(), body.clone(), base)),
                    DefKind::Op(body) => self.lambda_of(body, &base, in_action),
                    DefKind::Pending => None,
                }
            }
            H::Let { body, .. } => self.lambda_of(body, env, in_action),
            _ => None,
        }
    }

    /// Bind a function constructor's bound variables to the caller's `args`
    /// (evaluated in caller `env`), mirroring `Interp::bind_fn_args`.
    fn bind_fn_args(&mut self, bounds: &[Bound], args: &[Expr], env: &Env) -> Option<()> {
        if args.is_empty() || bounds.is_empty() {
            return None;
        }
        let arg = if args.len() == 1 {
            self.value(&args[0], env)
        } else {
            VShape::Shape(Shape::Tuple(args.iter().map(|a| self.value(a, env).as_shape()).collect()))
        };
        // One single-variable or tuple binder: bound directly to `arg`.
        if let [b] = bounds {
            match &b.vars {
                BoundVars::Many(ls) if ls.len() == 1 => {
                    self.push_scope(vec![(ls[0], Abs::Val(arg))]);
                    return Some(());
                }
                BoundVars::Tuple(ls) => {
                    let parts = tuple_parts(&arg.as_shape(), ls.len());
                    let entries = ls.iter().enumerate().map(|(i, l)| (*l, Abs::Val(VShape::Shape(parts[i].clone())))).collect();
                    self.push_scope(entries);
                    return Some(());
                }
                _ => {}
            }
        }
        // Multi-argument function: destructure the tuple argument across
        // each bound slot (`Many(ls)` takes `ls.len()` slots; `Tuple(_)`
        // takes one slot and destructures it).
        let slots: usize = bounds
            .iter()
            .map(|b| match &b.vars {
                BoundVars::Many(ls) => ls.len(),
                BoundVars::Tuple(_) => 1,
            })
            .sum();
        let parts = tuple_parts(&arg.as_shape(), slots);
        let mut entries = Vec::new();
        let mut idx = 0usize;
        for b in bounds {
            match &b.vars {
                BoundVars::Many(ls) => {
                    for l in ls {
                        entries.push((*l, Abs::Val(VShape::Shape(parts.get(idx).cloned().unwrap_or(Shape::Dyn)))));
                        idx += 1;
                    }
                }
                BoundVars::Tuple(ls) => {
                    let sub = tuple_parts(parts.get(idx).unwrap_or(&Shape::Dyn), ls.len());
                    entries.extend(ls.iter().enumerate().map(|(k, l)| (*l, Abs::Val(VShape::Shape(sub[k].clone())))));
                    idx += 1;
                }
            }
        }
        self.push_scope(entries);
        Some(())
    }

    /// Bind quantifier / comprehension bounds in one scope, mirroring
    /// `Interp::for_each_binding` (all domain expressions are evaluated in the
    /// outer scope; `BoundVars::Many(ls)` chooses `ls.len()` independent
    /// elements while `BoundVars::Tuple(ls)` destructures one tuple element).
    ///
    /// Always pushes a scope (binding unknown domains to `Dyn`). Returns an
    /// upper bound on the number of binding tuples when every bound has a
    /// finite set cardinality bound without overflow.
    fn bind_bounds(&mut self, bounds: &[Bound], env: &Env) -> Option<usize> {
        let mut card: Option<usize> = Some(1);
        let mut entries = Vec::new();
        for b in bounds {
            let set = self.value(&b.set, env);
            let elem = set.elem();
            let choices = match &b.vars {
                BoundVars::Many(ls) => ls.len(),
                BoundVars::Tuple(_) => 1,
            };
            match set.as_set() {
                Some((_, max_card)) => {
                    for _ in 0..choices {
                        card = card.and_then(|c| c.checked_mul(max_card));
                    }
                }
                None => card = None,
            }
            match &b.vars {
                BoundVars::Many(ls) => {
                    entries.extend(ls.iter().map(|l| (*l, Abs::Val(VShape::Shape(elem.clone())))));
                }
                BoundVars::Tuple(ls) => {
                    let parts = tuple_parts(&elem, ls.len());
                    entries.extend(
                        ls.iter().enumerate().map(|(i, l)| (*l, Abs::Val(VShape::Shape(parts.get(i).cloned().unwrap_or(Shape::Dyn))))),
                    );
                }
            }
        }
        self.push_scope(entries);
        card
    }

    // ------------------------------------------------------------------
    // definition application in action position

    fn apply_action(&mut self, e: &Expr, op: &OpRef, args: &[Expr], env: &Env) {
        match op {
            OpRef::Const(c) => match self.base.ip.const_op_ref(*c) {
                Some(OpRef::Def(d)) => self.call_def_action(d, args, env),
                Some(OpRef::Builtin(b)) => self.builtin_action(b, args, env),
                _ => {}
            },
            OpRef::Param(l) => {
                let binding = self.lookup(*l).cloned().or_else(|| {
                    env.lookup(*l).map(|b| match b {
                        Binding::Op(o) => Abs::Op(o.clone()),
                        _ => Abs::Val(VShape::Shape(Shape::Dyn)),
                    })
                });
                match binding {
                    Some(Abs::Op(OpVal::Ref(OpRef::Def(d)))) => self.call_def_action(d, args, env),
                    Some(Abs::Op(OpVal::Ref(OpRef::Builtin(b)))) => self.builtin_action(b, args, env),
                    Some(Abs::Op(OpVal::Ref(OpRef::Const(c)))) => match self.base.ip.const_op_ref(c) {
                        Some(OpRef::Def(d)) => self.call_def_action(d, args, env),
                        Some(OpRef::Builtin(b)) => self.builtin_action(b, args, env),
                        _ => {}
                    },
                    Some(Abs::Op(OpVal::Lambda { params, body, env: lenv })) => self.lambda_action(&params, &body, &lenv, args, env),
                    // An unbound operator parameter is an evaluation error in
                    // the enumerator's `test`: it assigns nothing. A value
                    // parameter applied as an operator is not a valid call.
                    _ => {}
                }
            }
            OpRef::Def(orig_d) => {
                if self.base.ip.has_def_value(*orig_d) {
                    let _ = e;
                    return;
                }
                let d = self.base.ip.redirect_def(*orig_d);
                let def = &self.base.ip.prog.defs[d.idx()];
                let expand = self.base.ip.defers_arg_errors(d) || self.base.ip.is_action_level(d);
                if expand && def.builtin.is_none() && !self.base.ip.has_def_value(d) && !self.base.ip.is_const_def(d) {
                    self.call_def_action(d, args, env);
                } else {
                    // The enumerator evaluates this application as a test.
                    let _ = e;
                }
            }
            OpRef::Builtin(b) => self.builtin_action(*b, args, env),
        }
    }

    /// Inline `d(args)` as an action.
    fn call_def_action(&mut self, orig_d: DefId, args: &[Expr], env: &Env) {
        if self.base.ip.has_def_value(orig_d) {
            return;
        }
        let d = self.base.ip.redirect_def(orig_d);
        let def = &self.base.ip.prog.defs[d.idx()];
        if def.builtin.is_some() || self.base.ip.has_def_value(d) || self.base.ip.is_const_def(d) {
            // The enumerator evaluates this application as a test (a Java
            // override, a cfg value, or a pre-evaluated constant definition).
            return;
        }
        if self.active.contains(&d) || self.depth > DEPTH {
            self.fail(format!("recursive definition {} cannot be proven closed", self.base.ip.prog.defs[d.idx()].name));
            return;
        }
        let Some(body) = self.body_of(d) else {
            self.fail(format!("definition {} cannot be inlined", self.base.ip.prog.defs[d.idx()].name));
            return;
        };
        match self.bind_params(d, args, env) {
            Ok(base) => {
                self.active.push(d);
                self.depth += 1;
                self.action(&body, &base);
                self.depth -= 1;
                self.active.pop();
                self.pop_scope();
            }
            Err(why) => self.fail(why),
        }
    }

    /// Inline a `LAMBDA`-valued operator argument as an action.
    fn lambda_action(&mut self, params: &[LocalId], body: &Expr, lenv: &Env, args: &[Expr], env: &Env) {
        let mut entries = Vec::with_capacity(params.len());
        for (p, a) in params.iter().zip(args.iter()) {
            let arity = self.base.ip.prog.locals[p.idx()].arity;
            if arity > 0 {
                match self.op_val(a, env) {
                    Some(o) => entries.push((*p, Abs::Op(o))),
                    None => {
                        self.fail("a lambda's operator argument cannot be resolved statically");
                        return;
                    }
                }
            } else {
                entries.push((*p, Abs::Thunk(a.clone(), env.clone())));
            }
        }
        self.push_scope(entries);
        self.depth += 1;
        self.action(body, lenv);
        self.depth -= 1;
        self.pop_scope();
    }

    fn body_of(&self, d: DefId) -> Option<Expr> {
        match &self.base.ip.prog.defs[d.idx()].kind {
            DefKind::Op(body) => Some(body.clone()),
            _ => None,
        }
    }

    // ------------------------------------------------------------------
    // value-position evaluation

    /// The values `e` can take (an over-approximation; `Dyn` when unknown).
    fn value(&mut self, e: &Expr, env: &Env) -> VShape {
        if !self.spend() {
            return VShape::Shape(Shape::Dyn);
        }
        if self.depth > DEPTH {
            return VShape::Shape(Shape::Dyn);
        }
        match &*e.kind {
            H::Num(n) => i64::try_from(*n).map_or(VShape::Shape(Shape::Dyn), |n| VShape::Shape(Shape::Int { lo: n, hi: n })),
            H::Decimal(_) => VShape::Shape(Shape::Dyn),
            H::Str(s) => VShape::Shape(Shape::Atom(vec![Value::Str(Sym::new(s.as_ref()))].into())),
            H::Bool(_) => VShape::Shape(Shape::Bool),
            H::Var(v) => VShape::Shape(self.refined_value(v.idx(), false)),
            H::InstVar { .. } => VShape::Shape(Shape::Dyn),
            H::Const(c) => self.const_value(e, *c, env),
            H::Local(l) => self.local_value(*l, env),
            H::Apply { op, args } => self.apply_value(op, args, env),
            H::Builtin { op, args } => self.builtin_value(*op, args, env),
            H::Lambda { .. } | H::OpArg(_) => VShape::Shape(Shape::Dyn),
            H::And(_) | H::Or(_) | H::TemporalQuant { .. } => VShape::Shape(Shape::Bool),
            H::Quant { .. } | H::QuantUnbounded { .. } => VShape::Shape(Shape::Bool),
            H::Choose { vars, set, body } => self.choose_value(vars, set.as_ref(), body, env),
            H::If { cond, then, els } => {
                let mark = self.refine.len();
                self.refine_guard(cond, env, true);
                let a = self.value(then, env);
                self.refine.truncate(mark);
                self.refine_guard(cond, env, false);
                let b = self.value(els, env);
                self.refine.truncate(mark);
                a.join(&b)
            }
            H::Case { arms, other } => {
                let mut out = VShape::Shape(Shape::Never);
                for (g, v) in arms {
                    let mark = self.refine.len();
                    self.refine_guard(g, env, true);
                    out = out.join(&self.value(v, env));
                    self.refine.truncate(mark);
                }
                if let Some(o) = other {
                    out = out.join(&self.value(o, env));
                }
                if matches!(&out, VShape::Shape(Shape::Never)) && other.is_none() {
                    VShape::Shape(Shape::Dyn)
                } else {
                    out
                }
            }
            H::Let { body, .. } => self.value(body, env),
            H::SetEnum(es) => {
                let elems: Vec<Shape> = es.iter().map(|e| self.value(e, env).as_shape()).collect();
                VShape::Shape(set_shape(join_all(elems), es.len()))
            }
            H::SetFilter { bound, pred } => {
                let source = self.value(&bound.set, env);
                let _ = pred;
                match source {
                    // A comprehension over an interval value may keep the
                    // interval representation; only `Set`-shaped sources are
                    // provably sets.
                    VShape::Shape(Shape::Set { elem, max_card }) => VShape::Shape(set_shape((*elem).clone(), max_card)),
                    _ => VShape::Shape(Shape::Dyn),
                }
            }
            H::SetMap { expr, bounds } => {
                let card = self.bind_bounds(bounds, env);
                let out = match card {
                    Some(0) => VShape::Shape(set_shape(Shape::Never, 0)),
                    Some(card) => VShape::Shape(set_shape(self.value(expr, env).as_shape(), card)),
                    None => VShape::Shape(Shape::Dyn),
                };
                self.pop_scope();
                out
            }
            H::Tuple(es) => VShape::Shape(Shape::Tuple(es.iter().map(|e| self.value(e, env).as_shape()).collect())),
            H::FnConstruct { bounds, body } => self.fn_construct(bounds, body, env),
            H::FnApp { func, args } => self.fn_app_value(func, args, env),
            H::FnSet { domain, range } => self.fn_set(domain, range, env),
            H::Record(fields) => {
                VShape::Shape(record_shape(fields.iter().map(|(n, e)| (Sym::new(n.as_ref()), self.value(e, env).as_shape())).collect()))
            }
            H::RecordSet(fields) => self.record_set(fields, env),
            H::Field { record, field } => self.field_value(record, field, env),
            H::Except { base, updates } => self.except_value(base, updates, env),
            H::At => VShape::Shape(self.at.clone().unwrap_or(Shape::Dyn)),
            H::BoxAction { .. } | H::AngleAction { .. } | H::Fairness { .. } => VShape::Shape(Shape::Bool),
        }
    }

    fn choose_value(&mut self, vars: &BoundVars, set: Option<&Expr>, body: &Expr, env: &Env) -> VShape {
        let Some(set) = set else { return VShape::Shape(Shape::Dyn) };
        let Some((elem, _)) = self.value(set, env).as_set() else { return VShape::Shape(Shape::Dyn) };
        let _ = (vars, body);
        VShape::Shape(elem)
    }

    /// A `CONSTANT`'s value: the definition the cfg substituted (respecting
    /// any cfg-assigned `def_value` or builtin override), or the literal value.
    /// Reading an already-computed literal cannot evaluate or create anything.
    fn const_value(&mut self, e: &Expr, c: ConstId, env: &Env) -> VShape {
        if let Some(orig_d) = self.base.ip.const_def(c) {
            let d = self.base.ip.redirect_def(orig_d);
            if self.base.ip.has_def_value(orig_d) || self.base.ip.has_def_value(d) {
                return self.eval_const_shape(e, env);
            }
            if self.base.ip.prog.defs[d.idx()].builtin.is_some() {
                return VShape::Shape(Shape::Dyn);
            }
            if let Some(body) = self.body_of(d) {
                if self.depth <= DEPTH && !self.active.contains(&d) {
                    self.active.push(d);
                    self.depth += 1;
                    let s = self.value(&body, &Env::default());
                    self.depth -= 1;
                    self.active.pop();
                    return s;
                }
            }
            return VShape::Shape(Shape::Dyn);
        }
        if self.base.ip.const_op_ref(c).is_some() {
            return VShape::Shape(Shape::Dyn);
        }
        // The remaining case is a literal value (`ConstVal::Value`); a table
        // of operator values is not a value and errors on use.
        self.eval_const_shape(e, env)
    }

    /// Shape of a cfg-assigned literal constant or `def_value`, bounded so an
    /// oversized or lazy set is never forced into memory.
    fn eval_const_shape(&self, e: &Expr, env: &Env) -> VShape {
        match self.base.ip.eval(e, env, &Ctx::NONE) {
            Ok(v) => shape_of_value(&v),
            Err(_) => VShape::Shape(Shape::Dyn),
        }
    }

    /// `f(args)` applied as a value.
    fn apply_value(&mut self, op: &OpRef, args: &[Expr], env: &Env) -> VShape {
        match op {
            OpRef::Def(orig_d) => {
                if self.base.ip.has_def_value(*orig_d) {
                    return VShape::Shape(Shape::Dyn);
                }
                let d = self.base.ip.redirect_def(*orig_d);
                let def = &self.base.ip.prog.defs[d.idx()];
                if def.builtin.is_some() || self.base.ip.has_def_value(d) {
                    return VShape::Shape(Shape::Dyn);
                }
                let body = match &def.kind {
                    DefKind::Op(body) => body.clone(),
                    _ => return VShape::Shape(Shape::Dyn),
                };
                if self.active.contains(&d) || self.depth > DEPTH {
                    return VShape::Shape(Shape::Dyn);
                }
                let shapes: Vec<VShape> = args.iter().map(|a| self.value(a, env)).collect();
                let Some(base) = self.bind_params_value(d, shapes, env) else { return VShape::Shape(Shape::Dyn) };
                self.active.push(d);
                self.depth += 1;
                let s = self.value(&body, &base);
                self.depth -= 1;
                self.active.pop();
                self.pop_scope();
                s
            }
            OpRef::Const(c) => match self.base.ip.const_op_ref(*c) {
                Some(r) => self.apply_value(&r, args, env),
                None => VShape::Shape(Shape::Dyn),
            },
            OpRef::Param(l) => {
                let binding = self.lookup(*l).cloned().or_else(|| {
                    env.lookup(*l).map(|b| match b {
                        Binding::Op(o) => Abs::Op(o.clone()),
                        _ => Abs::Val(VShape::Shape(Shape::Dyn)),
                    })
                });
                match binding {
                    Some(Abs::Op(OpVal::Ref(r))) => {
                        let shapes: Vec<Shape> = args.iter().map(|a| self.value(a, env).as_shape()).collect();
                        self.apply_op_shape(r, &shapes, env)
                    }
                    Some(Abs::Op(OpVal::Lambda { params, body, env: lenv })) => {
                        let shapes: Vec<Shape> = args.iter().map(|a| self.value(a, env).as_shape()).collect();
                        self.lambda_value(&params, &body, &lenv, &shapes)
                    }
                    _ => VShape::Shape(Shape::Dyn),
                }
            }
            OpRef::Builtin(b) => self.builtin_value(*b, args, env),
        }
    }

    /// Apply an operator reference to already-evaluated argument shapes.
    fn apply_op_shape(&mut self, r: OpRef, args: &[Shape], env: &Env) -> VShape {
        match r {
            OpRef::Def(orig_d) => {
                if self.base.ip.has_def_value(orig_d) {
                    return VShape::Shape(Shape::Dyn);
                }
                let d = self.base.ip.redirect_def(orig_d);
                let def = &self.base.ip.prog.defs[d.idx()];
                if def.builtin.is_some() || self.base.ip.has_def_value(d) {
                    return VShape::Shape(Shape::Dyn);
                }
                let body = match &def.kind {
                    DefKind::Op(body) => body.clone(),
                    _ => return VShape::Shape(Shape::Dyn),
                };
                if self.active.contains(&d) || self.depth > DEPTH {
                    return VShape::Shape(Shape::Dyn);
                }
                let shapes: Vec<VShape> = args.iter().cloned().map(VShape::Shape).collect();
                let Some(base) = self.bind_params_value(d, shapes, env) else { return VShape::Shape(Shape::Dyn) };
                self.active.push(d);
                self.depth += 1;
                let s = self.value(&body, &base);
                self.depth -= 1;
                self.active.pop();
                self.pop_scope();
                s
            }
            _ => VShape::Shape(Shape::Dyn),
        }
    }

    /// Bind a definition's parameters to value shapes (value position).
    fn bind_params_value(&mut self, d: DefId, args: Vec<VShape>, env: &Env) -> Option<Env> {
        let decl = &self.base.ip.prog.defs[d.idx()];
        if decl.params.len() != args.len() {
            return None;
        }
        let base = if self.base.ip.prog.def_is_let(d) { env.clone() } else { Env::default() };
        let entries = decl.params.iter().zip(args).map(|(p, s)| (*p, Abs::Val(s))).collect();
        self.push_scope(entries);
        Some(base)
    }

    fn lambda_value(&mut self, params: &[LocalId], body: &Expr, lenv: &Env, args: &[Shape]) -> VShape {
        if params.len() != args.len() {
            return VShape::Shape(Shape::Dyn);
        }
        let entries = params.iter().zip(args).map(|(p, s)| (*p, Abs::Val(VShape::Shape(s.clone())))).collect();
        self.push_scope(entries);
        self.depth += 1;
        let s = self.value(body, lenv);
        self.depth -= 1;
        self.pop_scope();
        s
    }

    /// `f[a]` applied as a value: the body of a lazily represented function
    /// with its arguments bound, or the range/component of a function value.
    fn fn_app_value(&mut self, func: &Expr, args: &[Expr], env: &Env) -> VShape {
        if let Some((bounds, body, fenv)) = self.lambda_of(func, env, false) {
            if self.bind_fn_args(&bounds, args, env).is_some() {
                self.depth += 1;
                let s = self.value(&body, &fenv);
                self.depth -= 1;
                self.pop_scope();
                return s;
            }
        }
        let f = self.value(func, env).as_shape();
        let arg_shapes: Vec<VShape> = args.iter().map(|a| self.value(a, env)).collect();
        match (&f, arg_shapes.as_slice()) {
            (Shape::Fcn { range, .. }, [_]) => VShape::Shape((**range).clone()),
            (Shape::Map { range, .. }, [_]) => VShape::Shape((**range).clone()),
            (Shape::Seq { elem, .. }, [_]) => VShape::Shape((**elem).clone()),
            (Shape::Tuple(es), [a]) => VShape::Shape(match singleton_index(&a.as_shape()) {
                Some(i) if i >= 1 && (i as usize) <= es.len() => es[i as usize - 1].clone(),
                _ => join_all(es.iter().cloned()),
            }),
            _ => VShape::Shape(Shape::Dyn),
        }
    }

    /// `[d \in S |-> e]`: a fixed-domain function when the domain is a known
    /// finite constant or an interval, otherwise a map over `S`'s elements.
    fn fn_construct(&mut self, bounds: &[Bound], body: &Expr, env: &Env) -> VShape {
        let [bound] = bounds else { return VShape::Shape(Shape::Dyn) };
        let single_slot = matches!(&bound.vars, BoundVars::Many(ls) if ls.len() == 1) || matches!(&bound.vars, BoundVars::Tuple(_));
        if !single_slot {
            return VShape::Shape(Shape::Dyn);
        }
        let domain = self.value(&bound.set, env);
        // The exact finite domain: keys, construction witness and the body's
        // values per key are known.
        if let Some((values, witness)) = self.exact_domain(&bound.set, env) {
            let range = self.body_over_domain(body, &bound.vars, &values, env);
            return VShape::Shape(fcn_shape(values, range, witness));
        }
        let Some((elem, _)) = domain.as_set() else { return VShape::Shape(Shape::Dyn) };
        let witness = self.domain_witness(&domain);
        let entries = match &bound.vars {
            BoundVars::Many(ls) => vec![(ls[0], Abs::Val(VShape::Shape(elem.clone())))],
            BoundVars::Tuple(ls) => {
                let parts = tuple_parts(&elem, ls.len());
                ls.iter().enumerate().map(|(i, l)| (*l, Abs::Val(VShape::Shape(parts[i].clone())))).collect()
            }
        };
        self.push_scope(entries);
        let range = self.value(body, env).as_shape();
        self.pop_scope();
        VShape::Shape(Shape::Map { key: Box::new(elem), range: Box::new(range), witness })
    }

    /// The body's shape over a finite domain: the join with the bound variable
    /// (scalar or tuple binder) taking each element.
    fn body_over_domain(&mut self, body: &Expr, vars: &BoundVars, values: &[Value], env: &Env) -> Shape {
        let mut out = Shape::Never;
        for v in values {
            let entries = match vars {
                BoundVars::Many(ls) => vec![(ls[0], Abs::Val(shape_of_value(v)))],
                BoundVars::Tuple(ls) => match v {
                    Value::Tuple(es) if es.len() == ls.len() => {
                        ls.iter().zip(es.iter()).map(|(l, e)| (*l, Abs::Val(shape_of_value(e)))).collect()
                    }
                    _ => ls.iter().map(|l| (*l, Abs::Val(VShape::Shape(Shape::Dyn)))).collect(),
                },
            };
            self.push_scope(entries);
            out = out.join(&self.value(body, env).as_shape());
            self.pop_scope();
            if matches!(out, Shape::Dyn) || self.reason.is_some() {
                return Shape::Dyn;
            }
        }
        out
    }

    /// The concrete elements of a closed finite domain (bounded by
    /// `MAX_EXACT_DOMAIN`) and its construction witness, when they are already
    /// explicit without forcing any lazy value.
    fn exact_domain(&mut self, e: &Expr, env: &Env) -> Option<(Vec<Value>, FcnWitness)> {
        let _ = env;
        let v = self.eval_bounded_const(e, 0)?;
        match v {
            Value::Interval(lo, hi) => {
                let n = if hi < lo { 0 } else { (hi as i128) - (lo as i128) + 1 };
                if n > MAX_EXACT_DOMAIN as i128 {
                    return None;
                }
                Some(((lo..=hi).map(Value::Int).collect(), FcnWitness::Interval))
            }
            Value::Set(es) => {
                if es.len() > MAX_EXACT_DOMAIN as usize {
                    return None;
                }
                Some((es.to_vec(), FcnWitness::Enumerated))
            }
            _ => None,
        }
    }

    /// The construction witness of a function over the abstract set `domain`:
    /// `Dynamic` unless the value is known to be a `Set` (enumerated domain).
    fn domain_witness(&mut self, domain: &VShape) -> FcnWitness {
        match domain {
            VShape::Interval { .. } => FcnWitness::Interval,
            VShape::Shape(s) if s.is_unbounded() => FcnWitness::Dynamic,
            // A non-`Dyn` slot holds a `Set` (an interval value cannot be
            // encoded there).
            VShape::Shape(Shape::Set { .. }) => FcnWitness::Enumerated,
            _ => FcnWitness::Dynamic,
        }
    }

    /// Evaluate a closed constant expression only when every intermediate and
    /// final set/collection stays within `MAX_EXACT_DOMAIN` without forcing
    /// unbounded lazy sets.
    fn eval_bounded_const(&self, e: &Expr, depth: usize) -> Option<Value> {
        if depth > 32 {
            return None;
        }
        let ip = &self.base.ip;
        let eval_and_check = |expr: &Expr| -> Option<Value> {
            let v = ip.eval(expr, &Env::default(), &Ctx::NONE).ok()?;
            value_within_domain_bound(&v).then_some(v)
        };
        match &*e.kind {
            H::Num(_) | H::Str(_) | H::Bool(_) => eval_and_check(e),
            H::Const(c) => {
                if ip.const_op_ref(*c).is_some() {
                    return None;
                }
                let ready = match ip.const_def(*c) {
                    None => true,
                    Some(orig_d) => {
                        let d = ip.redirect_def(orig_d);
                        ip.has_def_value(orig_d) || ip.has_def_value(d) || ip.const_def_evaluated(d)
                    }
                };
                if !ready {
                    return None;
                }
                eval_and_check(e)
            }
            H::Apply { op: OpRef::Def(orig_d), args } if args.is_empty() => {
                let d = ip.redirect_def(*orig_d);
                let ready = ip.has_def_value(*orig_d) || ip.has_def_value(d) || (ip.is_const_def(d) && ip.const_def_evaluated(d));
                if !ready {
                    return None;
                }
                eval_and_check(e)
            }
            H::Builtin { op, args } | H::Apply { op: OpRef::Builtin(op), args } => {
                // Only evaluation with a bounded, side-effect-free result:
                // no lazy-set constructors (`SUBSET`, `[S -> T]`, `Seq`, ...),
                // whose enumeration could be enormous, and every operand must
                // itself stay within the domain bound before evaluating `op`.
                let allowed = matches!(
                    op,
                    B::DotDot
                        | B::Plus
                        | B::Minus
                        | B::Mul
                        | B::Div
                        | B::Mod
                        | B::Pow
                        | B::Neg
                        | B::Cup
                        | B::Cap
                        | B::SetMinus
                        | B::Cardinality
                        | B::Len
                        | B::Head
                        | B::Tail
                        | B::Append
                        | B::Concat
                        | B::SubSeq
                        | B::Eq
                        | B::Neq
                        | B::Lt
                        | B::Le
                        | B::Gt
                        | B::Ge
                        | B::Not
                        | B::Implies
                        | B::Equiv
                        | B::In
                        | B::NotIn
                        | B::SubsetEq
                        | B::IsFiniteSet
                ) && !ip.is_builtin_overridden(*op)
                    && !op.is_volatile()
                    && !op.makes_strings();
                if !allowed {
                    return None;
                }
                for a in args {
                    self.eval_bounded_const(a, depth + 1)?;
                }
                eval_and_check(e)
            }
            H::SetEnum(es) | H::Tuple(es) => {
                if es.len() > MAX_EXACT_DOMAIN as usize {
                    return None;
                }
                for x in es {
                    self.eval_bounded_const(x, depth + 1)?;
                }
                eval_and_check(e)
            }
            H::Record(fs) => {
                if fs.len() > MAX_EXACT_DOMAIN as usize {
                    return None;
                }
                for (_, x) in fs {
                    self.eval_bounded_const(x, depth + 1)?;
                }
                eval_and_check(e)
            }
            _ => None,
        }
    }

    /// `[A -> B]`: the set of functions over a known finite domain.
    fn fn_set(&mut self, domain: &Expr, range: &Expr, env: &Env) -> VShape {
        let Some((range_elem, range_card)) = self.value(range, env).as_set() else { return VShape::Shape(Shape::Dyn) };
        let Some((dom, witness)) = self.exact_domain(domain, env) else { return VShape::Shape(Shape::Dyn) };
        let Some(card) = (range_card as u128).checked_pow(dom.len() as u32).and_then(|n| usize::try_from(n).ok()) else {
            return VShape::Shape(Shape::Dyn);
        };
        if card == 0 {
            return VShape::Shape(set_shape(Shape::Never, 0));
        }
        let range_shape = if dom.is_empty() { Shape::Never } else { range_elem };
        let f = fcn_shape(dom, range_shape, witness);
        VShape::Shape(set_shape(f, card))
    }

    fn record_set(&mut self, fields: &[(Arc<str>, Expr)], env: &Env) -> VShape {
        let mut card: usize = 1;
        let mut shapes = Vec::with_capacity(fields.len());
        for (name, e) in fields {
            let Some((elem, max_card)) = self.value(e, env).as_set() else { return VShape::Shape(Shape::Dyn) };
            let Some(next) = card.checked_mul(max_card) else { return VShape::Shape(Shape::Dyn) };
            card = next;
            shapes.push((Sym::new(name.as_ref()), elem));
        }
        if card == 0 {
            return VShape::Shape(set_shape(Shape::Never, 0));
        }
        VShape::Shape(set_shape(record_shape(shapes), card))
    }

    fn field_value(&mut self, record: &Expr, field: &Arc<str>, env: &Env) -> VShape {
        VShape::Shape(record_field(&self.value(record, env).as_shape(), &Sym::new(field.as_ref())))
    }

    /// `[f EXCEPT ![k] = v, ...]`.
    fn except_value(&mut self, base: &Expr, updates: &[(Vec<ExceptKey>, Expr)], env: &Env) -> VShape {
        let mut shape = self.value(base, env).as_shape();
        for (keys, value) in updates {
            let [key] = keys.as_slice() else { return VShape::Shape(Shape::Dyn) };
            let old = match (key, &shape) {
                (ExceptKey::Field(f), s) => record_field(s, &Sym::new(f.as_ref())),
                (ExceptKey::Index(ix), Shape::Tuple(es)) if ix.len() == 1 => {
                    let idx = self.value(&ix[0], env).as_shape();
                    match singleton_index(&idx) {
                        Some(i) if i >= 1 && (i as usize) <= es.len() => es[i as usize - 1].clone(),
                        _ => join_all(es.iter().cloned()),
                    }
                }
                (ExceptKey::Index(ix), Shape::Fcn { range, .. }) | (ExceptKey::Index(ix), Shape::Map { range, .. }) if ix.len() == 1 => {
                    (**range).clone()
                }
                (ExceptKey::Index(ix), Shape::Seq { elem, .. }) if ix.len() == 1 => (**elem).clone(),
                _ => return VShape::Shape(Shape::Dyn),
            };
            let prev = self.at.replace(old);
            let v = self.value(value, env).as_shape();
            self.at = prev;
            shape = match (key, &shape) {
                (ExceptKey::Field(f), Shape::Record(fs)) => {
                    let f = Sym::new(f.as_ref());
                    let mut fs = fs.to_vec();
                    match fs.iter_mut().find(|(n, _)| *n == f) {
                        Some((_, s)) => *s = v,
                        None => return VShape::Shape(Shape::Dyn),
                    }
                    Shape::Record(fs.into())
                }
                (ExceptKey::Index(ix), Shape::Tuple(es)) if ix.len() == 1 => {
                    let idx = self.value(&ix[0], env).as_shape();
                    match singleton_index(&idx) {
                        Some(i) if i >= 1 && (i as usize) <= es.len() => {
                            let mut es = es.to_vec();
                            es[i as usize - 1] = v;
                            Shape::Tuple(es.into())
                        }
                        _ => Shape::Tuple(es.iter().map(|e| e.join(&v)).collect()),
                    }
                }
                (ExceptKey::Index(_), Shape::Fcn { dom, range, witness, key_variants }) => {
                    Shape::Fcn { dom: dom.clone(), range: Box::new(range.join(&v)), witness: *witness, key_variants: key_variants.clone() }
                }
                (ExceptKey::Index(_), Shape::Map { key, range, witness }) => {
                    Shape::Map { key: key.clone(), range: Box::new(range.join(&v)), witness: *witness }
                }
                (ExceptKey::Index(_), Shape::Seq { elem, max_len }) => Shape::Seq { elem: Box::new(elem.join(&v)), max_len: *max_len },
                _ => return VShape::Shape(Shape::Dyn),
            };
        }
        VShape::Shape(shape)
    }

    // ------------------------------------------------------------------
    // built-in abstract operators

    fn builtin_value(&mut self, op: B, args: &[Expr], env: &Env) -> VShape {
        if self.base.ip.is_builtin_overridden(op) {
            return VShape::Shape(Shape::Dyn);
        }
        // Shape-valued (kind-level) operators first.
        match op {
            B::Prime => {
                let [a] = args else { return VShape::Shape(Shape::Dyn) };
                return match self.var_of(a, env) {
                    Some(v) => VShape::Shape(self.refined_value(v, true)),
                    None => VShape::Shape(Shape::Dyn),
                };
            }
            B::Unchanged | B::Enabled | B::Always | B::Eventually | B::LeadsTo | B::WhilePlus | B::Compose => {
                return VShape::Shape(Shape::Bool)
            }
            _ => {}
        }
        let args: Vec<VShape> = args.iter().map(|a| self.value(a, env)).collect();
        let sh = |i: usize| args.get(i).map(VShape::as_shape).unwrap_or(Shape::Dyn);
        match op {
            B::Eq
            | B::Neq
            | B::In
            | B::NotIn
            | B::SubsetEq
            | B::SqSubseteq
            | B::Lt
            | B::Gt
            | B::Le
            | B::Ge
            | B::Not
            | B::Implies
            | B::Equiv => VShape::Shape(Shape::Bool),
            B::Boolean => VShape::Shape(Shape::Set { elem: Box::new(Shape::Bool), max_card: 2 }),
            B::Nat | B::Int | B::StringSet | B::Any | B::Seq => VShape::Shape(Shape::Dyn),
            B::Plus => VShape::Shape(int_binop(&args, |a, b| (a.0.saturating_add(b.0), a.1.saturating_add(b.1)))),
            B::Minus => VShape::Shape(int_binop(&args, |a, b| (a.0.saturating_sub(b.1), a.1.saturating_sub(b.0)))),
            B::Mul => VShape::Shape(int_binop(&args, |a, b| {
                let c = [a.0 as i128 * b.0 as i128, a.0 as i128 * b.1 as i128, a.1 as i128 * b.0 as i128, a.1 as i128 * b.1 as i128];
                (i64::try_from(*c.iter().min().unwrap()).unwrap_or(i64::MIN), i64::try_from(*c.iter().max().unwrap()).unwrap_or(i64::MAX))
            })),
            B::Neg => match sh(0) {
                Shape::Int { lo, hi } => VShape::Shape(Shape::Int { lo: hi.saturating_neg(), hi: lo.saturating_neg() }),
                _ => VShape::Shape(Shape::Dyn),
            },
            B::Div => VShape::Shape(div_bounds(&args)),
            B::Mod => VShape::Shape(mod_bounds(&args)),
            B::Pow => VShape::Shape(pow_bounds(&args)),
            B::DotDot => match sh(0) {
                Shape::Int { lo, hi: _ } => match sh(1) {
                    Shape::Int { hi: bhi, .. } => VShape::Interval { lo, hi: bhi },
                    _ => VShape::Shape(Shape::Dyn),
                },
                _ => VShape::Shape(Shape::Dyn),
            },
            B::Subset => match args.first().and_then(VShape::as_set) {
                Some((elem, card)) => {
                    let inner = set_shape(elem, card);
                    if card < usize::BITS as usize {
                        VShape::Shape(set_shape(inner, 1usize << card))
                    } else {
                        VShape::Shape(Shape::Dyn)
                    }
                }
                None => VShape::Shape(Shape::Dyn),
            },
            B::Union => match args.first() {
                Some(VShape::Shape(Shape::Set { elem, max_card })) => match &**elem {
                    Shape::Set { elem: inner, max_card: inner_card } => match max_card.checked_mul(*inner_card) {
                        Some(card) => VShape::Shape(set_shape((**inner).clone(), card)),
                        None => VShape::Shape(Shape::Dyn),
                    },
                    _ => VShape::Shape(Shape::Dyn),
                },
                _ => VShape::Shape(Shape::Dyn),
            },
            B::Cup | B::Cap | B::SetMinus => {
                if matches!(args.first(), Some(VShape::Interval { .. })) || matches!(args.get(1), Some(VShape::Interval { .. })) {
                    // A union/difference can return one of its operands, an
                    // interval value; a `Set` shape does not describe it.
                    return VShape::Shape(Shape::Dyn);
                }
                let a = args.first().and_then(VShape::as_set);
                let b = args.get(1).and_then(VShape::as_set);
                match (op, a, b) {
                    (B::SetMinus, Some((ea, ma)), Some(_)) => VShape::Shape(set_shape(ea, ma)),
                    (B::Cup, Some((ea, ma)), Some((eb, mb))) => match ma.checked_add(mb) {
                        Some(card) => VShape::Shape(set_shape(ea.join(&eb), card)),
                        None => VShape::Shape(Shape::Dyn),
                    },
                    (B::Cap, Some((ea, ma)), Some((eb, mb))) => VShape::Shape(set_shape(ea.join(&eb), ma.min(mb))),
                    _ => VShape::Shape(Shape::Dyn),
                }
            }
            B::Times => {
                let mut parts = Vec::with_capacity(args.len());
                let mut card: usize = 1;
                for a in &args {
                    let Some((elem, max_card)) = a.as_set() else { return VShape::Shape(Shape::Dyn) };
                    parts.push(elem);
                    let Some(next) = card.checked_mul(max_card) else { return VShape::Shape(Shape::Dyn) };
                    card = next;
                }
                if card == 0 {
                    VShape::Shape(set_shape(Shape::Never, 0))
                } else {
                    VShape::Shape(set_shape(Shape::Tuple(parts.into()), card))
                }
            }
            B::Domain => self.domain_value(&sh(0)),
            B::Len => match sh(0) {
                Shape::Seq { max_len, .. } => VShape::Shape(Shape::Int { lo: 0, hi: i64::try_from(max_len).unwrap_or(i64::MAX) }),
                Shape::Tuple(es) => VShape::Shape(Shape::Int { lo: es.len() as i64, hi: es.len() as i64 }),
                Shape::Atom(_) => VShape::Shape(Shape::Int { lo: 0, hi: i64::MAX }),
                _ => VShape::Shape(Shape::Dyn),
            },
            B::Append => match (&args[0], &args[1]) {
                (VShape::Shape(Shape::Seq { elem, max_len }), v) => {
                    VShape::Shape(Shape::Seq { elem: Box::new(elem.join(&v.as_shape())), max_len: max_len.saturating_add(1) })
                }
                (VShape::Shape(Shape::Tuple(es)), v) => {
                    let mut out = es.to_vec();
                    out.push(v.as_shape());
                    VShape::Shape(Shape::Tuple(out.into()))
                }
                _ => VShape::Shape(Shape::Dyn),
            },
            B::Concat => match (&args[0], &args[1]) {
                (VShape::Shape(Shape::Seq { elem, max_len }), VShape::Shape(Shape::Seq { elem: e2, max_len: m2 })) => {
                    VShape::Shape(Shape::Seq { elem: Box::new(elem.join(e2)), max_len: max_len.saturating_add(*m2) })
                }
                (VShape::Shape(Shape::Tuple(es)), VShape::Shape(Shape::Tuple(es2))) => {
                    VShape::Shape(Shape::Tuple(es.iter().chain(es2.iter()).cloned().collect()))
                }
                _ => VShape::Shape(Shape::Dyn),
            },
            B::Head => match sh(0) {
                Shape::Seq { elem, .. } => VShape::Shape((*elem).clone()),
                Shape::Tuple(es) => VShape::Shape(es.first().cloned().unwrap_or(Shape::Dyn)),
                _ => VShape::Shape(Shape::Dyn),
            },
            B::Tail => match sh(0) {
                Shape::Seq { elem, max_len } => VShape::Shape(Shape::Seq { elem, max_len: max_len.saturating_sub(1) }),
                Shape::Tuple(es) => VShape::Shape(Shape::Tuple(es.iter().skip(1).cloned().collect())),
                _ => VShape::Shape(Shape::Dyn),
            },
            B::SubSeq => match sh(0) {
                Shape::Seq { elem, max_len } => VShape::Shape(Shape::Seq { elem, max_len }),
                Shape::Tuple(es) => VShape::Shape(Shape::Seq { elem: Box::new(join_all(es.iter().cloned())), max_len: es.len() }),
                _ => VShape::Shape(Shape::Dyn),
            },
            B::SelectSeq => match sh(0) {
                Shape::Seq { elem, max_len } => VShape::Shape(Shape::Seq { elem, max_len }),
                Shape::Tuple(es) => VShape::Shape(Shape::Seq { elem: Box::new(join_all(es.iter().cloned())), max_len: es.len() }),
                _ => VShape::Shape(Shape::Dyn),
            },
            B::Cardinality => match &args[0] {
                VShape::Shape(Shape::Set { max_card, .. }) => {
                    VShape::Shape(Shape::Int { lo: 0, hi: i64::try_from(*max_card).unwrap_or(i64::MAX) })
                }
                VShape::Interval { lo, hi } => {
                    let card = if hi < lo { 0 } else { hi.saturating_sub(*lo).saturating_add(1) };
                    VShape::Shape(Shape::Int { lo: 0, hi: card })
                }
                _ => VShape::Shape(Shape::Dyn),
            },
            B::IsFiniteSet => VShape::Shape(Shape::Bool),
            B::Print => args.get(1).cloned().unwrap_or(VShape::Shape(Shape::Dyn)),
            B::PrintT | B::Assert => VShape::Shape(Shape::Bool),
            B::ToString | B::ToJson | B::ToJsonArray | B::ToJsonObject => VShape::Shape(Shape::Dyn),
            _ => VShape::Shape(Shape::Dyn),
        }
    }

    fn domain_value(&mut self, s: &Shape) -> VShape {
        match s {
            Shape::Tuple(es) => VShape::Interval { lo: 1, hi: es.len() as i64 },
            Shape::Fcn { dom, witness, key_variants, .. } => match witness {
                FcnWitness::Enumerated => {
                    let elem = join_all(dom.iter().chain(key_variants.iter().flat_map(|(_, vs)| vs.iter())).map(Shape::of));
                    VShape::Shape(set_shape(elem, dom.len()))
                }
                FcnWitness::Interval => match (dom.first(), dom.last()) {
                    (Some(Value::Int(lo)), Some(Value::Int(hi))) => VShape::Interval { lo: *lo, hi: *hi },
                    _ => VShape::Shape(Shape::Dyn),
                },
                FcnWitness::Dynamic => VShape::Shape(Shape::Dyn),
            },
            Shape::Record(fs) => {
                let mut keys: Vec<Value> = fs.iter().map(|(k, _)| Value::Str(*k)).collect();
                keys.sort();
                VShape::Shape(set_shape(Shape::Atom(keys.into()), fs.len()))
            }
            Shape::Map { key, witness, .. } => match witness {
                FcnWitness::Enumerated => match key.cardinality() {
                    Some(card) => VShape::Shape(set_shape((**key).clone(), usize::try_from(card).unwrap_or(usize::MAX))),
                    None => VShape::Shape(Shape::Dyn),
                },
                FcnWitness::Interval => match &**key {
                    Shape::Int { lo, hi } => VShape::Interval { lo: *lo, hi: *hi },
                    _ => VShape::Shape(Shape::Dyn),
                },
                FcnWitness::Dynamic => VShape::Shape(Shape::Dyn),
            },
            _ => VShape::Shape(Shape::Dyn),
        }
    }
}

// ----------------------------------------------------------------------
// shape helpers

/// Whether the expression reads the next state (`e'`).
fn is_primed(e: &Expr) -> bool {
    matches!(&*e.kind, H::Builtin { op: B::Prime, .. })
}

/// Narrow representation shape `a` using a TLA+ equality/membership constraint
/// against values described by `b`.
///
/// Only scalar shapes (`Bool`, `Int`, `Atom`) have unique runtime
/// representations under TLA+ equality; compound values (`Set` vs `Interval`,
/// `Tuple` vs `Fcn` vs `Record` vs `Map` vs `Seq`) can be TLA+-equal across
/// distinct layout representations, so narrowing against compound `b` stays at
/// `a` rather than assuming a representation.
fn intersect(a: &Shape, b: &Shape) -> Shape {
    use Shape::*;
    match (a, b) {
        (Never, _) | (_, Never) => Never,
        (x, Dyn | Ref(_)) => x.clone(),
        (Dyn | Ref(_), x) if x.is_scalar() => x.clone(),
        (Int { lo, hi }, Int { lo: l2, hi: h2 }) => {
            let (lo, hi) = ((*lo).max(*l2), (*hi).min(*h2));
            if lo <= hi {
                Int { lo, hi }
            } else {
                Never
            }
        }
        (Bool, Bool) => Bool,
        (Atom(u), Atom(v)) => {
            let out: Vec<Value> = u.iter().filter(|x| v.binary_search(x).is_ok()).cloned().collect();
            if out.is_empty() {
                Never
            } else {
                Atom(out.into())
            }
        }
        (Union(arms), x) if x.is_scalar() => match x.kind_key() {
            Some(key) => match arms.iter().find(|arm| arm.kind_key().as_ref() == Some(&key)) {
                Some(arm) => intersect(arm, x),
                None => Never,
            },
            None => a.clone(),
        },
        // A concrete non-scalar (or scalar of another kind) can never equal a
        // scalar value in TLA+.
        (x, y) if y.is_scalar() && !x.is_unbounded() && !matches!(x, Union(_)) => Never,
        // Do not narrow against compound shapes: TLA+ equality crosses layout
        // representations (`Interval`/`Set`, `Tuple`/`Fcn`/`Record`/`Map`).
        _ => a.clone(),
    }
}

/// Whether `v` is already normalized (no lazy sets or functions anywhere
/// inside) and fits within `budget` total value nodes.
fn is_bounded_value(v: &Value, budget: &mut usize) -> bool {
    if *budget == 0 {
        return false;
    }
    *budget -= 1;
    match v {
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::ModelValue(_) | Value::Interval(..) => true,
        Value::Set(es) | Value::Tuple(es) => es.len() <= *budget && es.iter().all(|e| is_bounded_value(e, budget)),
        Value::Record(fs) => fs.len() <= *budget && fs.iter().all(|(_, e)| is_bounded_value(e, budget)),
        Value::Fcn(ps, _) => ps.len() <= *budget && ps.iter().all(|(k, x)| is_bounded_value(k, budget) && is_bounded_value(x, budget)),
        Value::LazySet(_) | Value::LazyFcn(_) => false,
    }
}

/// Unified admission check for both exact-domain evaluation and constant value
/// shape inspection: rejects any lazy value (`LazySet` / `LazyFcn`, at top
/// level or nested) and bounds total nodes and top-level cardinality without
/// ever calling `normalize()`.
fn value_within_domain_bound(v: &Value) -> bool {
    const NODE_BUDGET: usize = MAX_EXACT_DOMAIN as usize * 8;
    match v {
        Value::Interval(lo, hi) => hi < lo || ((*hi as i128) - (*lo as i128) + 1) <= MAX_EXACT_DOMAIN as i128,
        Value::Set(es) => {
            if es.len() > MAX_EXACT_DOMAIN as usize {
                return false;
            }
            let mut budget = NODE_BUDGET;
            is_bounded_value(v, &mut budget)
        }
        Value::LazySet(_) | Value::LazyFcn(_) => false,
        _ => {
            let mut budget = NODE_BUDGET;
            is_bounded_value(v, &mut budget)
        }
    }
}

/// Bounded `Shape::of` for a value, with interval values kept as
/// [`VShape::Interval`] (their shape-level abstraction is `Dyn`), using the
/// same admission check as `exact_domain` so lazy or oversized values are
/// never forced or traversed.
fn shape_of_value(v: &Value) -> VShape {
    match v {
        Value::Interval(lo, hi) => VShape::Interval { lo: *lo, hi: *hi },
        _ if value_within_domain_bound(v) => VShape::Shape(Shape::of(v)),
        _ => VShape::Shape(Shape::Dyn),
    }
}

fn tuple_parts(s: &Shape, n: usize) -> Vec<Shape> {
    match s {
        Shape::Tuple(es) if es.len() == n => es.to_vec(),
        Shape::Tuple(es) => es.iter().cloned().chain(std::iter::repeat(Shape::Dyn)).take(n).collect(),
        _ => vec![Shape::Dyn; n],
    }
}

fn record_shape(mut fields: Vec<(Sym, Shape)>) -> Shape {
    fields.sort_by_key(|f| f.0);
    fields.dedup_by_key(|f| f.0);
    Shape::Record(fields.into())
}

fn record_field(s: &Shape, f: &Sym) -> Shape {
    match s {
        Shape::Record(fs) => fs.iter().find(|(n, _)| n == f).map(|(_, s)| s.clone()).unwrap_or(Shape::Dyn),
        Shape::Union(arms) => {
            let mut out = Shape::Never;
            let mut any = false;
            for a in arms.iter() {
                if let Shape::Record(fs) = a {
                    if let Some((_, s)) = fs.iter().find(|(n, _)| n == f) {
                        out = out.join(s);
                        any = true;
                    }
                }
            }
            if any {
                out
            } else {
                Shape::Dyn
            }
        }
        _ => Shape::Dyn,
    }
}

/// The exact integer a singleton `Int` shape denotes.
fn singleton_index(s: &Shape) -> Option<i64> {
    match s {
        Shape::Int { lo, hi } if lo == hi => Some(*lo),
        _ => None,
    }
}

/// A function shape over the exact finite domain `dom` with construction
/// witness `witness` and range `range`.
///
/// `Interval` domains are TLC's `FcnRcdValue` over `lo..hi`: over `1..n` the
/// value is a tuple, otherwise an interval-domain function. `Enumerated`
/// domains are a `Fcn` even when the keys happen to be `1..n` (TLC keeps the
/// enumerated construction, `Value::fcn_from_pairs` would pick the tuple).
fn fcn_shape(dom: Vec<Value>, range: Shape, witness: FcnWitness) -> Shape {
    match witness {
        FcnWitness::Interval => {
            let tuple = dom.iter().enumerate().all(|(i, k)| matches!(k, Value::Int(n) if *n == i as i64 + 1));
            if tuple {
                Shape::Tuple(vec![range; dom.len()].into())
            } else {
                Shape::Fcn { dom: dom.into(), range: Box::new(range), witness: FcnWitness::Interval, key_variants: Arc::from([]) }
            }
        }
        _ => Shape::Fcn { dom: dom.into(), range: Box::new(range), witness: FcnWitness::Enumerated, key_variants: Arc::from([]) },
    }
}

fn int_binop(args: &[VShape], f: impl Fn((i64, i64), (i64, i64)) -> (i64, i64)) -> Shape {
    match (args.first().map(VShape::as_shape), args.get(1).map(VShape::as_shape)) {
        (Some(Shape::Int { lo: alo, hi: ahi }), Some(Shape::Int { lo: blo, hi: bhi })) => {
            let (lo, hi) = f((alo, ahi), (blo, bhi));
            Shape::Int { lo, hi }
        }
        _ => Shape::Dyn,
    }
}

fn div_bounds(args: &[VShape]) -> Shape {
    // A positive divisor: the endpoints' quotients bound the exact result up
    // to rounding (floor division or TLC's truncation on non-negative
    // operands); the interval is widened by one to stay sound under either.
    match (args.first().map(VShape::as_shape), args.get(1).map(VShape::as_shape)) {
        (Some(Shape::Int { lo: alo, hi: ahi }), Some(Shape::Int { lo: blo, hi: bhi })) if alo >= 0 && blo > 0 && bhi > 0 => {
            let lo = (alo / bhi).saturating_sub(1).max(0);
            let hi = (ahi / blo).saturating_add(1);
            Shape::Int { lo, hi }
        }
        _ => Shape::Dyn,
    }
}

fn mod_bounds(args: &[VShape]) -> Shape {
    match (args.first().map(VShape::as_shape), args.get(1).map(VShape::as_shape)) {
        (Some(Shape::Int { lo, .. }), Some(Shape::Int { lo: dlo, hi: dhi })) if lo >= 0 && dlo == dhi && dlo > 0 => {
            Shape::Int { lo: 0, hi: dlo - 1 }
        }
        _ => Shape::Dyn,
    }
}

fn pow_bounds(args: &[VShape]) -> Shape {
    match (args.first().map(VShape::as_shape), args.get(1).map(VShape::as_shape)) {
        (Some(Shape::Int { lo: alo, hi: ahi }), Some(Shape::Int { lo: blo, hi: bhi })) if alo >= 0 && blo == bhi && blo >= 0 => {
            let e = u32::try_from(blo).unwrap_or(u32::MAX);
            let lo = i64::try_from((alo as i128).checked_pow(e).unwrap_or(i128::from(i64::MAX))).unwrap_or(i64::MAX);
            let hi = i64::try_from((ahi as i128).checked_pow(e).unwrap_or(i128::from(i64::MAX))).unwrap_or(i64::MAX);
            Shape::Int { lo, hi }
        }
        _ => Shape::Dyn,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tlx_testkit::spec;

    fn model(src: &str) -> InterpModel {
        let src = tlx_testkit::module("Closed", src);
        spec::load(&src, "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n")
    }

    fn int(lo: i64, hi: i64) -> Shape {
        Shape::Int { lo, hi }
    }

    fn closed(m: &InterpModel, vars: Vec<Shape>) -> Result<(), String> {
        layout_is_closed(m, &vars, &[])
    }

    #[test]
    fn boolean_and_bounded_integer_slots_are_closed() {
        let m = model("EXTENDS Naturals\nVARIABLES b, n\nInit == b = FALSE /\\ n = 0\nNext == b' = ~b /\\ n' = IF n < 3 THEN n + 1 ELSE 0");
        assert_eq!(closed(&m, vec![Shape::Bool, int(0, 5)]), Ok(()));
    }

    #[test]
    fn a_too_narrow_integer_slot_keeps_the_archive() {
        let m = model("EXTENDS Naturals\nVARIABLES b, n\nInit == b = FALSE /\\ n = 0\nNext == b' = ~b /\\ n' = IF n < 3 THEN n + 1 ELSE 0");
        assert!(closed(&m, vec![Shape::Bool, int(0, 2)]).is_err());
    }

    #[test]
    fn dyn_slots_accept_anything() {
        let m = model("EXTENDS TLC\nVARIABLE x\nInit == x = \"a\"\nNext == x' = ToString(TLCGet(\"level\"))");
        assert_eq!(closed(&m, vec![Shape::Dyn]), Ok(()));
    }

    #[test]
    fn set_membership_assignments_use_the_element_shape() {
        let m = model("EXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' \\in 1..3");
        assert_eq!(closed(&m, vec![int(0, 5)]), Ok(()));
        assert!(closed(&m, vec![int(2, 5)]).is_err());
    }

    #[test]
    fn subset_assignments_become_set_shapes() {
        let m = model("EXTENDS Naturals\nVARIABLE x\nInit == x = {}\nNext == x' \\subseteq 1..3");
        assert_eq!(closed(&m, vec![Shape::Set { elem: Box::new(int(1, 3)), max_card: 3 }]), Ok(()));
        assert!(closed(&m, vec![Shape::Set { elem: Box::new(int(1, 3)), max_card: 2 }]).is_err());
    }

    #[test]
    fn an_interval_value_only_fits_a_dyn_slot() {
        let src = "EXTENDS Naturals\nVARIABLE x\nInit == x = {}\nNext == x' = 1..3";
        let m = model(src);
        // A `Value::Interval` is not encoded as a fixed `Set` layout.
        assert_eq!(closed(&m, vec![Shape::Dyn]), Ok(()));
        assert!(closed(&m, vec![Shape::Set { elem: Box::new(int(1, 3)), max_card: 3 }]).is_err());
    }

    #[test]
    fn function_witness_flips_keep_the_archive() {
        let src = "EXTENDS Naturals\nVARIABLE f\n\
            Init == f = [i \\in {1, 2} |-> 0]\n\
            Next == f' = IF f[1] = 0 THEN <<1, 2>> ELSE [i \\in 1..2 |-> 0]";
        let m = model(src);
        let en = Shape::Fcn {
            dom: Arc::from([Value::Int(1), Value::Int(2)]),
            range: Box::new(int(0, 2)),
            witness: FcnWitness::Enumerated,
            key_variants: Arc::from([]),
        };
        assert!(closed(&m, vec![en]).is_err());
        // A Dyn slot accepts the tuple and the interval-domain function.
        assert_eq!(closed(&m, vec![Shape::Dyn]), Ok(()));
    }

    #[test]
    fn a_constant_set_domain_function_fits_its_fixed_domain_slot() {
        let src = "EXTENDS Naturals\nVARIABLE f\n\
            Init == f = [i \\in {1, 2} |-> 0]\n\
            Next == f' = [i \\in {1, 2} |-> i]";
        let m = model(src);
        let en = Shape::Fcn {
            dom: Arc::from([Value::Int(1), Value::Int(2)]),
            range: Box::new(int(0, 2)),
            witness: FcnWitness::Enumerated,
            key_variants: Arc::from([]),
        };
        assert_eq!(closed(&m, vec![en]), Ok(()));
    }

    #[test]
    fn guarded_updates_are_narrowed_before_the_assignment() {
        let src = "EXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 4 /\\ x' = x + 1";
        let m = model(src);
        // x in 0..4 is narrowed to 0..3 by the guard, so x + 1 stays in 0..4.
        assert_eq!(closed(&m, vec![int(0, 4)]), Ok(()));
    }

    #[test]
    fn materialized_definitions_must_fit_their_shape() {
        let src = "EXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = IF x < 2 THEN x + 1 ELSE 0\nD == x + 1";
        let m = model(src);
        let d = m.ip.prog.defs.iter().position(|def| &*def.name == "D").expect("D") as u32;
        let d = DefId(d);
        // `x` carries the speculation's headroom (0..4), so `x + 1` reaches 5.
        assert_eq!(layout_is_closed(&m, &[int(0, 4)], &[(d, int(0, 5))]), Ok(()));
        assert!(layout_is_closed(&m, &[int(0, 4)], &[(d, int(0, 4))]).is_err());
    }

    #[test]
    fn an_unprovable_assignment_value_keeps_the_archive() {
        let src = "EXTENDS TLC\nVARIABLE x\nInit == x = \"a\"\nNext == x' = ToString(TLCGet(\"level\"))";
        let m = model(src);
        assert!(closed(&m, vec![Shape::Atom(Arc::from([Value::Str(Sym::new("a"))]))]).is_err());
        assert_eq!(closed(&m, vec![Shape::Dyn]), Ok(()));
    }

    #[test]
    fn unknown_quantifier_domain_still_checks_body_assignments() {
        // `S` is Dyn (or an IF joining interval and set -> Dyn): the body
        // assigns 42 to a slot holding 0, so the proof must fail.
        let src = "EXTENDS Naturals\nVARIABLES S, x\nInit == S = 1..1 /\\ x = 0\nNext == \\E i \\in S : x' = 42 /\\ UNCHANGED S";
        let m = model(src);
        assert!(closed(&m, vec![Shape::Dyn, int(0, 0)]).is_err());
        assert_eq!(closed(&m, vec![Shape::Dyn, int(0, 42)]), Ok(()));

        let src2 = "EXTENDS Naturals\nVARIABLES a, x\nInit == a = FALSE /\\ x = 0\n\
            Next == a' = TRUE /\\ \\E i \\in (IF a THEN 0..1 ELSE {0}) : x' = 100";
        let m2 = model(src2);
        assert!(closed(&m2, vec![Shape::Bool, int(0, 0)]).is_err());
    }

    #[test]
    fn guard_refinements_do_not_escape_their_branch() {
        // Outer guard `x >= 0` creates a refinement; the IF's true arm narrows
        // to `x < 2`, which must not overwrite the outer refinement for the
        // false arm or subsequent conjuncts.
        let src = "EXTENDS Naturals\nVARIABLES x, y\nInit == x \\in 0..9 /\\ y = 0\n\
            Next == x >= 0 /\\ x' = x /\\ y' = IF x < 2 THEN 0 ELSE x";
        let m = model(src);
        assert!(closed(&m, vec![int(0, 9), int(0, 0)]).is_err());
        assert_eq!(closed(&m, vec![int(0, 9), int(0, 9)]), Ok(()));

        // Guard refinement inside one conjunct's IF must not leak `Never` to a
        // later conjunct assigning `n` to a string slot.
        let src2 = "EXTENDS Naturals\nVARIABLES n, y\nInit == n \\in 0..2 /\\ y = \"ok\"\n\
            Next == n >= 0 /\\ n' = IF n < 1 THEN n ELSE n /\\ y' = n";
        let m2 = model(src2);
        let ok = Shape::Atom(Arc::from([Value::Str(Sym::new("ok"))]));
        assert!(closed(&m2, vec![int(0, 2), ok]).is_err());
    }

    #[test]
    fn interval_membership_narrows_union_to_integer_elements() {
        // `x` has a Union(Int, Atom) slot; `x \in 0..1` must narrow `x` to
        // `Int(0..1)`, not `Never` (which would falsely certify `y`'s string slot).
        let src = "EXTENDS Integers\nVARIABLES x, y\n\
            Init == (x = \"hi\" \\/ x = 0) /\\ y = \"ok\"\n\
            Next == x' = x /\\ y' = IF x \\in 0..1 THEN x ELSE \"ok\"";
        let m = model(src);
        let u = Shape::Union(Arc::from([int(0, 0), Shape::Atom(Arc::from([Value::Str(Sym::new("hi"))]))]));
        let ok = Shape::Atom(Arc::from([Value::Str(Sym::new("ok"))]));
        assert!(closed(&m, vec![u, ok]).is_err());
    }

    #[test]
    fn grouped_binders_multiply_set_comprehension_cardinality() {
        // `{<<i, j>> : i, j \in {0, 1, 2}}` has 9 elements, not 3.
        let src = "EXTENDS Naturals, FiniteSets\nVARIABLE x\n\
            Init == x = 0\nNext == x' = Cardinality({<<i, j>> : i, j \\in {0, 1, 2}})";
        let m = model(src);
        assert!(closed(&m, vec![int(0, 3)]).is_err());
        assert!(closed(&m, vec![int(0, 8)]).is_err());
        assert_eq!(closed(&m, vec![int(0, 9)]), Ok(()));
    }

    #[test]
    fn function_set_uses_range_element_shape_and_cardinality() {
        // `x' \in [{1} -> {0}]` assigns functions mapping 1 to the integer 0,
        // not to the set `{0}`.
        let src = "EXTENDS Naturals\nVARIABLE x\n\
            Init == x = [i \\in {1} |-> {0}]\nNext == x' \\in [{1} -> {0}]";
        let m = model(src);
        let set_range = Shape::Fcn {
            dom: Arc::from([Value::Int(1)]),
            range: Box::new(Shape::Set { elem: Box::new(int(0, 0)), max_card: 1 }),
            witness: FcnWitness::Enumerated,
            key_variants: Arc::from([]),
        };
        assert!(closed(&m, vec![set_range]).is_err());

        let src2 = "EXTENDS Naturals\nVARIABLE x\n\
            Init == x = [i \\in {1} |-> 0]\nNext == x' \\in [{1} -> {0, 1}]";
        let m2 = model(src2);
        let int_range = Shape::Fcn {
            dom: Arc::from([Value::Int(1)]),
            range: Box::new(int(0, 1)),
            witness: FcnWitness::Enumerated,
            key_variants: Arc::from([]),
        };
        assert_eq!(closed(&m2, vec![int_range]), Ok(()));
    }

    #[test]
    fn single_component_tuple_binder_destructures_tuple_elements() {
        // `[<<i>> \in {<<1>>} |-> i]` binds `i` to 1, not `<<1>>`.
        let src = "EXTENDS Naturals\nVARIABLE x\n\
            Init == x = [t \\in {<<1>>} |-> t]\nNext == x' = [<<i>> \\in {<<1>>} |-> i]";
        let m = model(src);
        let tuple_range = Shape::Fcn {
            dom: Arc::from([Value::Tuple(Arc::from([Value::Int(1)]))]),
            range: Box::new(Shape::Tuple(Arc::from([int(1, 1)]))),
            witness: FcnWitness::Enumerated,
            key_variants: Arc::from([]),
        };
        assert!(closed(&m, vec![tuple_range]).is_err());

        // Also check application of a 1-tuple binder function.
        let src2 = "EXTENDS Naturals\nVARIABLE x\n\
            F[<<i>> \\in {<<1>>}] == i\nInit == x = <<1>>\nNext == x' = F[<<1>>]";
        let m2 = model(src2);
        assert!(closed(&m2, vec![Shape::Tuple(Arc::from([int(1, 1)]))]).is_err());
    }

    #[test]
    fn tlc_assert_returns_boolean_not_diagnostic_argument() {
        let src = "EXTENDS TLC\nVARIABLE x\nInit == x = \"ok\"\nNext == x' = Assert(TRUE, \"ok\")";
        let m = model(src);
        let ok = Shape::Atom(Arc::from([Value::Str(Sym::new("ok"))]));
        assert!(closed(&m, vec![ok]).is_err());

        let src2 = "EXTENDS TLC\nVARIABLE x\nInit == x = TRUE\nNext == x' = Assert(TRUE, \"ok\")";
        let m2 = model(src2);
        assert_eq!(closed(&m2, vec![Shape::Bool]), Ok(()));
    }

    #[test]
    fn all_unbounded_slots_take_fast_path_without_action_proof() {
        // Even with unanalyzable / recursive actions, all-Ref / all-Dyn slots
        // can never raise a layout miss.
        let src = "EXTENDS Naturals\nVARIABLE x\n\
            RECURSIVE Loop(_)\nLoop(n) == IF n = 0 THEN x' = 0 ELSE Loop(n - 1)\n\
            Init == x = 0\nNext == Loop(1)";
        let m = model(src);
        let store = tlx_layout::store::StoreRef::new(usize::MAX);
        assert_eq!(closed(&m, vec![Shape::Ref(store.clone())]), Ok(()));
        assert_eq!(closed(&m, vec![Shape::Dyn]), Ok(()));
        assert!(closed(&m, vec![int(0, 0)]).is_err());
    }

    #[test]
    fn compose_does_not_leak_pre_state_refinements_into_second_action() {
        // `x < 2` holds on `s0`, not on the intermediate state produced by
        // `x' = 5`, so `y' = x` in the second operand can read 5.
        let src = "EXTENDS Naturals\nVARIABLES x, y\n\
            Init == x = 0 /\\ y = 0\n\
            Next == x < 2 /\\ ((x' = 5 /\\ y' = y) \\cdot (x' = x /\\ y' = x))";
        let m = model(src);
        assert!(closed(&m, vec![int(0, 5), int(0, 1)]).is_err());
        assert_eq!(closed(&m, vec![int(0, 5), int(0, 5)]), Ok(()));
    }

    #[test]
    fn dyn_membership_guard_does_not_assume_compound_representation() {
        // `1..2 \in {{1, 2}}` is true under TLA+ equality even though `1..2`
        // is an interval value that misses a fixed `Set` slot.
        let src = "EXTENDS Naturals\nVARIABLES s, y\n\
            Init == s = 1..2 /\\ y = {1, 2}\n\
            Next == s' = s /\\ y' = IF s \\in {{1, 2}} THEN s ELSE {1, 2}";
        let m = model(src);
        let set_slot = Shape::Set { elem: Box::new(int(1, 2)), max_card: 2 };
        assert!(closed(&m, vec![Shape::Dyn, set_slot]).is_err());
    }

    #[test]
    fn overridden_comparison_guard_does_not_narrow_branch() {
        // `CONSTANT < <- AlwaysLT` makes `x < 1` true even when `x = 12`, so
        // `refine_guard` must not narrow `x < 1` to `Never`.
        let src = tlx_testkit::module(
            "Closed",
            "EXTENDS Naturals\nVARIABLES x, y\n\
             AlwaysLT(u, v) == TRUE\n\
             Init == x = 12 /\\ y = 0\n\
             Next == x' = x /\\ y' = IF x < 1 THEN x ELSE 0",
        );
        let m = spec::load(&src, "INIT Init\nNEXT Next\nCONSTANT < <- AlwaysLT\nCHECK_DEADLOCK FALSE\n");
        assert!(closed(&m, vec![int(12, 12), int(0, 0)]).is_err());
    }

    #[test]
    fn constant_substitution_honors_configured_def_value() {
        // `K <- F` and `F = 100` overrides the source body `F == "ok"`, so `K`
        // evaluates to 100 and must not be certified for a string slot.
        let src = tlx_testkit::module(
            "Closed",
            "EXTENDS Integers\nCONSTANT K\nVARIABLE x\n\
             F == \"ok\"\n\
             Init == x = \"ok\"\n\
             Next == x' = K",
        );
        let m = spec::load(&src, "INIT Init\nNEXT Next\nCONSTANT K <- F\nCONSTANT F = 100\nCHECK_DEADLOCK FALSE\n");
        let ok = Shape::Atom(Arc::from([Value::Str(Sym::new("ok"))]));
        assert!(closed(&m, vec![ok.clone()]).is_err());
        assert_eq!(closed(&m, vec![Shape::Union(Arc::from([int(100, 100), ok]))]), Ok(()));
    }

    #[test]
    fn huge_lazy_domain_does_not_materialize_or_exhaust_budget() {
        // `SUBSET (1..19)` (524,288 subsets), `[1..250000 -> {0}]` (singleton
        // outer set with a 250,000-entry function element), and
        // `[pool: {SUBSET (1..19)}]` (singleton outer set with a nested lazy
        // powerset) must all be rejected before normalization.
        for def in ["Huge == SUBSET (1..19)", "Huge == [1..250000 -> {0}]", "Huge == [pool: {SUBSET (1..19)}]"] {
            let src = format!(
                "EXTENDS Naturals\n{def}\nVARIABLES b, x\n\
                 Init == b = FALSE /\\ x = 0\n\
                 Next == b' = b /\\ x' = IF b THEN [i \\in Huge |-> b] ELSE x"
            );
            let m = model(&src);
            let err = closed(&m, vec![Shape::Bool, int(0, 0)]).unwrap_err();
            assert!(!err.contains("budget is exhausted"), "{def}: unexpected budget exhaustion: {err}");
        }
        // Direct admission check: a singleton lazy function set over a huge
        // domain is rejected before normalization in both admission and shape
        // inspection.
        let wide =
            Value::LazySet(Arc::new(tlx_value::LazySet::FcnSet(Value::Interval(1, 250_000), Value::Set(Arc::from([Value::Int(0)])))));
        assert!(!value_within_domain_bound(&wide));
        assert!(matches!(shape_of_value(&wide), VShape::Shape(Shape::Dyn)));
        let nested = Value::LazySet(Arc::new(tlx_value::LazySet::RecordSet(vec![(
            Sym::new("pool"),
            Value::Set(Arc::from([Value::LazySet(Arc::new(tlx_value::LazySet::Subset(Value::Interval(1, 19))))])),
        )])));
        assert!(!value_within_domain_bound(&nested));
        assert!(matches!(shape_of_value(&nested), VShape::Shape(Shape::Dyn)));
    }
}
