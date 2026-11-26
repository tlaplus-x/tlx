//! Abstract environments, guard-derived path narrowing, and call parameter
//! binding for the closure analysis.

use tlx_eval::env::{Binding, Env, OpVal};
use tlx_layout::Shape;
use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{DefId, DefKind, Expr, ExprKind as H, LocalId, OpRef};
use tlx_value::Value;

use super::expr::shape_of_value;
use super::{Abs, Analyzer, Refine, VShape, DEPTH};

impl<'a> Analyzer<'a> {
    pub(super) fn push_scope(&mut self, entries: Vec<(LocalId, Abs)>) {
        self.scopes.push(entries);
    }

    pub(super) fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    pub(super) fn lookup(&self, l: LocalId) -> Option<&Abs> {
        self.scopes.iter().rev().find_map(|s| s.iter().rev().find(|(id, _)| *id == l).map(|(_, b)| b))
    }

    /// The shape of a local bound to a value (a call-by-name argument is
    /// evaluated).
    pub(super) fn local_value(&mut self, l: LocalId, env: &Env) -> VShape {
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
    pub(super) fn refined_value(&self, v: usize, primed: bool) -> Shape {
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
    pub(super) fn refine_guard(&mut self, guard: &Expr, env: &Env, truth: bool) {
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
    pub(super) fn op_val(&mut self, arg: &Expr, env: &Env) -> Option<OpVal> {
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
    pub(super) fn bind_params(&mut self, def: DefId, args: &[Expr], env: &Env) -> Result<Env, String> {
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
}

// ----------------------------------------------------------------------
// path-narrowing helpers

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
