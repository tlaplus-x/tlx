//! Value-position abstract evaluation: the HIR expression transfer functions of
//! the analysis, its exact-domain inspection, and the shape/bound helpers they
//! build on.

use std::sync::Arc;

use tlx_eval::env::{Binding, Env, OpVal};
use tlx_eval::eval::Ctx;
use tlx_layout::shape::{join_all, set_shape};
use tlx_layout::{FcnWitness, Shape};
use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{Bound, BoundVars, ConstId, DefId, DefKind, ExceptKey, Expr, ExprKind as H, LocalId, OpRef};
use tlx_value::{Sym, Value};

use super::{Abs, Analyzer, VShape, DEPTH, MAX_EXACT_DOMAIN};

impl<'a> Analyzer<'a> {
    /// The values `e` can take (an over-approximation; `Dyn` when unknown).
    pub(super) fn value(&mut self, e: &Expr, env: &Env) -> VShape {
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
            // Synthesized only by a certified normalization, never by a program
            // the compiled tier lowers.
            H::CfgLiteral(_) => VShape::Shape(Shape::Dyn),
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
pub(super) fn value_within_domain_bound(v: &Value) -> bool {
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
pub(super) fn shape_of_value(v: &Value) -> VShape {
    match v {
        Value::Interval(lo, hi) => VShape::Interval { lo: *lo, hi: *hi },
        _ if value_within_domain_bound(v) => VShape::Shape(Shape::of(v)),
        _ => VShape::Shape(Shape::Dyn),
    }
}

pub(super) fn tuple_parts(s: &Shape, n: usize) -> Vec<Shape> {
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
