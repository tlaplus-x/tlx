//! Expression evaluation (value semantics).

mod context;

#[cfg(test)]
mod tests;

use std::sync::Arc;

use tlx_sema::hir::*;
use tlx_value::{ops, LazyFcn, Sym, Value};

use crate::apply::{apply_tail, field_tail, Cow};
use crate::env::{Binding, Env, LetCell, LetFrame, OpVal, Thunk};
use crate::error::{EResult, EvalError};
use crate::except::{self, Unchanged};
use crate::interp::local::{self, Slot};
use crate::interp::{ConstVal, Interp};
use crate::lazy::{LambdaFcn, RecursiveFcn};
use context::count_def_eval;
pub use context::{Ctx, DefCache, MemoSource, StateMemo};

/// Pseudo-local holding the value of `@` inside an EXCEPT update.
pub(crate) const AT: LocalId = LocalId(u32::MAX);

/// TLC passes operator arguments unevaluated (LazyValue). This matters only
/// when the body can observe the next state (`v'`, `UNCHANGED v`, ENABLED):
/// arguments of such (action-level) definitions are passed by name, in
/// action contexts and also in state contexts, where ENABLED primes them
/// (`Foo(A) == ENABLED (A' = 1)` in an invariant, `Foo(y)`).
fn by_name(cx: &Ctx) -> bool {
    !cx.init
}

/// The domain of a function whose arguments range over `sets`: a single set,
/// or their product.
pub(crate) fn fn_domain(mut sets: Vec<Value>) -> EResult<Value> {
    if sets.len() == 1 {
        Ok(sets.pop().unwrap())
    } else {
        Ok(ops::product(sets)?)
    }
}

/// The elements of a finite set (in its enumeration order), sharing the
/// storage of an enumerated set.
pub(crate) fn elems(set: &Value) -> EResult<Arc<[Value]>> {
    Ok(match set {
        Value::Set(es) => es.clone(),
        _ => ops::enumerate(set)?.into(),
    })
}

/// The elements of a finite set in its enumeration order, without
/// materializing intervals or copying enumerated sets.
#[derive(Clone)]
pub(crate) enum Elems {
    Shared(Arc<[Value]>, usize),
    Interval(i64, i64),
}

impl Elems {
    pub(crate) fn of(set: &Value) -> EResult<Elems> {
        Ok(match set {
            Value::Interval(lo, _) => Elems::Interval(*lo, *lo + ops::cardinality(set)?),
            _ => Elems::Shared(elems(set)?, 0),
        })
    }

    #[inline]
    pub(crate) fn len(&self) -> usize {
        match self {
            Elems::Shared(es, start) => es.len().saturating_sub(*start),
            Elems::Interval(lo, end) => (*end - *lo).max(0) as usize,
        }
    }

    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub(crate) fn get(&self, i: usize) -> Value {
        match self {
            Elems::Shared(es, start) => es[*start + i].clone(),
            Elems::Interval(lo, _) => Value::Int(*lo + i as i64),
        }
    }
}

/// The elements of a bound variable's domain (`bound_elems`): materialized, or
/// — for a `SUBSET S`/`kSubset(k, S)` — a value enumerated on the fly by the
/// caller (`ops::for_each_enumerated`).
///
/// Which domains TLC streams and which it materializes (and so which are
/// limited by `-maxSetSize`) is decided by `ops::bound_kind`, the same
/// decision the compiled tier's boxed-domain iteration uses. The streamed
/// order is the normalized order
/// (`tlx-value/tests/ops.rs::streaming_order_is_the_normalized_order`), and it
/// can stop early: a body that finds its witness before the end never needs
/// the whole `SUBSET S`.
#[derive(Clone)]
pub(crate) enum BoundElems {
    Elems(Elems),
    /// A `SUBSET S`/`kSubset(k, S)` and the set itself. The set is enumerated
    /// element by element instead of being held in memory.
    Stream(Value),
}

impl Iterator for Elems {
    type Item = Value;

    #[inline]
    fn next(&mut self) -> Option<Value> {
        match self {
            Elems::Shared(es, i) => {
                let x = es.get(*i)?.clone();
                *i += 1;
                Some(x)
            }
            Elems::Interval(next, end) => {
                if *next >= *end {
                    return None;
                }
                *next += 1;
                Some(Value::Int(*next - 1))
            }
        }
    }
}

/// `v`, with a lazy function built (for code matching on representations).
pub(crate) fn force_lazy_fcn(v: Value) -> EResult<Value> {
    match &v {
        Value::LazyFcn(_) if ops::is_finite_set(&ops::domain(&v)?)? => Ok(v.normalize()?),
        _ => Ok(v),
    }
}

/// `force_lazy_fcn` for a sequence argument: a function over an enumerated
/// domain `1..n` is the equal `Tuple` (TLC's `toTuple`; see `Value::Fcn`).
pub(crate) fn force_seq(v: Value) -> EResult<Value> {
    let v = force_lazy_fcn(v)?;
    Ok(match v.fcn_canonical() {
        Some(t @ Value::Tuple(_)) => t,
        _ => v,
    })
}

/// Whether `a` and `b` are the same value representation (a compound value
/// shared by reference with the same lookup witness, or an equal scalar):
/// then `a` is as normal as `b`
/// and has its fingerprint.
#[inline]
pub(crate) fn same_rep(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Set(x), Value::Set(y)) | (Value::Tuple(x), Value::Tuple(y)) => Arc::ptr_eq(x, y),
        (Value::Record(x), Value::Record(y)) => Arc::ptr_eq(x, y),
        (Value::Fcn(x, xd), Value::Fcn(y, yd)) => xd == yd && Arc::ptr_eq(x, y),
        (Value::Bool(x), Value::Bool(y)) => x == y,
        (Value::Int(x), Value::Int(y)) => x == y,
        (Value::Str(x), Value::Str(y)) | (Value::ModelValue(x), Value::ModelValue(y)) => x == y,
        (Value::Interval(a, b), Value::Interval(c, d)) => a == c && b == d,
        _ => false,
    }
}

pub(crate) fn as_bool(v: &Value, span: Span) -> EResult<bool> {
    match v {
        Value::Bool(b) => Ok(*b),
        _ => Err(EvalError::at(format!("A non-boolean expression ({v}) was used as a boolean."), span)),
    }
}

impl Interp {
    pub fn var_name(&self, v: VarId) -> &str {
        match self.prog.vars.get(v.idx()) {
            Some(info) => &info.name,
            None => &self.prog.inst_vars[v.idx() - self.prog.vars.len()].name,
        }
    }

    /// The variable an ENABLED gives `ExprKind::InstVar` `slot` in its
    /// partial next state: the slots follow the state variables.
    pub(crate) fn inst_var(&self, slot: u32) -> VarId {
        VarId(self.prog.vars.len() as u32 + slot)
    }

    pub(crate) fn read_var(&self, v: VarId, cx: &Ctx, span: Span) -> EResult<Value> {
        if cx.primed || cx.init {
            if let Some(s1) = cx.s1 {
                if let Some(x) = &s1[v.idx()] {
                    return Ok(x.clone());
                }
            }
            let name = self.var_name(v);
            let shown = if cx.primed && !cx.init { format!("{name}'") } else { name.to_string() };
            return Err(EvalError::at(format!("In evaluation, the identifier {shown} is either undefined or not an operator."), span));
        }
        match cx.s0 {
            Some(s0) => Ok(s0[v.idx()].clone()),
            None => Err(EvalError::at(format!("Attempted to evaluate variable {} in a constant context.", self.var_name(v)), span)),
        }
    }

    pub(crate) fn const_value(self: &Arc<Self>, c: ConstId, span: Span) -> EResult<Value> {
        match &self.consts[c.idx()] {
            Some(ConstVal::Value(v)) => local::get(self.uid, Slot::Const(c.idx()), || Ok(v.clone())),
            Some(ConstVal::Def(d)) => self.call_def(*d, &Env::default(), &Ctx::NONE, span),
            Some(ConstVal::Op(_) | ConstVal::Table(_)) => Err(EvalError::at("operator constant used as a value", span)),
            None => Err(EvalError::at(
                format!("The constant parameter {} is not assigned a value by the configuration file.", self.prog.consts[c.idx()].name),
                span,
            )),
        }
    }

    /// The value of `e`.
    pub fn eval(self: &Arc<Self>, e: &Expr, env: &Env, cx: &Ctx) -> EResult<Value> {
        match self.code_of(e) {
            Some(c) => self.exec(c, env, cx),
            None => self.eval_tree(e, env, cx),
        }
    }

    /// `eval` by walking the expression (its subexpressions are evaluated by
    /// `eval`).
    pub(crate) fn eval_tree(self: &Arc<Self>, e: &Expr, env: &Env, cx: &Ctx) -> EResult<Value> {
        self.eval_inner(e, env, cx).map_err(|err| err.with_span(e.span))
    }

    pub fn eval_bool(self: &Arc<Self>, e: &Expr, env: &Env, cx: &Ctx) -> EResult<bool> {
        if let Some(c) = self.code_of(e) {
            return self.exec_bool(c, env, cx);
        }
        let v = self.eval_tree(e, env, cx)?;
        as_bool(&v, e.span)
    }

    /// `eval`, borrowing the value where it is stored when `e` reads a
    /// variable, a bound local, a constant or a part of one of these
    /// (`f[x]`, `r.field`); the same value and errors.
    pub(crate) fn eval_cow<'a>(self: &'a Arc<Self>, e: &'a Expr, env: &'a Env, cx: &Ctx<'a>) -> EResult<Cow<'a>> {
        if let Some(c) = self.code_of(e) {
            return self.exec_cow(c, env, cx);
        }
        match &*e.kind {
            ExprKind::Var(v) => {
                let r = if cx.primed || cx.init { cx.s1.and_then(|s1| s1[v.idx()].as_ref()) } else { cx.s0.map(|s0| &s0[v.idx()]) };
                match r {
                    Some(x) => Ok(Cow::Ref(x)),
                    None => self.eval(e, env, cx).map(Cow::Own),
                }
            }
            ExprKind::Local(l) => match env.lookup(*l) {
                Some(Binding::Val(v)) => Ok(Cow::Ref(v)),
                _ => self.eval(e, env, cx).map(Cow::Own),
            },
            ExprKind::Const(c) => match &self.consts[c.idx()] {
                Some(ConstVal::Value(v)) => Ok(Cow::Ref(v)),
                _ => self.eval(e, env, cx).map(Cow::Own),
            },
            ExprKind::Apply { op: OpRef::Def(d), args } if args.is_empty() => match self.const_def_ref(*d) {
                Some(v) => Ok(Cow::Ref(v)),
                None => self.eval(e, env, cx).map(Cow::Own),
            },
            ExprKind::FnApp { func, args } => self.fn_app_cow(func, args, env, cx).map_err(|err| err.with_span(e.span)),
            ExprKind::Field { record, field } => self.field_cow(record, field, env, cx).map_err(|err| err.with_span(e.span)),
            _ => self.eval(e, env, cx).map(Cow::Own),
        }
    }

    /// The value of 0-ary definition `d` if it is known without evaluating
    /// anything: assigned by the cfg, or a constant definition already
    /// computed (what `call_def` returns).
    pub(crate) fn const_def_ref(&self, d: DefId) -> Option<&Value> {
        if self.is_recursive(d) {
            return None;
        }
        if let Some(v) = self.def_value.get(&d) {
            return Some(v);
        }
        let d = self.redirect_def(d);
        if let Some(v) = self.def_value.get(&d) {
            return Some(v);
        }
        if self.prog.defs[d.idx()].builtin.is_some() || !self.def_const[d.idx()] {
            return None;
        }
        match self.const_cache[d.idx()].get() {
            Some(Ok(v)) => Some(v),
            _ => None,
        }
    }

    /// `func[args]` (see `eval_cow`).
    fn fn_app_cow<'a>(self: &'a Arc<Self>, func: &'a Expr, args: &'a [Expr], env: &'a Env, cx: &Ctx<'a>) -> EResult<Cow<'a>> {
        // TLC evaluates the function with KeepLazy (Tool.java
        // OPCODE_fa): a function constructor there is not built, so
        // only the applied point is evaluated.
        let f = self.eval_cow(func, env, &cx.lazy(true))?;
        let arg = self.eval_args(args, env, cx)?;
        apply_tail(f, &arg, cx)
    }

    /// `record.field` (see `eval_cow`).
    fn field_cow<'a>(self: &'a Arc<Self>, record: &'a Expr, field: &Arc<str>, env: &'a Env, cx: &Ctx<'a>) -> EResult<Cow<'a>> {
        let r = self.eval_cow(record, env, cx)?;
        let field = self.syms.get(field);
        field_tail(r, field)
    }

    fn eval_inner(self: &Arc<Self>, e: &Expr, env: &Env, cx: &Ctx) -> EResult<Value> {
        let span = e.span;
        Ok(match &*e.kind {
            ExprKind::Num(n) => {
                if *n > i32::MAX as i128 {
                    return Err(EvalError::of_kind(
                        tlx_runtime::ErrorKind::IntegerTooBig,
                        format!("TLC can't handle a number this big.\n{n}"),
                    ));
                }
                Value::Int(*n as i64)
            }
            ExprKind::Decimal(d) => return Err(EvalError::new(format!("real number literal {d} is not supported"))),
            ExprKind::Str(s) => Value::Str(self.syms.get(s)),
            ExprKind::Bool(b) => Value::Bool(*b),
            ExprKind::Var(v) => self.read_var(*v, cx, span)?,
            // Primed in an ENABLED that quantifies over it: its own value
            // in the partial next state (see `Interp::enabled`).
            ExprKind::InstVar { slot, subst } => match cx.s1 {
                Some(s1) if cx.primed && !cx.init && self.prog.vars.len() + (*slot as usize) < s1.len() => {
                    self.read_var(self.inst_var(*slot), cx, span)?
                }
                _ => self.eval(subst, env, cx)?,
            },
            ExprKind::Const(c) => self.const_value(*c, span)?,
            ExprKind::Local(l) => self.read_local(*l, env, cx)?,
            ExprKind::At => self.read_local(AT, env, cx)?,
            ExprKind::Apply { op, args } => self.apply(*op, args, env, cx, span)?,
            ExprKind::Builtin { op, args } => self.builtin(*op, args, env, cx, span)?,
            ExprKind::OpArg(_) | ExprKind::Lambda { .. } => return Err(EvalError::new("an operator was used where a value is expected")),
            ExprKind::And(es) => {
                for c in es {
                    if !self.eval_bool(c, env, cx)? {
                        return Ok(Value::FALSE);
                    }
                }
                Value::TRUE
            }
            ExprKind::Or(es) => {
                for c in es {
                    if self.eval_bool(c, env, cx)? {
                        return Ok(Value::TRUE);
                    }
                }
                Value::FALSE
            }
            ExprKind::Quant { kind, bounds, body } => {
                let want = *kind == QuantKind::Exists;
                let mut found = !want;
                self.for_each_binding(bounds, env, cx, &mut |env2| {
                    if self.eval_bool(body, env2, cx)? == want {
                        found = want;
                        return Ok(false);
                    }
                    Ok(true)
                })?;
                Value::Bool(found)
            }
            ExprKind::QuantUnbounded { .. } => return Err(EvalError::new("TLC cannot handle an unbounded quantifier.")),
            ExprKind::TemporalQuant { .. } => return Err(EvalError::new("temporal quantifiers are not supported")),
            ExprKind::Choose { vars, set, body } => {
                let Some(set) = set else {
                    return Err(EvalError::new("TLC attempted to evaluate an unbounded CHOOSE."));
                };
                let s = self.eval(set, env, cx)?;
                let always_true = matches!(&*body.kind, ExprKind::Bool(true)) && matches!(vars, BoundVars::Many(ls) if ls.len() == 1);
                self.choose_in(vars, &s, env, always_true, &mut |env2| self.eval_bool(body, env2, cx))?
            }
            ExprKind::If { cond, then, els } => {
                if self.eval_bool(cond, env, cx)? {
                    self.eval(then, env, cx)?
                } else {
                    self.eval(els, env, cx)?
                }
            }
            ExprKind::Case { arms, other } => {
                for (g, v) in arms {
                    if self.eval_bool(g, env, cx)? {
                        return self.eval(v, env, cx);
                    }
                }
                match other {
                    Some(o) => self.eval(o, env, cx)?,
                    None => return Err(EvalError::new("Attempted to evaluate a CASE with no conditions true.")),
                }
            }
            ExprKind::Let { defs, body } => {
                let (env2, _frame) = self.let_env(defs, env);
                self.eval(body, &env2, cx)?
            }
            ExprKind::SetEnum(es) => {
                let vs = es.iter().map(|x| self.eval(x, env, cx)).collect::<EResult<Vec<_>>>()?;
                Value::set_literal(vs)?
            }
            ExprKind::SetFilter { bound, pred } => self.set_filter(bound, pred, env, cx)?,
            ExprKind::SetMap { expr, bounds } => {
                let mut out = Vec::new();
                self.for_each_binding(bounds, env, cx, &mut |env2| {
                    tlx_value::limits::push(&mut out, self.eval(expr, env2, cx)?)?;
                    Ok(true)
                })?;
                Value::set_enum(out)?
            }
            ExprKind::Tuple(es) => Value::tuple(es.iter().map(|x| self.eval(x, env, cx)).collect::<EResult<_>>()?),
            ExprKind::FnConstruct { bounds, body } => self.fn_construct(bounds, body, env, cx)?,
            ExprKind::FnApp { func, args } => self.fn_app_cow(func, args, env, cx)?.into_owned(),
            ExprKind::FnSet { domain, range } => {
                let d = self.eval(domain, env, cx)?;
                let r = self.eval(range, env, cx)?;
                ops::fcn_set(&d, &r)?
            }
            ExprKind::Record(fs) => Value::record(self.eval_fields(fs, env, cx)?),
            ExprKind::RecordSet(fs) => ops::record_set(self.eval_fields(fs, env, cx)?)?,
            ExprKind::Field { record, field } => self.field_cow(record, field, env, cx)?.into_owned(),
            ExprKind::Except { base, updates } => self.except(base, updates, env, cx)?,
            ExprKind::BoxAction { action, sub } => {
                if self.eval_bool(action, env, cx)? {
                    Value::TRUE
                } else {
                    Value::Bool(self.unchanged(sub, env, cx)?)
                }
            }
            ExprKind::AngleAction { action, sub } => Value::Bool(self.eval_bool(action, env, cx)? && !self.unchanged(sub, env, cx)?),
            ExprKind::Fairness { .. } => return Err(EvalError::new("fairness formulas cannot be evaluated as values")),
        })
    }

    /// `CHOOSE vars \in s : pred` in TLC's normalized order: streams when
    /// `ops::streams_normalized(s)` holds (`SUBSET S` / `kSubset(k, S)`), and
    /// materializes via `ops::enumerate_normalized(s)` (or borrows an already
    /// enumerated `Value::Set`) for all other sets.
    pub(crate) fn choose_in(
        self: &Arc<Self>,
        vars: &BoundVars,
        s: &Value,
        env: &Env,
        always_true: bool,
        pred: &mut dyn FnMut(&Env) -> EResult<bool>,
    ) -> EResult<Value> {
        if ops::streams_normalized(s) {
            let mut found = None;
            let mut err = None;
            ops::for_each_enumerated(s, &mut |x| {
                // (`CHOOSE x \in S : TRUE`: binding one variable cannot fail;
                // runs only after `for_each_enumerated` validates `s` and
                // yields an element.)
                if always_true {
                    found = Some(x);
                    return Ok(false);
                }
                let r = self.bind_bound_vars(vars, x.clone(), env).and_then(|env2| pred(&env2));
                match r {
                    Ok(true) => {
                        found = Some(x);
                        Ok(false)
                    }
                    Ok(false) => Ok(true),
                    Err(e) => {
                        err = Some(e);
                        Ok(false)
                    }
                }
            })?;
            if let Some(e) = err {
                return Err(e);
            }
            if let Some(x) = found {
                return Ok(x);
            }
        } else {
            // (An enumerated set is normalized: its elements in order.)
            let owned;
            let elems: &[Value] = match s {
                Value::Set(es) => es,
                _ => {
                    owned = ops::enumerate_normalized(s)?;
                    &owned
                }
            };
            for x in elems {
                if always_true {
                    return Ok(x.clone());
                }
                let env2 = self.bind_bound_vars(vars, x.clone(), env)?;
                if pred(&env2)? {
                    return Ok(x.clone());
                }
            }
        }
        Err(EvalError::new("Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P."))
    }

    /// The fields of a record constructor or record set, evaluated in order.
    fn eval_fields(self: &Arc<Self>, fs: &[(Arc<str>, Expr)], env: &Env, cx: &Ctx) -> EResult<Vec<(Sym, Value)>> {
        fs.iter().map(|(n, x)| Ok((self.syms.get(n), self.eval(x, env, cx)?))).collect()
    }

    /// Evaluate the tuple of `es` (or the single value when there is one).
    pub(crate) fn eval_args(self: &Arc<Self>, es: &[Expr], env: &Env, cx: &Ctx) -> EResult<Value> {
        if es.len() == 1 {
            self.eval(&es[0], env, cx)
        } else {
            Ok(Value::tuple(es.iter().map(|x| self.eval(x, env, cx)).collect::<EResult<_>>()?))
        }
    }

    /// `[base EXCEPT !path1 = e1, ...]` (`except::except`).
    fn except(self: &Arc<Self>, base: &Expr, updates: &[(Vec<ExceptKey>, Expr)], env: &Env, cx: &Ctx) -> EResult<Value> {
        let base = self.eval_cow(base, env, cx)?;
        except::except(
            base,
            updates,
            env,
            Unchanged::Rebuild,
            |(keys, _)| {
                keys.iter()
                    .map(|k| match k {
                        ExceptKey::Field(f) => Ok(Value::Str(self.syms.get(f))),
                        ExceptKey::Index(ix) => self.eval_args(ix, env, cx),
                    })
                    .collect()
            },
            |(_, val), env| self.eval(val, env, cx),
        )
    }

    pub(crate) fn read_local(self: &Arc<Self>, l: LocalId, env: &Env, cx: &Ctx) -> EResult<Value> {
        match env.lookup(l) {
            Some(Binding::Val(v)) => Ok(v.clone()),
            // A by-name argument with one value per context: its first
            // unprimed evaluation serves the later ones. Under KeepLazy only
            // a part of it may be needed (e.g. the applied points of a
            // function constructor): evaluated lazily, not kept.
            Some(Binding::Thunk(t)) if !cx.primed && t.memo.as_ref().is_some_and(|m| m.get().is_some() || !cx.keep_lazy) => {
                let memo = t.memo.as_ref().unwrap();
                if let Some(v) = memo.get() {
                    return Ok(v.clone());
                }
                let v = self.eval(&t.expr, &t.env, cx)?;
                Ok(memo.get_or_init(|| v).clone())
            }
            Some(b @ (Binding::Thunk(_) | Binding::Name(..))) => {
                let (e, env) = b.by_name(&self.prog).unwrap();
                self.eval(e, env, cx)
            }
            Some(Binding::Op(_)) => Err(EvalError::new("an operator argument was used as a value")),
            Some(Binding::LetCache(_)) => Err(EvalError::new("internal error: a LET cache was read as a local")),
            None => {
                let name = if l == AT { "@".into() } else { self.prog.locals[l.idx()].name.to_string() };
                Err(EvalError::new(format!("internal error: unbound local `{name}`")))
            }
        }
    }

    /// `e' = e`
    pub(crate) fn unchanged(self: &Arc<Self>, e: &Expr, env: &Env, cx: &Ctx) -> EResult<bool> {
        // `UNCHANGED <<x, y, ...>>` of variables with values in both
        // states: the tuples compare element by element (`eq_seq`), so the
        // variables are compared in order without building the tuples.
        if let (ExprKind::Tuple(es), Some(s0), Some(s1), false, false) = (&*e.kind, cx.s0, cx.s1, cx.primed, cx.init) {
            let var = |x: &Expr| match &*x.kind {
                ExprKind::Var(v) if v.idx() < s0.len() && s1.get(v.idx()).is_some_and(Option::is_some) => Some(*v),
                _ => None,
            };
            if es.iter().all(|x| var(x).is_some()) {
                for x in es {
                    let v = var(x).unwrap().idx();
                    if !tlx_value::order::eq_tlc(&s0[v], s1[v].as_ref().unwrap())? {
                        return Ok(false);
                    }
                }
                return Ok(true);
            }
        }
        let now = self.eval_cow(e, env, cx)?;
        let next = self.eval_cow(e, env, &cx.primed())?;
        Ok(tlx_value::order::eq_tlc(&now, &next)?)
    }

    // ------------------------------------------------------------------
    // bound variables

    /// Enumerate the bindings of `bounds` (first variable varies fastest, like
    /// TLC's ContextEnumerator). `f` returns false to stop.
    pub(crate) fn for_each_binding(
        self: &Arc<Self>,
        bounds: &[Bound],
        env: &Env,
        cx: &Ctx,
        f: &mut dyn FnMut(&Env) -> EResult<bool>,
    ) -> EResult<bool> {
        // The common case: one variable over one set. The binding is
        // updated in place unless `f` kept the environment.
        if let [Bound { vars: BoundVars::Many(ls), set }] = bounds {
            if let [l] = ls.as_slice() {
                let mut elems = match self.bound_elems(set, env, cx)? {
                    BoundElems::Elems(elems) => elems,
                    // The domain cannot be materialized: stream it
                    // (`for_each_enumerated`, TLC's `Enumerable.elements()`)
                    // and stop as soon as `f` does.
                    BoundElems::Stream(v) => {
                        let mut err = None;
                        let done = ops::for_each_enumerated(&v, &mut |x| match f(&env.bind_val(*l, x)) {
                            Ok(go_on) => Ok(go_on),
                            Err(e) => {
                                err = Some(e);
                                Ok(false)
                            }
                        })?;
                        return match err {
                            Some(e) => Err(e),
                            None => Ok(done),
                        };
                    }
                };
                let Some(first) = elems.next() else {
                    return Ok(true);
                };
                let mut env2 = env.bind_val(*l, first);
                loop {
                    if !f(&env2)? {
                        return Ok(false);
                    }
                    let Some(x) = elems.next() else {
                        return Ok(true);
                    };
                    if let Err(x) = env2.rebind_head(x) {
                        env2 = env.bind_val(*l, x);
                    }
                }
            }
        }
        // Flatten `x, y \in S` into one (var, domain) slot per variable.
        // Validate every domain in left-to-right source order and track
        // emptiness before iterating the product, matching TLC's Tool.contexts.
        let mut slots: Vec<(&BoundVars, Option<LocalId>, BoundElems)> = Vec::new();
        let mut any_empty = false;
        let mut has_stream = false;
        for b in bounds {
            let elems = self.bound_elems(&b.set, env, cx)?;
            match &elems {
                BoundElems::Elems(e) => any_empty |= e.is_empty(),
                BoundElems::Stream(v) => {
                    has_stream = true;
                    // Probing the first element performs full Subset/KSubset
                    // base validation and detects empty kSubset(k, S) in
                    // O(|base|).
                    any_empty |= ops::for_each_enumerated(v, &mut |_| Ok(false))?;
                }
            }
            match &b.vars {
                BoundVars::Many(ls) => {
                    for l in ls {
                        slots.push((&b.vars, Some(*l), elems.clone()));
                    }
                }
                BoundVars::Tuple(_) => slots.push((&b.vars, None, elems)),
            }
        }
        if any_empty {
            return Ok(true);
        }
        if has_stream {
            return self.for_each_stream_slot(&slots, env, f);
        }
        let mut idx = vec![0usize; slots.len()];
        loop {
            let mut env2 = env.clone();
            for (k, (vars, l, elems)) in slots.iter().enumerate() {
                let BoundElems::Elems(e) = elems else { unreachable!() };
                let x = e.get(idx[k]);
                env2 = match l {
                    Some(l) => env2.bind_val(*l, x),
                    None => self.bind_bound_vars(vars, x, &env2)?,
                };
            }
            if !f(&env2)? {
                return Ok(false);
            }
            // Odometer, first slot fastest.
            let mut k = 0;
            loop {
                if k == slots.len() {
                    return Ok(true);
                }
                let BoundElems::Elems(e) = &slots[k].2 else { unreachable!() };
                idx[k] += 1;
                if idx[k] < e.len() {
                    break;
                }
                idx[k] = 0;
                k += 1;
            }
        }
    }

    /// Collect all bindings of `bounds` in a constant context (`Ctx::NONE`) for
    /// action splitting and liveness leaf matching. When any bound is
    /// `BoundElems::Stream` (`SUBSET S` / `kSubset(k, S)`), refuses to expand
    /// if any streamed cardinality overflows or the product exceeds
    /// `-maxSetSize` (`tlx_value::limits::growth_limit()`), returning `None`
    /// so the caller preserves the unsplit action without OOMing.
    pub(crate) fn collect_split_bindings(self: &Arc<Self>, bounds: &[Bound], env: &Env) -> Option<Vec<Env>> {
        let limit = usize::try_from(tlx_value::limits::growth_limit()).unwrap_or(usize::MAX);
        let mut has_stream = false;
        let mut total: usize = 1;
        for b in bounds {
            let card = match self.bound_elems(&b.set, env, &Ctx::NONE).ok()? {
                BoundElems::Elems(e) => e.len(),
                BoundElems::Stream(v) => {
                    has_stream = true;
                    usize::try_from(ops::cardinality(&v).ok()?).ok()?
                }
            };
            let slots = match &b.vars {
                BoundVars::Many(ls) => ls.len(),
                BoundVars::Tuple(_) => 1,
            };
            for _ in 0..slots {
                total = total.checked_mul(card)?;
            }
        }
        if has_stream && total > limit {
            return None;
        }
        let mut envs = Vec::with_capacity(total);
        self.for_each_binding(bounds, env, &Ctx::NONE, &mut |env2| {
            envs.push(env2.clone());
            Ok(true)
        })
        .ok()?;
        Some(envs)
    }

    /// Recursive product traversal when at least one slot is `BoundElems::Stream`.
    /// Descends from the last slot (outermost) down to slot 0 (innermost) so
    /// the first variable varies fastest, matching TLC's `ContextEnumerator`.
    fn for_each_stream_slot(
        self: &Arc<Self>,
        slots: &[(&BoundVars, Option<LocalId>, BoundElems)],
        env: &Env,
        f: &mut dyn FnMut(&Env) -> EResult<bool>,
    ) -> EResult<bool> {
        let Some(((vars, local, elems), rest)) = slots.split_last() else {
            return f(env);
        };
        let mut step = |x: Value| -> EResult<bool> {
            let env2 = match local {
                Some(l) => env.bind_val(*l, x),
                None => self.bind_bound_vars(vars, x, env)?,
            };
            self.for_each_stream_slot(rest, &env2, f)
        };
        match elems {
            BoundElems::Elems(e) => {
                for i in 0..e.len() {
                    if !step(e.get(i))? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            BoundElems::Stream(v) => {
                let mut err = None;
                let done = ops::for_each_enumerated(v, &mut |x| match step(x) {
                    Ok(go_on) => Ok(go_on),
                    Err(e) => {
                        err = Some(e);
                        Ok(false)
                    }
                })?;
                match err {
                    Some(e) => Err(e),
                    None => Ok(done),
                }
            }
        }
    }

    /// Bind a single-variable or tuple binder to `x`.
    pub(crate) fn bind_bound_vars(&self, vars: &BoundVars, x: Value, env: &Env) -> EResult<Env> {
        match vars {
            BoundVars::Many(ls) if ls.len() == 1 => Ok(env.bind_val(ls[0], x)),
            BoundVars::Many(_) => Err(EvalError::new("internal error: multi-variable binder")),
            BoundVars::Tuple(ls) => {
                let x = force_lazy_fcn(x)?;
                let Value::Tuple(elems) = &x else {
                    return Err(EvalError::new(format!("A tuple binder was bound to the non-tuple value {x}")));
                };
                if elems.len() != ls.len() {
                    return Err(EvalError::new(format!("A tuple binder of length {} was bound to {x}", ls.len())));
                }
                Ok(env.bind_all(ls.iter().zip(elems.iter()).map(|(l, v)| (*l, Binding::Val(v.clone())))))
            }
        }
    }

    /// The elements of `set`, the domain of a bound variable, in its
    /// enumeration order. A closed constant domain (`closed_bounds`: e.g.
    /// `\E p \in Seq(Nodes)` with `Seq <- LimitedSeq`, or `SUBSET Nodes`
    /// inside an operator) has the same elements wherever it is evaluated:
    /// each thread enumerates it once (unless it is large). Errors are not
    /// kept.
    pub(crate) fn bound_elems(self: &Arc<Self>, set: &Expr, env: &Env, cx: &Ctx) -> EResult<BoundElems> {
        const MAX_CACHED: usize = 1 << 14;
        let i = if self.closed_bounds.is_empty() { None } else { self.closed_bounds.get(&(Arc::as_ptr(&set.kind) as usize)) };
        let Some(&i) = i else {
            let v = self.eval_cow(set, env, cx)?;
            return self.bound_elems_of(&v, set);
        };
        // KeepLazy may change the representation of the elements.
        let slot = Slot::Bound(2 * i as usize + cx.keep_lazy as usize);
        match local::peek(self.uid, slot) {
            Some(Value::Tuple(es)) => return Ok(BoundElems::Elems(Elems::Shared(es, 0))),
            Some(Value::Interval(lo, hi)) => return Ok(BoundElems::Elems(Elems::of(&Value::Interval(lo, hi))?)),
            _ => {}
        }
        let v = self.eval(set, env, cx)?;
        let elems = self.bound_elems_of(&v, set)?;
        if let BoundElems::Elems(e) = &elems {
            match e {
                Elems::Shared(es, _) if es.len() <= MAX_CACHED => local::put(self.uid, slot, Value::Tuple(es.clone())),
                Elems::Interval(lo, end) => local::put(self.uid, slot, Value::Interval(*lo, *end - 1)),
                _ => {}
            }
        }
        Ok(elems)
    }

    /// `bound_elems` of an evaluated domain, following `ops::bound_kind`:
    /// TLC's normalized enumeration streams a `SUBSET S`/`kSubset(k, S)`,
    /// shares an enumerated set or an interval, and materializes every other
    /// lazy set — where the `-maxSetSize` bound applies, and an overflowing
    /// size is that error rather than a reason to stream.
    fn bound_elems_of(&self, v: &Value, set: &Expr) -> EResult<BoundElems> {
        match ops::bound_kind(v) {
            ops::BoundKind::Stream => Ok(BoundElems::Stream(v.clone())),
            ops::BoundKind::Overflow => Err(self.bound_error(v, set, tlx_value::limits::too_many_elements().into())),
            ops::BoundKind::Share | ops::BoundKind::Materialize => {
                Elems::of(v).map(BoundElems::Elems).map_err(|e| self.bound_error(v, set, e))
            }
        }
    }

    /// The error of a quantifier bound `v` (the value of `set`) that cannot
    /// be enumerated: for a set that is not `Enumerable` (an overridden
    /// value: Nat, Int, Seq(S), STRING, Any), TLC's message from
    /// `getNonEnumerableErrorMsg` (Tool's quantifier enumeration), which
    /// includes the location of the bound and, for Nat, Int and Seq(S), an
    /// explanation; otherwise `e`, the error of the enumeration.
    fn bound_error(&self, v: &Value, set: &Expr, e: EvalError) -> EvalError {
        use tlx_value::LazySet;
        let Value::LazySet(l) = v else { return e };
        let at = self.prog.location(set.span);
        let explain = |what: &str, note: &str| {
            format!(
                "TLC encountered the non-enumerable quantifier bound\n{v}\n{at}\n{what}As a result, TLC cannot evaluate expressions that\n\
                 universally (\\A) or existentially (\\E) quantify over {v}, because this would require checking an\n\
                 infinite number of cases. {note}"
            )
        };
        let msg = match **l {
            LazySet::Nat | LazySet::Int => explain(
                &format!("The set {v} contains infinitely many elements. "),
                &format!("Note that TLC handles set membership like T \\subseteq {v} for any finite set T."),
            ),
            LazySet::Seq(_) => explain(
                "In TLA+, Seq(S) represents the set of all finite sequences whose elements come from the set S. Even when S\n\
                 is a finite set, the number of possible sequences in Seq(S) is unbounded because sequences can have any\n\
                 finite length (e.g., length 0, 1, 2, and so on). ",
                "Note that for a finite set of sequences s, TLC handles s \\subseteq Seq(S).\n\
                 See https://explain.tlapl.us/seq-unenumerable for additional details.",
            ),
            LazySet::StringSet | LazySet::Any => format!("TLC encountered a non-enumerable quantifier bound\n{v}.\n{at}"),
            _ => return e,
        };
        EvalError::at(msg, set.span)
    }

    pub(crate) fn set_filter(self: &Arc<Self>, bound: &Bound, pred: &Expr, env: &Env, cx: &Ctx) -> EResult<Value> {
        let set = self.eval(&bound.set, env, cx)?;
        if set.enum_elements().is_none() && !matches!(set, Value::Interval(..)) {
            return Ok(crate::lazy::lazy_filter(self, &bound.vars, set, pred, env, cx));
        }
        let mut out = Vec::new();
        for x in Elems::of(&set)? {
            let env2 = self.bind_bound_vars(&bound.vars, x.clone(), env)?;
            if self.eval_bool(pred, &env2, cx)? {
                tlx_value::limits::push(&mut out, x)?;
            }
        }
        Ok(Value::set_enum(out)?)
    }

    /// The argument domain of each variable of the function binders `bounds`
    /// (a tuple binder counts as one variable).
    pub(crate) fn bound_sets(self: &Arc<Self>, bounds: &[Bound], env: &Env, cx: &Ctx) -> EResult<Vec<Value>> {
        let mut sets = Vec::new();
        for b in bounds {
            let s = self.eval(&b.set, env, cx)?;
            let n = match &b.vars {
                BoundVars::Many(ls) => ls.len(),
                BoundVars::Tuple(_) => 1,
            };
            sets.extend(std::iter::repeat_n(s, n));
        }
        Ok(sets)
    }

    fn fn_construct(self: &Arc<Self>, bounds: &[Bound], body: &Expr, env: &Env, cx: &Ctx) -> EResult<Value> {
        let sets = self.bound_sets(bounds, env, cx)?;
        // Like TLC (FcnLambdaValue), the function is built eagerly only when
        // every domain is an enumerated set or interval (Reducible), and it
        // is not the function of an application (KeepLazy).
        let plain = sets.iter().all(|s| matches!(s, Value::Set(_) | Value::Interval(..)));
        let domain = fn_domain(sets)?;
        if !plain || cx.keep_lazy {
            let f = LambdaFcn::new(self.clone(), bounds.to_vec(), body.clone(), domain, env.clone(), cx, plain);
            return Ok(Value::LazyFcn(Arc::new(f)));
        }
        let mut pairs = Vec::new();
        for x in ops::enumerate_normalized(&domain)? {
            let env2 = self.bind_fn_args(bounds, &x, env)?;
            pairs.push((x, self.eval(body, &env2, cx)?));
        }
        Ok(Value::fcn_over(&domain, pairs)?)
    }

    /// Bind the variables of a function constructor/definition to argument `x`.
    pub(crate) fn bind_fn_args(&self, bounds: &[Bound], x: &Value, env: &Env) -> EResult<Env> {
        // One variable (or one tuple binder): bound to the argument itself.
        if let [b] = bounds {
            if matches!(&b.vars, BoundVars::Many(ls) if ls.len() == 1) || matches!(&b.vars, BoundVars::Tuple(_)) {
                return self.bind_bound_vars(&b.vars, x.clone(), env);
            }
        }
        let forced;
        let x = if matches!(x, Value::LazyFcn(_)) {
            forced = force_lazy_fcn(x.clone())?;
            &forced
        } else {
            x
        };
        let Value::Tuple(parts) = x else {
            return Err(EvalError::new(format!("function argument {x} is not a tuple")));
        };
        if bounds.iter().all(|b| matches!(b.vars, BoundVars::Many(_))) {
            let ls = bounds.iter().flat_map(|b| match &b.vars {
                BoundVars::Many(ls) => &ls[..],
                BoundVars::Tuple(_) => &[],
            });
            return Ok(env.bind_all(ls.zip(parts.iter()).map(|(l, v)| (*l, Binding::Val(v.clone())))));
        }
        let mut env2 = env.clone();
        let mut i = 0;
        for b in bounds {
            match &b.vars {
                BoundVars::Many(ls) => {
                    for l in ls {
                        env2 = env2.bind_val(*l, parts[i].clone());
                        i += 1;
                    }
                }
                BoundVars::Tuple(_) => {
                    env2 = self.bind_bound_vars(&b.vars, parts[i].clone(), &env2)?;
                    i += 1;
                }
            }
        }
        Ok(env2)
    }

    // ------------------------------------------------------------------
    // operator application

    /// Evaluate an operator-valued argument.
    pub(crate) fn op_val(&self, e: &Expr, env: &Env) -> EResult<OpVal> {
        match &*e.kind {
            ExprKind::OpArg(r) => Ok(match r {
                OpRef::Param(l) => match env.lookup(*l) {
                    Some(Binding::Op(o)) => o.clone(),
                    _ => return Err(EvalError::at("operator parameter is not bound to an operator", e.span)),
                },
                // A LET definition closes over the current environment.
                OpRef::Def(d) if self.prog.def_is_let(*d) => match &self.prog.defs[d.idx()].kind {
                    DefKind::Op(body) => {
                        OpVal::Lambda { params: self.prog.defs[d.idx()].params.clone().into(), body: body.clone(), env: env.clone() }
                    }
                    _ => OpVal::Ref(*r),
                },
                r => OpVal::Ref(*r),
            }),
            ExprKind::Lambda { params, body } => Ok(OpVal::Lambda { params: params.clone().into(), body: body.clone(), env: env.clone() }),
            _ => Err(EvalError::at("expected an operator argument", e.span)),
        }
    }

    /// An operator argument of a native that TLC implements in Java and
    /// that requires an operator (BagOfAll, the folds, SortSeq, ...). TLC
    /// passes an operator whose body is a numeral or string literal
    /// (`LAMBDA x : 2`, `Op(x) == "a"`) as that literal's value: SANY's
    /// literal nodes carry their value (SpecProcessor.processConstants),
    /// and looking an operator up returns its body's value if it has one
    /// (SymbolNodeValueLookupProvider.lookup). The override then rejects
    /// it: "The first argument of BagOfAll should be an operator, but
    /// instead it is: 2" (Bags.java), or a failed cast to OpValue. (A
    /// TLA+-defined operator applies such a value as a constant, which is
    /// what the literal body gives anyway.)
    pub(crate) fn native_op_val(&self, e: &Expr, env: &Env, which: &str, name: &str, span: Span) -> EResult<OpVal> {
        let op = self.op_val(e, env)?;
        let body = match &op {
            OpVal::Lambda { body, .. } => Some(body),
            OpVal::Ref(OpRef::Def(d)) if !self.def_redirect.contains_key(d) && self.prog.defs[d.idx()].builtin.is_none() => {
                match &self.prog.defs[d.idx()].kind {
                    DefKind::Op(body) => Some(body),
                    _ => None,
                }
            }
            _ => None,
        };
        let lit = match body.map(|b| &*b.kind) {
            Some(ExprKind::Num(n)) => n.to_string(),
            Some(ExprKind::Str(s)) => format!("{:?}", &**s),
            _ => return Ok(op),
        };
        Err(EvalError::of_kind(
            tlx_runtime::ErrorKind::ArgumentError,
            format!("The {which} argument of {name} should be an operator, but instead it is: {lit}"),
        )
        .with_span(span))
    }

    /// Bind the parameters of definition `d` to the argument expressions.
    /// Operator parameters get operator values; others are evaluated
    /// (or bound by name when `lazy`).
    ///
    /// With `defer_errors`, an argument whose (eager) evaluation fails is
    /// bound by name instead: TLC passes arguments unevaluated (LazyValue),
    /// so the error is raised only if the body uses the argument.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn bind_params(
        self: &Arc<Self>,
        params: &[LocalId],
        args: &[Expr],
        env: &Env,
        cx: &Ctx,
        base: Env,
        lazy: bool,
        defer_errors: bool,
    ) -> EResult<Env> {
        let mut err = None;
        let bind = |p: &LocalId, a: &Expr| -> EResult<Binding> {
            Ok(if self.prog.locals[p.idx()].arity > 0 {
                Binding::Op(self.op_val(a, env)?)
            } else if lazy {
                // State arguments must still be expressions under a prime
                // (ENABLED can supply a next state), but repeatedly unfolding
                // their unprimed bindings builds quadratic recursive chains.
                if cx.s0.is_some() && cx.s1.is_none() && !cx.primed && !cx.keep_lazy && self.state_argument_in(a, env) {
                    Binding::Thunk(Arc::new(Thunk { expr: a.clone(), env: env.clone(), memo: Some(Default::default()) }))
                } else {
                    self.bind_by_name(a, env)
                }
            } else {
                match self.eval(a, env, cx) {
                    Ok(v) => Binding::Val(v),
                    Err(e) if defer_errors && !crate::depth::is_depth_error(&e) => self.bind_by_name(a, env),
                    Err(e) => return Err(e),
                }
            })
        };
        if let ([p], [a]) = (params, args) {
            return Ok(base.bind(*p, bind(p, a)?));
        }
        let out = base.bind_all(params.iter().zip(args).map_while(|(p, a)| match bind(p, a) {
            Ok(b) => Some((*p, b)),
            Err(e) => {
                err = Some(e);
                None
            }
        }));
        match err {
            Some(e) => Err(e),
            None => Ok(out),
        }
    }

    pub(crate) fn bind_by_name(&self, expr: &Expr, env: &Env) -> Binding {
        // A parameter passed on (`Op(n) == ... Op(n)`) shares the binding:
        // a chain of names, one per level of a recursion, would take time
        // proportional to its length to read.
        if let ExprKind::Local(id) = &*expr.kind {
            if let Some(b @ (Binding::Name(..) | Binding::Thunk(_) | Binding::Val(_))) = env.lookup(*id) {
                return b.clone();
            }
        }
        match self.prog.expr_id(expr) {
            Some(id) => Binding::Name(id, env.clone()),
            None => Binding::Thunk(Arc::new(Thunk { expr: expr.clone(), env: env.clone(), memo: None })),
        }
    }

    /// The recursion-depth guard, applied only when `d` can call itself
    /// (a non-recursive application must not touch the thread-local
    /// counter, which is on the interpreter's hot path).
    fn depth_guard(&self, d: DefId, span: Span) -> EResult<Option<crate::depth::Guard>> {
        if self.is_recursive(d) {
            Ok(Some(crate::depth::Guard::enter(span)?))
        } else {
            Ok(None)
        }
    }

    pub(crate) fn apply(self: &Arc<Self>, op: OpRef, args: &[Expr], env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        match op {
            OpRef::Def(d) => {
                if args.is_empty() {
                    return self.call_def(d, env, cx, span);
                }
                if let Some(v) = self.def_value.get(&d) {
                    return Ok(v.clone());
                }
                let d = self.redirect_def(d);
                if let Some(b) = self.prog.defs[d.idx()].builtin {
                    return self.builtin(b, args, env, cx, span);
                }
                self.call_def_with_args(d, args, env, cx, span)
            }
            OpRef::Const(c) => match &self.consts[c.idx()] {
                Some(ConstVal::Op(r)) => self.apply(*r, args, env, cx, span),
                Some(ConstVal::Table(_)) => {
                    let vs = args.iter().map(|a| self.eval(a, env, cx)).collect::<EResult<Vec<_>>>()?;
                    self.apply_const_table(c, &vs, span)
                }
                _ => Err(EvalError::at(
                    format!("The constant parameter {} is not assigned a value by the configuration file.", self.prog.consts[c.idx()].name),
                    span,
                )),
            },
            OpRef::Param(l) => {
                let Some(Binding::Op(o)) = env.lookup(l).cloned() else {
                    return Err(EvalError::at("operator parameter is not bound to an operator", span));
                };
                self.apply_opval(&o, args, env, cx, span)
            }
            OpRef::Builtin(b) => self.builtin(b, args, env, cx, span),
        }
    }

    /// Apply operator constant `c` given by a table in the cfg (`F(1) = 2`):
    /// its value at `args`, which must be one of the table's arguments
    /// (TLC's OpRcdValue.apply).
    fn apply_const_table(&self, c: ConstId, args: &[Value], span: Span) -> EResult<Value> {
        let Some(ConstVal::Table(rows)) = &self.consts[c.idx()] else { unreachable!("not a table") };
        for (a, v) in rows.iter() {
            if a.len() == args.len()
                && a.iter().zip(args).try_fold(true, |eq, (x, y)| Ok::<_, EvalError>(eq && tlx_value::order::eq_tlc(x, y)?))?
            {
                return Ok(v.clone());
            }
        }
        let shown = args.iter().map(|a| a.to_string()).collect::<Vec<_>>().join(", ");
        Err(EvalError::at(
            format!("Attempted to apply the operator {} to arguments ({shown}), which is undefined.", self.prog.consts[c.idx()].name),
            span,
        ))
    }

    /// Apply a cfg-overridden standard-module definition (`Seq <- LimitedSeq`).
    pub(crate) fn apply_overridden(self: &Arc<Self>, d: DefId, args: &[Expr], env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        if let Some(v) = self.def_value.get(&d) {
            return Ok(v.clone());
        }
        let t = self.redirect_def(d);
        // (`\o <- +`: a native target is applied natively.)
        if let Some(b) = self.prog.defs[t.idx()].builtin {
            return self.builtin(b, args, env, cx, span);
        }
        if args.is_empty() {
            return self.call_def(t, env, cx, span);
        }
        self.call_def_with_args(t, args, env, cx, span)
    }

    /// Apply the (redirected, non-builtin) definition `d` to argument
    /// expressions. Arguments of action-level definitions are passed by name
    /// in action contexts.
    fn call_def_with_args(self: &Arc<Self>, d: DefId, args: &[Expr], env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        let _depth = self.depth_guard(d, span)?;
        if self.def_memo[d.idx()] && cx.s0.is_none() && cx.s1.is_none() {
            return self.call_def_memo(d, args, env, cx, span);
        }
        let lazy = by_name(cx) && self.def_by_name[d.idx()];
        let env2 =
            self.bind_params(&self.prog.defs[d.idx()].params, args, env, cx, self.def_env(d, env), lazy, self.def_defer_errors[d.idx()])?;
        self.def_body(d, &env2, cx, span)
    }

    /// `call_def_with_args` of a `def_memo` definition in a constant
    /// context: the arguments are bound as `bind_params` binds them, and
    /// when they are all values the application is memoized (`memo`).
    pub(crate) fn call_def_memo(self: &Arc<Self>, d: DefId, args: &[Expr], env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        let defer_errors = self.def_defer_errors[d.idx()];
        let mut vals = Vec::with_capacity(args.len());
        let mut all_vals = true;
        let mut err = None;
        let env2 = Env::default().bind_all(self.prog.defs[d.idx()].params.iter().zip(args).map_while(|(p, a)| {
            let b = match self.eval(a, env, cx) {
                Ok(v) => {
                    vals.push(v.clone());
                    Binding::Val(v)
                }
                Err(e) if defer_errors && !crate::depth::is_depth_error(&e) => {
                    all_vals = false;
                    self.bind_by_name(a, env)
                }
                Err(e) => {
                    err = Some(e);
                    return None;
                }
            };
            Some((*p, b))
        }));
        if let Some(e) = err {
            return Err(e);
        }
        if !all_vals || !crate::memo::keyable(&vals) {
            return self.def_body(d, &env2, cx, span);
        }
        crate::memo::get_or_eval(self.uid, d, cx.keep_lazy, vals, || self.def_body(d, &env2, cx, span))
    }

    /// Apply an operator value to argument expressions.
    pub(crate) fn apply_opval(self: &Arc<Self>, o: &OpVal, args: &[Expr], env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        let _depth = crate::depth::Guard::enter(span)?;
        match o {
            OpVal::Ref(r) => self.apply(*r, args, env, cx, span),
            OpVal::Lambda { params, body, env: lenv } => {
                let lazy = by_name(cx) && self.lambda_is_action(body);
                let env2 = self.bind_params(params, args, env, cx, lenv.clone(), lazy, self.lambda_lazy_args(body.span.file))?;
                self.eval(body, &env2, cx)
            }
        }
    }

    /// Apply an operator value to already evaluated arguments.
    pub(crate) fn apply_opval_values(self: &Arc<Self>, o: &OpVal, args: Vec<Value>, cx: &Ctx, span: Span) -> EResult<Value> {
        let _depth = crate::depth::Guard::enter(span)?;
        let (params, body, base): (Vec<LocalId>, Expr, Env) = match o {
            OpVal::Lambda { params, body, env } => (params.to_vec(), body.clone(), env.clone()),
            OpVal::Ref(OpRef::Def(d)) => {
                let d = self.redirect_def(*d);
                if let Some(b) = self.prog.defs[d.idx()].builtin {
                    return self.builtin_values(b, &args, cx, span);
                }
                let DefKind::Op(body) = &self.prog.defs[d.idx()].kind else {
                    return Err(EvalError::at("operator argument is not an operator definition", span));
                };
                (self.prog.defs[d.idx()].params.clone(), body.clone(), Env::default())
            }
            OpVal::Ref(OpRef::Builtin(b)) => return self.builtin_values(*b, &args, cx, span),
            OpVal::Ref(OpRef::Const(c)) => match &self.consts[c.idx()] {
                Some(ConstVal::Op(r)) => return self.apply_opval_values(&OpVal::Ref(*r), args, cx, span),
                Some(ConstVal::Table(_)) => return self.apply_const_table(*c, &args, span),
                _ => return Err(EvalError::at("unassigned operator constant", span)),
            },
            OpVal::Ref(OpRef::Param(_)) => return Err(EvalError::at("internal error: unresolved operator parameter", span)),
        };
        if params.len() != args.len() {
            return Err(EvalError::at("wrong number of arguments for operator argument", span));
        }
        let env = base.bind_all(params.iter().zip(args).map(|(p, a)| (*p, Binding::Val(a))));
        self.eval(&body, &env, cx)
    }

    /// Value of a 0-ary use of a definition (cached when constant-level, or
    /// memoized in the context's `DefCache` when state-cacheable).
    pub(crate) fn call_def(self: &Arc<Self>, d: DefId, env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        let _depth = self.depth_guard(d, span)?;
        if let Some(v) = self.def_value.get(&d) {
            return local::get(self.uid, Slot::Def(d.idx()), || Ok(v.clone()));
        }
        let d = self.redirect_def(d);
        if let Some(v) = self.def_value.get(&d) {
            return local::get(self.uid, Slot::Def(d.idx()), || Ok(v.clone()));
        }
        if let Some(b) = self.prog.defs[d.idx()].builtin {
            return self.builtin(b, &[], env, cx, span);
        }
        if cx.keep_lazy {
            return self.call_def_keep_lazy(d, env, cx, span);
        }
        self.call_def_cached(d, env, cx, span)
    }

    /// `call_def` under KeepLazy. TLC does not cache 0-ary definitions
    /// (except constant ones, evaluated eagerly at startup), so it evaluates
    /// the body with KeepLazy. Cached values are equal to the KeepLazy
    /// result and are used when they can be computed; when that fails, the
    /// body is evaluated lazily (not cached), as TLC would.
    fn call_def_keep_lazy(self: &Arc<Self>, d: DefId, env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        if self.def_const[d.idx()] {
            return match self.call_def_cached(d, env, &cx.lazy(false), span) {
                Ok(v) => Ok(v),
                Err(_) => self.def_body(d, &Env::default(), &Ctx::NONE.lazy(true), span),
            };
        }
        let memo = cx.cache.and_then(|c| c.memo(cx)).is_some() && self.def_state_cacheable[d.idx()];
        let let_cache = self.let_cacheable[d.idx()]
            && !cx.primed
            && matches!(env.lookup(crate::env::let_cache_key(d)), Some(Binding::LetCache(c)) if c.get().is_some());
        if memo || let_cache {
            if let Ok(v) = self.call_def_cached(d, env, &cx.lazy(false), span) {
                return Ok(v);
            }
            let denv = if memo { Env::default() } else { self.def_env(d, env) };
            return self.def_body(d, &denv, cx, span);
        }
        self.def_body(d, &self.def_env(d, env), cx, span)
    }

    /// `call_def` of a non-builtin definition without overrides.
    pub(crate) fn call_def_cached(self: &Arc<Self>, d: DefId, env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        if self.def_const[d.idx()] {
            return local::get(self.uid, Slot::Def(d.idx()), || {
                self.const_cache[d.idx()].get_or_init(|| self.def_body(d, &Env::default(), &Ctx::NONE, span)).clone()
            });
        }
        let state_level = self.def_state_cacheable[d.idx()];
        if state_level {
            if let Some(m) = cx.cache.and_then(|c| c.memo(cx)) {
                return m.get_or_eval(d, || {
                    count_def_eval(cx);
                    self.def_body(d, &Env::default(), cx, span)
                });
            }
        }
        if self.let_cacheable[d.idx()] && !cx.primed {
            if let Some(cell) = env.lookup(crate::env::let_cache_key(d)).and_then(|b| match b {
                Binding::LetCache(c) => c.get(),
                _ => None,
            }) {
                if let Some(v) = cell.get() {
                    return Ok(v.clone());
                }
                if state_level {
                    count_def_eval(cx);
                }
                let v = self.def_body(d, &self.def_env(d, env), cx, span)?;
                let _ = cell.set(v.clone());
                return Ok(v);
            }
        }
        if state_level {
            count_def_eval(cx);
        }
        self.def_body(d, &self.def_env(d, env), cx, span)
    }

    /// `env` with fresh value caches for the cacheable definitions of a LET,
    /// which live as long as the returned frame (keep it while the body is
    /// evaluated; see `LetCell::Frame`).
    pub(crate) fn let_env(&self, defs: &[DefId], env: &Env) -> (Env, LetFrame) {
        let k = defs.iter().filter(|d| self.let_cacheable[d.idx()]).count();
        if k == 0 {
            return (env.clone(), LetFrame::new(None));
        }
        let cells: Arc<[std::sync::OnceLock<Value>]> = (0..k).map(|_| std::sync::OnceLock::new()).collect();
        let out = env.bind_all(
            defs.iter()
                .filter(|d| self.let_cacheable[d.idx()])
                .enumerate()
                .map(|(i, d)| (crate::env::let_cache_key(*d), Binding::LetCache(LetCell::Frame(Arc::downgrade(&cells), i as u32)))),
        );
        (out, LetFrame::new(Some(cells)))
    }

    pub(crate) fn def_body(self: &Arc<Self>, d: DefId, env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        match &self.prog.defs[d.idx()].kind {
            DefKind::Op(body) => self.eval(body, env, cx),
            DefKind::Fn { bounds, body } if self.is_recursive_fn(d) => {
                let f = RecursiveFcn::new(self.clone(), d, bounds.clone(), body.clone(), env.clone(), cx)?;
                Ok(Value::LazyFcn(f as Arc<dyn LazyFcn>))
            }
            DefKind::Fn { bounds, body } => self.fn_construct(bounds, body, env, cx),
            DefKind::Pending => Err(EvalError::at(format!("definition {} could not be resolved", self.prog.defs[d.idx()].name), span)),
        }
    }
}
