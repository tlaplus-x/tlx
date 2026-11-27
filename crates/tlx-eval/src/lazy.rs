//! Lazily evaluated values that need the interpreter: functions over
//! infinite domains, recursive function definitions, and filters over
//! infinite sets.

use std::fmt;
use std::sync::{Arc, Mutex, OnceLock, Weak};

use tlx_base::hash::FxMap;
use tlx_sema::hir::*;
use tlx_value::{ops, CustomSet, LazyFcn, LazySet, Value, ValueError};

use crate::env::{let_cache_key, Binding, Env, LetCell};
use crate::error::{EResult, EvalError};
use crate::eval::{fn_domain, Ctx};
use crate::interp::Interp;
use crate::seqfilter::SeqPred;
use crate::subsetfilter::SubsetPred;

/// Owned snapshot of an evaluation context.
#[derive(Clone)]
pub(crate) struct Snap {
    s0: Option<Arc<[Value]>>,
    s1: Option<Arc<[Option<Value>]>>,
    primed: bool,
    init: bool,
    level: u32,
    keep_lazy: bool,
}

impl Snap {
    pub(crate) fn of(cx: &Ctx) -> Snap {
        Snap {
            s0: cx.s0.map(Arc::from),
            s1: cx.s1.map(Arc::from),
            primed: cx.primed,
            init: cx.init,
            level: cx.level,
            keep_lazy: cx.keep_lazy,
        }
    }

    pub(crate) fn ctx(&self) -> Ctx<'_> {
        Ctx {
            s0: self.s0.as_deref(),
            s1: self.s1.as_deref(),
            primed: self.primed,
            init: self.init,
            level: self.level,
            cache: None,
            keep_lazy: self.keep_lazy,
        }
    }
}

fn verr(e: EvalError) -> ValueError {
    e.into()
}

/// Memo results of pure lazy functions survive restarts. Effectful ones
/// are invalidated with the journal that rolls their evaluations back.
struct LazyMemo {
    /// (Allocated on first use: most lazy functions memoize nothing.)
    values: OnceLock<Arc<Mutex<FxMap<Value, Value>>>>,
    /// Whether the body is not constant-level (computed when first needed:
    /// only when undo records are kept).
    rollback_sensitive: OnceLock<bool>,
}

impl LazyMemo {
    fn new() -> Self {
        Self { values: OnceLock::new(), rollback_sensitive: OnceLock::new() }
    }

    fn sensitive(&self, ip: &Interp, body: &Expr, env: &Env) -> bool {
        *self.rollback_sensitive.get_or_init(|| !ip.is_constant_in(body, env))
    }

    fn values(&self) -> &Arc<Mutex<FxMap<Value, Value>>> {
        self.values.get_or_init(Default::default)
    }

    fn get(&self, arg: &Value) -> Option<Value> {
        self.values.get()?.lock().unwrap().get(arg).cloned()
    }

    fn insert(&self, ip: &Interp, body: &Expr, env: &Env, arg: Value, value: Value) {
        self.values().lock().unwrap().insert(arg.clone(), value);
        if ip.effects_memo_undo_wanted() && self.sensitive(ip, body, env) {
            let memo = Arc::downgrade(self.values());
            ip.effects_memo_undo(Arc::new(move || {
                if let Some(memo) = memo.upgrade() {
                    memo.lock().unwrap().remove(&arg);
                }
            }));
        }
    }
}

/// `[x \in S |-> body]` with an infinite domain.
pub(crate) struct LambdaFcn {
    ip: Arc<Interp>,
    bounds: Vec<Bound>,
    body: Expr,
    domain: Value,
    env: Env,
    snap: Snap,
    /// Lazy only because of KeepLazy (the domain is enumerable).
    kept: bool,
    /// Values of the points applied so far (kept-lazy functions only: one
    /// may be applied repeatedly, e.g. a row computed by a memoized
    /// recursive function; TLC re-evaluates the point each time).
    memo: LazyMemo,
}

impl LambdaFcn {
    /// `[x \in domain |-> body]`; `kept`: the domain is enumerable and the
    /// function is lazy only because it is constructed under KeepLazy.
    pub(crate) fn new(ip: Arc<Interp>, bounds: Vec<Bound>, body: Expr, domain: Value, env: Env, cx: &Ctx, kept: bool) -> LambdaFcn {
        LambdaFcn { ip, bounds, body, domain, env, snap: Snap::of(cx), kept, memo: LazyMemo::new() }
    }
}

impl fmt::Debug for LambdaFcn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[x \\in {} |-> ...]", self.domain)
    }
}

impl LazyFcn for LambdaFcn {
    fn apply(&self, arg: &Value) -> tlx_value::Result<Value> {
        let _depth = crate::depth::Guard::enter(self.body.span).map_err(verr)?;
        if !ops::member(arg, &self.domain)? {
            return Err(ValueError::new(format!("Attempted to apply function to argument {arg}, which is not in its domain.")));
        }
        if self.kept {
            if let Some(v) = self.memo.get(arg) {
                return Ok(v);
            }
        }
        let env = self.ip.bind_fn_args(&self.bounds, arg, &self.env).map_err(verr)?;
        let v = self.ip.eval(&self.body, &env, &self.snap.ctx()).map_err(verr)?;
        if self.kept {
            self.memo.insert(&self.ip, &self.body, &self.env, arg.clone(), v.clone());
        }
        Ok(v)
    }

    fn domain(&self) -> tlx_value::Result<Value> {
        Ok(self.domain.clone())
    }

    fn kept_lazy(&self) -> bool {
        self.kept
    }
}

/// A recursive function definition `f[x \in S] == body` (memoized).
pub(crate) struct RecursiveFcn {
    ip: Arc<Interp>,
    def: DefId,
    bounds: Vec<Bound>,
    body: Expr,
    domain: Value,
    /// The environment of the definition, without the value cache of `f`
    /// if `f` is a LET definition (`rebind`): that cache holds this
    /// function, which would then hold itself and never be freed (with its
    /// memo and the state it was made in, once per evaluation of the LET).
    env: Env,
    /// Whether the body sees `f` through a LET cache, bound to this
    /// function (`me`) for each evaluation of the body instead.
    rebind: bool,
    me: Weak<RecursiveFcn>,
    snap: Snap,
    memo: LazyMemo,
}

impl RecursiveFcn {
    pub(crate) fn new(ip: Arc<Interp>, def: DefId, bounds: Vec<Bound>, body: Expr, env: Env, cx: &Ctx) -> EResult<Arc<RecursiveFcn>> {
        let domain = fn_domain(ip.bound_sets(&bounds, &env, cx)?)?;
        // TLC evaluates the body of a recursive function with KeepLazy
        // (FcnLambdaValue.makeRecursive).
        let snap = Snap::of(&cx.lazy(true));
        let (env, rebind) = match env.without(let_cache_key(def)) {
            Some(env) => (env, true),
            None => (env, false),
        };
        let memo = LazyMemo::new();
        Ok(Arc::new_cyclic(|me| RecursiveFcn { ip, def, bounds, body, domain, env, rebind, me: me.clone(), snap, memo }))
    }
}

impl fmt::Debug for RecursiveFcn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}[x \\in {}]", self.ip.prog.defs[self.def.idx()].name, self.domain)
    }
}

impl LazyFcn for RecursiveFcn {
    fn apply(&self, arg: &Value) -> tlx_value::Result<Value> {
        let _depth = crate::depth::Guard::enter(self.body.span).map_err(verr)?;
        if let Some(v) = self.memo.get(arg) {
            return Ok(v);
        }
        if !ops::member(arg, &self.domain)? {
            return Err(ValueError::new(format!("Attempted to apply function to argument {arg}, which is not in its domain.")));
        }
        // (The cache made here holds this function only while the body is
        // evaluated: a value that captures the environment refers to it
        // weakly, see `LetCell::Frame`.)
        let me = if self.rebind { self.me.upgrade() } else { None };
        let frame: Option<Arc<[OnceLock<Value>]>> = me.map(|me| Arc::new([OnceLock::from(Value::LazyFcn(me))]) as _);
        let env = match &frame {
            Some(cell) => self.env.bind(let_cache_key(self.def), Binding::LetCache(LetCell::Frame(Arc::downgrade(cell), 0))),
            None => self.env.clone(),
        };
        let env = self.ip.bind_fn_args(&self.bounds, arg, &env).map_err(verr)?;
        let v = self.ip.eval(&self.body, &env, &self.snap.ctx()).map_err(verr)?;
        self.memo.insert(&self.ip, &self.body, &self.env, arg.clone(), v.clone());
        Ok(v)
    }

    fn domain(&self) -> tlx_value::Result<Value> {
        Ok(self.domain.clone())
    }
}

/// `{x \in S : P}` over a set S that is not enumerated (e.g. infinite, or a
/// set of records).
struct FilterSet {
    ip: Arc<Interp>,
    vars: BoundVars,
    base: Value,
    pred: Expr,
    env: Env,
    snap: Snap,
    /// The elements, once an enumeration completed (in its order), if the
    /// predicate is constant-level (no variable, nothing effectful) and
    /// there are at most `MAX_MEMO_ELEMS`: a constant definition such as
    /// `SortedSeqs == {s \in Seq(V) : ...}` is enumerated by the pre-run,
    /// the lowering and the search, and each enumeration would evaluate the
    /// predicate on the whole base set again.
    memo: OnceLock<Arc<[Value]>>,
    /// The predicate compiled for sets of sequences, if it can be decided
    /// on prefixes (`seqfilter`).
    seq_pred: OnceLock<Option<SeqPred>>,
    /// The predicate compiled for powersets, if leading conjuncts can prune
    /// the subset domain (`subsetfilter`).
    subset_pred: OnceLock<Option<SubsetPred>>,
}

/// The elements of a `FilterSet`'s base set, with its sets of sequences
/// filtered on prefixes (`SeqPred::filter`); `visit(x, known)` visits an
/// element whose membership is `known` (else evaluates the predicate).
struct SeqVisitor<'a> {
    pred: &'a SeqPred,
    visit: &'a mut dyn FnMut(Value, Option<bool>) -> tlx_value::Result<bool>,
}

impl ops::SeqsVisitor for SeqVisitor<'_> {
    fn elem(&mut self, v: Value) -> tlx_value::Result<bool> {
        (self.visit)(v, None)
    }

    fn seqs(&mut self, n: usize, range: &[Value]) -> tlx_value::Result<Option<bool>> {
        self.pred.filter(n, range, self.visit)
    }
}

/// The elements of a `FilterSet`'s base set, with its powersets pruned by
/// leading subset constraints (`SubsetPred::filter`).
struct FilterSubsetVisitor<'a> {
    ip: &'a Arc<Interp>,
    env: &'a Env,
    cx: &'a Ctx<'a>,
    pred: &'a SubsetPred,
    visit: &'a mut dyn FnMut(Value, Option<bool>) -> tlx_value::Result<bool>,
}

impl ops::SubsetVisitor for FilterSubsetVisitor<'_> {
    fn elem(&mut self, v: Value) -> tlx_value::Result<bool> {
        (self.visit)(v, None)
    }

    fn subsets(&mut self, base: &ops::SubsetBase<'_>) -> tlx_value::Result<Option<bool>> {
        self.pred.filter(self.ip, self.env, self.cx, base, self.visit)
    }
}

/// The most elements a `FilterSet` keeps after enumerating them.
const MAX_MEMO_ELEMS: usize = 1 << 17;

impl fmt::Debug for FilterSet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{x \\in {} : ...}}", self.base)
    }
}

impl CustomSet for FilterSet {
    fn contains(&self, v: &Value) -> tlx_value::Result<bool> {
        if !ops::member(v, &self.base)? {
            return Ok(false);
        }
        let env = self.ip.bind_bound_vars(&self.vars, v.clone(), &self.env).map_err(verr)?;
        self.ip.eval_bool(&self.pred, &env, &self.snap.ctx()).map_err(verr)
    }

    /// TLC's SetPredValue.isFinite: finite if the base set is, else an
    /// error (the filtered set may be finite or not).
    fn is_finite(&self) -> tlx_value::Result<bool> {
        if self.memo.get().is_some() || ops::is_finite_set(&self.base)? {
            return Ok(true);
        }
        Err(tlx_value::ValueError::new(format!(
            "Attempted to check if expression of form {{x \\in S : p(x)}} is a finite set, but cannot check if S:\n{}\nis finite.",
            self.base
        )))
    }

    /// TLC's SetPredValue enumerates its base set if that is `Enumerable`
    /// (with the base's error), and otherwise refuses.
    fn not_enumerable(&self, _: &Value) -> tlx_value::ValueError {
        if ops::is_enumerable(&self.base) {
            if let Err(e) = ops::for_each_element(&self.base, &mut |_| Ok(false)) {
                return e;
            }
        }
        tlx_value::ValueError::new(format!("Attempted to enumerate {{ x \\in S : p(x) }} when S:\n{}\nis not enumerable", self.base))
    }

    fn enumerate(&self) -> tlx_value::Result<Option<Vec<Value>>> {
        if let Some(m) = self.memo.get() {
            return Ok(Some(m.to_vec()));
        }
        if !ops::is_finite_set(&self.base)? {
            return Ok(None);
        }
        let mut out = Vec::new();
        self.for_each(&mut |x| {
            out.push(x);
            Ok(true)
        })?;
        Ok(Some(out))
    }

    fn for_each(&self, f: &mut dyn FnMut(Value) -> tlx_value::Result<bool>) -> tlx_value::Result<Option<bool>> {
        if let Some(m) = self.memo.get() {
            for x in m.iter() {
                if !f(x.clone())? {
                    return Ok(Some(false));
                }
            }
            return Ok(Some(true));
        }
        if !ops::is_finite_set(&self.base)? {
            return Ok(None);
        }
        let mut kept = self.ip.is_constant_in(&self.pred, &self.env).then(Vec::new);
        let mut visit = |x: Value, known: Option<bool>| {
            let member = match known {
                Some(b) => b,
                None => {
                    let env = self.ip.bind_bound_vars(&self.vars, x.clone(), &self.env).map_err(verr)?;
                    self.ip.eval_bool(&self.pred, &env, &self.snap.ctx()).map_err(verr)?
                }
            };
            if member {
                if let Some(k) = &mut kept {
                    if k.len() < MAX_MEMO_ELEMS {
                        k.push(x.clone());
                    } else {
                        kept = None;
                    }
                }
                f(x)
            } else {
                Ok(true)
            }
        };
        let cx = self.snap.ctx();
        let done = match &self.base {
            Value::LazySet(l) if matches!(**l, LazySet::Subset(_)) => {
                match self.subset_pred.get_or_init(|| SubsetPred::compile(&self.ip, &self.vars, &self.pred, &self.env)) {
                    Some(pred) => ops::for_each_enumerated_subsets(
                        &self.base,
                        &mut FilterSubsetVisitor { ip: &self.ip, env: &self.env, cx: &cx, pred, visit: &mut visit },
                    )?,
                    None => ops::for_each_enumerated(&self.base, &mut |x| visit(x, None))?,
                }
            }
            Value::LazySet(l) if matches!(**l, LazySet::FcnSet(..)) => {
                match self.seq_pred.get_or_init(|| SeqPred::compile(&self.ip, &self.vars, &self.pred, &self.env)) {
                    Some(pred) => ops::for_each_enumerated_seqs(&self.base, &mut SeqVisitor { pred, visit: &mut visit })?,
                    None => ops::for_each_enumerated(&self.base, &mut |x| visit(x, None))?,
                }
            }
            Value::LazySet(l) if matches!(**l, LazySet::Union(_)) => {
                if let Some(pred) = self.seq_pred.get_or_init(|| SeqPred::compile(&self.ip, &self.vars, &self.pred, &self.env)) {
                    ops::for_each_enumerated_seqs(&self.base, &mut SeqVisitor { pred, visit: &mut visit })?
                } else if let Some(pred) = self.subset_pred.get_or_init(|| SubsetPred::compile(&self.ip, &self.vars, &self.pred, &self.env))
                {
                    ops::for_each_enumerated_subsets(
                        &self.base,
                        &mut FilterSubsetVisitor { ip: &self.ip, env: &self.env, cx: &cx, pred, visit: &mut visit },
                    )?
                } else {
                    ops::for_each_enumerated(&self.base, &mut |x| visit(x, None))?
                }
            }
            _ => ops::for_each_enumerated(&self.base, &mut |x| visit(x, None))?,
        };
        if done {
            if let Some(k) = kept {
                let _ = self.memo.set(k.into());
            }
        }
        Ok(Some(done))
    }
}

/// `{x \in S : P}` where S is not an enumerated set stays lazy, like TLC's
/// SetPredValue: membership tests S and P without enumerating S.
pub(crate) fn lazy_filter(ip: &Arc<Interp>, vars: &BoundVars, base: Value, pred: &Expr, env: &Env, cx: &Ctx) -> Value {
    let s = FilterSet {
        ip: ip.clone(),
        vars: vars.clone(),
        base,
        pred: pred.clone(),
        env: env.clone(),
        snap: Snap::of(cx),
        memo: OnceLock::new(),
        seq_pred: OnceLock::new(),
        subset_pred: OnceLock::new(),
    };
    Value::LazySet(Arc::new(LazySet::Custom(Box::new(s))))
}

#[cfg(test)]
mod memo_effect_tests {
    use super::*;

    #[test]
    fn rollback_preserves_pure_memo_and_dry_checks_do_not_cache_effects() {
        let dir = tlx_testkit::TempDir::new("lazy-memo");
        let path = dir.join("MemoEffects.tla");
        std::fs::write(
            &path,
            r#"---- MODULE MemoEffects ----
EXTENDS Naturals, TLC
Pure[i \in 1..2] == IF i = 1 THEN 1 ELSE Pure[i-1] + 1
Effect[i \in 1..2] == IF i = 1 THEN IF PrintT("memo effect") THEN 1 ELSE 0 ELSE Effect[i-1] + 1
====
"#,
        )
        .unwrap();
        let ip = Interp::new(tlx_sema::Program::load(&path, &[]).unwrap(), Default::default()).unwrap();
        let make = |name| {
            let def = ip.root_def(name).unwrap();
            let DefKind::Fn { bounds, body } = &ip.prog.defs[def.idx()].kind else { panic!("function") };
            RecursiveFcn::new(ip.clone(), def, bounds.clone(), body.clone(), Env::default(), &Ctx::NONE).unwrap()
        };
        let pure = make("Pure");
        let effect = make("Effect");
        assert!(!pure.memo.sensitive(&ip, &pure.body, &pure.env));
        assert!(effect.memo.sensitive(&ip, &effect.body, &effect.env));
        ip.effects_active(true);
        assert_eq!(pure.apply(&Value::Int(2)).unwrap(), Value::Int(2));
        assert_eq!(effect.apply(&Value::Int(2)).unwrap(), Value::Int(2));
        let entries = pure.memo.values().lock().unwrap().len();
        assert!(entries > 0);
        ip.effects_rollback_run().unwrap();
        assert_eq!(pure.memo.values().lock().unwrap().len(), entries);
        assert!(effect.memo.values().lock().unwrap().is_empty());
        assert_eq!(ip.without_effects(|| effect.apply(&Value::Int(2))).unwrap(), Value::Int(2));
        assert!(effect.memo.values().lock().unwrap().is_empty());
    }
}

#[cfg(test)]
mod let_cycle_tests {
    use super::*;

    /// A lazy value cached by a LET captures the LET's environment; the
    /// cache must not keep the value alive through it (an `Arc` cycle
    /// leaked about 40 KB per state on GameOfLife). (The definitions take a
    /// parameter, so that the LETs are not closed constant expressions,
    /// whose values are kept per thread.)
    #[test]
    fn lazy_values_cached_by_a_let_are_freed() {
        let dir = tlx_testkit::TempDir::new("let-cycle");
        let path = dir.join("LetCycle.tla");
        std::fs::write(
            &path,
            "---- MODULE LetCycle ----\nEXTENDS Naturals\n\
             Filter(k) == LET n == {q \\in Nat : q > k} IN n\n\
             Lambda(k) == LET f == [q \\in Nat |-> q + k] IN f\n\
             Used(k) == LET n == {q \\in Nat : q > k} IN IF 3 \\in n THEN n ELSE {}\n====\n",
        )
        .unwrap();
        let ip = Interp::new(tlx_sema::Program::load(&path, &[]).unwrap(), Default::default()).unwrap();
        let eval = |name: &str| {
            let def = ip.root_def(name).unwrap();
            let DefKind::Op(body) = &ip.prog.defs[def.idx()].kind else { panic!("operator") };
            let env = Env::default().bind_val(ip.prog.defs[def.idx()].params[0], Value::Int(1));
            ip.eval(body, &env, &Ctx::NONE).unwrap()
        };
        for name in ["Filter", "Lambda", "Used"] {
            let v = eval(name);
            let count = match &v {
                Value::LazySet(s) => Arc::strong_count(s),
                Value::LazyFcn(f) => Arc::strong_count(f),
                v => panic!("{name}: not lazy: {v}"),
            };
            assert_eq!(count, 1, "{name}: the LET cache still holds the value");
        }
        // Still usable after the LET's evaluation ended (re-evaluated).
        let v = eval("Used");
        assert!(ops::member(&Value::Int(5), &v).unwrap());
        assert!(!ops::member(&Value::Int(1), &v).unwrap());
    }
}
