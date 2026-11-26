//! Init / Next state enumeration, following TLC's algorithm
//! (tlc-semantics.md §5.2–5.3): conjuncts are processed left to right over a
//! partially assigned target state; `x' = e` / `x' \in S` / `x' \subseteq S`
//! with x' unassigned are assignments, everything else is a test.
//!
//! `go_inner` is the exhaustive state machine over expression kinds; the work
//! of each kind is carried by the continuation-responsibility helpers in the
//! child modules: `junction` (`\land`, `\lor` and `=>`), `binders` (`\E`,
//! `\A`, `IF/THEN/ELSE`, `CASE`, `LET` and a lazily represented function
//! applied), `calls` (an operator applied), `assign` (the assignment-shaped
//! built-ins), `enabled` (`UNCHANGED`, `[A]_e` and `<<A>>_e`) and `compose`
//! (`A \cdot B`).

mod assign;
mod binders;
mod calls;
mod compose;
mod enabled;
mod junction;

use std::rc::Rc;
use std::sync::Arc;

use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::*;
use tlx_value::Value;

use crate::env::Env;
use crate::error::{EResult, EvalError};
use crate::eval::{Ctx, DefCache, StateMemo};
use crate::interp::Interp;

/// The evaluation context over a partial target state `s1`: Init when there
/// is no current state, otherwise an action context memoizing over `s0`.
fn ctx_over<'b>(s0: Option<&'b [Value]>, level: u32, s1: &'b [Option<Value>], cache: &'b DefCache<'b>) -> Ctx<'b> {
    match s0 {
        None => Ctx::init(s1),
        Some(s0) => Ctx::action(s0, s1, level).with_cache(cache),
    }
}

/// A pending conjunct.
#[derive(Clone, Copy)]
enum Item<'c> {
    Expr(&'c Expr, &'c Env),
    /// From `<<A>>_e`: e must change.
    MustChange(&'c Expr, &'c Env),
    /// `UNCHANGED e` (an element of `UNCHANGED <<...>>`).
    Unchanged(&'c Expr, &'c Env),
}

/// Consecutive pending conjuncts of one kind.
#[derive(Clone, Copy)]
enum Seg<'c> {
    /// Conjuncts in one environment.
    Conj(&'c [Expr], &'c Env),
    /// One body in several environments (an expanded `\A`).
    Forall(&'c Expr, &'c [Env]),
    /// `UNCHANGED e` for each expression (`UNCHANGED <<...>>`).
    Unchanged(&'c [Expr], &'c Env),
    /// The same, last expression first.
    UnchangedRev(&'c [Expr], &'c Env),
    MustChange(&'c Expr, &'c Env),
}

impl<'c> Seg<'c> {
    /// The first conjunct and the rest of the segment (None when empty).
    fn split_first(self) -> Option<(Item<'c>, Option<Seg<'c>>)> {
        Some(match self {
            Seg::Conj(es, env) => {
                let (e, r) = es.split_first()?;
                (Item::Expr(e, env), Some(Seg::Conj(r, env)))
            }
            Seg::Forall(body, envs) => {
                let (env, r) = envs.split_first()?;
                (Item::Expr(body, env), Some(Seg::Forall(body, r)))
            }
            Seg::Unchanged(es, env) => {
                let (e, r) = es.split_first()?;
                (Item::Unchanged(e, env), Some(Seg::Unchanged(r, env)))
            }
            Seg::UnchangedRev(es, env) => {
                let (e, r) = es.split_last()?;
                (Item::Unchanged(e, env), Some(Seg::UnchangedRev(r, env)))
            }
            Seg::MustChange(e, env) => (Item::MustChange(e, env), None),
        })
    }
}

/// The continuation: the conjuncts still to process, next one first. It
/// lives on the stack, borrowing the expressions being enumerated.
#[derive(Clone, Copy, Default)]
struct Cont<'c> {
    seg: Option<Seg<'c>>,
    rest: Option<&'c Cont<'c>>,
}

impl<'c> Cont<'c> {
    /// `seg`, then `rest`.
    fn push(seg: Seg<'c>, rest: &'c Cont<'c>) -> Cont<'c> {
        Cont { seg: Some(seg), rest: Some(rest) }
    }

    /// The next conjunct and the continuation after it.
    fn next(&self) -> Option<(Item<'c>, Cont<'c>)> {
        let mut cur = *self;
        loop {
            if let Some((item, tail)) = cur.seg.and_then(Seg::split_first) {
                return Some((item, Cont { seg: tail, rest: cur.rest }));
            }
            cur = *cur.rest?;
        }
    }
}

/// Emits a complete target state; returns false to stop enumeration.
pub type Emit<'a> = dyn FnMut(&[Option<Value>]) -> EResult<bool> + 'a;

/// Enumeration from one current state (or of Init). The enumeration methods
/// return `Ok(false)` once `emit` asked to stop.
pub(crate) struct Enumerator<'a> {
    ip: &'a Arc<Interp>,
    /// Current state (None when enumerating Init).
    s0: Option<&'a [Value]>,
    /// Target state being built.
    s1: Vec<Option<Value>>,
    /// The variables of `s1` without a value.
    unassigned: usize,
    /// Level of `s0` (0 when enumerating Init).
    level: u32,
    emit: &'a mut Emit<'a>,
    /// Memo of state-level definitions over `s0` (unprimed reads only: the
    /// next state is partial).
    cache: Rc<DefCache<'static>>,
    /// Generation mode (TLC's `-generate`): alternatives are tried in a
    /// random order until the action has a successor (TLC's
    /// `Tool.probabilistic`; see `tlx_runtime::live::generating`).
    random: bool,
    /// Evaluating `ENABLED` (only whether there is a successor matters).
    enabled: bool,
    /// Enumerating the successors of a state for the search: the
    /// intermediate states of an action composition count as generated
    /// (TLC counts them only there: `nss.incrementStatesGenerated` is a
    /// no-op for the state vectors of nested compositions and of ENABLED).
    count_composed: bool,
    /// Complete assignments rejected by the conjuncts after them (see
    /// `cont_all_assigned`).
    rejected: u64,
}

thread_local! {
    /// Target-state buffers of finished enumerations, for the next ones
    /// (an enumeration per action and state).
    static TARGETS: std::cell::RefCell<Vec<Vec<Option<Value>>>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// A target state of `n` unassigned variables.
fn target_buffer(n: usize) -> Vec<Option<Value>> {
    let mut v = TARGETS.with(|t| t.borrow_mut().pop()).unwrap_or_default();
    v.clear();
    v.resize(n, None);
    v
}

impl Drop for Enumerator<'_> {
    fn drop(&mut self) {
        let mut v = std::mem::take(&mut self.s1);
        v.clear();
        TARGETS.with(|t| {
            let mut t = t.borrow_mut();
            if t.len() < 8 {
                t.push(v);
            }
        });
    }
}

impl<'a> Enumerator<'a> {
    pub(crate) fn new(ip: &'a Arc<Interp>, s0: Option<&'a [Value]>, level: u32, emit: &'a mut Emit<'a>) -> Enumerator<'a> {
        Enumerator::with_cache(ip, s0, level, emit, DefCache::unprimed())
    }

    /// An enumerator whose definition memo of `s0` is `cache` (only its
    /// unprimed part is used: the next state is partial).
    pub(crate) fn with_cache(
        ip: &'a Arc<Interp>,
        s0: Option<&'a [Value]>,
        level: u32,
        emit: &'a mut Emit<'a>,
        cache: DefCache<'static>,
    ) -> Enumerator<'a> {
        let n = ip.prog.vars.len();
        Enumerator {
            ip,
            s0,
            s1: target_buffer(n),
            unassigned: n,
            level,
            emit,
            cache: Rc::new(cache),
            random: false,
            enabled: false,
            count_composed: false,
            rejected: 0,
        }
    }

    /// Try the alternatives `alts` in a random order (generation mode) until
    /// one leaves the action with a successor.
    fn try_randomly<T>(&mut self, mut alts: Vec<T>, mut f: impl FnMut(&mut Self, T) -> EResult<bool>) -> EResult<bool> {
        while !alts.is_empty() {
            let x = alts.swap_remove(tlx_runtime::live::gen_below(alts.len()));
            if !f(self, x)? {
                return Ok(false);
            }
            if tlx_runtime::live::has_states() {
                break;
            }
        }
        Ok(true)
    }

    pub(crate) fn run(&mut self, e: &Expr, env: &Env) -> EResult<bool> {
        self.go(e, env, &Cont::default())
    }

    fn init(&self) -> bool {
        self.s0.is_none()
    }

    /// Evaluation context over the current partial target state.
    fn cx(&self) -> Ctx<'_> {
        ctx_over(self.s0, self.level, &self.s1, &self.cache)
    }

    fn eval(&self, e: &Expr, env: &Env) -> EResult<Value> {
        self.ip.eval(e, env, &self.cx())
    }

    fn eval_bool(&self, e: &Expr, env: &Env) -> EResult<bool> {
        self.ip.eval_bool(e, env, &self.cx())
    }

    /// `e' = e` over the current partial target state (Next only).
    fn is_unchanged(&self, e: &Expr, env: &Env) -> EResult<bool> {
        self.ip.unchanged(e, env, &Ctx::action(self.s0.unwrap(), &self.s1, self.level).with_cache(&self.cache))
    }

    /// Continue with the pending conjuncts `k`; emit when none is left.
    fn cont(&mut self, k: &Cont) -> EResult<bool> {
        let Some((item, rest)) = k.next() else {
            return (self.emit)(&self.s1);
        };
        // TLC (getNextStatesAllAssigned, and getInitStates for the initial
        // states): once every (primed) variable is assigned, the remaining
        // conjuncts are only evaluated as predicates, so later
        // disjunctions/existentials do not produce duplicates.
        if self.unassigned == 0 {
            return self.cont_all_assigned(item, rest);
        }
        match item {
            Item::Expr(e, env) => self.go(e, env, &rest),
            Item::Unchanged(e, env) => self.unchanged(e, env, &rest).map_err(|err| err.with_span(e.span)),
            Item::MustChange(e, env) => {
                if self.is_unchanged(e, env)? {
                    Ok(true)
                } else {
                    self.cont(&rest)
                }
            }
        }
    }

    /// The pending conjuncts (`item`, then `rest`) as predicates over the
    /// complete target state.
    fn cont_all_assigned(&mut self, item: Item, rest: Cont) -> EResult<bool> {
        let mut next = Some((item, rest));
        while let Some((item, rest)) = next {
            let ok = match item {
                Item::Expr(e, env) => self.eval_bool(e, env).map_err(|err| err.with_span(e.span))?,
                Item::MustChange(e, env) => !self.is_unchanged(e, env)?,
                Item::Unchanged(e, env) => self.is_unchanged(e, env).map_err(|err| err.with_span(e.span))?,
            };
            if !ok {
                // (TLC counts these for the coverage of Init.)
                self.rejected += 1;
                return Ok(true);
            }
            next = rest.next();
        }
        (self.emit)(&self.s1)
    }

    fn assign(&mut self, v: VarId, val: Value, k: &Cont) -> EResult<bool> {
        let old = self.s1[v.idx()].replace(val);
        let fresh = old.is_none();
        self.unassigned -= fresh as usize;
        let r = self.cont(k);
        self.s1[v.idx()] = old;
        self.unassigned += fresh as usize;
        r
    }

    /// Assign each of `vals` to `v` in turn (in generation mode: in a random
    /// order, until the action has a successor).
    fn assign_each(&mut self, v: VarId, vals: Vec<Value>, k: &Cont) -> EResult<bool> {
        if self.random {
            return self.try_randomly(vals, |en, x| en.assign(v, x, k));
        }
        for x in vals {
            if !self.assign(v, x, k)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// The variable `e` denotes syntactically (through call-by-name params and
    /// 0-ary definitions).
    fn var_of(&self, e: &Expr, env: &Env) -> Option<VarId> {
        match &*e.kind {
            ExprKind::Var(v) => Some(*v),
            // (Only in an ENABLED whose partial state has its slot.)
            ExprKind::InstVar { slot, .. } => Some(self.ip.inst_var(*slot)).filter(|v| v.idx() < self.s1.len()),
            ExprKind::Local(l) => match env.lookup(*l) {
                Some(b) if b.by_name(&self.ip.prog).is_some() => {
                    let (e, env) = b.by_name(&self.ip.prog).unwrap();
                    self.var_of(e, env)
                }
                _ => None,
            },
            ExprKind::Apply { op: OpRef::Def(d), args } if args.is_empty() => {
                let (_, body) = self.ip.plain_op_body(*d)?;
                self.var_of(body, env)
            }
            // TLC's getVar and getPrimedVar look through LET.
            ExprKind::Let { body, .. } => self.var_of(body, env),
            _ => None,
        }
    }

    /// The (bounds, body, environment) of a lazily represented function denoted
    /// syntactically by `f` (through 0-ary definitions and call-by-name params).
    fn lambda_of(&self, f: &Expr, env: &Env) -> Option<(Vec<Bound>, Expr, Env)> {
        match &*f.kind {
            ExprKind::FnConstruct { bounds, body } => Some((bounds.clone(), body.clone(), env.clone())),
            ExprKind::Local(l) => match env.lookup(*l) {
                Some(b) if b.by_name(&self.ip.prog).is_some() => {
                    let (e, env) = b.by_name(&self.ip.prog).unwrap();
                    self.lambda_of(e, env)
                }
                _ => None,
            },
            ExprKind::Apply { op: OpRef::Def(d), args } if args.is_empty() => {
                let ip = self.ip;
                let d = ip.redirect_def(*d);
                let def = &ip.prog.defs[d.idx()];
                if def.builtin.is_some() || ip.def_value.contains_key(&d) {
                    return None;
                }
                // TLC pre-evaluates constant definitions: a non-recursive constant
                // function over a plain set/interval is then an ordinary value.
                if ip.def_const[d.idx()] && !ip.is_recursive_fn(d) {
                    let ok_domain = match ip.call_def(d, env, &Ctx::NONE, f.span) {
                        Ok(Value::LazyFcn(_)) | Err(_) => false,
                        Ok(_) => true,
                    };
                    if ok_domain {
                        return None;
                    }
                }
                let base = ip.def_env(d, env);
                match &def.kind {
                    DefKind::Fn { bounds, body } => Some((bounds.clone(), body.clone(), base)),
                    DefKind::Op(body) => self.lambda_of(body, &base),
                    DefKind::Pending => None,
                }
            }
            _ => None,
        }
    }

    /// The variable being assigned by an `=` / `\in` / `\subseteq` left-hand side.
    fn target(&self, lhs: &Expr, env: &Env) -> Option<VarId> {
        if self.init() {
            return self.var_of(lhs, env);
        }
        match &*lhs.kind {
            ExprKind::Builtin { op: B::Prime, args } => self.var_of(&args[0], env),
            ExprKind::Local(l) => match env.lookup(*l) {
                Some(b) if b.by_name(&self.ip.prog).is_some() => {
                    let (e, env) = b.by_name(&self.ip.prog).unwrap();
                    self.target(e, env)
                }
                _ => None,
            },
            ExprKind::Apply { op: OpRef::Def(d), args } if args.is_empty() => {
                let (_, body) = self.ip.plain_op_body(*d)?;
                self.target(body, env)
            }
            ExprKind::Let { body, .. } => self.target(body, env),
            _ => None,
        }
    }

    /// The target variable of an assignment-shaped left-hand side, if it is
    /// not assigned yet (otherwise the conjunct is a test).
    fn unassigned_target(&self, lhs: &Expr, env: &Env) -> Option<VarId> {
        self.target(lhs, env).filter(|v| self.s1[v.idx()].is_none())
    }

    fn go(&mut self, e: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        self.go_inner(e, env, k).map_err(|err| err.with_span(e.span))
    }

    fn go_inner(&mut self, e: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        // TLC (getInitStates): once every variable is assigned, the remaining
        // conjuncts of Init are only evaluated as predicates, so disjunctions
        // and existentials there do not produce duplicate initial states.
        if self.init() && self.unassigned == 0 {
            return self.test(e, env, k);
        }
        match &*e.kind {
            ExprKind::Builtin { op: B::Compose, args } if !self.init() => self.compose(&args[0], &args[1], env, k),
            ExprKind::And(es) => self.conjunction(es, env, k),
            ExprKind::Or(es) if self.random => self.disjunction_random(es, env, k),
            ExprKind::Or(es) => self.disjunction(es, env, k),
            ExprKind::Quant { kind: QuantKind::Exists, bounds, body } => self.exists(bounds, body, env, k),
            ExprKind::Quant { kind: QuantKind::Forall, bounds, body } => self.forall(e, bounds, body, env, k),
            ExprKind::If { cond, then, els } => self.conditional(cond, then, els, env, k),
            ExprKind::Case { .. } if self.random => Err(EvalError::of_kind(
                tlx_runtime::ErrorKind::Unsupported,
                "Probabilistic evaluation of next-state relation not implemented for CASE yet.",
            )),
            ExprKind::Case { arms, other } => self.case_expr(arms, other, env, k),
            ExprKind::Let { defs, body } => self.let_expr(defs, body, env, k),
            ExprKind::FnApp { func, args } => self.fn_app(func, args, e, env, k),
            ExprKind::Apply { op: OpRef::Const(c), args } => self.apply_const(c, args, e, env, k),
            ExprKind::Apply { op: OpRef::Param(l), args } => self.apply_param(l, args, e, env, k),
            ExprKind::Apply { op: OpRef::Def(d), args } => self.go_call(*d, args, e, env, k),
            ExprKind::Apply { op: OpRef::Builtin(b), args } => self.go_builtin(*b, args, e, env, k),
            ExprKind::Local(l) => self.local_expr(l, e, env, k),
            ExprKind::Builtin { op: B::Eq, args } => self.assign_eq(args, e, env, k),
            ExprKind::Builtin { op: B::In, args } => self.assign_in(args, e, env, k),
            ExprKind::Builtin { op: B::SubsetEq, args } => self.assign_subseteq(args, e, env, k),
            ExprKind::Builtin { op: B::Unchanged, args } if !self.init() => self.unchanged(&args[0], env, k),
            ExprKind::Builtin { op: B::Implies, args } => self.implies(args, env, k),
            ExprKind::BoxAction { action, sub } if !self.init() => self.box_action(action, sub, env, k),
            ExprKind::AngleAction { action, sub } if !self.init() => self.angle_action(action, sub, env, k),
            _ => self.test(e, env, k),
        }
    }

    /// Evaluate `e` as a condition; continue if true.
    fn test(&mut self, e: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        if self.eval_bool(e, env)? {
            self.cont(k)
        } else {
            Ok(true)
        }
    }
}

// ----------------------------------------------------------------------
// action splitting (TLC getActions, tlc-semantics.md §5.1)

/// An action of the next-state relation, as TLC splits it
/// (Tool.getActions): the maximal prefix of disjunctions, existentials over
/// constant sets and definitions applied to constant arguments.
#[derive(Clone)]
pub struct Action {
    /// TLC's name: the definition the action was expanded from or that it
    /// applies (`Action` for an expression not from a definition).
    pub name: Arc<str>,
    pub expr: Expr,
    pub env: Env,
    /// The operator the action was expanded from (its parameters are bound
    /// in `env`, for TLC's trace labels like `A(1)`), or that it applies to
    /// arguments that are not constant.
    pub def: Option<DefId>,
    /// TLC's location of the action when it is not that of `expr`: the
    /// INSTANCE statement, for an action under its substitutions (TLC's
    /// `SubstInNode`, which TLC does not split).
    pub at: Option<Span>,
}

impl Action {
    /// The location TLC reports for the action (its predicate).
    pub fn span(&self) -> Span {
        self.at.unwrap_or(self.expr.span)
    }
}

impl Interp {
    /// Split the next-state relation into actions as TLC does
    /// (Tool.getActions; does not change the set of successors, only their
    /// grouping and order). `within`: the next-state relation is under the
    /// substitutions of the INSTANCE statement at this location (a
    /// SPECIFICATION from an instance), so it is one action.
    pub fn split_actions(self: &Arc<Self>, next: &Expr, within: Option<Span>) -> Vec<Action> {
        let mut out = Vec::new();
        match within {
            Some(at) => out.push(Action { name: "Action".into(), expr: next.clone(), env: Env::default(), def: None, at: Some(at) }),
            None => self.split(next, &Env::default(), "Action".into(), None, &mut out),
        }
        out
    }

    fn split(self: &Arc<Self>, e: &Expr, env: &Env, name: Arc<str>, def: Option<DefId>, out: &mut Vec<Action>) {
        let leaf = |out: &mut Vec<Action>, name, def| out.push(Action { name, expr: e.clone(), env: env.clone(), def, at: None });
        match &*e.kind {
            ExprKind::Or(es) => {
                for c in es {
                    self.split(c, env, name.clone(), def, out);
                }
            }
            ExprKind::Let { body, .. } => self.split(body, env, name, def, out),
            ExprKind::Quant { kind: QuantKind::Exists, bounds, body } => match self.collect_split_bindings(bounds, env) {
                // (TLC keeps an existential over an empty or non-materializable
                // set as a single unsplit action.)
                Some(envs) if !envs.is_empty() => {
                    for env2 in envs {
                        self.split(body, &env2, name.clone(), def, out);
                    }
                }
                _ => leaf(out, name, def),
            },
            ExprKind::Apply { op: OpRef::Def(d), args } => match self.expand_for_split(*d, args, env) {
                Some((def_name, body, env2)) => {
                    let d2 = self.redirect_def(*d);
                    match self.prog.def_instance(d2) {
                        // The body of an instance's definition seen from
                        // outside the instance is under its substitutions
                        // (TLC's SubstInNode, located at the INSTANCE
                        // statement), which TLC does not split.
                        Some((_, at)) => out.push(Action {
                            name: self.prog.def_qualified_name(d2),
                            expr: body.clone(),
                            env: env2,
                            def: Some(d2),
                            at: Some(at),
                        }),
                        None => self.split(body, &env2, def_name, Some(d2), out),
                    }
                }
                // An operator applied to arguments that are not constant (or
                // a definition TLC evaluates to a value): TLC names the
                // action after the operator (Tool.getActionsAppl).
                None => leaf(out, self.prog.def_qualified_name(*d), Some(*d)),
            },
            _ => leaf(out, name, def),
        }
    }

    /// The name, body and environment of a call of user operator `d` that
    /// action splitting looks through: only if all arguments are constant-level.
    pub(crate) fn expand_for_split(self: &Arc<Self>, d: DefId, args: &[Expr], env: &Env) -> Option<(Arc<str>, &Expr, Env)> {
        let d = self.redirect_def(d);
        let def = &self.prog.defs[d.idx()];
        if def.builtin.is_some() || self.def_value.contains_key(&d) || self.def_const[d.idx()] {
            return None;
        }
        let DefKind::Op(body) = &def.kind else {
            return None;
        };
        let env2 = self.bind_params(&def.params, args, env, &Ctx::NONE, self.def_env(d, env), false, false).ok()?;
        Some((def.name.clone(), body, env2))
    }

    /// Enumerate the states satisfying `init`.
    pub fn init_states(self: &Arc<Self>, init: &Expr, emit: &mut Emit<'_>) -> EResult<()> {
        Interp::begin_random_scope();
        let mut en = Enumerator::new(self, None, 0, emit);
        let r = en.run(init, &Env::default());
        self.init_rejected.store(en.rejected, std::sync::atomic::Ordering::Relaxed);
        r?;
        Ok(())
    }

    /// Enumerate the successors of `s` (at BFS `level`) under `action`.
    pub fn successors(self: &Arc<Self>, s: &[Value], level: u32, action: &Action, emit: &mut Emit<'_>) -> EResult<bool> {
        self.successors_memo(s, level, action, Default::default(), emit)
    }

    /// `successors`, memoizing state-level definitions of `s` in `memo`.
    pub(crate) fn successors_memo(
        self: &Arc<Self>,
        s: &[Value],
        level: u32,
        action: &Action,
        memo: Rc<StateMemo>,
        emit: &mut Emit<'_>,
    ) -> EResult<bool> {
        Interp::begin_random_scope();
        let mut en = Enumerator::with_cache(self, Some(s), level, emit, DefCache::over(memo, None));
        en.random = tlx_runtime::live::generating();
        en.count_composed = true;
        en.run(&action.expr, &action.env)
    }

    /// An enumerator of the successors of `s` (at BFS `level`) under one
    /// action after another (`ActionRunner::run`; the same as
    /// `successors_memo` per action, set up once per state).
    pub(crate) fn action_runner<'a>(
        self: &'a Arc<Self>,
        s: &'a [Value],
        level: u32,
        memo: Rc<StateMemo>,
        emit: &'a mut Emit<'a>,
    ) -> ActionRunner<'a> {
        let mut en = Enumerator::with_cache(self, Some(s), level, emit, DefCache::over(memo, None));
        en.count_composed = true;
        ActionRunner { en }
    }

    /// `ENABLED A` in state `s0`.
    pub(crate) fn enabled(self: &Arc<Self>, a: &Expr, env: &Env, cx: &Ctx) -> EResult<bool> {
        // In Init, the current state is the initial state being built, as
        // in TLC (Tool.getInitStates evaluates with s0 = the partial state).
        let init_state: Vec<Value>;
        let s0 = match (cx.s0, cx.s1) {
            (Some(s0), _) => s0,
            (None, Some(s1)) if cx.init && s1.iter().all(Option::is_some) => {
                init_state = s1.iter().map(|v| v.clone().unwrap()).collect();
                &init_state
            }
            _ => return Err(EvalError::new("ENABLED evaluated without a current state")),
        };
        let mut found = false;
        let mut emit = |_: &[Option<Value>]| {
            found = true;
            Ok(false)
        };
        // The memo of the current state carries over (unless this is a
        // primed or Init context, where it is not the memo of `s0`).
        let cache = match cx.cache {
            Some(c) if !cx.primed && !cx.init => DefCache::over(c.current(), None),
            _ => DefCache::unprimed(),
        };
        let mut en = Enumerator::with_cache(self, Some(s0), cx.level, &mut emit, cache);
        en.enabled = true;
        // The variables of instantiated modules ENABLED quantifies over
        // (`ExprKind::InstVar`) follow the state variables.
        en.s1.resize(self.prog.vars.len() + self.prog.inst_vars.len(), None);
        en.unassigned = en.s1.iter().filter(|v| v.is_none()).count();
        let r = en.run(a, env);
        drop(en);
        r?;
        Ok(found)
    }
}

/// See `Interp::action_runner`.
pub(crate) struct ActionRunner<'a> {
    en: Enumerator<'a>,
}

impl ActionRunner<'_> {
    /// `successors_memo` of `action`.
    pub(crate) fn run(&mut self, action: &Action) -> EResult<bool> {
        Interp::begin_random_scope();
        let en = &mut self.en;
        en.s1.iter_mut().for_each(|v| *v = None);
        en.unassigned = en.s1.len();
        en.random = tlx_runtime::live::generating();
        en.run(&action.expr, &action.env)
    }
}

/// The intermediate states of an action composition `A \cdot B` from
/// `s0`: the successors of A (`e`), each variable A leaves undetermined
/// with its value in `s0`.
pub(crate) fn composition_mids(ip: &Arc<Interp>, s0: &[Value], level: u32, e: &Expr, env: &Env) -> EResult<Vec<Vec<Value>>> {
    composition_mids_for(ip, s0, level, e, env, false)
}

pub(super) fn composition_mids_for(
    ip: &Arc<Interp>,
    s0: &[Value],
    level: u32,
    e: &Expr,
    env: &Env,
    enabled: bool,
) -> EResult<Vec<Vec<Value>>> {
    let succ = partial_successors_for(ip, s0, level, e, env, usize::MAX, enabled)?.unwrap_or_default();
    Ok(succ.into_iter().map(|t| t.into_iter().zip(s0).map(|(v, old)| v.unwrap_or_else(|| old.clone())).collect()).collect())
}

/// The successor states of `s0` under action expression `e`, with None
/// for the variables `e` leaves undetermined (it does not mention them
/// primed), or None as soon as there are more than `max` of them.
pub(crate) fn partial_successors_at_most(
    ip: &Arc<Interp>,
    s0: &[Value],
    level: u32,
    e: &Expr,
    env: &Env,
    max: usize,
) -> EResult<Option<Vec<Vec<Option<Value>>>>> {
    partial_successors_for(ip, s0, level, e, env, max, false)
}

pub(super) fn partial_successors_for(
    ip: &Arc<Interp>,
    s0: &[Value],
    level: u32,
    e: &Expr,
    env: &Env,
    max: usize,
    enabled: bool,
) -> EResult<Option<Vec<Vec<Option<Value>>>>> {
    let mut out = Vec::new();
    let mut over = false;
    {
        let mut emit = |s1: &[Option<Value>]| -> EResult<bool> {
            if out.len() == max {
                over = true;
                return Ok(false);
            }
            out.push(s1.to_vec());
            Ok(true)
        };
        let mut en = Enumerator::new(ip, Some(s0), level, &mut emit);
        if enabled {
            en.enabled = true;
            en.s1.resize(ip.prog.vars.len() + ip.prog.inst_vars.len(), None);
            en.unassigned = en.s1.len();
        }
        en.run(e, env)?;
    }
    Ok((!over).then_some(out))
}
