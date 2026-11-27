//! Set filters over powersets (`{E \in SUBSET B : P(E)}`) pruned by
//! element-level, membership, subset, and cardinality constraints.
//!
//! `{E \in SUBSET B : \A e \in E : Q(e)}` otherwise enumerates all `2^|B|`
//! subsets of `B` even when only a small subset `B' = {b \in B : Q(b)}` can
//! contribute elements (for example `SpanTreeTest5Nodes`, where
//! `|SUBSET Nodes| = 32` gives `2^32` subsets while only 10 two-element edges
//! satisfy `Cardinality(e) = 2`, leaving `2^10 = 1,024` subsets).
//!
//! Soundness and TLC error preservation:
//! - Constraints are extracted strictly left-to-right from the leading prefix
//!   of top-level conjuncts (peeling pure single-argument aliases of `E`).
//! - Every extracted constraint must be effect-free and must succeed without
//!   error across the entire current candidate domain (for example, probing
//!   `Q(b)` on every currently reachable element `b` and requiring `Ok(Bool)`
//!   on all of them). If any probe errors or encounters an unsupported value,
//!   extraction stops immediately: if no prefix constraint applied yet, the
//!   filter falls back to unpruned `SUBSET` streaming; otherwise the failing
//!   conjunct and all later conjuncts remain as residuals evaluated in exact
//!   left-to-right order on every surviving subset.
//! - Once the candidate space becomes empty, later prefix conjuncts are not
//!   evaluated (preserving TLC `/\` short-circuiting).
//! - Surviving subsets are streamed through `ops::for_each_constrained_subset`,
//!   which preserves TLC's exact `SUBSET` enumeration order (increasing
//!   cardinality, then lexicographic by base index).

use std::collections::HashSet;
use std::sync::Arc;

use tlx_front::ast::QuantKind;
use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{BoundVars, DefId, DefKind, Expr, ExprKind as H, LocalId, OpRef};
use tlx_value::{ops, order, LazySet, Value, ValueError};

use crate::env::Env;
use crate::error::EvalError;
use crate::eval::Ctx;
use crate::interp::Interp;

/// Maximum base size for per-element constraint probing (`\A e \in E : Q(e)`,
/// `E \subseteq T`, membership comparability). Keeps up-front probing bounded
/// when a caller may stop early on a huge base set.
const MAX_PROBE_BASE: usize = 4096;

/// Maximum depth when peeling pure top-level operator aliases.
const MAX_EXPAND: usize = 8;

/// Maximum depth when scanning a captured value for lazy callables that could
/// hide side effects.
const MAX_VALUE_SCAN_DEPTH: usize = 8;

fn verr(e: EvalError) -> ValueError {
    e.into()
}

/// Compiled leading-prefix plan for filtering `SUBSET B` with bound variable `var`.
pub(crate) struct SubsetPred {
    var: LocalId,
    steps: Vec<Step>,
}

enum Step {
    /// Record an alias local (parameter of an expanded pure 1-arg operator)
    /// that binds to the same subset `E` when evaluating residual conjuncts.
    BindAlias(LocalId),
    /// A recognized leading constraint together with its original conjunct
    /// expression (used verbatim if runtime probing falls back to residual).
    Constraint { kind: Constraint, expr: Expr },
    /// An unrecognized conjunct evaluated verbatim on every surviving subset.
    Residual(Expr),
}

#[derive(Clone, Copy)]
enum CardOp {
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
}

impl CardOp {
    fn flip(self) -> Self {
        match self {
            CardOp::Eq => CardOp::Eq,
            CardOp::Neq => CardOp::Neq,
            CardOp::Lt => CardOp::Gt,
            CardOp::Le => CardOp::Ge,
            CardOp::Gt => CardOp::Lt,
            CardOp::Ge => CardOp::Le,
        }
    }
}

enum Constraint {
    /// `\A v \in E : body` (`negate = false`) or `~(\E v \in E : body)` (`negate = true`).
    ForallElem { vars: BoundVars, body: Expr, negate: bool },
    /// `E \subseteq rhs`.
    SubsetUpper { rhs: Expr },
    /// `lhs \subseteq E`.
    SubsetLower { lhs: Expr },
    /// `elem \in E` (`required = true`) or `elem \notin E` / `~(elem \in E)` (`required = false`).
    ElemMem { elem: Expr, required: bool },
    /// `E \cap other = {}` (`var_on_left = true`) or `other \cap E = {}` (`var_on_left = false`).
    Disjoint { other: Expr, var_on_left: bool },
    /// `Cardinality(E) <op> rhs`.
    CardCmp { op: CardOp, rhs: Expr },
    /// `Cardinality(E) \in set`.
    CardIn { set: Expr },
    /// `E = {}` (`empty = true`) or `E /= {}` (`empty = false`).
    EmptyCmp { empty: bool },
}

/// Narrowed subset search space `(required, optional, min_card..=max_card)`.
struct CandidateState {
    required: Vec<usize>,
    optional: Vec<usize>,
    min_card: usize,
    max_card: usize,
}

impl CandidateState {
    fn new(base_len: usize) -> Self {
        Self { required: Vec::new(), optional: (0..base_len).collect(), min_card: 0, max_card: base_len }
    }

    fn is_empty(&self) -> bool {
        self.min_card > self.max_card || self.max_card < self.required.len() || self.min_card > self.max_possible_card()
    }

    fn max_possible_card(&self) -> usize {
        self.required.len() + self.optional.len()
    }

    /// Tighten invariants: if `max_card == required.len()`, no optional element
    /// can ever be chosen; if `min_card == max_possible_card()`, every optional
    /// element must be chosen.
    fn canonicalize(&mut self) {
        if self.is_empty() {
            self.min_card = 1;
            self.max_card = 0;
            self.required.clear();
            self.optional.clear();
            return;
        }
        self.min_card = self.min_card.max(self.required.len());
        self.max_card = self.max_card.min(self.max_possible_card());
        if self.max_card == self.required.len() {
            self.optional.clear();
        } else if self.min_card == self.max_possible_card() && !self.optional.is_empty() {
            let mut merged = Vec::with_capacity(self.required.len() + self.optional.len());
            let (mut ri, mut oi) = (0, 0);
            while ri < self.required.len() && oi < self.optional.len() {
                if self.required[ri] < self.optional[oi] {
                    merged.push(self.required[ri]);
                    ri += 1;
                } else {
                    merged.push(self.optional[oi]);
                    oi += 1;
                }
            }
            merged.extend_from_slice(&self.required[ri..]);
            merged.extend_from_slice(&self.optional[oi..]);
            self.required = merged;
            self.optional.clear();
        }
    }

    fn mark_empty(&mut self) {
        self.min_card = 1;
        self.max_card = 0;
        self.required.clear();
        self.optional.clear();
    }

    /// Require base index `idx` to appear in every candidate subset.
    fn require_index(&mut self, idx: usize) {
        if self.required.binary_search(&idx).is_ok() {
            return;
        }
        match self.optional.binary_search(&idx) {
            Ok(opt_pos) => {
                self.optional.remove(opt_pos);
                let req_pos = self.required.partition_point(|&r| r < idx);
                self.required.insert(req_pos, idx);
            }
            Err(_) => self.mark_empty(),
        }
    }

    /// Forbid base index `idx` from appearing in any candidate subset.
    fn forbid_index(&mut self, idx: usize) {
        if self.required.binary_search(&idx).is_ok() {
            self.mark_empty();
            return;
        }
        if let Ok(pos) = self.optional.binary_search(&idx) {
            self.optional.remove(pos);
        }
    }
}

enum Applied {
    /// Constraint proved total/error-free on the current candidate space and
    /// completely enforced by the updated `CandidateState`.
    Consumed,
    /// Constraint tightened `CandidateState` soundly (error-free on the current
    /// space), but must still be checked on surviving subsets (e.g. non-contiguous
    /// `Cardinality(E) \in {1, 3}`).
    TightenedKeepResidual,
    /// Constraint could not be safely applied (error on probe, non-int, large
    /// base, or incomparable element): stop prefix extraction and keep as residual.
    Stop,
}

impl SubsetPred {
    /// Compile `pred` (in `env`) for a filter `{E \in SUBSET B : pred}` if at
    /// least one leading conjunct can be pruned structurally.
    pub(crate) fn compile(ip: &Interp, vars: &BoundVars, pred: &Expr, env: &Env) -> Option<SubsetPred> {
        let BoundVars::Many(ls) = vars else { return None };
        let [var] = ls.as_slice() else { return None };
        let mut steps = Vec::new();
        let mut has_constraint = false;
        collect_steps(ip, pred, *var, env, 0, &mut steps, &mut has_constraint);
        has_constraint.then_some(SubsetPred { var: *var, steps })
    }

    /// Stream filtered subsets of `base` in TLC's `SUBSET` order. Returns
    /// `Ok(None)` if no leading constraint could be applied at runtime (caller
    /// falls back to unpruned `SUBSET` streaming), else `Ok(Some(completed))`.
    pub(crate) fn filter(
        &self,
        ip: &Arc<Interp>,
        env: &Env,
        cx: &Ctx,
        base: &ops::SubsetBase<'_>,
        visit: &mut dyn FnMut(Value, Option<bool>) -> tlx_value::Result<bool>,
    ) -> tlx_value::Result<Option<bool>> {
        // Candidate index storage and up-front probing must stay bounded
        // even when a consumer stops after the first surviving subset.
        if base.len() > MAX_PROBE_BASE {
            return Ok(None);
        }
        let mut aliases: Vec<LocalId> = vec![self.var];
        let mut state = CandidateState::new(base.len());
        let mut applied = 0usize;
        let mut stop_idx = self.steps.len();

        for (i, step) in self.steps.iter().enumerate() {
            match step {
                Step::BindAlias(alias) => {
                    if !aliases.contains(alias) {
                        aliases.push(*alias);
                    }
                }
                Step::Constraint { kind, .. } => {
                    match apply_constraint(kind, ip, env, cx, base, &mut state) {
                        Applied::Consumed => {
                            applied += 1;
                            state.canonicalize();
                            if state.is_empty() {
                                // Earlier prefix conjunct already proved the set empty
                                // without error: short-circuit before evaluating any
                                // later conjuncts.
                                return Ok(Some(true));
                            }
                        }
                        Applied::TightenedKeepResidual => {
                            applied += 1;
                            state.canonicalize();
                            if state.is_empty() {
                                return Ok(Some(true));
                            }
                            stop_idx = i;
                            break;
                        }
                        Applied::Stop => {
                            stop_idx = i;
                            break;
                        }
                    }
                }
                Step::Residual(_) => {
                    stop_idx = i;
                    break;
                }
            }
        }

        if applied == 0 {
            return Ok(None);
        }
        if state.is_empty() {
            return Ok(Some(true));
        }

        let remaining = &self.steps[stop_idx..];
        let done =
            ops::for_each_constrained_subset(base, &state.required, &state.optional, state.min_card, state.max_card, &mut |subset| {
                if remaining.is_empty() || eval_remaining(remaining, &subset, env, &aliases, ip, cx).map_err(verr)? {
                    visit(subset, Some(true))
                } else {
                    Ok(true)
                }
            })?;
        Ok(Some(done))
    }
}

/// Evaluate remaining steps (`steps[stop_idx..]`) left-to-right for one
/// surviving subset `E`, short-circuiting on `false`.
fn eval_remaining(
    steps: &[Step],
    subset: &Value,
    base_env: &Env,
    aliases: &[LocalId],
    ip: &Arc<Interp>,
    cx: &Ctx,
) -> crate::error::EResult<bool> {
    let mut env = base_env.clone();
    for &id in aliases {
        env = env.bind_val(id, subset.clone());
    }
    for step in steps {
        match step {
            Step::BindAlias(alias) => {
                env = env.bind_val(*alias, subset.clone());
            }
            Step::Constraint { expr, .. } | Step::Residual(expr) => {
                if !ip.eval_bool(expr, &env, cx)? {
                    return Ok(false);
                }
            }
        }
    }
    Ok(true)
}

/// Flatten leading conjuncts of `e` into `steps`. Stops recognizing constraints
/// once an unrecognized conjunct is encountered (recording it and all subsequent
/// conjuncts as `Step::Residual`), preserving exact left-to-right order.
fn collect_steps(ip: &Interp, e: &Expr, target: LocalId, env: &Env, depth: usize, steps: &mut Vec<Step>, has_constraint: &mut bool) {
    // Once a residual has appeared, stop flattening/peeling so later
    // constraints can never be reordered ahead of it and recursive/complex
    // residuals are left intact.
    if steps.iter().any(|s| matches!(s, Step::Residual(_))) {
        steps.push(Step::Residual(e.clone()));
        return;
    }

    match &*e.kind {
        H::And(es) => {
            for c in es {
                collect_steps(ip, c, target, env, depth, steps, has_constraint);
            }
            return;
        }
        H::Apply { op: OpRef::Def(d), args } if depth < MAX_EXPAND && args.len() == 1 && is_target_var(&args[0], target) => {
            if let Some((rd, body)) = ip.plain_op_body(*d) {
                let def = &ip.prog.defs[rd.idx()];
                if !ip.prog.def_is_let(rd) && !ip.def_effectful(rd) && !ip.is_recursive(rd) && def.params.len() == 1 {
                    let param = def.params[0];
                    steps.push(Step::BindAlias(param));
                    collect_steps(ip, body, param, &Env::default(), depth + 1, steps, has_constraint);
                    return;
                }
            }
        }
        _ => {}
    }

    if let Some(kind) = recognize_constraint(ip, e, target, env) {
        *has_constraint = true;
        steps.push(Step::Constraint { kind, expr: e.clone() });
    } else {
        steps.push(Step::Residual(e.clone()));
    }
}

fn is_target_var(e: &Expr, target: LocalId) -> bool {
    matches!(&*e.kind, H::Local(l) if *l == target)
}

fn is_empty_set_literal(e: &Expr) -> bool {
    matches!(&*e.kind, H::SetEnum(es) if es.is_empty())
}

fn is_cardinality_of(ip: &Interp, e: &Expr, target: LocalId) -> bool {
    if ip.builtin_override(B::Cardinality).is_some() {
        return false;
    }
    match &*e.kind {
        H::Builtin { op: B::Cardinality, args } | H::Apply { op: OpRef::Builtin(B::Cardinality), args } => {
            args.len() == 1 && is_target_var(&args[0], target)
        }
        H::Apply { op: OpRef::Def(d), args } if args.len() == 1 && is_target_var(&args[0], target) => {
            let rd = ip.redirect_def(*d);
            !ip.def_value.contains_key(&rd) && ip.prog.defs[rd.idx()].builtin == Some(B::Cardinality)
        }
        _ => false,
    }
}

fn builtin_op<'a>(ip: &Interp, e: &'a Expr) -> Option<(B, &'a [Expr])> {
    match &*e.kind {
        H::Builtin { op, args } | H::Apply { op: OpRef::Builtin(op), args } if ip.builtin_override(*op).is_none() => {
            Some((*op, args.as_slice()))
        }
        H::Apply { op: OpRef::Def(d), args } => {
            let rd = ip.redirect_def(*d);
            if ip.def_value.contains_key(&rd) {
                return None;
            }
            let op = ip.prog.defs[rd.idx()].builtin?;
            ip.builtin_override(op).is_none().then_some((op, args.as_slice()))
        }
        _ => None,
    }
}

/// Whether `e` is effect-free and does not depend on `target`.
fn is_pure_independent(ip: &Interp, e: &Expr, target: LocalId, env: &Env) -> bool {
    ip.is_effect_free_in(e, env) && !expr_mentions_local(ip, e, target, env, &mut HashSet::new())
}

fn recognize_constraint(ip: &Interp, e: &Expr, target: LocalId, env: &Env) -> Option<Constraint> {
    // `\A v \in E : Q(v)`
    if let H::Quant { kind: QuantKind::Forall, bounds, body } = &*e.kind {
        if let [b] = bounds.as_slice() {
            if is_target_var(&b.set, target) && is_single_elem_binder(&b.vars) && is_pure_independent(ip, body, target, env) {
                return Some(Constraint::ForallElem { vars: b.vars.clone(), body: body.clone(), negate: false });
            }
        }
    }

    let (op, args) = builtin_op(ip, e)?;
    match (op, args) {
        // `~(...)`: negated existential, negated membership, or `~(E = {})`.
        (B::Not, [inner]) => {
            if let H::Quant { kind: QuantKind::Exists, bounds, body } = &*inner.kind {
                if let [b] = bounds.as_slice() {
                    if is_target_var(&b.set, target) && is_single_elem_binder(&b.vars) && is_pure_independent(ip, body, target, env) {
                        return Some(Constraint::ForallElem { vars: b.vars.clone(), body: body.clone(), negate: true });
                    }
                }
            }
            if let Some((iop, iargs)) = builtin_op(ip, inner) {
                match (iop, iargs) {
                    (B::In, [elem, set]) if is_target_var(set, target) && is_pure_independent(ip, elem, target, env) => {
                        return Some(Constraint::ElemMem { elem: elem.clone(), required: false });
                    }
                    (B::NotIn, [elem, set]) if is_target_var(set, target) && is_pure_independent(ip, elem, target, env) => {
                        return Some(Constraint::ElemMem { elem: elem.clone(), required: true });
                    }
                    (B::Eq, [a, b])
                        if (is_target_var(a, target) && is_empty_set_literal(b))
                            || (is_target_var(b, target) && is_empty_set_literal(a)) =>
                    {
                        return Some(Constraint::EmptyCmp { empty: false });
                    }
                    _ => {}
                }
            }
            None
        }
        // `E \subseteq T` or `T \subseteq E`
        (B::SubsetEq, [lhs, rhs]) => {
            if is_target_var(lhs, target) && is_pure_independent(ip, rhs, target, env) {
                Some(Constraint::SubsetUpper { rhs: rhs.clone() })
            } else if is_target_var(rhs, target) && is_pure_independent(ip, lhs, target, env) {
                Some(Constraint::SubsetLower { lhs: lhs.clone() })
            } else {
                None
            }
        }
        // `x \in E`, `x \notin E`, `Cardinality(E) \in S`
        (B::In, [lhs, rhs]) => {
            if is_target_var(rhs, target) && is_pure_independent(ip, lhs, target, env) {
                Some(Constraint::ElemMem { elem: lhs.clone(), required: true })
            } else if is_cardinality_of(ip, lhs, target) && is_pure_independent(ip, rhs, target, env) {
                Some(Constraint::CardIn { set: rhs.clone() })
            } else {
                None
            }
        }
        (B::NotIn, [lhs, rhs]) if is_target_var(rhs, target) && is_pure_independent(ip, lhs, target, env) => {
            Some(Constraint::ElemMem { elem: lhs.clone(), required: false })
        }
        // `E = {}`, `E /= {}`, `E \cap T = {}`, `Cardinality(E) <cmp> k`
        (B::Eq | B::Neq | B::Lt | B::Le | B::Gt | B::Ge, [lhs, rhs]) => {
            let cmp = match op {
                B::Eq => CardOp::Eq,
                B::Neq => CardOp::Neq,
                B::Lt => CardOp::Lt,
                B::Le => CardOp::Le,
                B::Gt => CardOp::Gt,
                B::Ge => CardOp::Ge,
                _ => unreachable!(),
            };
            if matches!(op, B::Eq | B::Neq) {
                if (is_target_var(lhs, target) && is_empty_set_literal(rhs)) || (is_target_var(rhs, target) && is_empty_set_literal(lhs)) {
                    return Some(Constraint::EmptyCmp { empty: op == B::Eq });
                }
                if op == B::Eq {
                    let cap_side = if is_empty_set_literal(rhs) {
                        Some(lhs)
                    } else if is_empty_set_literal(lhs) {
                        Some(rhs)
                    } else {
                        None
                    };
                    if let Some(cap_expr) = cap_side {
                        if let Some((B::Cap, [a, b])) = builtin_op(ip, cap_expr) {
                            if is_target_var(a, target) && is_pure_independent(ip, b, target, env) {
                                return Some(Constraint::Disjoint { other: b.clone(), var_on_left: true });
                            }
                            if is_target_var(b, target) && is_pure_independent(ip, a, target, env) {
                                return Some(Constraint::Disjoint { other: a.clone(), var_on_left: false });
                            }
                        }
                    }
                }
            }
            if is_cardinality_of(ip, lhs, target) && is_pure_independent(ip, rhs, target, env) {
                Some(Constraint::CardCmp { op: cmp, rhs: rhs.clone() })
            } else if is_cardinality_of(ip, rhs, target) && is_pure_independent(ip, lhs, target, env) {
                Some(Constraint::CardCmp { op: cmp.flip(), rhs: lhs.clone() })
            } else {
                None
            }
        }
        _ => None,
    }
}

fn is_single_elem_binder(vars: &BoundVars) -> bool {
    match vars {
        BoundVars::Many(ls) => ls.len() == 1,
        BoundVars::Tuple(_) => true,
    }
}

/// Whether `e` mentions `target`, following by-name bindings and `LET` bodies.
fn expr_mentions_local(ip: &Interp, e: &Expr, target: LocalId, env: &Env, seen_defs: &mut HashSet<DefId>) -> bool {
    match &*e.kind {
        H::Local(l) => {
            if *l == target {
                return true;
            }
            if let Some(b) = env.lookup(*l) {
                if let Some((a, aenv)) = b.by_name(&ip.prog) {
                    return expr_mentions_local(ip, a, target, aenv, seen_defs);
                }
            }
            false
        }
        H::Let { defs, body } => {
            defs.iter().any(|&d| def_mentions_local(ip, d, target, env, seen_defs)) || expr_mentions_local(ip, body, target, env, seen_defs)
        }
        H::Apply { op: OpRef::Def(d), args } if ip.prog.def_is_let(*d) => {
            def_mentions_local(ip, *d, target, env, seen_defs) || args.iter().any(|a| expr_mentions_local(ip, a, target, env, seen_defs))
        }
        H::OpArg(OpRef::Def(d)) if ip.prog.def_is_let(*d) => def_mentions_local(ip, *d, target, env, seen_defs),
        _ => {
            let mut found = false;
            tlx_sema::visit::children(e, &mut |c| {
                if !found {
                    found = expr_mentions_local(ip, c, target, env, seen_defs);
                }
            });
            found
        }
    }
}

fn def_mentions_local(ip: &Interp, d: DefId, target: LocalId, env: &Env, seen_defs: &mut HashSet<DefId>) -> bool {
    if !seen_defs.insert(d) {
        return false;
    }
    match &ip.prog.defs[d.idx()].kind {
        DefKind::Op(body) => expr_mentions_local(ip, body, target, env, seen_defs),
        DefKind::Fn { bounds, body } => {
            bounds.iter().any(|b| expr_mentions_local(ip, &b.set, target, env, seen_defs))
                || expr_mentions_local(ip, body, target, env, seen_defs)
        }
        DefKind::Pending => true,
    }
}

/// Conservative check that `e` does not read a runtime value containing a
/// `LazyFcn` or `LazySet::Custom` (which could wrap an effectful expression).
fn expr_reads_lazy_callable(ip: &Interp, e: &Expr, env: &Env, cx: &Ctx) -> bool {
    let here = match &*e.kind {
        H::Local(l) => match env.lookup(*l) {
            Some(crate::env::Binding::Val(v)) => value_has_lazy_callable(v, 0),
            Some(b) => b.by_name(&ip.prog).is_some_and(|(a, aenv)| expr_reads_lazy_callable(ip, a, aenv, cx)),
            None => false,
        },
        H::Var(v) => {
            let cur = if cx.primed || cx.init {
                cx.s1.and_then(|s| s.get(v.idx())).and_then(|x| x.as_ref())
            } else {
                cx.s0.and_then(|s| s.get(v.idx()))
            };
            cur.is_some_and(|val| value_has_lazy_callable(val, 0))
        }
        H::InstVar { slot, .. } => {
            let v = ip.inst_var(*slot);
            let cur = if cx.primed || cx.init {
                cx.s1.and_then(|s| s.get(v.idx())).and_then(|x| x.as_ref())
            } else {
                cx.s0.and_then(|s| s.get(v.idx()))
            };
            cur.is_some_and(|val| value_has_lazy_callable(val, 0))
        }
        _ => false,
    };
    if here {
        return true;
    }
    let mut found = false;
    tlx_sema::visit::children(e, &mut |c| {
        if !found {
            found = expr_reads_lazy_callable(ip, c, env, cx);
        }
    });
    found
}

fn value_has_lazy_callable(v: &Value, depth: usize) -> bool {
    if depth >= MAX_VALUE_SCAN_DEPTH {
        return true;
    }
    match v {
        Value::LazyFcn(_) => true,
        Value::LazySet(l) => match &**l {
            LazySet::Custom(_) => true,
            LazySet::Enum(es) | LazySet::Product(es) => es.iter().any(|x| value_has_lazy_callable(x, depth + 1)),
            LazySet::Subset(b) | LazySet::KSubset(_, b) | LazySet::Seq(b) | LazySet::Union(b) => value_has_lazy_callable(b, depth + 1),
            LazySet::FcnSet(a, b) | LazySet::Cup(a, b) | LazySet::Cap(a, b) | LazySet::Diff(a, b) => {
                value_has_lazy_callable(a, depth + 1) || value_has_lazy_callable(b, depth + 1)
            }
            LazySet::RecordSet(fs) => fs.iter().any(|(_, x)| value_has_lazy_callable(x, depth + 1)),
            LazySet::Nat | LazySet::Int | LazySet::StringSet | LazySet::Any => false,
        },
        Value::Set(es) | Value::Tuple(es) => es.iter().any(|x| value_has_lazy_callable(x, depth + 1)),
        Value::Record(fs) => fs.iter().any(|(_, x)| value_has_lazy_callable(x, depth + 1)),
        Value::Fcn(ps, _) => ps.iter().any(|(k, x)| value_has_lazy_callable(k, depth + 1) || value_has_lazy_callable(x, depth + 1)),
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::ModelValue(_) | Value::Interval(..) => false,
    }
}

/// Apply one prefix constraint to `state` if it is provably total and
/// error-free over the entire current candidate space.
fn apply_constraint(
    c: &Constraint,
    ip: &Arc<Interp>,
    env: &Env,
    cx: &Ctx,
    base: &ops::SubsetBase<'_>,
    state: &mut CandidateState,
) -> Applied {
    match c {
        Constraint::ForallElem { vars, body, negate } => {
            if expr_reads_lazy_callable(ip, body, env, cx) {
                return Applied::Stop;
            }
            apply_element_predicate(base, state, |val| {
                let b_env = ip.bind_bound_vars(vars, val.clone(), env).ok()?;
                let b = ip.eval_bool(body, &b_env, cx).ok()?;
                Some(if *negate { !b } else { b })
            })
        }
        Constraint::SubsetUpper { rhs } => {
            if expr_reads_lazy_callable(ip, rhs, env, cx) {
                return Applied::Stop;
            }
            let Ok(rhs_val) = ip.eval(rhs, env, cx) else { return Applied::Stop };
            if value_has_lazy_callable(&rhs_val, 0) {
                return Applied::Stop;
            }
            apply_element_predicate(base, state, |val| ops::member(val, &rhs_val).ok())
        }
        Constraint::Disjoint { other, var_on_left } => {
            if expr_reads_lazy_callable(ip, other, env, cx) {
                return Applied::Stop;
            }
            let Ok(other_val) = ip.eval(other, env, cx) else { return Applied::Stop };
            if value_has_lazy_callable(&other_val, 0) {
                return Applied::Stop;
            }
            if !*var_on_left && ops::is_reducible(&other_val) {
                // `T \cap E` iterates `T` and tests `t \in E`; verify every
                // element of `T` compares cleanly with every reachable base
                // element without materializing huge intervals.
                match &other_val {
                    Value::Set(t_elems) => {
                        if t_elems.len().saturating_mul(state.max_possible_card()) > MAX_PROBE_BASE * 4 {
                            return Applied::Stop;
                        }
                        for t in t_elems.iter() {
                            if !all_reachable_comparable(base, state, t) {
                                return Applied::Stop;
                            }
                        }
                    }
                    Value::Interval(lo, hi) => {
                        if ops::size_if_known(&other_val).is_none() {
                            return Applied::Stop;
                        }
                        if lo <= hi && !all_reachable_comparable(base, state, &Value::Int(*lo)) {
                            return Applied::Stop;
                        }
                    }
                    _ => return Applied::Stop,
                }
            }
            apply_element_predicate(base, state, |val| ops::member(val, &other_val).ok().map(|m| !m))
        }
        Constraint::ElemMem { elem, required } => {
            if expr_reads_lazy_callable(ip, elem, env, cx) {
                return Applied::Stop;
            }
            let Ok(val) = ip.eval(elem, env, cx) else { return Applied::Stop };
            if value_has_lazy_callable(&val, 0) {
                return Applied::Stop;
            }
            let Some(found) = find_comparable_index(base, state, &val) else {
                return Applied::Stop;
            };
            match (found, *required) {
                (Some(idx), true) => state.require_index(idx),
                (None, true) => state.mark_empty(),
                (Some(idx), false) => state.forbid_index(idx),
                (None, false) => {}
            }
            Applied::Consumed
        }
        Constraint::SubsetLower { lhs } => {
            if expr_reads_lazy_callable(ip, lhs, env, cx) {
                return Applied::Stop;
            }
            let Ok(lhs_val) = ip.eval(lhs, env, cx) else { return Applied::Stop };
            if value_has_lazy_callable(&lhs_val, 0) {
                return Applied::Stop;
            }
            // Only handle small concrete enumerable lower bounds so we never
            // enumerate huge/infinite sets on `T \subseteq E`.
            let elems = match &lhs_val {
                Value::Set(es) if es.len() <= MAX_PROBE_BASE => es.to_vec(),
                Value::Interval(lo, hi) if *hi < *lo => Vec::new(),
                Value::Interval(lo, hi) if (*hi as i128 - *lo as i128 + 1) <= MAX_PROBE_BASE as i128 => {
                    (*lo..=*hi).map(Value::Int).collect()
                }
                _ => return Applied::Stop,
            };
            // Verify comparability for ALL elements of `lhs` before mutating `state`
            // (so an error on a later element of `lhs` never gets swallowed by an
            // earlier missing element when `state` is non-empty).
            let mut to_require = Vec::with_capacity(elems.len());
            let mut missing = false;
            for t in &elems {
                let Some(found) = find_comparable_index(base, state, t) else {
                    return Applied::Stop;
                };
                match found {
                    Some(idx) => to_require.push(idx),
                    None => missing = true,
                }
            }
            if missing {
                state.mark_empty();
            } else {
                for idx in to_require {
                    state.require_index(idx);
                }
            }
            Applied::Consumed
        }
        Constraint::EmptyCmp { empty } => {
            if *empty {
                state.max_card = 0;
            } else {
                state.min_card = state.min_card.max(1);
            }
            Applied::Consumed
        }
        Constraint::CardCmp { op, rhs } => {
            if expr_reads_lazy_callable(ip, rhs, env, cx) {
                return Applied::Stop;
            }
            let Ok(Value::Int(k)) = ip.eval(rhs, env, cx) else { return Applied::Stop };
            apply_card_cmp(*op, k as i128, state)
        }
        Constraint::CardIn { set } => {
            if expr_reads_lazy_callable(ip, set, env, cx) {
                return Applied::Stop;
            }
            let Ok(set_val) = ip.eval(set, env, cx) else { return Applied::Stop };
            match &set_val {
                Value::Interval(lo, hi) => {
                    if hi < lo {
                        state.mark_empty();
                    } else {
                        apply_card_bounds(*lo as i128, *hi as i128, state);
                    }
                    Applied::Consumed
                }
                Value::Set(es) => {
                    if es.is_empty() {
                        state.mark_empty();
                        return Applied::Consumed;
                    }
                    if !es.iter().all(|v| matches!(v, Value::Int(_))) {
                        return Applied::Stop;
                    }
                    let lo = es.first().unwrap().as_int().unwrap() as i128;
                    let hi = es.last().unwrap().as_int().unwrap() as i128;
                    apply_card_bounds(lo, hi, state);
                    if (hi - lo + 1) == es.len() as i128 {
                        Applied::Consumed
                    } else {
                        Applied::TightenedKeepResidual
                    }
                }
                _ => Applied::Stop,
            }
        }
    }
}

/// Probe `pred(b)` on EVERY reachable element `b` (`required \cup optional`).
/// Only commits the filter if ALL probes succeed (`Some(bool)`), ensuring no
/// error on any subset in the current candidate space can be skipped.
fn apply_element_predicate(
    base: &ops::SubsetBase<'_>,
    state: &mut CandidateState,
    mut pred: impl FnMut(&Value) -> Option<bool>,
) -> Applied {
    // Probe `required` first, then `optional` — but NEVER return early on a
    // `false` result because another reachable element might error!
    let mut req_conflict = false;
    for &idx in &state.required {
        let v = base.get(idx);
        if value_has_lazy_callable(&v, 0) {
            return Applied::Stop;
        }
        match pred(&v) {
            Some(true) => {}
            Some(false) => req_conflict = true,
            None => return Applied::Stop,
        }
    }
    let mut kept_optional = Vec::new();
    for &idx in &state.optional {
        let v = base.get(idx);
        if value_has_lazy_callable(&v, 0) {
            return Applied::Stop;
        }
        match pred(&v) {
            Some(true) => kept_optional.push(idx),
            Some(false) => {}
            None => return Applied::Stop,
        }
    }
    if req_conflict {
        state.mark_empty();
    } else {
        state.optional = kept_optional;
    }
    Applied::Consumed
}

/// Verify `val` compares cleanly (`cmp_tlc`) against every currently reachable
/// element of `base`, returning `Some(Some(idx))` if `val` equals `base[idx]`,
/// `Some(None)` if `val` is absent and comparable with all reachable elements,
/// or `None` if comparability cannot be guaranteed without error.
fn find_comparable_index(base: &ops::SubsetBase<'_>, state: &CandidateState, val: &Value) -> Option<Option<usize>> {
    // Fast path for integer intervals: O(1) comparability and index lookup.
    if let (Some((lo, hi)), Value::Int(x)) = (base.as_interval(), val) {
        if *x < lo || *x > hi {
            return Some(None);
        }
        let idx = (*x - lo) as usize;
        let present = state.required.binary_search(&idx).is_ok() || state.optional.binary_search(&idx).is_ok();
        return Some(present.then_some(idx));
    }
    let mut found = None;
    for &idx in state.required.iter().chain(&state.optional) {
        let v = base.get(idx);
        if value_has_lazy_callable(&v, 0) {
            return None;
        }
        match order::cmp_tlc(&v, val) {
            Ok(std::cmp::Ordering::Equal) => found = Some(idx),
            Ok(_) => {}
            Err(_) => return None,
        }
    }
    Some(found)
}

fn all_reachable_comparable(base: &ops::SubsetBase<'_>, state: &CandidateState, val: &Value) -> bool {
    find_comparable_index(base, state, val).is_some()
}

fn apply_card_bounds(lo: i128, hi: i128, state: &mut CandidateState) {
    if lo > hi || hi < 0 || lo > state.max_card as i128 || hi < state.min_card as i128 {
        state.mark_empty();
        return;
    }
    if lo > state.min_card as i128 {
        state.min_card = lo as usize;
    }
    if hi < state.max_card as i128 {
        state.max_card = hi as usize;
    }
}

fn apply_card_cmp(op: CardOp, k: i128, state: &mut CandidateState) -> Applied {
    match op {
        CardOp::Eq => {
            apply_card_bounds(k, k, state);
            Applied::Consumed
        }
        CardOp::Le => {
            apply_card_bounds(0, k, state);
            Applied::Consumed
        }
        CardOp::Lt => {
            apply_card_bounds(0, k - 1, state);
            Applied::Consumed
        }
        CardOp::Ge => {
            apply_card_bounds(k, state.max_card as i128, state);
            Applied::Consumed
        }
        CardOp::Gt => {
            apply_card_bounds(k + 1, state.max_card as i128, state);
            Applied::Consumed
        }
        CardOp::Neq => {
            let min = state.min_card as i128;
            let max = state.max_card as i128;
            if k < min || k > max {
                Applied::Consumed
            } else if k == min {
                apply_card_bounds(min + 1, max, state);
                Applied::Consumed
            } else if k == max {
                apply_card_bounds(min, max - 1, state);
                Applied::Consumed
            } else {
                Applied::Stop
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use tlx_sema::hir::DefKind;
    use tlx_value::{ops, Value};

    use crate::env::Env;
    use crate::eval::Ctx;
    use crate::interp::Interp;

    fn load_and_eval(spec: &str, name: &str) -> Result<Vec<Value>, String> {
        let dir = tlx_testkit::TempDir::new("subsetfilter");
        let path = dir.join("Test.tla");
        std::fs::write(&path, spec).unwrap();
        let ip = Interp::new(tlx_sema::Program::load(&path, &[]).unwrap(), Default::default()).unwrap();
        let def = ip.root_def(name).unwrap();
        let DefKind::Op(body) = &ip.prog.defs[def.idx()].kind else { panic!("expected operator") };
        let set = ip.eval(body, &Env::default(), &Ctx::NONE).map_err(|e| e.to_string())?;
        ops::enumerate(&set).map_err(|e| e.to_string())
    }

    fn eval_value(spec: &str, name: &str) -> Result<Value, String> {
        eval_with_config(spec, name, "")
    }

    fn eval_with_config(spec: &str, name: &str, cfg: &str) -> Result<Value, String> {
        let dir = tlx_testkit::TempDir::new("subsetfilter-val");
        let path = dir.join("Test.tla");
        std::fs::write(&path, spec).unwrap();
        let ip = Interp::new(tlx_sema::Program::load(&path, &[]).unwrap(), tlx_front::cfg::parse_cfg(cfg).unwrap()).unwrap();
        let def = ip.root_def(name).unwrap();
        let DefKind::Op(body) = &ip.prog.defs[def.idx()].kind else { panic!("expected operator") };
        ip.eval(body, &Env::default(), &Ctx::NONE).map_err(|e| e.to_string())
    }

    #[test]
    fn large_interval_filters_stream_the_first_witness() {
        let spec = r#"---- MODULE Test ----
EXTENDS Integers
Nonempty == {S \in SUBSET (1..1000000000) : S /= {}} \subseteq {}
Exclude == {S \in SUBSET (1..1000000000) : 1 \notin S} \subseteq {}
====
"#;
        for name in ["Nonempty", "Exclude"] {
            assert_eq!(eval_value(spec, name).unwrap(), Value::Bool(false));
        }
    }

    #[test]
    fn left_interval_intersection_preserves_length_error() {
        let spec = r#"---- MODULE Test ----
EXTENDS Integers
Filtered == {E \in SUBSET {1, 2} : (-1500000000..1500000000) \cap E = {}}
====
"#;
        let error = load_and_eval(spec, "Filtered").unwrap_err();
        assert!(error.contains("Size of interval value exceeds the maximum representable size"), "{error}");
    }

    #[test]
    fn probes_preserve_register_effects_and_lazy_early_stop() {
        let spec = r#"---- MODULE Test ----
EXTENDS Integers, FiniteSets, TLC
TestOp(Op(_)) == LET Helper(e) == Op(e) IN {E \in SUBSET {1,2} : \A e \in E : Helper(e)}
HigherOrder == TLCSet(9,0) /\ Cardinality(TestOp(LAMBDA e : TLCSet(9,TLCGet(9)+1) /\ e = 1)) = 2 /\ TLCGet(9) = 4
BadSet == {z \in SUBSET {1} : TLCSet(9,TLCGet(9)+1) /\ z = {}}
LazyBase == TLCSet(9,0) /\ ~({S \in SUBSET {BadSet} : \A s \in S : {} \in s} \subseteq {}) /\ TLCGet(9) = 0
F == [z \in Nat |-> IF TLCSet(9,TLCGet(9)+1) THEN z ELSE z]
Check(e) == F[e] = 1
LazyDef == TLCSet(9,0) /\ Cardinality({S \in SUBSET {1,2} : \A e \in S : Check(e)}) = 2 /\ TLCGet(9) = 4
MyCard(e) == IF TLCSet(9,TLCGet(9)+1) THEN 2 ELSE 2
Override == TLCSet(9,0) /\ ({S \in SUBSET {{1,2},{3}} : \A e \in S : Cardinality(e) = 2} = SUBSET {{1,2},{3}}) /\ TLCGet(9) = 4
====
"#;
        for name in ["HigherOrder", "LazyBase", "LazyDef"] {
            assert_eq!(eval_value(spec, name).unwrap(), Value::Bool(true), "{name}");
        }
        assert_eq!(eval_with_config(spec, "Override", "CONSTANT Cardinality <- MyCard").unwrap(), Value::Bool(true));
    }

    #[test]
    fn spantree_5_nodes_edge_sets_prunes_exponential_powerset() {
        let spec = r#"---- MODULE Test ----
EXTENDS Integers, FiniteSets
Nodes == {1, 2, 3, 4, 5}
EdgeSets == {E \in SUBSET (SUBSET Nodes) : \A e \in E : Cardinality(e) = 2}
====
"#;
        let elems = load_and_eval(spec, "EdgeSets").unwrap();
        assert_eq!(elems.len(), 1024);
        assert_eq!(elems[0], Value::Set(Vec::new().into()));
        // Last element must be the set of all 10 two-element edges.
        let Value::Set(last) = elems.last().unwrap() else { panic!("expected set") };
        assert_eq!(last.len(), 10);
    }

    #[test]
    fn constrained_subset_matches_brute_force_order_and_semantics() {
        let spec = r#"---- MODULE Test ----
EXTENDS Integers, FiniteSets
S == 1..6
Id(x) == x
IsEven(e) == e % 2 = 0
OnlyEven(E) == \A e \in E : IsEven(e)

F1 == {E \in SUBSET S : \A e \in E : e % 2 = 0}
F2 == {E \in SUBSET S : OnlyEven(E) /\ Cardinality(E) = 2}
F3 == {E \in SUBSET S : 2 \in E /\ 5 \notin E /\ Cardinality(E) <= 3}
F4 == {E \in SUBSET S : {2, 4} \subseteq E /\ E \subseteq {1, 2, 4, 6}}
F5 == {E \in SUBSET S : E \cap {1, 3, 5} = {} /\ E /= {}}
F6 == {E \in SUBSET S : ~(\E e \in E : e > 3) /\ Cardinality(E) \in {1, 3}}
F7 == {E \in SUBSET S : LET k == 2 IN (\A e \in E : e <= 4) /\ Cardinality(E) = k}
F8 == {E \in SUBSET S : (\A e \in E : e <= 4) /\ (\E x \in E : x = 3)}
F9 == {E \in SUBSET (1..40) : Cardinality(E) = 2 /\ 1 \in E}

\* Unpruned reference using a non-matching leading conjunct (TRUE \/ E = {}).
Ref1 == {E \in SUBSET S : (TRUE \/ E = {}) /\ (\A e \in E : e % 2 = 0)}
Ref2 == {E \in SUBSET S : (TRUE \/ E = {}) /\ OnlyEven(E) /\ Cardinality(E) = 2}
Ref3 == {E \in SUBSET S : (TRUE \/ E = {}) /\ 2 \in E /\ 5 \notin E /\ Cardinality(E) <= 3}
Ref4 == {E \in SUBSET S : (TRUE \/ E = {}) /\ {2, 4} \subseteq E /\ E \subseteq {1, 2, 4, 6}}
Ref5 == {E \in SUBSET S : (TRUE \/ E = {}) /\ E \cap {1, 3, 5} = {} /\ E /= {}}
Ref6 == {E \in SUBSET S : (TRUE \/ E = {}) /\ ~(\E e \in E : e > 3) /\ Cardinality(E) \in {1, 3}}
Ref7 == {E \in SUBSET S : (TRUE \/ E = {}) /\ (LET k == 2 IN (\A e \in E : e <= 4) /\ Cardinality(E) = k)}
Ref8 == {E \in SUBSET S : (TRUE \/ E = {}) /\ (\A e \in E : e <= 4) /\ (\E x \in E : x = 3)}
====
"#;
        for i in 1..=8 {
            let opt = load_and_eval(spec, &format!("F{i}")).unwrap();
            let reference = load_and_eval(spec, &format!("Ref{i}")).unwrap();
            assert_eq!(opt, reference, "mismatch on F{i}");
        }
        let f9 = load_and_eval(spec, "F9").unwrap();
        assert_eq!(f9.len(), 39);
    }

    #[test]
    fn preserves_errors_and_early_stop_semantics() {
        let spec = r#"---- MODULE Test ----
EXTENDS Integers, FiniteSets
\* Streaming early stop on E = {} must NOT trigger 1 \div 0 on e = 0.
FullEnumErr == {E \in SUBSET {0, 1, 2} : \A e \in E : 1 \div e = 1}
\* Non-boolean body on e = 2 must report error on full enumeration, not silently drop 2.
NonBoolErr == {E \in SUBSET {1, 2} : \A e \in E : IF e = 1 THEN TRUE ELSE 42}
\* Earlier residual error must NOT be swallowed by a later subset constraint.
ResidualOrderErr == {E \in SUBSET {1, 2} : (IF 2 \in E THEN 1 \div 0 = 0 ELSE TRUE) /\ (\A e \in E : e = 1)}
\* Incomparable membership must still report comparison error on {1}.
IncomparableErr == {E \in SUBSET {1, 2} : "a" \in E}
\* Earlier prefix constraint eliminating 0 prevents division by zero in second conjunct.
ShortCircuitSafe == {E \in SUBSET {0, 1, 2} : (\A e \in E : e /= 0) /\ (\A e \in E : 1 \div e = 1)}
\* Empty prefix short-circuits later erroring conjunct.
EmptyPrefixShortCircuit == {E \in SUBSET {1, 2} : 99 \in E /\ (1 \div 0 = 0)}
\* LET depending on E must NOT share its cache across subsets.
LetDependingOnE == {E \in SUBSET {1, 2, 3} : LET c == Cardinality(E) IN c = 2}
====
"#;
        let err_set = eval_value(spec, "FullEnumErr").unwrap();
        let mut first = None;
        let completed = ops::for_each_enumerated(&err_set, &mut |e| {
            first = Some(e);
            Ok(false)
        })
        .unwrap();
        assert!(!completed);
        assert_eq!(first, Some(Value::Set(Vec::new().into())));
        assert!(load_and_eval(spec, "FullEnumErr").is_err());
        assert!(load_and_eval(spec, "NonBoolErr").is_err());
        assert!(load_and_eval(spec, "ResidualOrderErr").is_err());
        assert!(load_and_eval(spec, "IncomparableErr").is_err());
        let safe = load_and_eval(spec, "ShortCircuitSafe").unwrap();
        assert_eq!(safe.len(), 2);
        let empty = load_and_eval(spec, "EmptyPrefixShortCircuit").unwrap();
        assert!(empty.is_empty());
        let let_e = load_and_eval(spec, "LetDependingOnE").unwrap();
        assert_eq!(let_e.len(), 3);
    }

    #[test]
    fn additional_shapes_union_tuple_disjoint_and_effects() {
        let spec = r#"---- MODULE Test ----
EXTENDS Integers, FiniteSets, TLC
\* Tuple-destructured element filter.
Pairs == {E \in SUBSET ((1..3) \X (1..3)) : \A <<a, b>> \in E : a < b}
PairsRef == {E \in SUBSET ((1..3) \X (1..3)) : (TRUE \/ E = {}) /\ (\A <<a, b>> \in E : a < b)}
\* Left-hand reducible intersection including a large interval and an incomparable error.
CapLeft == {E \in SUBSET (1..6) : {1, 3, 5} \cap E = {} /\ Cardinality(E) /= 0}
CapLeftRef == {E \in SUBSET (1..6) : (TRUE \/ E = {}) /\ ({1, 3, 5} \cap E = {}) /\ Cardinality(E) /= 0}
CapBigInterval == {E \in SUBSET (1..4) : (2..2000000) \cap E = {}}
CapIncomparableErr == {E \in SUBSET {1, 2} : {"a"} \cap E = {}}
\* UNION of powersets filtered by an element constraint.
UnionSubsets == {E \in UNION {SUBSET {1, 2, 3}, SUBSET {2, 3, 4}} : \A e \in E : e % 2 = 0}
UnionSubsetsRef == {E \in UNION {SUBSET {1, 2, 3}, SUBSET {2, 3, 4}} : (TRUE \/ E = {}) /\ (\A e \in E : e % 2 = 0)}
\* Impossible negative cardinality yields empty set immediately.
NegCard == {E \in SUBSET (1..40) : Cardinality(E) = -1}
\* Effectful element predicate must NOT be pre-probed or skip effects.
EffCounter ==
    /\ TLCSet(9, 0)
    /\ Cardinality({E \in SUBSET {1, 2} : \A e \in E : TLCSet(9, TLCGet(9) + 1) /\ e = 1}) = 2
    /\ TLCGet(9) = 4
====
"#;
        assert_eq!(load_and_eval(spec, "Pairs").unwrap(), load_and_eval(spec, "PairsRef").unwrap());
        assert_eq!(load_and_eval(spec, "CapLeft").unwrap(), load_and_eval(spec, "CapLeftRef").unwrap());
        assert_eq!(load_and_eval(spec, "CapBigInterval").unwrap().len(), 2);
        assert!(load_and_eval(spec, "CapIncomparableErr").is_err());
        assert_eq!(load_and_eval(spec, "UnionSubsets").unwrap(), load_and_eval(spec, "UnionSubsetsRef").unwrap());
        assert!(load_and_eval(spec, "NegCard").unwrap().is_empty());
        assert_eq!(eval_value(spec, "EffCounter").unwrap(), Value::Bool(true));
    }
}
