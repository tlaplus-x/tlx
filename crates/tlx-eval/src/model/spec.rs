//! Syntactic analysis of temporal formulas: splitting a SPECIFICATION into
//! Init and Next, and classifying the parts of a PROPERTY that TLC checks
//! during breadth-first search.

use std::collections::HashMap;
use std::sync::Arc;

use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::*;
use tlx_value::Value;

use crate::env::Env;
use crate::error::{EResult, EvalError};
use crate::eval::Ctx;
use crate::interp::Interp;

/// A part of a PROPERTY that TLC checks during breadth-first search, with
/// the name TLC reports its violation by (see `classify_property`).
pub(super) enum PropPart {
    /// `[]P` with P a state predicate: checked like an invariant.
    Invariant(String, Expr),
    /// `[][A]_v`: checked on every transition.
    Action(String, Expr),
    /// A state predicate without `[]`: must hold in the initial states.
    Init(String, Expr),
    /// Anything else: a temporal (liveness) formula (reported by the name
    /// of its PROPERTY).
    Liveness(Expr),
}

/// TLC's error for a property that is trivially true
/// (EC.TLC_LIVE_FORMULA_TAUTOLOGY).
pub const TAUTOLOGY: &str = "Temporal formula is a tautology (its negation is unsatisfiable).";

/// Split the temporal property `e` of the PROPERTY `name` (its definition
/// applied) into the parts TLC checks during BFS, as TLC's
/// `SpecProcessor.processConfigProps` decomposes it, starting with the body
/// of the PROPERTY's definition: through 0-ary definitions, LET,
/// conjunctions, operators applied to arguments (the arguments bound, also
/// operator arguments; not within an INSTANCE with substitutions) and
/// universal quantification over constant sets (an empty one makes the
/// property a tautology, an error). A part is named as TLC names it: by the
/// innermost definition it was reached through, or by the location of the
/// conjunct or quantifier body it was split off as (TLC's
/// `SemanticNode.toString`) when that came later; the operator `X` of an
/// invariant `[]X`. A part under quantifiers is the part quantified over
/// their sets: TLC checks it once per element, under the same name, so
/// checking the conjunction finds the same first violation. A 0-ary
/// constant-level definition is a value for TLC: TRUE adds nothing, FALSE
/// is an error (TLC_CONFIG_SPEC_IS_TRIVIAL).
pub(super) fn classify_property(ip: &Arc<Interp>, e: &Expr, name: &str, out: &mut Vec<PropPart>) -> EResult<()> {
    let mut quants = Vec::new();
    match &*e.kind {
        ExprKind::Apply { op: OpRef::Def(d), args } if args.is_empty() => match ip.plain_op_body(*d) {
            Some((t, body)) if !tlc_has_value(ip, t) => {
                classify(ip, body, name.to_string(), ip.prog.def_instance(t).is_some(), &mut quants, &mut Names::new(), out)
            }
            _ => classify(ip, e, name.to_string(), false, &mut quants, &mut Names::new(), out),
        },
        _ => classify(ip, e, name.to_string(), false, &mut quants, &mut Names::new(), out),
    }
}

/// The quantifiers (`\A` over constant sets) a part of a property is under.
type Quants = Vec<(Vec<Bound>, Span)>;

/// Applications of operator parameters replaced by `unfold`: their
/// location and the parameter's name.
type Names = HashMap<Span, Arc<str>>;

/// `subs`: `e` is in the body of a definition from an INSTANCE with
/// substitutions, where TLC no longer inlines operators applied to
/// arguments.
fn classify(
    ip: &Arc<Interp>,
    e: &Expr,
    name: String,
    subs: bool,
    quants: &mut Quants,
    names: &mut Names,
    out: &mut Vec<PropPart>,
) -> EResult<()> {
    let wrap = |x: &Expr, quants: &Quants| {
        quants.iter().rev().fold(x.clone(), |x, (bounds, span)| {
            Expr::new(ExprKind::Quant { kind: QuantKind::Forall, bounds: bounds.clone(), body: x }, *span)
        })
    };
    let loc = |x: &Expr| super::span_location(ip, x.span);
    let enter = |d: DefId| subs || ip.prog.def_instance(ip.redirect_def(d)).is_some();
    match &*e.kind {
        ExprKind::And(es) => {
            for c in es {
                classify(ip, c, loc(c), subs, quants, names, out)?;
            }
        }
        ExprKind::Let { body, .. } => classify(ip, body, name, subs, quants, names, out)?,
        ExprKind::Apply { op: OpRef::Def(d), args } if args.is_empty() => {
            let def_name = applied_name(ip, e, *d, names);
            if tlc_has_value(ip, *d) {
                if let Ok(Value::Bool(b)) = ip.eval(e, &Env::default(), &Ctx::NONE) {
                    if !b {
                        return Err(EvalError::new(format!("The spec is trivially false because {def_name} is false.")));
                    }
                    return Ok(());
                }
            }
            match ip.plain_op_body(*d) {
                // A state predicate that is not split further is checked as
                // a whole (TLC names it by the operator).
                Some((_, body))
                    if !matches!(&*body.kind, ExprKind::And(_) | ExprKind::Let { .. })
                        && constant_forall(ip, body).is_none()
                        && is_state_level(ip, e, &mut Vec::new())
                        && !is_temporal(ip, e) =>
                {
                    out.push(PropPart::Init(def_name, wrap(e, quants)))
                }
                Some((_, body)) => classify(ip, body, def_name, enter(*d), quants, names, out)?,
                None => out.push(PropPart::Liveness(wrap(e, quants))),
            }
        }
        // An operator applied to arguments (`id([]P)`, `op(TRUE)` with
        // `op(b) == [][b]_x`): TLC binds the arguments and classifies the
        // body. When that yields only liveness parts, the application is
        // kept as one formula.
        ExprKind::Apply { op: OpRef::Def(d), args } if !subs && !args.is_empty() => match unfold(ip, *d, args, names) {
            Some(body) if is_temporal(ip, &body) => {
                let mut parts = Vec::new();
                classify(ip, &body, applied_name(ip, e, *d, names), enter(*d), quants, names, &mut parts)?;
                if parts.iter().all(|p| matches!(p, PropPart::Liveness(_))) {
                    out.push(PropPart::Liveness(wrap(e, quants)));
                } else {
                    out.extend(parts);
                }
            }
            _ if is_state_level(ip, e, &mut Vec::new()) && !is_temporal(ip, e) => out.push(PropPart::Init(name, wrap(e, quants))),
            _ => out.push(PropPart::Liveness(wrap(e, quants))),
        },
        ExprKind::Quant { bounds, body, .. } => match constant_forall(ip, e) {
            Some(true) => return Err(EvalError::new(TAUTOLOGY)),
            Some(false) => {
                quants.push((bounds.clone(), e.span));
                let r = classify(ip, body, loc(body), subs, quants, names, out);
                quants.pop();
                r?;
            }
            None if is_state_level(ip, e, &mut Vec::new()) && !is_temporal(ip, e) => {
                out.push(PropPart::Init(name, wrap(e, quants)));
            }
            None => out.push(PropPart::Liveness(wrap(e, quants))),
        },
        _ if !matches!(&*e.kind, ExprKind::Builtin { op: B::Always, .. })
            && is_state_level(ip, e, &mut Vec::new())
            && !is_temporal(ip, e) =>
        {
            out.push(PropPart::Init(name, wrap(e, quants)))
        }
        ExprKind::Builtin { op: B::Always, args } => match &*args[0].kind {
            ExprKind::BoxAction { .. } => out.push(PropPart::Action(name, wrap(&args[0], quants))),
            _ if is_state_level(ip, &args[0], &mut Vec::new()) => {
                // `[]X` with X an operator without arguments: named X.
                let name = match &*args[0].kind {
                    ExprKind::Apply { op: OpRef::Def(d), args } if args.is_empty() => ip.prog.defs[d.idx()].name.to_string(),
                    ExprKind::Var(v) => ip.prog.vars[v.idx()].name.to_string(),
                    ExprKind::Const(c) => ip.prog.consts[c.idx()].name.to_string(),
                    ExprKind::Bool(b) => if *b { "TRUE" } else { "FALSE" }.to_string(),
                    _ => name,
                };
                out.push(PropPart::Invariant(name, wrap(&args[0], quants)))
            }
            _ => out.push(PropPart::Liveness(wrap(e, quants))),
        },
        _ => out.push(PropPart::Liveness(wrap(e, quants))),
    }
    Ok(())
}

/// The name of the operator applied in `e` (an application of `d`) as
/// written there: the operator parameter it replaced, if any (`Names`).
fn applied_name(ip: &Interp, e: &Expr, d: DefId, names: &Names) -> String {
    names.get(&e.span).map_or_else(|| ip.prog.defs[d.idx()].name.to_string(), |n| n.to_string())
}

/// Whether TLC evaluates definition `d` (after cfg redirection) at startup
/// and keeps its value in place of the definition
/// (SpecProcessor.processConstantDefns): a 0-ary constant-level definition.
/// (TLC's Java overrides with a `minLevel`, as TLCGet and IOExec, make a
/// definition non-constant there; approximated by tlx's pure ones.)
pub(super) fn tlc_has_value(ip: &Interp, d: DefId) -> bool {
    if ip.has_def_value(d) {
        return true;
    }
    let d = ip.redirect_def(d);
    if ip.has_def_value(d) {
        return true;
    }
    // (Temporal and action operators are not constant level for TLC.)
    ip.is_const_def(d)
        && ip.is_pure_def(d)
        && ip.plain_op_body(d).is_some_and(|(_, body)| is_state_level(ip, body, &mut Vec::new()) && !is_temporal(ip, body))
}

/// For `\A x \in S, ... : P` over constant sets: whether the product of their
/// domains is empty (`Some(true)` = empty tautology, `Some(false)` = non-empty
/// valid constant bounds; TLC unrolls such a quantifier in a PROPERTY,
/// `SpecProcessor.processConfigProps` with `OPCODE_bf`); `None` for anything
/// else, or when any domain or tuple binder fails validation. Validates each
/// domain (and each tuple-bound domain's elements) individually without
/// walking the Cartesian product or materializing `SUBSET S` / `kSubset(k, S)`.
fn constant_forall(ip: &Arc<Interp>, e: &Expr) -> Option<bool> {
    use crate::eval::BoundElems;

    let ExprKind::Quant { kind: QuantKind::Forall, bounds, .. } = &*e.kind else { return None };
    let env = Env::default();
    if !bounds.iter().all(|b| ip.is_constant_in(&b.set, &env)) {
        return None;
    }
    let mut empty = false;
    let mut tuple_bounds = Vec::new();
    for b in bounds {
        match ip.bound_elems(&b.set, &env, &Ctx::NONE).ok()? {
            BoundElems::Elems(elems) => {
                if elems.is_empty() {
                    empty = true;
                } else if matches!(b.vars, BoundVars::Tuple(_)) {
                    tuple_bounds.push((&b.vars, elems));
                }
            }
            BoundElems::Stream(v) => {
                if tlx_value::ops::for_each_enumerated(&v, &mut |_| Ok(false)).ok()? {
                    empty = true;
                } else if matches!(b.vars, BoundVars::Tuple(_)) {
                    // Every element of `SUBSET S` / `kSubset(k, S)` is a set
                    // (never a tuple), so a non-empty streamed domain cannot
                    // satisfy a tuple binder.
                    return None;
                }
            }
        }
    }
    if empty {
        return Some(true);
    }
    for (vars, elems) in tuple_bounds {
        for i in 0..elems.len() {
            ip.bind_bound_vars(vars, elems.get(i), &env).ok()?;
        }
    }
    Some(false)
}

/// Whether `e` contains no primes, actions or temporal operators (`seen`:
/// definitions already being looked through).
fn is_state_level(ip: &Interp, e: &Expr, seen: &mut Vec<DefId>) -> bool {
    // ENABLED A is a state predicate, whatever A is.
    if matches!(&*e.kind, ExprKind::Builtin { op: B::Enabled, .. }) {
        return true;
    }
    let body_is_state_level = |kind: &DefKind, seen: &mut Vec<DefId>| match kind {
        DefKind::Op(body) | DefKind::Fn { body, .. } => is_state_level(ip, body, seen),
        DefKind::Pending => true,
    };
    let here = match &*e.kind {
        ExprKind::Builtin { op: B::Prime | B::Unchanged | B::Always | B::Eventually | B::LeadsTo, .. }
        | ExprKind::BoxAction { .. }
        | ExprKind::AngleAction { .. }
        | ExprKind::Fairness { .. }
        | ExprKind::TemporalQuant { .. } => false,
        ExprKind::Apply { op: OpRef::Def(d), .. } | ExprKind::OpArg(OpRef::Def(d)) => {
            let d = ip.redirect_def(*d);
            if seen.contains(&d) {
                true
            } else {
                seen.push(d);
                body_is_state_level(&ip.prog.defs[d.idx()].kind, seen)
            }
        }
        ExprKind::Let { defs, .. } => defs.iter().all(|d| body_is_state_level(&ip.prog.defs[d.idx()].kind, seen)),
        _ => true,
    };
    if !here {
        return false;
    }
    let mut ok = true;
    tlx_sema::visit::children(e, &mut |c| {
        if ok && !is_state_level(ip, c, seen) {
            ok = false;
        }
    });
    ok
}

/// Split `Init /\ [][Next]_vars /\ fairness` into its parts: `next` is
/// `(Next, vars, within)`, `within` the INSTANCE statement if
/// `[][Next]_vars` was found under the substitutions of an instance (TLC's
/// SpecProcessor then wraps Next in them: one unnamed action located there,
/// see `Interp::split_actions`); the temporal conjuncts other than
/// `[][Next]_vars` (fairness, ...) go to `temporal`; the initial parts to
/// `inits`, each with the INSTANCE statement it is under. `under`: the
/// INSTANCE statement `e` is under, if any.
pub(super) type NextPart = (Expr, Expr, Option<Span>);

pub(super) fn split_spec(
    ip: &Interp,
    e: &Expr,
    under: Option<Span>,
    inits: &mut Vec<(Expr, Option<Span>)>,
    next: &mut Option<NextPart>,
    temporal: &mut Vec<Expr>,
) {
    match &*e.kind {
        ExprKind::And(es) => es.iter().for_each(|c| split_spec(ip, c, under, inits, next, temporal)),
        ExprKind::Apply { op: OpRef::Def(d), args } if args.is_empty() => match temporal_body(ip, *d) {
            // Only look through definitions that are themselves temporal.
            Some(body) => {
                let under = under.or_else(|| ip.prog.def_instance(ip.redirect_def(*d)).map(|(_, at)| at));
                split_spec(ip, body, under, inits, next, temporal)
            }
            None => inits.push((e.clone(), under)),
        },
        ExprKind::Let { body, .. } => split_spec(ip, body, under, inits, next, temporal),
        ExprKind::Apply { op: OpRef::Def(d), args } => {
            // An operator wrapping (part of) the behavior spec, e.g.
            // `MyNext([][Next]_vars)`, `LET id(a) == a IN id(Init /\ ...)` or
            // a parameterized instance's `I(7)!Spec`: split its body with the
            // arguments substituted (as TLC's SpecProcessor does, binding them
            // in a context). Fairness only (`Fair(v) == WF_v(Next)`) stays
            // one temporal conjunct.
            // (Not under an INSTANCE's substitutions: as `classify`.)
            if let Some(body) = unfold(ip, *d, args, &mut Names::new()).filter(|b| under.is_none() && is_temporal(ip, b)) {
                let under = under.or_else(|| ip.prog.def_instance(ip.redirect_def(*d)).map(|(_, at)| at));
                let (mut i2, mut n2, mut t2) = (Vec::new(), next.clone(), Vec::new());
                split_spec(ip, &body, under, &mut i2, &mut n2, &mut t2);
                if !i2.is_empty() || n2.is_some() != next.is_some() {
                    inits.extend(i2);
                    *next = n2;
                    temporal.extend(t2);
                    return;
                }
            }
            if temporal_body(ip, *d).is_none() && !is_temporal(ip, e) {
                inits.push((e.clone(), under));
            } else {
                temporal.push(e.clone());
            }
        }
        ExprKind::Builtin { op: B::Always, args } => match &*args[0].kind {
            ExprKind::BoxAction { action, sub } if next.is_none() => *next = Some((action.clone(), sub.clone(), under)),
            _ => temporal.push(e.clone()),
        },
        ExprKind::Fairness { .. } | ExprKind::Builtin { op: B::Eventually | B::LeadsTo, .. } | ExprKind::TemporalQuant { .. } => {
            temporal.push(e.clone())
        }
        ExprKind::Quant { body, .. } if is_temporal(ip, body) => temporal.push(e.clone()),
        _ => inits.push((e.clone(), under)),
    }
}

/// The state variables that the subscript `sub` of the next-state relation
/// does not seem to contain (TLC's warning): those not among its
/// components, found as TLC's `SubscriptCollector` does, through tuples,
/// definitions, LET and instantiation; other expressions are ignored.
pub(super) fn vars_not_in_subscript(ip: &Interp, sub: &Expr) -> Vec<VarId> {
    /// The arguments of the definitions entered (for their parameters),
    /// each to be looked at in the scope it was found in.
    struct Scope<'a> {
        args: Vec<(LocalId, &'a Expr)>,
        up: Option<&'a Scope<'a>>,
    }
    fn collect<'a>(ip: &'a Interp, e: &'a Expr, scope: &Scope<'a>, depth: u32, out: &mut Vec<VarId>) {
        if depth > 64 {
            return;
        }
        match &*e.kind {
            ExprKind::Var(v) => out.push(*v),
            ExprKind::Tuple(es) => es.iter().for_each(|c| collect(ip, c, scope, depth + 1, out)),
            ExprKind::Let { body, .. } => collect(ip, body, scope, depth + 1, out),
            ExprKind::Local(l) => {
                if let (Some((_, arg)), Some(up)) = (scope.args.iter().find(|(p, _)| p == l), scope.up) {
                    collect(ip, arg, up, depth + 1, out);
                }
            }
            ExprKind::Apply { op: OpRef::Def(d), args } => {
                let d = ip.redirect_def(*d);
                if ip.has_def_value(d) {
                    return;
                }
                let def = &ip.prog.defs[d.idx()];
                if let DefKind::Op(body) = &def.kind {
                    let inner = Scope { args: def.params.iter().copied().zip(args.iter()).collect(), up: Some(scope) };
                    collect(ip, body, &inner, depth + 1, out);
                }
            }
            _ => {}
        }
    }
    let mut found = Vec::new();
    collect(ip, sub, &Scope { args: Vec::new(), up: None }, 0, &mut found);
    (0..ip.prog.vars.len()).map(|i| VarId(i as u32)).filter(|v| !found.contains(v)).collect()
}

/// A state predicate: no primes, actions or temporal operators.
pub(super) fn is_action_free(ip: &Interp, e: &Expr) -> bool {
    is_state_level(ip, e, &mut Vec::new())
}

/// Whether `e` contains temporal operators (through 0-ary definitions).
pub(super) fn is_temporal_expr(ip: &Interp, e: &Expr) -> bool {
    is_temporal(ip, e)
}

/// The body of operator definition `d` (after cfg redirection) if it
/// contains temporal operators.
pub(super) fn temporal_body(ip: &Interp, d: DefId) -> Option<&Expr> {
    temporal_body_in(ip, d, &mut Vec::new())
}

/// `temporal_body`; `seen`: the definitions being looked through (a
/// recursive definition is not temporal through its recursive calls).
fn temporal_body_in<'a>(ip: &'a Interp, d: DefId, seen: &mut Vec<DefId>) -> Option<&'a Expr> {
    let d = ip.redirect_def(d);
    if seen.contains(&d) {
        return None;
    }
    let DefKind::Op(body) = &ip.prog.defs[d.idx()].kind else { return None };
    seen.push(d);
    let temporal = is_temporal_in(ip, body, seen);
    seen.pop();
    temporal.then_some(body)
}

/// Whether `e` (looking through definitions) contains temporal operators.
fn is_temporal(ip: &Interp, e: &Expr) -> bool {
    is_temporal_in(ip, e, &mut Vec::new())
}

fn is_temporal_in(ip: &Interp, e: &Expr, seen: &mut Vec<DefId>) -> bool {
    // (Definitions that refer to each other forever, e.g. through cfg
    // redirections `Init <- ReDefInit` with `ReDefInit == Init`, count as
    // not temporal here: evaluating them reports the runaway recursion.)
    if tlx_base::stack::low() {
        return false;
    }
    match &*e.kind {
        ExprKind::Builtin { op: B::Always | B::Eventually | B::LeadsTo, .. } | ExprKind::Fairness { .. } => true,
        ExprKind::And(es) | ExprKind::Or(es) => es.iter().any(|c| is_temporal_in(ip, c, seen)),
        ExprKind::Builtin { op: B::Not | B::Implies | B::Equiv, args } => args.iter().any(|c| is_temporal_in(ip, c, seen)),
        ExprKind::If { then, els, .. } => is_temporal_in(ip, then, seen) || is_temporal_in(ip, els, seen),
        ExprKind::Quant { body, .. } | ExprKind::Let { body, .. } => is_temporal_in(ip, body, seen),
        // A temporal definition, or an operator applied to a temporal
        // formula (`id([]P)`).
        ExprKind::Apply { op, args } => {
            matches!(op, OpRef::Def(d) if temporal_body_in(ip, *d, seen).is_some()) || args.iter().any(|a| is_temporal_in(ip, a, seen))
        }
        _ => false,
    }
}

/// The body of definition `d` (after cfg redirection) applied to `args`,
/// with the arguments substituted for the parameters; operator arguments
/// (`F(_)` parameters given a definition or a LAMBDA) are applied in place.
/// `None` for a definition without a TLA+ body (native, cfg value) and when
/// a LET definition in the body uses a parameter (its body is a separate
/// definition that the substitution does not reach).
///
/// `names` receives, for each operator parameter applied in the body
/// (`F(...)` with `F(_)` given an operator), the location of that
/// application and the parameter's name: TLC names a property part reached
/// through an operator application by the operator as written there
/// (`SpecProcessor.processConfigProps` uses `opNode.getName()`), which is the
/// parameter, not the operator it was given.
fn unfold(ip: &Interp, d: DefId, args: &[Expr], names: &mut Names) -> Option<Expr> {
    let (d, body) = ip.plain_op_body(d)?;
    let def = &ip.prog.defs[d.idx()];
    if def.params.len() != args.len() || ip.has_def_value(d) {
        return None;
    }
    let map: HashMap<LocalId, Expr> = def.params.iter().copied().zip(args.iter().cloned()).collect();
    if let_uses(ip, body, &map, &mut Vec::new()) {
        return None;
    }
    let mut out = body.clone();
    subst(ip, &mut out, &map, names).then_some(out)
}

/// Substitute `map` in `e` (see `unfold`); false if an operator parameter is
/// applied but its argument is neither an operator nor a LAMBDA.
fn subst(ip: &Interp, e: &mut Expr, map: &HashMap<LocalId, Expr>, names: &mut Names) -> bool {
    match &*e.kind {
        ExprKind::Local(l) | ExprKind::OpArg(OpRef::Param(l)) => {
            if let Some(r) = map.get(l) {
                *e = r.clone();
            }
            return true;
        }
        ExprKind::Apply { op: OpRef::Param(l), args } if map.contains_key(l) => {
            let mut args = args.clone();
            if !args.iter_mut().all(|a| subst(ip, a, map, names)) {
                return false;
            }
            let span = e.span;
            match &*map[l].kind {
                ExprKind::OpArg(op) => {
                    names.insert(span, ip.prog.locals[l.idx()].name.clone());
                    *e = Expr::new(ExprKind::Apply { op: *op, args }, span)
                }
                ExprKind::Lambda { params, body } if params.len() == args.len() => {
                    let inner: HashMap<LocalId, Expr> = params.iter().copied().zip(args).collect();
                    let mut b = body.clone();
                    if !subst(ip, &mut b, &inner, names) {
                        return false;
                    }
                    *e = b;
                }
                _ => return false,
            }
            return true;
        }
        _ => {}
    }
    let mut ok = true;
    tlx_sema::visit::children_mut(e, &mut |c| ok &= subst(ip, c, map, names));
    ok
}

/// Whether a LET definition in `e` (or nested in one) uses a local of `map`.
fn let_uses(ip: &Interp, e: &Expr, map: &HashMap<LocalId, Expr>, seen: &mut Vec<DefId>) -> bool {
    let here = match &*e.kind {
        ExprKind::Local(l) | ExprKind::OpArg(OpRef::Param(l)) | ExprKind::Apply { op: OpRef::Param(l), .. } => {
            !seen.is_empty() && map.contains_key(l)
        }
        ExprKind::Let { defs, .. } => defs.iter().any(|d| {
            if seen.contains(d) {
                return false;
            }
            seen.push(*d);
            let uses = match &ip.prog.defs[d.idx()].kind {
                DefKind::Op(b) => let_uses(ip, b, map, seen),
                DefKind::Fn { bounds, body } => bounds.iter().any(|b| let_uses(ip, &b.set, map, seen)) || let_uses(ip, body, map, seen),
                DefKind::Pending => false,
            };
            seen.pop();
            uses
        }),
        _ => false,
    };
    if here {
        return true;
    }
    let mut found = false;
    tlx_sema::visit::children(e, &mut |c| found = found || let_uses(ip, c, map, seen));
    found
}
