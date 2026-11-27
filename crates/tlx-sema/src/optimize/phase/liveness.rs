//! Backward liveness on (control phase, data slot) pairs. Reads are roots;
//! an untouched live successor slot makes its predecessor slot live.
//!
//! Supports both record / fixed-domain map-of-records control fields (including
//! whole-record and `EXCEPT ![actor] = [...]` writes) and parallel scalar or
//! fixed-domain companion variables governed by a shared control variable.

mod lean;
pub(super) mod sym;

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::{builtins::Builtin as B, hir::*, visit, Program};

use super::domain::{self, Atom, Domain, Domains};
use super::{binding, mentions_local, mentions_var, mentions_var_where, variable, Branch, FieldProjection};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Control {
    /// Control field inside a record or fixed-domain map-of-records variable.
    RecordField { var: VarId, field: Arc<str> },
    /// Standalone scalar phase variable or fixed-domain phase map variable.
    Var { var: VarId },
}

impl Control {
    pub(super) fn var(&self) -> VarId {
        match self {
            Self::RecordField { var, .. } | Self::Var { var } => *var,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Slot {
    RecordField(Arc<str>),
    CompanionVar(VarId),
}

pub(super) struct Analysis<'a> {
    pub(super) domains: &'a Domains,
    pub(super) control: Control,
    pub(super) phases: &'a BTreeSet<Atom>,
    pub(super) keys: Option<&'a BTreeSet<Atom>>,
    pub(super) live: BTreeMap<Slot, BTreeSet<Atom>>,
    projected_vars: BTreeSet<VarId>,
    remaining: usize,
}

pub(super) struct Transfer {
    pub(super) actor: Option<LocalId>,
    pub(super) writes: BTreeMap<Slot, Expr>,
    pub(super) target: Option<Atom>,
}

/// Visitor callbacks for the single context-aware state-predicate traversal
/// (`Analysis::walk_obs`).
pub(super) trait ObsSink {
    fn step(&mut self) -> Option<()> {
        Some(())
    }
    fn proved_membership(&mut self, e: &Expr) -> Option<Option<Expr>>;
    fn fixed_domain(&mut self, e: &Expr) -> Option<Option<Expr>>;
    fn control_read(&mut self, e: &Expr, index: Option<Expr>) -> Option<Option<Expr>>;
    fn slot_read(&mut self, e: &Expr, slot: &Slot, index: Option<Expr>, allowed: &BTreeSet<Atom>) -> Option<Option<Expr>>;
    fn bare_projected_var(&mut self, e: &Expr, var: VarId) -> Option<Option<Expr>>;
    fn bare_control_var(&mut self, e: &Expr) -> Option<Option<Expr>>;
}

/// Phase-context narrowing for state predicates (`INVARIANT`, `CONSTRAINT`,
/// `init_props`), supporting phase-guarded observations such as
/// `ctrl = P => Q(slot)` and `\A k \in K : ctrl[k] = P => Q(m[k])`.
#[derive(Clone)]
pub(super) enum ObsContext {
    Scalar(BTreeSet<Atom>),
    Keyed(BTreeMap<LocalId, BTreeSet<Atom>>),
}

#[derive(Clone, Default)]
pub(super) struct PhaseGuards {
    scalar: Option<BTreeSet<Atom>>,
    keyed: BTreeMap<LocalId, BTreeSet<Atom>>,
}

impl ObsContext {
    pub(super) fn all(phases: &BTreeSet<Atom>, keyed: bool) -> Self {
        if keyed {
            Self::Keyed(BTreeMap::new())
        } else {
            Self::Scalar(phases.clone())
        }
    }

    pub(super) fn narrow(&self, guards: &PhaseGuards, phases: &BTreeSet<Atom>) -> Self {
        match self {
            Self::Scalar(cur) => match &guards.scalar {
                Some(g) => Self::Scalar(cur.intersection(g).cloned().collect()),
                None => Self::Scalar(cur.clone()),
            },
            Self::Keyed(cur) => {
                let mut next = cur.clone();
                for (l, g) in &guards.keyed {
                    let base = next.get(l).unwrap_or(phases);
                    let inter: BTreeSet<Atom> = base.intersection(g).cloned().collect();
                    next.insert(*l, inter);
                }
                Self::Keyed(next)
            }
        }
    }

    pub(super) fn remove_locals(&self, locals: &[LocalId]) -> Self {
        match self {
            Self::Scalar(_) => self.clone(),
            Self::Keyed(cur) => {
                let mut next = cur.clone();
                for l in locals {
                    next.remove(l);
                }
                Self::Keyed(next)
            }
        }
    }

    pub(super) fn phases_for<'a>(&'a self, reader: Option<LocalId>, all: &'a BTreeSet<Atom>) -> &'a BTreeSet<Atom> {
        match self {
            Self::Scalar(ps) => ps,
            Self::Keyed(map) => reader.and_then(|l| map.get(&l)).unwrap_or(all),
        }
    }
}

impl PhaseGuards {
    fn intersect(&mut self, other: Self, phases: &BTreeSet<Atom>) {
        if let Some(os) = other.scalar {
            self.scalar = Some(match self.scalar.take() {
                Some(cur) => cur.intersection(&os).cloned().collect(),
                None => phases.intersection(&os).cloned().collect(),
            });
        }
        for (l, og) in other.keyed {
            let base = self.keyed.get(&l).unwrap_or(phases);
            let inter: BTreeSet<Atom> = base.intersection(&og).cloned().collect();
            self.keyed.insert(l, inter);
        }
    }

    fn union_common(items: &[Self]) -> Self {
        let Some((first, rest)) = items.split_first() else {
            return Self::default();
        };
        let mut out = Self::default();
        if let Some(fs) = &first.scalar {
            if rest.iter().all(|g| g.scalar.is_some()) {
                let mut acc = fs.clone();
                for g in rest {
                    acc.extend(g.scalar.as_ref().unwrap().iter().cloned());
                }
                out.scalar = Some(acc);
            }
        }
        for (l, fg) in &first.keyed {
            if rest.iter().all(|g| g.keyed.contains_key(l)) {
                let mut acc = fg.clone();
                for g in rest {
                    acc.extend(g.keyed[l].iter().cloned());
                }
                out.keyed.insert(*l, acc);
            }
        }
        out
    }
}

pub(super) fn derive_analysis<'a>(
    domains: &'a Domains,
    control: Control,
    phases: &'a BTreeSet<Atom>,
    keys: Option<&'a BTreeSet<Atom>>,
    branches: (&[Branch], &[(Branch, Vec<usize>)]),
    spec: super::CheckSpec<'_>,
) -> Option<Analysis<'a>> {
    let (initial, step_pos) = branches;
    if initial.is_empty() || step_pos.is_empty() {
        return None;
    }
    let steps: Vec<Branch> = step_pos.iter().map(|(b, _)| b.clone()).collect();
    match &control {
        Control::RecordField { var, field } => {
            let fields = match &domains.vars[var.idx()] {
                Domain::Record(fs) if keys.is_none() => fs,
                Domain::Function(ks, range) if keys == Some(ks) => {
                    let Domain::Record(fs) = &**range else { return None };
                    fs
                }
                _ => return None,
            };
            let mut a = Analysis {
                domains,
                control: control.clone(),
                phases,
                keys,
                live: fields.keys().map(|f| (Slot::RecordField(f.clone()), BTreeSet::new())).collect(),
                projected_vars: BTreeSet::from([*var]),
                remaining: 100_000,
            };
            a.live.get_mut(&Slot::RecordField(field.clone()))?.extend(phases.iter().cloned());
            a.run_liveness(step_pos, spec)?;
            // Keep singleton-valued fields live in every phase so the emitted
            // Lean `live` table matches the runtime `VIEW` exactly.
            for (f, dom) in fields {
                if is_singleton_domain(dom) {
                    if let Some(live) = a.live.get_mut(&Slot::RecordField(f.clone())) {
                        live.extend(phases.iter().cloned());
                    }
                }
            }
            Some(a)
        }
        Control::Var { var: ctrl } => {
            // Verify the control variable itself has constant initial phases and valid transfers.
            if !valid_control_init(domains, *ctrl, phases, keys, initial)
                || !valid_control_action(domains, *ctrl, keys, spec)
                || !steps.iter().all(|b| control_var_transfer(domains, *ctrl, phases, keys, b).is_some())
            {
                return None;
            }
            let mut cands: Vec<VarId> = (0..domains.vars.len())
                .filter(|&j| j != ctrl.idx())
                .filter(|&j| match keys {
                    None => !is_singleton_domain(&domains.vars[j]),
                    Some(ks) => matches!(&domains.vars[j], Domain::Function(k2, r) if k2 == ks && !is_singleton_domain(r)),
                })
                .map(|j| VarId(j as u32))
                .collect();
            if cands.is_empty() {
                return None;
            }
            // Fixed-point pruning: drop any companion variable that fails seed,
            // single-actor transfer/alignment, action check, or turns out live in
            // every phase, moving dropped companions back into retained state C.
            let final_analysis = loop {
                if cands.is_empty() {
                    return None;
                }
                let mut drop = BTreeSet::new();
                // 1. Validate Init seeds for surviving companions (no cyclic/self mentions).
                let active_set: BTreeSet<VarId> = cands.iter().copied().chain(std::iter::once(*ctrl)).collect();
                for &v in &cands {
                    if !valid_companion_init(domains, v, keys, initial, &active_set) {
                        drop.insert(v);
                    }
                }
                // Check non-binding Init terms do not mention projected companions.
                for init_b in initial {
                    for term in &init_b.terms {
                        if let ExprKind::Builtin { op: B::Eq, args } = &*term.kind {
                            if args.len() == 2 && variable(&args[0], false).is_some_and(|v| active_set.contains(&v)) {
                                continue;
                            }
                        }
                        if let ExprKind::Builtin { op: B::In, args } = &*term.kind {
                            if args.len() == 2 {
                                if let Some(v) = variable(&args[0], false) {
                                    if active_set.contains(&v) && domains.belongs(&domains.vars[v.idx()], &args[1]) {
                                        continue;
                                    }
                                }
                            }
                        }
                        for &v in &cands {
                            if mentions_var(term, v) {
                                drop.insert(v);
                            }
                        }
                    }
                    for bound in &init_b.bounds {
                        for &v in &cands {
                            if mentions_var(&bound.set, v) {
                                drop.insert(v);
                            }
                        }
                    }
                }
                // 2. Validate Next transfers & actor alignment across `{ctrl} ∪ cands`.
                for b in &steps {
                    let (ctrl_actor, _) = control_var_transfer(domains, *ctrl, phases, keys, b)?;
                    let guard_actor =
                        if ctrl_actor.is_none() && keys.is_some() { find_control_guard_actor(domains, &control, keys, b) } else { None };
                    let fixed_actor = ctrl_actor.or(guard_actor);
                    let mut updating: Vec<(VarId, LocalId)> = Vec::new();
                    for &v in &cands {
                        if drop.contains(&v) {
                            continue;
                        }
                        match companion_var_transfer(domains, v, keys, b) {
                            None => {
                                drop.insert(v);
                            }
                            Some(CompanionWrite::Unchanged) => {}
                            Some(CompanionWrite::Written { actor, .. }) => {
                                if let Some(a) = actor {
                                    if fixed_actor.is_some_and(|fa| fa != a) {
                                        drop.insert(v);
                                    } else {
                                        updating.push((v, a));
                                    }
                                }
                            }
                        }
                    }
                    if fixed_actor.is_none() {
                        let actors: BTreeSet<LocalId> = updating.iter().map(|(_, a)| *a).collect();
                        if actors.len() > 1 {
                            for (v, _) in updating {
                                drop.insert(v);
                            }
                        }
                    }
                }
                // 3. Validate action checks for each companion.
                for &v in &cands {
                    if !drop.contains(&v) && !valid_companion_action(domains, *ctrl, v, keys, spec) {
                        drop.insert(v);
                    }
                }
                if !drop.is_empty() {
                    cands.retain(|v| !drop.contains(v));
                    continue;
                }
                // 4. Run backward liveness on surviving companions.
                let mut a = Analysis {
                    domains,
                    control: control.clone(),
                    phases,
                    keys,
                    live: cands.iter().map(|&v| (Slot::CompanionVar(v), BTreeSet::new())).collect(),
                    projected_vars: cands.iter().copied().collect(),
                    remaining: 100_000,
                };
                a.run_liveness(step_pos, spec)?;
                let all_live: BTreeSet<VarId> = cands
                    .iter()
                    .copied()
                    .filter(|v| a.live.get(&Slot::CompanionVar(*v)).is_none_or(|ps| ps.len() >= phases.len()))
                    .collect();
                if !all_live.is_empty() {
                    cands.retain(|v| !all_live.contains(v));
                    continue;
                }
                break a;
            };
            Some(final_analysis)
        }
    }
}

/// Ordered control-source candidates eligible for phase-dependent field masking
/// (record field, fixed-domain map-of-records field, fixed-domain control map,
/// and scalar control variable). Single owner shared by the `VIEW` installer
/// (`phase.rs`) and symmetry composition matcher (`liveness/sym.rs`).
pub(super) fn control_candidates(domains: &Domains, span: Span) -> Vec<(Control, &BTreeSet<Atom>, Option<&BTreeSet<Atom>>)> {
    let mut out = Vec::new();
    let eligible_phases = |phases: &BTreeSet<Atom>, min: usize| -> bool {
        (min..=32).contains(&phases.len())
            && super::domain::compatible(phases)
            && phases.iter().all(|p| domains.atom_expr(p, span).is_some())
    };
    for (i, d) in domains.vars.iter().enumerate() {
        let var = VarId(i as u32);
        match d {
            Domain::Record(fs) if fs.len() <= 32 => {
                for (control, values) in fs {
                    if let Some(phases) = values.atoms() {
                        if eligible_phases(phases, 1) {
                            out.push((Control::RecordField { var, field: control.clone() }, phases, None));
                        }
                    }
                }
            }
            Domain::Function(keys, range) if !keys.is_empty() && keys.len() <= 256 && super::domain::compatible(keys) => match &**range {
                Domain::Record(fs) if fs.len() <= 32 => {
                    for (control, values) in fs {
                        if let Some(phases) = values.atoms() {
                            if eligible_phases(phases, 1) {
                                out.push((Control::RecordField { var, field: control.clone() }, phases, Some(keys)));
                            }
                        }
                    }
                }
                _ => {
                    if let Some(phases) = range.atoms() {
                        if eligible_phases(phases, 2) {
                            out.push((Control::Var { var }, phases, Some(keys)));
                        }
                    }
                }
            },
            Domain::Atoms(phases) if eligible_phases(phases, 2) => {
                out.push((Control::Var { var }, phases, None));
            }
            _ => {}
        }
    }
    out
}

#[allow(clippy::too_many_arguments)]
pub(super) fn derive(
    program: &Program,
    domains: &Domains,
    control: Control,
    phases: &BTreeSet<Atom>,
    keys: Option<&BTreeSet<Atom>>,
    branches: (&[Branch], &[(Branch, Vec<usize>)]),
    spec: super::CheckSpec<'_>,
    avoid_keys: Option<&BTreeSet<Arc<str>>>,
) -> Option<(FieldProjection, Option<super::OpenCert>)> {
    let (initial, step_pos) = branches;
    let a = derive_analysis(domains, control, phases, keys, branches, spec)?;
    let steps: Vec<Branch> = step_pos.iter().map(|(b, _)| b.clone()).collect();
    let projection = a.view(program, initial, avoid_keys)?;
    let cert = lean::emit(&a, initial, &steps, spec);
    Some((projection, cert))
}

fn is_empty_domain(d: &Domain) -> bool {
    match d {
        Domain::Bottom => true,
        Domain::Atoms(a) => a.is_empty(),
        Domain::Record(fs) => fs.values().any(is_empty_domain),
        Domain::Records(rs) => rs.iter().all(|fs| fs.values().any(is_empty_domain)),
        Domain::Function(ks, r) => !ks.is_empty() && is_empty_domain(r),
        _ => false,
    }
}

fn is_singleton_domain(d: &Domain) -> bool {
    match d {
        Domain::Bottom => true,
        Domain::Atoms(a) => a.len() <= 1,
        Domain::Set(elem) | Domain::Seq(elem) => is_empty_domain(elem),
        Domain::Record(fs) => fs.values().all(is_singleton_domain),
        Domain::Records(rs) => rs.is_empty() || (rs.len() == 1 && rs[0].values().all(is_singleton_domain)),
        Domain::Function(ks, r) => ks.is_empty() || is_singleton_domain(r),
        Domain::Top | Domain::Integer(_) | Domain::Mapping(_) => false,
    }
}

fn is_closed_const_expr(domains: &Domains, e: &Expr, depth: usize) -> bool {
    if depth >= 16 {
        return false;
    }
    if domains.atom_value(e).is_some() {
        return true;
    }
    match &*e.kind {
        ExprKind::Const(_) => true,
        ExprKind::SetEnum(es) | ExprKind::Tuple(es) => es.iter().all(|x| is_closed_const_expr(domains, x, depth + 1)),
        ExprKind::Record(fs) => fs.iter().all(|(_, x)| is_closed_const_expr(domains, x, depth + 1)),
        ExprKind::FnConstruct { bounds, body } if bounds.len() == 1 => {
            let b = &bounds[0];
            if let BoundVars::Many(ids) = &b.vars {
                ids.len() == 1
                    && domains.exact_set(&b.set).is_some()
                    && !mentions_local(body, ids[0])
                    && is_closed_const_expr(domains, body, depth + 1)
            } else {
                false
            }
        }
        _ => false,
    }
}

fn unwrap_singleton_fn_construct<'e>(domains: &Domains, e: &'e Expr, keys: &BTreeSet<Atom>) -> Option<&'e Expr> {
    if keys.len() != 1 {
        return None;
    }
    let ExprKind::FnConstruct { bounds, body } = &*e.kind else { return None };
    let [bound] = bounds.as_slice() else { return None };
    let BoundVars::Many(ids) = &bound.vars else { return None };
    let [id] = ids.as_slice() else { return None };
    if domains.exact_set(&bound.set).as_ref() != Some(keys) || mentions_local(body, *id) {
        return None;
    }
    Some(body)
}

fn unwrap_init_map_body<'e>(domains: &Domains, e: &'e Expr, keys: &BTreeSet<Atom>) -> Option<(&'e Expr, LocalId)> {
    let ExprKind::FnConstruct { bounds, body } = &*e.kind else { return None };
    let [bound] = bounds.as_slice() else { return None };
    let BoundVars::Many(ids) = &bound.vars else { return None };
    let [id] = ids.as_slice() else { return None };
    if domains.exact_set(&bound.set).as_ref() != Some(keys) {
        return None;
    }
    Some((body, *id))
}

fn valid_control_init(domains: &Domains, ctrl: VarId, phases: &BTreeSet<Atom>, keys: Option<&BTreeSet<Atom>>, initial: &[Branch]) -> bool {
    for b in initial {
        let Some(rhs) = binding(b, ctrl, false) else { return false };
        let body = match keys {
            None => &rhs,
            Some(ks) => {
                let Some((body, k_id)) = unwrap_init_map_body(domains, &rhs, ks) else { return false };
                if mentions_local(body, k_id) {
                    return false;
                }
                body
            }
        };
        let Some(p) = domains.atom_value(body) else { return false };
        if !phases.contains(&p) {
            return false;
        }
    }
    true
}

fn valid_companion_init(domains: &Domains, v: VarId, keys: Option<&BTreeSet<Atom>>, initial: &[Branch], active: &BTreeSet<VarId>) -> bool {
    for b in initial {
        let Some(rhs) = binding(b, v, false) else { return false };
        let body = match keys {
            None => &rhs,
            Some(ks) => {
                let Some((body, _)) = unwrap_init_map_body(domains, &rhs, ks) else { return false };
                body
            }
        };
        if mentions_var_where(body, &mut |v| active.contains(&v)) {
            return false;
        }
    }
    true
}

/// Single shared classification for action-check expressions (`ACTION_CONSTRAINT`
/// and `action_props`), consumed identically by companion pruning, liveness
/// analysis, and Lean certificate lowering.
pub(super) enum ActionRead<'e> {
    /// Keyed or scalar slot/control read (`r.f`, `r[k].f`, `v`, `v[k]`, optionally primed).
    Slot { slot: Option<Slot>, key: Option<&'e Expr>, map_primed: bool, key_primed: bool },
    /// Inductively proved membership (`v \in S`) that needs no slot values.
    ProvedMembership,
    /// Fixed-domain query (`DOMAIN v`) on a fixed-key map that needs no slot values.
    FixedDomain,
    /// Bare reference to the control variable (whole phase map, retained verbatim).
    ControlMap,
    /// `[action]_sub` whose stuttering subscript mentions no managed variable.
    BoxAction { action: &'e Expr, sub: &'e Expr },
    /// `UNCHANGED args` over unmanaged variables only.
    Unchanged(&'e [Expr]),
    /// Unsupported managed action shape (bare projected map, managed subscript,
    /// `<<A>>_v`, `@`, `ENABLED`, managed `UNCHANGED`/`Prime`, double-primed lookup).
    Unsupported,
    /// Ordinary composite expression: recurse on children.
    Recurse,
}

fn unprime(e: &Expr) -> (&Expr, bool) {
    if let ExprKind::Builtin { op: B::Prime, args } = &*e.kind {
        if let [inner] = args.as_slice() {
            return (inner, true);
        }
    }
    (e, false)
}

fn classify_action_expr<'e>(
    domains: &Domains,
    control: &Control,
    keys: Option<&BTreeSet<Atom>>,
    is_projected: &impl Fn(VarId) -> bool,
    e: &'e Expr,
) -> ActionRead<'e> {
    let is_control_var = |v: VarId| matches!(control, Control::Var { var } if v == *var);
    let is_managed = |v: VarId| v == control.var() || is_projected(v);
    let mentions_managed = |expr: &Expr| -> bool {
        fn rec(e: &Expr, is_managed: &impl Fn(VarId) -> bool) -> bool {
            if matches!(&*e.kind, ExprKind::Var(v) if is_managed(*v)) {
                return true;
            }
            let mut found = false;
            visit::children(e, &mut |c| found |= rec(c, is_managed));
            found
        }
        rec(expr, &is_managed)
    };

    // 1. Slot or control lookup (`r.f`, `r[k].f`, `v`, `v[k]`, with at most one prime).
    let slot_hit = match control {
        Control::RecordField { var, field: ctrl_field } => {
            if let ExprKind::Field { record, field } = &*e.kind {
                let (record, lookup_primed) = unprime(record);
                let slot = if field == ctrl_field { None } else { Some(Slot::RecordField(field.clone())) };
                if keys.is_none() && variable(record, false) == Some(*var) {
                    Some((slot, None, lookup_primed, false))
                } else if keys.is_some() {
                    if let ExprKind::FnApp { func, args } = &*record.kind {
                        if let [key] = args.as_slice() {
                            let (func, map_primed) = unprime(func);
                            if variable(func, false) == Some(*var) {
                                if lookup_primed && map_primed {
                                    return ActionRead::Unsupported;
                                }
                                Some((slot, Some(key), lookup_primed || map_primed, lookup_primed))
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            }
        }
        Control::Var { var: ctrl } => {
            if keys.is_none() {
                let (inner, primed) = unprime(e);
                variable(inner, false).and_then(|v| {
                    if v == *ctrl {
                        Some((None, None, primed, false))
                    } else if is_projected(v) {
                        Some((Some(Slot::CompanionVar(v)), None, primed, false))
                    } else {
                        None
                    }
                })
            } else {
                let (outer, lookup_primed) = unprime(e);
                if let ExprKind::FnApp { func, args } = &*outer.kind {
                    if let [key] = args.as_slice() {
                        let (f, map_primed) = unprime(func);
                        if let Some(v) = variable(f, false) {
                            if is_managed(v) {
                                if lookup_primed && map_primed {
                                    return ActionRead::Unsupported;
                                }
                                let slot = if v == *ctrl { None } else { Some(Slot::CompanionVar(v)) };
                                Some((slot, Some(key), lookup_primed || map_primed, lookup_primed))
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
        }
    };
    if let Some((slot, key, map_primed, key_primed)) = slot_hit {
        return ActionRead::Slot { slot, key, map_primed, key_primed };
    }

    // 2. Proved membership (`v \in S`) and fixed-domain queries (`DOMAIN v`).
    if let ExprKind::Builtin { op: B::In, args } = &*e.kind {
        if args.len() == 2
            && variable(&args[0], false).is_some_and(is_managed)
            && domains.belongs(&domains.vars[variable(&args[0], false).unwrap().idx()], &args[1])
        {
            return ActionRead::ProvedMembership;
        }
    }
    if keys.is_some() {
        if let ExprKind::Builtin { op: B::Domain, args } = &*e.kind {
            if args.len() == 1 && variable(&args[0], false).is_some_and(is_managed) {
                return ActionRead::FixedDomain;
            }
        }
    }

    // 3. Remaining managed variable / temporal-action shapes.
    match &*e.kind {
        ExprKind::Var(v) if is_projected(*v) => ActionRead::Unsupported,
        ExprKind::Var(v) if is_control_var(*v) => ActionRead::ControlMap,
        ExprKind::BoxAction { action, sub } => {
            if mentions_managed(sub) {
                ActionRead::Unsupported
            } else {
                ActionRead::BoxAction { action, sub }
            }
        }
        ExprKind::AngleAction { .. } | ExprKind::At => ActionRead::Unsupported,
        ExprKind::Builtin { op: B::Enabled, .. } => ActionRead::Unsupported,
        ExprKind::Builtin { op: B::Unchanged, args } => {
            if args.iter().any(mentions_managed) {
                ActionRead::Unsupported
            } else {
                ActionRead::Unchanged(args)
            }
        }
        ExprKind::Builtin { op: B::Prime, args } => {
            if args.iter().any(mentions_managed) {
                ActionRead::Unsupported
            } else {
                ActionRead::Recurse
            }
        }
        _ => ActionRead::Recurse,
    }
}

fn check_action_scope(
    domains: &Domains,
    control: &Control,
    keys: Option<&BTreeSet<Atom>>,
    is_projected: &impl Fn(VarId) -> bool,
    spec: super::CheckSpec<'_>,
) -> bool {
    fn walk(domains: &Domains, control: &Control, keys: Option<&BTreeSet<Atom>>, is_projected: &impl Fn(VarId) -> bool, e: &Expr) -> bool {
        match classify_action_expr(domains, control, keys, is_projected, e) {
            ActionRead::Slot { key, .. } => key.is_none_or(|k| walk(domains, control, keys, is_projected, k)),
            ActionRead::ProvedMembership | ActionRead::FixedDomain | ActionRead::ControlMap => true,
            ActionRead::BoxAction { action, .. } => walk(domains, control, keys, is_projected, action),
            ActionRead::Unchanged(args) => args.iter().all(|a| walk(domains, control, keys, is_projected, a)),
            ActionRead::Unsupported => false,
            ActionRead::Recurse => {
                let mut ok = true;
                visit::children(e, &mut |c| ok &= walk(domains, control, keys, is_projected, c));
                ok
            }
        }
    }
    spec.action_constraints.iter().chain(spec.action_props.iter()).all(|e| walk(domains, control, keys, is_projected, e))
}

fn valid_control_action(domains: &Domains, ctrl: VarId, keys: Option<&BTreeSet<Atom>>, spec: super::CheckSpec<'_>) -> bool {
    check_action_scope(domains, &Control::Var { var: ctrl }, keys, &|_| false, spec)
}

fn valid_companion_action(domains: &Domains, ctrl: VarId, v: VarId, keys: Option<&BTreeSet<Atom>>, spec: super::CheckSpec<'_>) -> bool {
    check_action_scope(domains, &Control::Var { var: ctrl }, keys, &|x| x == v, spec)
}

/// Extract the control variable's transfer `(actor, target_phase)` on a branch.
fn control_var_transfer(
    domains: &Domains,
    ctrl: VarId,
    phases: &BTreeSet<Atom>,
    keys: Option<&BTreeSet<Atom>>,
    branch: &Branch,
) -> Option<(Option<LocalId>, Option<Atom>)> {
    let rhs = binding(branch, ctrl, true)?;
    if variable(&rhs, false) == Some(ctrl) {
        return Some((None, None));
    }
    match keys {
        None => {
            let phase = domains.atom_value(&rhs)?;
            phases.contains(&phase).then_some((None, Some(phase)))
        }
        Some(ks) => {
            if let Some(body) = unwrap_singleton_fn_construct(domains, &rhs, ks) {
                let phase = domains.atom_value(body)?;
                return phases.contains(&phase).then_some((None, Some(phase)));
            }
            let ExprKind::Except { base, updates } = &*rhs.kind else { return None };
            if variable(base, false) != Some(ctrl) || updates.len() != 1 {
                return None;
            }
            let (path, val) = &updates[0];
            let [ExceptKey::Index(args)] = path.as_slice() else { return None };
            let [idx] = args.as_slice() else { return None };
            let ExprKind::Local(actor) = &*idx.kind else { return None };
            let locals = domains.locals(&branch.bounds);
            if !locals.get(actor)?.atoms()?.is_subset(ks) {
                return None;
            }
            let phase = domains.atom_value(val)?;
            phases.contains(&phase).then_some((Some(*actor), Some(phase)))
        }
    }
}

enum CompanionWrite {
    Unchanged,
    Written { actor: Option<LocalId>, rhs: Expr },
}

fn companion_var_transfer(domains: &Domains, v: VarId, keys: Option<&BTreeSet<Atom>>, branch: &Branch) -> Option<CompanionWrite> {
    let rhs = binding(branch, v, true)?;
    if variable(&rhs, false) == Some(v) {
        return Some(CompanionWrite::Unchanged);
    }
    match keys {
        None => Some(CompanionWrite::Written { actor: None, rhs }),
        Some(ks) => {
            if let Some(body) = unwrap_singleton_fn_construct(domains, &rhs, ks) {
                return Some(CompanionWrite::Written { actor: None, rhs: body.clone() });
            }
            let ExprKind::Except { base, updates } = &*rhs.kind else { return None };
            if variable(base, false) != Some(v) || updates.is_empty() {
                return None;
            }
            let locals = domains.locals(&branch.bounds);
            if updates.len() == 1 {
                let (path, val) = &updates[0];
                if let [ExceptKey::Index(args)] = path.as_slice() {
                    let [idx] = args.as_slice() else { return None };
                    let ExprKind::Local(actor) = &*idx.kind else { return None };
                    if !locals.get(actor)?.atoms()?.is_subset(ks) {
                        return None;
                    }
                    return Some(CompanionWrite::Written { actor: Some(*actor), rhs: val.clone() });
                }
            }
            // Partial nested update(s) on one actor entry (`[v EXCEPT ![a][j] = e, ...]`),
            // lowered as a full-entry write whose RHS reads `v[a]` so liveness keeps `v`
            // live in the source phase.
            let mut actor: Option<LocalId> = None;
            let mut inner_updates = Vec::with_capacity(updates.len());
            for (path, val) in updates {
                let (first, rest) = path.split_first()?;
                if rest.is_empty() {
                    return None;
                }
                let ExceptKey::Index(args) = first else { return None };
                let [idx] = args.as_slice() else { return None };
                let ExprKind::Local(a) = &*idx.kind else { return None };
                if actor.is_some_and(|old| old != *a) || !locals.get(a)?.atoms()?.is_subset(ks) {
                    return None;
                }
                actor = Some(*a);
                inner_updates.push((rest.to_vec(), val.clone()));
            }
            let a = actor?;
            let entry = Expr::new(
                ExprKind::FnApp { func: Expr::new(ExprKind::Var(v), rhs.span), args: vec![Expr::new(ExprKind::Local(a), rhs.span)] },
                rhs.span,
            );
            let sub_rhs = Expr::new(ExprKind::Except { base: entry, updates: inner_updates }, rhs.span);
            Some(CompanionWrite::Written { actor: Some(a), rhs: sub_rhs })
        }
    }
}

fn find_control_guard_actor(domains: &Domains, control: &Control, keys: Option<&BTreeSet<Atom>>, branch: &Branch) -> Option<LocalId> {
    let ks = keys?;
    let locals = domains.locals(&branch.bounds);
    branch.terms.iter().find_map(|e| {
        let e = match &*e.kind {
            ExprKind::Builtin { op: B::Not, args } if args.len() == 1 => &args[0],
            _ => e,
        };
        let ExprKind::Builtin { op, args } = &*e.kind else { return None };
        if args.len() != 2 {
            return None;
        }
        let check_side = |expr: &Expr| -> Option<LocalId> {
            let actor = match control {
                Control::RecordField { var, field } => {
                    let ExprKind::Field { record, field: f } = &*expr.kind else { return None };
                    if f != field {
                        return None;
                    }
                    let ExprKind::FnApp { func, args } = &*record.kind else { return None };
                    if variable(func, false) != Some(*var) || args.len() != 1 {
                        return None;
                    }
                    let ExprKind::Local(a) = &*args[0].kind else { return None };
                    *a
                }
                Control::Var { var } => {
                    let ExprKind::FnApp { func, args } = &*expr.kind else { return None };
                    if variable(func, false) != Some(*var) || args.len() != 1 {
                        return None;
                    }
                    let ExprKind::Local(a) = &*args[0].kind else { return None };
                    *a
                }
            };
            locals.get(&actor)?.atoms()?.is_subset(ks).then_some(actor)
        };
        if matches!(op, B::Eq | B::Neq) {
            check_side(&args[0]).or_else(|| check_side(&args[1]))
        } else if matches!(op, B::In | B::NotIn) {
            check_side(&args[0])
        } else {
            None
        }
    })
}

impl Analysis<'_> {
    pub(super) fn data_slots(&self) -> Vec<Slot> {
        match &self.control {
            Control::RecordField { field, .. } => {
                self.live.keys().filter(|s| !matches!(s, Slot::RecordField(f) if f == field)).cloned().collect()
            }
            Control::Var { .. } => self.live.keys().cloned().collect(),
        }
    }

    pub(super) fn is_projected_var(&self, v: VarId) -> bool {
        self.projected_vars.contains(&v)
    }

    pub(super) fn is_control_or_projected_var(&self, v: VarId) -> bool {
        v == self.control.var() || self.is_projected_var(v)
    }

    fn run_liveness(&mut self, step_pos: &[(Branch, Vec<usize>)], spec: super::CheckSpec<'_>) -> Option<()> {
        let root_ctx = ObsContext::all(self.phases, self.keys.is_some());
        for e in spec.all_state_preds() {
            self.read_obs(e, &root_ctx)?;
        }
        // Action checks preserve both endpoints of a step. A projected slot they
        // read is retained in every phase and stays observed, so the masked
        // representative keeps the exact value the check needs.
        for e in spec.action_constraints.iter().chain(spec.action_props.iter()) {
            self.action(e)?;
        }
        let mut edges = Vec::new();
        for (branch, bound_pos) in step_pos {
            let transfer = self.transfer_branch(branch)?;
            let mut context = self.phases.clone();
            // Process bounds placed at `term_pos == 0` (before any term in the branch).
            for (b, &pos) in branch.bounds.iter().zip(bound_pos.iter()) {
                if pos == 0 {
                    self.read(&b.set, &context, transfer.actor)?;
                }
            }
            for (idx, term) in branch.terms.iter().enumerate() {
                match &*term.kind {
                    ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 && variable(&args[0], true).is_some() => {
                        let lhs_var = variable(&args[0], true).unwrap();
                        match &self.control {
                            Control::RecordField { var, .. } if lhs_var == *var => {
                                for rhs in transfer.writes.values() {
                                    self.read(rhs, &context, transfer.actor)?;
                                }
                            }
                            Control::Var { var: ctrl } if lhs_var == *ctrl => {}
                            Control::Var { .. } if self.is_projected_var(lhs_var) => {
                                if let Some(rhs) = transfer.writes.get(&Slot::CompanionVar(lhs_var)) {
                                    self.read(rhs, &context, transfer.actor)?;
                                }
                            }
                            _ => {
                                self.read(&args[1], &context, transfer.actor)?;
                            }
                        }
                    }
                    ExprKind::Builtin { op: B::Unchanged, args } if args.len() == 1 => {
                        self.read_unchanged(&args[0])?;
                    }
                    _ => {
                        self.read(term, &context, transfer.actor)?;
                        if let Some(allowed) = self.guard(term, transfer.actor) {
                            context.retain(|p| allowed.contains(p));
                        }
                    }
                }
                let next_pos = idx + 1;
                for (b, &pos) in branch.bounds.iter().zip(bound_pos.iter()) {
                    if pos == next_pos {
                        self.read(&b.set, &context, transfer.actor)?;
                    }
                }
            }
            for source in context {
                let target = transfer.target.as_ref().unwrap_or(&source).clone();
                edges.push((source, target, transfer.writes.keys().cloned().collect::<BTreeSet<_>>()));
            }
        }
        loop {
            let mut changed = false;
            for (source, target, writes) in &edges {
                for (slot, live) in &mut self.live {
                    if !writes.contains(slot) && live.contains(target) {
                        changed |= live.insert(source.clone());
                    }
                }
            }
            if !changed {
                break;
            }
        }
        Some(())
    }

    pub(super) fn transfer_branch(&self, branch: &Branch) -> Option<Transfer> {
        match &self.control {
            Control::RecordField { var, field: ctrl_field } => {
                let rhs = binding(branch, *var, true)?;
                self.transfer_record(*var, ctrl_field, &rhs, branch)
            }
            Control::Var { var: ctrl } => {
                let (ctrl_actor, target) = control_var_transfer(self.domains, *ctrl, self.phases, self.keys, branch)?;
                let mut actor = ctrl_actor.or_else(|| {
                    if self.keys.is_some() {
                        find_control_guard_actor(self.domains, &self.control, self.keys, branch)
                    } else {
                        None
                    }
                });
                let mut writes = BTreeMap::new();
                for slot in self.live.keys() {
                    let Slot::CompanionVar(v) = *slot else { return None };
                    match companion_var_transfer(self.domains, v, self.keys, branch)? {
                        CompanionWrite::Unchanged => {}
                        CompanionWrite::Written { actor: w_actor, rhs } => {
                            if let Some(a) = w_actor {
                                if actor.is_some_and(|old| old != a) {
                                    return None;
                                }
                                actor = Some(a);
                            }
                            writes.insert(Slot::CompanionVar(v), rhs);
                        }
                    }
                }
                Some(Transfer { actor, writes, target })
            }
        }
    }

    fn insert_record_fields(&self, ctrl_field: &str, fs: &[(Arc<str>, Expr)], out: &mut Transfer) -> Option<()> {
        if fs.len() != self.live.len() {
            return None;
        }
        for (field, value) in fs {
            let slot = Slot::RecordField(field.clone());
            if !self.live.contains_key(&slot) || out.writes.insert(slot, value.clone()).is_some() {
                return None;
            }
            if &**field == ctrl_field {
                let phase = self.domains.atom_value(value)?;
                if !self.phases.contains(&phase) {
                    return None;
                }
                out.target = Some(phase);
            }
        }
        Some(())
    }

    fn transfer_record(&self, var: VarId, ctrl_field: &str, rhs: &Expr, branch: &Branch) -> Option<Transfer> {
        let mut out = Transfer { actor: None, writes: BTreeMap::new(), target: None };
        if variable(rhs, false) == Some(var) {
            // An unchanged map can still have actor-specific guards. Using
            // one referenced actor keeps its phase context; other actors'
            // reads remain conservative in `read`.
            if self.keys.is_some() {
                out.actor = find_control_guard_actor(self.domains, &self.control, self.keys, branch);
            }
            return Some(out);
        }
        if self.keys.is_none() {
            if let ExprKind::Record(fs) = &*rhs.kind {
                self.insert_record_fields(ctrl_field, fs, &mut out)?;
                return Some(out);
            }
        } else if let Some(keys) = self.keys {
            if let Some(body) = unwrap_singleton_fn_construct(self.domains, rhs, keys) {
                let ExprKind::Record(fs) = &*body.kind else { return None };
                out.actor = find_control_guard_actor(self.domains, &self.control, self.keys, branch);
                self.insert_record_fields(ctrl_field, fs, &mut out)?;
                return Some(out);
            }
        }
        let ExprKind::Except { base, updates } = &*rhs.kind else { return None };
        if variable(base, false) != Some(var) {
            return None;
        }
        let locals = self.domains.locals(&branch.bounds);
        for (path, value) in updates {
            match (self.keys, path.as_slice()) {
                (None, [ExceptKey::Field(f)]) => {
                    let slot = Slot::RecordField(f.clone());
                    if !self.live.contains_key(&slot) || out.writes.insert(slot, value.clone()).is_some() {
                        return None;
                    }
                    if &**f == ctrl_field {
                        let phase = self.domains.atom_value(value)?;
                        if !self.phases.contains(&phase) {
                            return None;
                        }
                        out.target = Some(phase);
                    }
                }
                (Some(keys), [ExceptKey::Index(args), ExceptKey::Field(f)]) if args.len() == 1 => {
                    let ExprKind::Local(actor) = &*args[0].kind else { return None };
                    if out.actor.is_some_and(|old| old != *actor) {
                        return None;
                    }
                    // An EXCEPT outside the domain does not overwrite anything.
                    if !locals.get(actor)?.atoms()?.is_subset(keys) {
                        return None;
                    }
                    out.actor = Some(*actor);
                    let slot = Slot::RecordField(f.clone());
                    if !self.live.contains_key(&slot) || out.writes.insert(slot, value.clone()).is_some() {
                        return None;
                    }
                    if &**f == ctrl_field {
                        let phase = self.domains.atom_value(value)?;
                        if !self.phases.contains(&phase) {
                            return None;
                        }
                        out.target = Some(phase);
                    }
                }
                (Some(keys), [ExceptKey::Index(args)]) if args.len() == 1 => {
                    let ExprKind::Local(actor) = &*args[0].kind else { return None };
                    if out.actor.is_some_and(|old| old != *actor) || !locals.get(actor)?.atoms()?.is_subset(keys) {
                        return None;
                    }
                    out.actor = Some(*actor);
                    match &*value.kind {
                        ExprKind::Record(fs) => {
                            self.insert_record_fields(ctrl_field, fs, &mut out)?;
                        }
                        ExprKind::Except { base: inner_base, updates: inner_updates } if updates.len() == 1 => {
                            // `[m EXCEPT ![actor] = [m[actor] EXCEPT !.f = e, ...]]` (expanded from `@`).
                            let ExprKind::FnApp { func, args: iargs } = &*inner_base.kind else { return None };
                            if variable(func, false) != Some(var)
                                || iargs.len() != 1
                                || !matches!(&*iargs[0].kind, ExprKind::Local(l) if *l == *actor)
                            {
                                return None;
                            }
                            for (ipath, ival) in inner_updates {
                                let [ExceptKey::Field(f)] = ipath.as_slice() else { return None };
                                let slot = Slot::RecordField(f.clone());
                                if !self.live.contains_key(&slot) || out.writes.insert(slot, ival.clone()).is_some() {
                                    return None;
                                }
                                if &**f == ctrl_field {
                                    let phase = self.domains.atom_value(ival)?;
                                    if !self.phases.contains(&phase) {
                                        return None;
                                    }
                                    out.target = Some(phase);
                                }
                            }
                        }
                        _ => return None,
                    }
                }
                _ => return None,
            }
        }
        Some(out)
    }

    /// Recognize a control-phase read (returning the optional index expression).
    pub(super) fn control_read<'e>(&self, e: &'e Expr) -> Option<Option<&'e Expr>> {
        match &self.control {
            Control::RecordField { var, field } => {
                let ExprKind::Field { record, field: f } = &*e.kind else { return None };
                if f != field {
                    return None;
                }
                if self.keys.is_none() && variable(record, false) == Some(*var) {
                    return Some(None);
                }
                if self.keys.is_some() {
                    if let ExprKind::FnApp { func, args } = &*record.kind {
                        if variable(func, false) == Some(*var) && args.len() == 1 {
                            return Some(Some(&args[0]));
                        }
                    }
                }
                None
            }
            Control::Var { var } => {
                if self.keys.is_none() && variable(e, false) == Some(*var) {
                    return Some(None);
                }
                if self.keys.is_some() {
                    if let ExprKind::FnApp { func, args } = &*e.kind {
                        if variable(func, false) == Some(*var) && args.len() == 1 {
                            return Some(Some(&args[0]));
                        }
                    }
                }
                None
            }
        }
    }

    /// Recognize a data-slot read, returning `(slot, optional_index_expr)`.
    pub(super) fn slot_read<'e>(&self, e: &'e Expr) -> Option<(Slot, Option<&'e Expr>)> {
        match &self.control {
            Control::RecordField { var, field: ctrl_field } => {
                let ExprKind::Field { record, field } = &*e.kind else { return None };
                if field == ctrl_field {
                    return None;
                }
                if self.keys.is_none() && variable(record, false) == Some(*var) {
                    return Some((Slot::RecordField(field.clone()), None));
                }
                if self.keys.is_some() {
                    if let ExprKind::FnApp { func, args } = &*record.kind {
                        if variable(func, false) == Some(*var) && args.len() == 1 {
                            return Some((Slot::RecordField(field.clone()), Some(&args[0])));
                        }
                    }
                }
                None
            }
            Control::Var { .. } => {
                if self.keys.is_none() {
                    let v = variable(e, false)?;
                    return self.is_projected_var(v).then_some((Slot::CompanionVar(v), None));
                }
                let ExprKind::FnApp { func, args } = &*e.kind else { return None };
                if args.len() != 1 {
                    return None;
                }
                let v = variable(func, false)?;
                self.is_projected_var(v).then_some((Slot::CompanionVar(v), Some(&args[0])))
            }
        }
    }

    fn read(&mut self, e: &Expr, context: &BTreeSet<Atom>, actor: Option<LocalId>) -> Option<()> {
        if self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        if let Some(index) = self.control_read(e) {
            if let Some(idx) = index {
                self.read(idx, context, actor)?;
            }
            return Some(());
        }
        if let Some((slot, index)) = self.slot_read(e) {
            if let Some(idx) = index {
                self.read(idx, context, actor)?;
            }
            let reader = index.and_then(|i| match &*i.kind {
                ExprKind::Local(l) => Some(*l),
                _ => None,
            });
            let phases = if self.keys.is_some() && (actor.is_none() || actor != reader) { self.phases } else { context };
            // Missing fields can fail; the record shape is retained, so no
            // stored value can affect that error.
            if let Some(live) = self.live.get_mut(&slot) {
                live.extend(phases.iter().cloned());
            }
            return Some(());
        }
        if self.is_proved_membership(e) || self.is_fixed_domain_read(e) {
            return Some(());
        }
        match &*e.kind {
            ExprKind::Var(v) if self.is_projected_var(*v) => match &self.control {
                Control::RecordField { .. } => {
                    for live in self.live.values_mut() {
                        live.extend(self.phases.iter().cloned());
                    }
                }
                Control::Var { .. } => {
                    if let Some(live) = self.live.get_mut(&Slot::CompanionVar(*v)) {
                        live.extend(self.phases.iter().cloned());
                    }
                }
            },
            ExprKind::Var(v) if matches!(&self.control, Control::Var { var } if *v == *var) => {}
            // These contexts change what a variable reference denotes. The
            // ordinary current-state read walk cannot justify a projection.
            ExprKind::Builtin { op: B::Prime, args }
                if args.len() == 1 && variable(&args[0], false).is_some_and(|v| !self.is_control_or_projected_var(v)) => {}
            ExprKind::At | ExprKind::Builtin { op: B::Prime | B::Enabled, .. } => return None,
            _ => {
                let mut valid = true;
                visit::children(e, &mut |child| {
                    valid &= self.read(child, context, actor).is_some();
                });
                if !valid {
                    return None;
                }
            }
        }
        Some(())
    }

    /// Single owner of phase-guarded observation traversal (`INVARIANT`,
    /// `init_props`, `CONSTRAINT`). Both backward liveness seeding (`read_obs`)
    /// and Lean certificate lowering (`mask_obs`) walk state predicates through
    /// this method so short-circuit order, true/false branch narrowing, binder
    /// scope, and reader-key selection cannot diverge.
    pub(super) fn walk_obs(&self, e: &Expr, ctx: &ObsContext, sink: &mut impl ObsSink, rebuild: bool) -> Option<Option<Expr>> {
        sink.step()?;
        if self.is_proved_membership(e) {
            return sink.proved_membership(e);
        }
        if self.is_fixed_domain_read(e) {
            return sink.fixed_domain(e);
        }
        if let Some(index) = self.control_read(e) {
            let masked_idx = match index {
                Some(idx) => self.walk_obs(idx, ctx, sink, rebuild)?,
                None => None,
            };
            return sink.control_read(e, masked_idx);
        }
        if let Some((slot, index)) = self.slot_read(e) {
            let reader = index.and_then(|i| match &*i.kind {
                ExprKind::Local(l) => Some(*l),
                _ => None,
            });
            let allowed = ctx.phases_for(reader, self.phases);
            let masked_idx = match index {
                Some(idx) => self.walk_obs(idx, ctx, sink, rebuild)?,
                None => None,
            };
            return sink.slot_read(e, &slot, masked_idx, allowed);
        }
        match &*e.kind {
            ExprKind::And(es) => {
                let mut cur = ctx.clone();
                let mut out = rebuild.then(|| Vec::with_capacity(es.len()));
                for item in es {
                    let m = self.walk_obs(item, &cur, sink, rebuild)?;
                    if let Some(out) = &mut out {
                        out.push(m?);
                    }
                    cur = cur.narrow(&self.implied_guards(item), self.phases);
                }
                return Some(out.map(|v| Expr::new(ExprKind::And(v), e.span)));
            }
            ExprKind::Or(es) => {
                let mut cur = ctx.clone();
                let mut out = rebuild.then(|| Vec::with_capacity(es.len()));
                for item in es {
                    let m = self.walk_obs(item, &cur, sink, rebuild)?;
                    if let Some(out) = &mut out {
                        out.push(m?);
                    }
                    cur = cur.narrow(&self.negated_guards(item), self.phases);
                }
                return Some(out.map(|v| Expr::new(ExprKind::Or(v), e.span)));
            }
            ExprKind::Builtin { op: B::Implies, args } if args.len() == 2 => {
                let lhs = self.walk_obs(&args[0], ctx, sink, rebuild)?;
                let narrowed = ctx.narrow(&self.implied_guards(&args[0]), self.phases);
                let rhs = self.walk_obs(&args[1], &narrowed, sink, rebuild)?;
                return Some(if rebuild {
                    Some(Expr::new(ExprKind::Builtin { op: B::Implies, args: vec![lhs?, rhs?] }, e.span))
                } else {
                    None
                });
            }
            ExprKind::If { cond, then, els } => {
                let c = self.walk_obs(cond, ctx, sink, rebuild)?;
                let then_ctx = ctx.narrow(&self.implied_guards(cond), self.phases);
                let else_ctx = ctx.narrow(&self.negated_guards(cond), self.phases);
                let t = self.walk_obs(then, &then_ctx, sink, rebuild)?;
                let el = self.walk_obs(els, &else_ctx, sink, rebuild)?;
                return Some(if rebuild { Some(Expr::new(ExprKind::If { cond: c?, then: t?, els: el? }, e.span)) } else { None });
            }
            ExprKind::Case { arms, other } => {
                let mut out_arms = rebuild.then(|| Vec::with_capacity(arms.len()));
                for (g, body) in arms {
                    let mg = self.walk_obs(g, ctx, sink, rebuild)?;
                    let arm_ctx = ctx.narrow(&self.implied_guards(g), self.phases);
                    let mb = self.walk_obs(body, &arm_ctx, sink, rebuild)?;
                    if let Some(out_arms) = &mut out_arms {
                        out_arms.push((mg?, mb?));
                    }
                }
                let out_other = match other {
                    Some(o) => {
                        let mo = self.walk_obs(o, ctx, sink, rebuild)?;
                        if rebuild {
                            Some(mo?)
                        } else {
                            None
                        }
                    }
                    None => None,
                };
                return Some(out_arms.map(|arms| Expr::new(ExprKind::Case { arms, other: out_other }, e.span)));
            }
            ExprKind::Quant { kind, bounds, body } => {
                let mut inner = ctx.clone();
                let mut out_bounds = rebuild.then(|| Vec::with_capacity(bounds.len()));
                for b in bounds {
                    let set = self.walk_obs(&b.set, &inner, sink, rebuild)?;
                    inner = inner.remove_locals(b.vars.locals());
                    if let Some(out_bounds) = &mut out_bounds {
                        out_bounds.push(Bound { vars: b.vars.clone(), set: set? });
                    }
                }
                let body = self.walk_obs(body, &inner, sink, rebuild)?;
                return Some(if rebuild {
                    Some(Expr::new(ExprKind::Quant { kind: *kind, bounds: out_bounds.unwrap(), body: body? }, e.span))
                } else {
                    None
                });
            }
            ExprKind::FnConstruct { bounds, body } => {
                let mut inner = ctx.clone();
                let mut out_bounds = rebuild.then(|| Vec::with_capacity(bounds.len()));
                for b in bounds {
                    let set = self.walk_obs(&b.set, &inner, sink, rebuild)?;
                    inner = inner.remove_locals(b.vars.locals());
                    if let Some(out_bounds) = &mut out_bounds {
                        out_bounds.push(Bound { vars: b.vars.clone(), set: set? });
                    }
                }
                let body = self.walk_obs(body, &inner, sink, rebuild)?;
                return Some(if rebuild {
                    Some(Expr::new(ExprKind::FnConstruct { bounds: out_bounds.unwrap(), body: body? }, e.span))
                } else {
                    None
                });
            }
            ExprKind::SetMap { expr, bounds } => {
                let mut inner = ctx.clone();
                let mut out_bounds = rebuild.then(|| Vec::with_capacity(bounds.len()));
                for b in bounds {
                    let set = self.walk_obs(&b.set, &inner, sink, rebuild)?;
                    inner = inner.remove_locals(b.vars.locals());
                    if let Some(out_bounds) = &mut out_bounds {
                        out_bounds.push(Bound { vars: b.vars.clone(), set: set? });
                    }
                }
                let expr = self.walk_obs(expr, &inner, sink, rebuild)?;
                return Some(if rebuild {
                    Some(Expr::new(ExprKind::SetMap { expr: expr?, bounds: out_bounds.unwrap() }, e.span))
                } else {
                    None
                });
            }
            ExprKind::SetFilter { bound, pred } => {
                let set = self.walk_obs(&bound.set, ctx, sink, rebuild)?;
                let inner = ctx.remove_locals(bound.vars.locals());
                let pred = self.walk_obs(pred, &inner, sink, rebuild)?;
                return Some(if rebuild {
                    Some(Expr::new(ExprKind::SetFilter { bound: Bound { vars: bound.vars.clone(), set: set? }, pred: pred? }, e.span))
                } else {
                    None
                });
            }
            ExprKind::Choose { vars, set, body } => {
                let set = match set {
                    Some(s) => {
                        let ms = self.walk_obs(s, ctx, sink, rebuild)?;
                        if rebuild {
                            Some(ms?)
                        } else {
                            None
                        }
                    }
                    None => None,
                };
                let inner = ctx.remove_locals(vars.locals());
                let body = self.walk_obs(body, &inner, sink, rebuild)?;
                return Some(if rebuild {
                    Some(Expr::new(ExprKind::Choose { vars: vars.clone(), set, body: body? }, e.span))
                } else {
                    None
                });
            }
            ExprKind::Var(v) if self.is_projected_var(*v) => return sink.bare_projected_var(e, *v),
            ExprKind::Var(v) if matches!(&self.control, Control::Var { var } if *v == *var) => return sink.bare_control_var(e),
            ExprKind::At | ExprKind::Builtin { op: B::Prime | B::Enabled, .. } => return None,
            _ => {}
        }
        if rebuild {
            let mut result = e.clone();
            let mut valid = true;
            visit::children_mut(&mut result, &mut |child| {
                if let Some(Some(m)) = self.walk_obs(child, ctx, sink, true) {
                    *child = m;
                } else {
                    valid = false;
                }
            });
            valid.then_some(Some(result))
        } else {
            let mut valid = true;
            visit::children(e, &mut |child| {
                valid &= self.walk_obs(child, ctx, sink, false).is_some();
            });
            valid.then_some(None)
        }
    }

    /// Scan a state predicate (`INVARIANT`, `init_props`, `CONSTRAINT`), narrowing
    /// observed phases under phase guards (`=>`, `/\`, `\/`, `IF`, `CASE`).
    fn read_obs(&mut self, e: &Expr, ctx: &ObsContext) -> Option<()> {
        struct LivenessObsSink<'a> {
            control: &'a Control,
            phases: &'a BTreeSet<Atom>,
            live: BTreeMap<Slot, BTreeSet<Atom>>,
            remaining: usize,
        }
        impl ObsSink for LivenessObsSink<'_> {
            fn step(&mut self) -> Option<()> {
                if self.remaining == 0 {
                    return None;
                }
                self.remaining -= 1;
                Some(())
            }
            fn proved_membership(&mut self, _e: &Expr) -> Option<Option<Expr>> {
                Some(None)
            }
            fn fixed_domain(&mut self, _e: &Expr) -> Option<Option<Expr>> {
                Some(None)
            }
            fn control_read(&mut self, _e: &Expr, _index: Option<Expr>) -> Option<Option<Expr>> {
                Some(None)
            }
            fn slot_read(&mut self, _e: &Expr, slot: &Slot, _index: Option<Expr>, allowed: &BTreeSet<Atom>) -> Option<Option<Expr>> {
                if let Some(live) = self.live.get_mut(slot) {
                    live.extend(allowed.iter().cloned());
                }
                Some(None)
            }
            fn bare_projected_var(&mut self, _e: &Expr, var: VarId) -> Option<Option<Expr>> {
                match self.control {
                    Control::RecordField { .. } => {
                        for live in self.live.values_mut() {
                            live.extend(self.phases.iter().cloned());
                        }
                    }
                    Control::Var { .. } => {
                        if let Some(live) = self.live.get_mut(&Slot::CompanionVar(var)) {
                            live.extend(self.phases.iter().cloned());
                        }
                    }
                }
                Some(None)
            }
            fn bare_control_var(&mut self, _e: &Expr) -> Option<Option<Expr>> {
                Some(None)
            }
        }
        let mut sink = LivenessObsSink {
            control: &self.control,
            phases: self.phases,
            live: std::mem::take(&mut self.live),
            remaining: self.remaining,
        };
        let res = self.walk_obs(e, ctx, &mut sink, false);
        self.live = sink.live;
        self.remaining = sink.remaining;
        res.map(|_| ())
    }

    pub(super) fn is_proved_membership(&self, e: &Expr) -> bool {
        let ExprKind::Builtin { op: B::In, args } = &*e.kind else { return false };
        if args.len() != 2 {
            return false;
        }
        let Some(v) = variable(&args[0], false) else { return false };
        self.is_control_or_projected_var(v) && self.domains.belongs(&self.domains.vars[v.idx()], &args[1])
    }

    pub(super) fn is_fixed_domain_read(&self, e: &Expr) -> bool {
        if self.keys.is_none() {
            return false;
        }
        let ExprKind::Builtin { op: B::Domain, args } = &*e.kind else { return false };
        args.len() == 1 && variable(&args[0], false).is_some_and(|v| self.is_control_or_projected_var(v))
    }

    /// Shared action-read classifier consumed by both `Analysis::action` and
    /// `Emitter::action_mask`.
    pub(super) fn classify_action_read<'e>(&self, e: &'e Expr) -> ActionRead<'e> {
        classify_action_expr(self.domains, &self.control, self.keys, &|v| self.is_projected_var(v), e)
    }

    /// Action predicates read both endpoints (`s` and `t`). Every slot they
    /// read must be preserved in every phase; whole-record/map, `UNCHANGED` and
    /// `ENABLED` shapes are refused because the projection cannot justify them.
    fn action(&mut self, e: &Expr) -> Option<()> {
        if self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        match self.classify_action_read(e) {
            ActionRead::Slot { slot, key, .. } => {
                if let Some(slot) = slot {
                    let live = self.live.get_mut(&slot)?;
                    live.extend(self.phases.iter().cloned());
                }
                // Reads inside the key expression are reads too.
                if let Some(key) = key {
                    self.action(key)?;
                }
                Some(())
            }
            ActionRead::ProvedMembership | ActionRead::FixedDomain | ActionRead::ControlMap => Some(()),
            ActionRead::BoxAction { action, .. } => self.action(action),
            ActionRead::Unchanged(args) => {
                for a in args {
                    self.action(a)?;
                }
                Some(())
            }
            ActionRead::Unsupported => None,
            ActionRead::Recurse => {
                let mut valid = true;
                visit::children(e, &mut |child| valid &= self.action(child).is_some());
                valid.then_some(())
            }
        }
    }

    pub(super) fn mentions_any_managed(&self, e: &Expr) -> bool {
        if matches!(&*e.kind, ExprKind::Var(v) if self.is_control_or_projected_var(*v)) {
            return true;
        }
        let mut found = false;
        visit::children(e, &mut |c| found |= self.mentions_any_managed(c));
        found
    }

    fn read_unchanged(&mut self, e: &Expr) -> Option<()> {
        match &*e.kind {
            ExprKind::Var(_) => Some(()),
            ExprKind::Tuple(es) => {
                for e in es {
                    self.read_unchanged(e)?;
                }
                Some(())
            }
            _ => None,
        }
    }

    /// Recognize an atomic phase guard (`ctrl = p`, `ctrl /= p`, `ctrl \in S`,
    /// `ctrl \notin S`), returning `(optional_local_key, phases_when_true)`.
    fn atomic_phase_guard(&self, e: &Expr) -> Option<(Option<LocalId>, BTreeSet<Atom>)> {
        let ExprKind::Builtin { op, args } = &*e.kind else { return None };
        if args.len() != 2 {
            return None;
        }
        let extract_reader = |idx: Option<&Expr>| -> Option<Option<LocalId>> {
            match (self.keys.is_some(), idx) {
                (false, None) => Some(None),
                (true, Some(k)) => match &*k.kind {
                    ExprKind::Local(l) => Some(Some(*l)),
                    _ => None,
                },
                _ => None,
            }
        };
        let (reader, tested, negate) = match op {
            B::Eq | B::Neq => {
                let neg = matches!(op, B::Neq);
                if let Some(idx) = self.control_read(&args[0]) {
                    (extract_reader(idx)?, BTreeSet::from([self.domains.atom_value(&args[1])?]), neg)
                } else if let Some(idx) = self.control_read(&args[1]) {
                    (extract_reader(idx)?, BTreeSet::from([self.domains.atom_value(&args[0])?]), neg)
                } else {
                    return None;
                }
            }
            B::In | B::NotIn => {
                let idx = self.control_read(&args[0])?;
                (extract_reader(idx)?, self.domains.exact_set(&args[1])?, matches!(op, B::NotIn))
            }
            _ => return None,
        };
        let mut union = self.phases.clone();
        union.extend(tested.iter().cloned());
        if !domain::compatible(&union) {
            return None;
        }
        let allowed =
            if negate { self.phases.difference(&tested).cloned().collect() } else { self.phases.intersection(&tested).cloned().collect() };
        Some((reader, allowed))
    }

    pub(super) fn guard(&self, e: &Expr, actor: Option<LocalId>) -> Option<BTreeSet<Atom>> {
        if let ExprKind::Builtin { op: B::Not, args } = &*e.kind {
            if args.len() == 1 {
                let (reader, allowed) = self.atomic_phase_guard(&args[0])?;
                if reader != actor || (self.keys.is_some() && actor.is_none()) {
                    return None;
                }
                return Some(self.phases.difference(&allowed).cloned().collect());
            }
        }
        let (reader, allowed) = self.atomic_phase_guard(e)?;
        if reader != actor || (self.keys.is_some() && actor.is_none()) {
            return None;
        }
        Some(allowed)
    }

    /// Phase restrictions guaranteed to hold whenever `e` evaluates to `TRUE`.
    pub(super) fn implied_guards(&self, e: &Expr) -> PhaseGuards {
        let mut out = PhaseGuards::default();
        if let Some((reader, allowed)) = self.atomic_phase_guard(e) {
            match reader {
                None => out.scalar = Some(allowed),
                Some(l) => {
                    out.keyed.insert(l, allowed);
                }
            }
            return out;
        }
        match &*e.kind {
            ExprKind::Builtin { op: B::Not, args } if args.len() == 1 => self.negated_guards(&args[0]),
            ExprKind::And(es) => {
                for item in es {
                    out.intersect(self.implied_guards(item), self.phases);
                }
                out
            }
            ExprKind::Or(es) if !es.is_empty() => {
                let items: Vec<_> = es.iter().map(|item| self.implied_guards(item)).collect();
                PhaseGuards::union_common(&items)
            }
            _ => out,
        }
    }

    /// Phase restrictions guaranteed to hold whenever `e` evaluates to `FALSE`.
    pub(super) fn negated_guards(&self, e: &Expr) -> PhaseGuards {
        let mut out = PhaseGuards::default();
        if let Some((reader, allowed)) = self.atomic_phase_guard(e) {
            let neg: BTreeSet<Atom> = self.phases.difference(&allowed).cloned().collect();
            match reader {
                None => out.scalar = Some(neg),
                Some(l) => {
                    out.keyed.insert(l, neg);
                }
            }
            return out;
        }
        match &*e.kind {
            ExprKind::Builtin { op: B::Not, args } if args.len() == 1 => self.implied_guards(&args[0]),
            ExprKind::Or(es) => {
                for item in es {
                    out.intersect(self.negated_guards(item), self.phases);
                }
                out
            }
            ExprKind::And(es) if es.len() == 1 => self.negated_guards(&es[0]),
            ExprKind::Builtin { op: B::Implies, args } if args.len() == 2 => {
                out.intersect(self.implied_guards(&args[0]), self.phases);
                out.intersect(self.negated_guards(&args[1]), self.phases);
                out
            }
            _ => out,
        }
    }

    pub(super) fn slot_domain(&self, slot: &Slot) -> Option<&Domain> {
        match (&self.control, slot) {
            (Control::RecordField { var, .. }, Slot::RecordField(f)) => match &self.domains.vars[var.idx()] {
                Domain::Record(fs) => fs.get(f),
                Domain::Function(_, range) => match &**range {
                    Domain::Record(fs) => fs.get(f),
                    _ => None,
                },
                _ => None,
            },
            (Control::Var { .. }, Slot::CompanionVar(v)) => match (self.keys.is_some(), &self.domains.vars[v.idx()]) {
                (false, d) => Some(d),
                (true, Domain::Function(_, range)) => Some(range),
                _ => None,
            },
            _ => None,
        }
    }

    fn init_seed_for_slot(&self, slot: &Slot, initial: &[Branch]) -> Option<Expr> {
        let first = initial.first()?;
        match (&self.control, slot) {
            (Control::RecordField { var, .. }, Slot::RecordField(field)) => {
                let rhs = binding(first, *var, false)?;
                let rec = match self.keys {
                    None => &rhs,
                    Some(ks) => unwrap_init_map_body(self.domains, &rhs, ks)?.0,
                };
                let ExprKind::Record(fs) = &*rec.kind else { return None };
                let (_, val) = fs.iter().find(|(f, _)| f == field)?;
                is_closed_const_expr(self.domains, val, 0).then(|| val.clone())
            }
            (Control::Var { .. }, Slot::CompanionVar(v)) => {
                let rhs = binding(first, *v, false)?;
                let body = match self.keys {
                    None => &rhs,
                    Some(ks) => {
                        let (body, k_id) = unwrap_init_map_body(self.domains, &rhs, ks)?;
                        if mentions_local(body, k_id) {
                            return None;
                        }
                        body
                    }
                };
                is_closed_const_expr(self.domains, body, 0).then(|| body.clone())
            }
            _ => None,
        }
    }

    fn is_avoided_atom(a: &Atom, avoid_keys: Option<&BTreeSet<Arc<str>>>) -> bool {
        matches!(a, Atom::Model(m) if avoid_keys.is_some_and(|s| s.contains(m)))
    }

    fn expr_mentions_avoided_key(&self, e: &Expr, avoid_keys: Option<&BTreeSet<Arc<str>>>) -> bool {
        let Some(avoid) = avoid_keys.filter(|s| !s.is_empty()) else {
            return false;
        };
        match &*e.kind {
            ExprKind::Const(_) => {
                if let Some(a) = self.domains.atom_value(e) {
                    return Self::is_avoided_atom(&a, Some(avoid));
                }
                if let Some(set) = self.domains.exact_set(e) {
                    return set.iter().any(|a| Self::is_avoided_atom(a, Some(avoid)));
                }
                true
            }
            _ => {
                if let Some(a) = self.domains.atom_value(e) {
                    if Self::is_avoided_atom(&a, Some(avoid)) {
                        return true;
                    }
                }
                let mut found = false;
                visit::children(e, &mut |c| found |= self.expr_mentions_avoided_key(c, Some(avoid)));
                found
            }
        }
    }

    pub(super) fn sentinel_for_slot(
        &self,
        slot: &Slot,
        initial: &[Branch],
        avoid_keys: Option<&BTreeSet<Arc<str>>>,
        span: Span,
    ) -> Option<Expr> {
        let dom = self.slot_domain(slot)?;
        let init_seed = self.init_seed_for_slot(slot, initial);
        Some(self.sentinel_expr(dom, init_seed.as_ref(), avoid_keys, span))
    }

    fn sentinel_expr(&self, dom: &Domain, init_seed: Option<&Expr>, avoid_keys: Option<&BTreeSet<Arc<str>>>, span: Span) -> Expr {
        match dom {
            Domain::Atoms(atoms) if !atoms.is_empty() => {
                if let Some(seed) = init_seed {
                    if let Some(a) = self.domains.atom_value(seed) {
                        if atoms.contains(&a) && !Self::is_avoided_atom(&a, avoid_keys) {
                            if let Some(e) = self.domains.atom_expr(&a, span) {
                                return e;
                            }
                        }
                    }
                }
                for preferred in [Atom::Num(0), Atom::Bool(false), Atom::Str("".into())] {
                    if atoms.contains(&preferred) {
                        if let Some(e) = self.domains.atom_expr(&preferred, span) {
                            return e;
                        }
                    }
                }
                for a in atoms {
                    if !Self::is_avoided_atom(a, avoid_keys) {
                        if let Some(e) = self.domains.atom_expr(a, span) {
                            return e;
                        }
                    }
                }
            }
            Domain::Integer(lo) => {
                let n = if *lo <= 0 { 0 } else { *lo };
                if i32::try_from(n).is_ok() {
                    return Expr::new(ExprKind::Num(n), span);
                }
            }
            Domain::Set(_) => return Expr::new(ExprKind::SetEnum(vec![]), span),
            Domain::Seq(_) => return Expr::new(ExprKind::Tuple(vec![]), span),
            Domain::Record(fs) => {
                let mut init_fields: BTreeMap<&str, &Expr> = BTreeMap::new();
                if let Some(seed) = init_seed {
                    if let ExprKind::Record(sfs) = &*seed.kind {
                        for (k, v) in sfs {
                            init_fields.insert(k.as_ref(), v);
                        }
                    }
                }
                let built: Vec<(Arc<str>, Expr)> = fs
                    .iter()
                    .map(|(k, d)| (k.clone(), self.sentinel_expr(d, init_fields.get(k.as_ref()).copied(), avoid_keys, span)))
                    .collect();
                return Expr::new(ExprKind::Record(built), span);
            }
            _ => {}
        }
        if let Some(seed) = init_seed {
            if !self.expr_mentions_avoided_key(seed, avoid_keys) {
                return seed.clone();
            }
        }
        Expr::new(ExprKind::Bool(false), span)
    }

    fn masked_value_expr(&self, ctrl_expr: Expr, val_expr: Expr, live: &BTreeSet<Atom>, sentinel: Expr, span: Span) -> Option<Expr> {
        let dead: Vec<Expr> = self.phases.difference(live).map(|p| self.domains.atom_expr(p, span)).collect::<Option<_>>()?;
        if dead.is_empty() {
            return None;
        }
        if live.is_empty() {
            return Some(sentinel);
        }
        let live_exprs: Vec<Expr> = live.iter().map(|p| self.domains.atom_expr(p, span)).collect::<Option<_>>()?;
        // Branch on the smaller of `live` vs `dead`, using scalar `=` for a singleton.
        if live_exprs.len() <= dead.len() {
            let cond = if live_exprs.len() == 1 {
                Expr::new(ExprKind::Builtin { op: B::Eq, args: vec![ctrl_expr, live_exprs.into_iter().next().unwrap()] }, span)
            } else {
                Expr::new(ExprKind::Builtin { op: B::In, args: vec![ctrl_expr, Expr::new(ExprKind::SetEnum(live_exprs), span)] }, span)
            };
            Some(Expr::new(ExprKind::If { cond, then: val_expr, els: sentinel }, span))
        } else {
            let cond = if dead.len() == 1 {
                Expr::new(ExprKind::Builtin { op: B::Eq, args: vec![ctrl_expr, dead.into_iter().next().unwrap()] }, span)
            } else {
                Expr::new(ExprKind::Builtin { op: B::In, args: vec![ctrl_expr, Expr::new(ExprKind::SetEnum(dead), span)] }, span)
            };
            Some(Expr::new(ExprKind::If { cond, then: sentinel, els: val_expr }, span))
        }
    }

    pub(super) fn view(&self, program: &Program, initial: &[Branch], avoid_keys: Option<&BTreeSet<Arc<str>>>) -> Option<FieldProjection> {
        let mut next_local = program.locals.len() as u32;
        match &self.control {
            Control::RecordField { var, field: ctrl_field } => {
                let span = program.vars[var.idx()].span;
                let var_expr = Expr::new(ExprKind::Var(*var), span);
                let local = LocalId(next_local);
                let record = if self.keys.is_some() {
                    Expr::new(ExprKind::FnApp { func: var_expr.clone(), args: vec![Expr::new(ExprKind::Local(local), span)] }, span)
                } else {
                    var_expr.clone()
                };
                let mut updates = Vec::new();
                let mut fields = Vec::new();
                for (slot, live) in &self.live {
                    let Slot::RecordField(field) = slot else { continue };
                    if field == ctrl_field || live.len() >= self.phases.len() {
                        continue;
                    }
                    let dom = self.slot_domain(slot)?;
                    if is_singleton_domain(dom) {
                        continue;
                    }
                    let init_seed = self.init_seed_for_slot(slot, initial);
                    let sentinel = self.sentinel_expr(dom, init_seed.as_ref(), avoid_keys, span);
                    let ctrl_expr = Expr::new(ExprKind::Field { record: record.clone(), field: ctrl_field.clone() }, span);
                    let old = Expr::new(ExprKind::Field { record: record.clone(), field: field.clone() }, span);
                    let value = self.masked_value_expr(ctrl_expr, old, live, sentinel, span)?;
                    updates.push((vec![ExceptKey::Field(field.clone())], value));
                    fields.push(format!("{}{}.{field}", program.vars[var.idx()].name, if self.keys.is_some() { "[*]" } else { "" }));
                }
                if updates.is_empty() {
                    return None;
                }
                let mut projected = Expr::new(ExprKind::Except { base: record, updates }, span);
                if self.keys.is_some() {
                    let set = Expr::new(ExprKind::Builtin { op: B::Domain, args: vec![var_expr] }, span);
                    projected = Expr::new(
                        ExprKind::FnConstruct { bounds: vec![Bound { vars: BoundVars::Many(vec![local]), set }], body: projected },
                        span,
                    );
                }
                let values = program
                    .vars
                    .iter()
                    .enumerate()
                    .map(|(i, v)| if i == var.idx() { projected.clone() } else { Expr::new(ExprKind::Var(VarId(i as u32)), v.span) })
                    .collect();
                Some(FieldProjection {
                    ordered: None,
                    view: Expr::new(ExprKind::Tuple(values), span),
                    fields,
                    certificate: None,
                    mathematical_counter_arithmetic: false,
                })
            }
            Control::Var { var: ctrl } => {
                let ctrl_span = program.vars[ctrl.idx()].span;
                let ctrl_var_expr = Expr::new(ExprKind::Var(*ctrl), ctrl_span);
                let mut projected_vars: BTreeMap<VarId, Expr> = BTreeMap::new();
                let mut fields = Vec::new();
                for (slot, live) in &self.live {
                    let Slot::CompanionVar(v) = *slot else { continue };
                    if live.len() >= self.phases.len() {
                        continue;
                    }
                    let dom = self.slot_domain(slot)?;
                    if is_singleton_domain(dom) {
                        continue;
                    }
                    let v_span = program.vars[v.idx()].span;
                    let v_expr = Expr::new(ExprKind::Var(v), v_span);
                    let init_seed = self.init_seed_for_slot(slot, initial);
                    let sentinel = self.sentinel_expr(dom, init_seed.as_ref(), avoid_keys, v_span);
                    let projected = if self.keys.is_some() {
                        let local = LocalId(next_local);
                        next_local += 1;
                        let key_expr = Expr::new(ExprKind::Local(local), v_span);
                        let ctrl_at_k = Expr::new(ExprKind::FnApp { func: ctrl_var_expr.clone(), args: vec![key_expr.clone()] }, v_span);
                        let val_at_k = Expr::new(ExprKind::FnApp { func: v_expr.clone(), args: vec![key_expr] }, v_span);
                        let body = self.masked_value_expr(ctrl_at_k, val_at_k, live, sentinel, v_span)?;
                        let set = Expr::new(ExprKind::Builtin { op: B::Domain, args: vec![v_expr] }, v_span);
                        Expr::new(ExprKind::FnConstruct { bounds: vec![Bound { vars: BoundVars::Many(vec![local]), set }], body }, v_span)
                    } else {
                        self.masked_value_expr(ctrl_var_expr.clone(), v_expr, live, sentinel, v_span)?
                    };
                    projected_vars.insert(v, projected);
                    fields.push(format!("{}{}", program.vars[v.idx()].name, if self.keys.is_some() { "[*]" } else { "" }));
                }
                if projected_vars.is_empty() {
                    return None;
                }
                let values = program
                    .vars
                    .iter()
                    .enumerate()
                    .map(|(i, v)| {
                        let vid = VarId(i as u32);
                        projected_vars.get(&vid).cloned().unwrap_or_else(|| Expr::new(ExprKind::Var(vid), v.span))
                    })
                    .collect();
                Some(FieldProjection {
                    ordered: None,
                    view: Expr::new(ExprKind::Tuple(values), ctrl_span),
                    fields,
                    certificate: None,
                    mathematical_counter_arithmetic: false,
                })
            }
        }
    }
}
