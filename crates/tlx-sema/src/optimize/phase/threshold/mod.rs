//! In-place threshold-counter saturation projection.
//!
//! One or more monotone/resettable natural-number counters (scalar variables or
//! fixed-domain per-actor maps `[Actor -> Nat]`) are saturated in `VIEW` at
//! `min(n_i, cap_i)` alongside arbitrary retained TLA+ state `C`.
//!
//! Concrete actions and counter values remain un-saturated during execution so
//! counterexample traces preserve true un-capped counter values and deadlocks
//! are preserved exactly.

mod lean;
pub(super) mod sym;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use tlx_front::cfg::Config;

use crate::{builtins::Builtin as B, hir::*, visit, Program};

use super::{
    binding, binding_with_index, branches_with_if,
    domain::{compatible, Atom, Domain, Domains, Locals},
    normalize::{opaque_recursive_def_vars, Normalizer},
    variable, Branch, CheckSpec, FieldProjection,
};

const MAX_CAP: i128 = (i32::MAX as i128) - 1;
const MAX_MAP_KEYS: usize = 64;
const MAX_TOTAL_SLOTS: usize = 256;
const MAX_CHECK_WORK: usize = 100_000;

#[derive(Clone, Debug)]
pub(super) enum CounterKind {
    Scalar,
    Map(BTreeSet<Atom>),
}

#[derive(Clone, Debug)]
pub(super) struct CounterSpec {
    pub var: VarId,
    pub kind: CounterKind,
    pub cap: i128,
    pub has_positive_add: bool,
    pub upper_bound: Option<i128>,
    pub eval_upper_bound: Option<i128>,
}

/// Prove an in-place threshold-counter saturation projection for invariants only.
pub fn threshold_counter_projection(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    observations: &[Expr],
) -> Option<FieldProjection> {
    threshold_counter_projection_with_spec(program, cfg, init, next, CheckSpec::invariants_only(observations))
}

pub(super) fn analyze_counters(
    program: &Program,
    cfg: &Config,
    initial: &[Branch],
    steps: &[Branch],
    norm_spec: CheckSpec<'_>,
    opaque_cache: &mut HashMap<DefId, Option<BTreeSet<VarId>>>,
) -> Option<(Domains, Vec<CounterSpec>)> {
    let domains = Domains::infer(program, cfg, initial, steps)?;

    let mut candidates = BTreeMap::new();
    for (i, dom) in domains.vars.iter().enumerate() {
        let var = VarId(i as u32);
        match dom {
            Domain::Function(keys, range)
                if !keys.is_empty() && keys.len() <= MAX_MAP_KEYS && compatible(keys) && range.integer_min().is_some_and(|m| m >= 0) =>
            {
                candidates.insert(
                    var,
                    CounterSpec {
                        var,
                        kind: CounterKind::Map(keys.clone()),
                        cap: 0,
                        has_positive_add: false,
                        upper_bound: None,
                        eval_upper_bound: None,
                    },
                );
            }
            d if d.integer_min().is_some_and(|m| m >= 0) => {
                candidates.insert(
                    var,
                    CounterSpec {
                        var,
                        kind: CounterKind::Scalar,
                        cap: 0,
                        has_positive_add: false,
                        upper_bound: None,
                        eval_upper_bound: None,
                    },
                );
            }
            _ => {}
        }
    }
    if candidates.is_empty() {
        return None;
    }

    // Fixed-point pruning: whenever a candidate fails validation or is proved
    // non-profitable, remove it (moving it to retained state C) and re-validate
    // the remaining candidates cleanly from scratch so caps and bounds stay exact.
    loop {
        if candidates.is_empty() {
            return None;
        }
        for c in candidates.values_mut() {
            c.cap = 0;
            c.has_positive_add = false;
            c.upper_bound = None;
            c.eval_upper_bound = None;
        }

        let mut checker = Checker {
            program,
            cfg,
            domains: &domains,
            candidates: &mut candidates,
            invalid: BTreeSet::new(),
            opaque_cache,
            remaining: MAX_CHECK_WORK,
            aborted: false,
        };

        checker.check_all(initial, steps, norm_spec);
        if checker.aborted {
            return None;
        }
        let invalid = checker.invalid;
        if !invalid.is_empty() {
            for v in invalid {
                candidates.remove(&v);
            }
            continue;
        }

        // Static profitability & upper-bound analysis for every surviving candidate.
        let mut to_prune = Vec::new();
        let vars: Vec<VarId> = candidates.keys().copied().collect();
        for v in vars {
            let (ub, eval_ub) = compute_bounds(&domains, &candidates[&v], initial, steps, norm_spec.constraints);
            let spec_c = candidates.get_mut(&v).unwrap();
            spec_c.upper_bound = ub;
            spec_c.eval_upper_bound = eval_ub;
            let profitable = spec_c.has_positive_add && ub.is_none_or(|u| u > spec_c.cap);
            if !profitable {
                to_prune.push(v);
            }
        }
        if !to_prune.is_empty() {
            for v in to_prune {
                candidates.remove(&v);
            }
            continue;
        }
        break;
    }

    let counters: Vec<CounterSpec> = candidates.into_values().collect();
    if counters.is_empty() {
        return None;
    }
    let total_slots: usize = counters
        .iter()
        .map(|c| match &c.kind {
            CounterKind::Scalar => 1,
            CounterKind::Map(ks) => ks.len(),
        })
        .sum();
    if total_slots == 0 || total_slots > MAX_TOTAL_SLOTS {
        return None;
    }
    Some((domains, counters))
}

/// Prove an in-place threshold-counter saturation projection covering invariants,
/// init properties, state constraints, and counter-independent action checks.
pub fn threshold_counter_projection_with_spec(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: CheckSpec<'_>,
) -> Option<FieldProjection> {
    if !super::cfg_constants_supported(program, cfg) {
        return None;
    }
    let mut expand = Normalizer::with_config_threshold(program, cfg);
    let initial = branches_with_if(&expand.root(init)?)?;
    let steps = branches_with_if(&expand.root(next)?)?;
    if initial.is_empty() || steps.is_empty() {
        return None;
    }
    let norm = spec.try_map(|e| expand.root(e))?;
    let norm_spec = norm.as_spec();
    let (domains, counters) = analyze_counters(program, cfg, &initial, &steps, norm_spec, expand.opaque_vars_cache_mut())?;

    if spec.is_constrained() && !super::sym_totality::check_projection_observations_total(program, cfg, init, next, spec) {
        return None;
    }

    let open_cert = lean::emit(
        lean::EmitInput { program, cfg, domains: &domains, counters: &counters, initial: &initial, steps: &steps, spec: norm_spec },
        expand.opaque_vars_cache_mut(),
    )?;
    let certificate = expand.attach_const_subst(open_cert)?;
    let mathematical_counter_arithmetic = counters.iter().any(|c| c.eval_upper_bound.is_none_or(|u| u > i32::MAX as i128));

    let view = build_view(program, &counters, init.span);
    let fields = counters.iter().map(|c| format!("{}<={}", program.vars[c.var.idx()].name, c.cap)).collect();

    Some(FieldProjection { ordered: None, view, fields, certificate: Some(certificate), mathematical_counter_arithmetic })
}

pub(super) fn build_view(program: &Program, counters: &[CounterSpec], span: Span) -> Expr {
    let by_var: HashMap<VarId, &CounterSpec> = counters.iter().map(|c| (c.var, c)).collect();
    let mut next_local = program.locals.len() as u32;
    let values = program
        .vars
        .iter()
        .enumerate()
        .map(|(i, v)| {
            let id = VarId(i as u32);
            let var_expr = Expr::new(ExprKind::Var(id), v.span);
            let Some(counter) = by_var.get(&id) else {
                return var_expr;
            };
            match &counter.kind {
                CounterKind::Scalar => {
                    if counter.cap == 0 {
                        Expr::new(ExprKind::Num(0), v.span)
                    } else {
                        let cap_expr = Expr::new(ExprKind::Num(counter.cap), v.span);
                        Expr::new(
                            ExprKind::If {
                                cond: Expr::new(ExprKind::Builtin { op: B::Ge, args: vec![var_expr.clone(), cap_expr.clone()] }, v.span),
                                then: cap_expr,
                                els: var_expr,
                            },
                            v.span,
                        )
                    }
                }
                CounterKind::Map(_) => {
                    let local = LocalId(next_local);
                    next_local += 1;
                    let body = if counter.cap == 0 {
                        Expr::new(ExprKind::Num(0), v.span)
                    } else {
                        let entry = Expr::new(
                            ExprKind::FnApp { func: var_expr.clone(), args: vec![Expr::new(ExprKind::Local(local), v.span)] },
                            v.span,
                        );
                        let cap_expr = Expr::new(ExprKind::Num(counter.cap), v.span);
                        Expr::new(
                            ExprKind::If {
                                cond: Expr::new(ExprKind::Builtin { op: B::Ge, args: vec![entry.clone(), cap_expr.clone()] }, v.span),
                                then: cap_expr,
                                els: entry,
                            },
                            v.span,
                        )
                    };
                    Expr::new(
                        ExprKind::FnConstruct {
                            bounds: vec![Bound {
                                vars: BoundVars::Many(vec![local]),
                                set: Expr::new(ExprKind::Builtin { op: B::Domain, args: vec![var_expr] }, v.span),
                            }],
                            body,
                        },
                        v.span,
                    )
                }
            }
        })
        .collect();
    Expr::new(ExprKind::Tuple(values), span)
}

pub(super) fn ordinary_unchanged(e: &Expr) -> bool {
    match &*e.kind {
        ExprKind::Var(_) => true,
        ExprKind::Tuple(es) => es.iter().all(ordinary_unchanged),
        _ => false,
    }
}

pub(super) fn required_cap(op: B, thresh: i128, reversed: bool) -> Option<i128> {
    let norm_op = if reversed {
        match op {
            B::Lt => B::Gt,
            B::Le => B::Ge,
            B::Gt => B::Lt,
            B::Ge => B::Le,
            x => x,
        }
    } else {
        op
    };
    if thresh < 0 {
        return Some(0);
    }
    let req = match norm_op {
        B::Lt | B::Ge => thresh,
        B::Le | B::Gt | B::Eq | B::Neq => thresh.checked_add(1)?,
        _ => return None,
    };
    (req <= MAX_CAP).then_some(req)
}

pub(super) fn atom_nat(domains: &Domains, e: &Expr) -> Option<i128> {
    let Atom::Num(n) = domains.atom_value(e)? else { return None };
    (0..=i128::from(i32::MAX)).contains(&n).then_some(n)
}

pub(super) fn is_index_in_domain(domains: &Domains, idx: &Expr, keys: &BTreeSet<Atom>, locals: &Locals) -> bool {
    match domains.value(idx, locals) {
        Domain::Atoms(atoms) => !atoms.is_empty() && atoms.is_subset(keys),
        _ => false,
    }
}

struct Checker<'a> {
    program: &'a Program,
    cfg: &'a Config,
    domains: &'a Domains,
    candidates: &'a mut BTreeMap<VarId, CounterSpec>,
    invalid: BTreeSet<VarId>,
    opaque_cache: &'a mut HashMap<DefId, Option<BTreeSet<VarId>>>,
    remaining: usize,
    aborted: bool,
}

impl Checker<'_> {
    fn tick(&mut self) -> bool {
        if self.aborted || self.remaining == 0 {
            self.aborted = true;
            return false;
        }
        self.remaining -= 1;
        true
    }

    fn invalidate(&mut self, v: VarId) {
        if self.candidates.contains_key(&v) {
            self.invalid.insert(v);
        }
    }

    fn invalidate_all(&mut self) {
        for &v in self.candidates.keys() {
            self.invalid.insert(v);
        }
    }

    fn raise_cap(&mut self, v: VarId, req: i128) {
        if req > MAX_CAP {
            self.invalidate(v);
            return;
        }
        if let Some(c) = self.candidates.get_mut(&v) {
            c.cap = c.cap.max(req);
        }
    }

    fn check_all(&mut self, initial: &[Branch], steps: &[Branch], spec: CheckSpec<'_>) {
        let candidate_vars: Vec<VarId> = self.candidates.keys().copied().collect();

        // 1. Init branches: every candidate must have a single init seed binding;
        // bounds and all other Init terms must be counter-free.
        for b in initial {
            if !self.tick() {
                return;
            }
            for bound in &b.bounds {
                self.require_counter_free(&bound.set);
            }
            for &v in &candidate_vars {
                let Some(rhs) = binding(b, v, false) else {
                    self.invalidate(v);
                    continue;
                };
                if !self.check_init_seed(v, &rhs) {
                    self.invalidate(v);
                }
            }
            for term in &b.terms {
                if matches!(&*term.kind, ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 && variable(&args[0], false).is_some_and(|v| self.candidates.contains_key(&v)))
                {
                    continue;
                }
                self.require_counter_free(term);
            }
        }

        // 2. Next branches: every candidate must have a single valid transfer binding;
        // bounds must be counter-free; remaining terms must be valid predicates.
        for b in steps {
            if !self.tick() {
                return;
            }
            let locals = self.domains.locals(&b.bounds);
            for bound in &b.bounds {
                self.require_counter_free(&bound.set);
            }
            for &v in &candidate_vars {
                let Some(rhs) = binding(b, v, true) else {
                    self.invalidate(v);
                    continue;
                };
                if !self.check_transfer(v, &rhs, &locals) {
                    self.invalidate(v);
                }
            }
            for term in &b.terms {
                if matches!(&*term.kind, ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 && variable(&args[0], true).is_some_and(|v| self.candidates.contains_key(&v)))
                {
                    continue;
                }
                if let ExprKind::Builtin { op: B::Unchanged, args } = &*term.kind {
                    if args.len() == 1 {
                        if !ordinary_unchanged(&args[0]) {
                            self.require_counter_free(term);
                        }
                        continue;
                    }
                }
                self.check_pred(term, &locals);
            }
        }

        // 3. State observations & constraints (invariants, init_props, constraints).
        let empty_locals = Locals::new();
        for pred in spec.all_state_preds() {
            if !self.tick() {
                return;
            }
            self.check_pred(pred, &empty_locals);
        }

        // 4. Action constraints & action properties: must be completely counter-free.
        for pred in spec.action_constraints.iter().chain(spec.action_props.iter()) {
            if !self.tick() {
                return;
            }
            self.require_counter_free(pred);
        }
    }

    /// Reject any candidate counter referenced inside `e` (including via opaque
    /// recursive defs), except `DOMAIN v` for map counters `v`.
    fn require_counter_free(&mut self, e: &Expr) {
        if !self.tick() {
            return;
        }
        match &*e.kind {
            ExprKind::Var(v) => {
                self.invalidate(*v);
                return;
            }
            ExprKind::Builtin { op: B::Domain, args } if args.len() == 1 => {
                if let Some(v) = variable(&args[0], false) {
                    if matches!(self.candidates.get(&v).map(|c| &c.kind), Some(CounterKind::Map(_))) {
                        return;
                    }
                }
            }
            ExprKind::Apply { op: OpRef::Def(id), args } => {
                match opaque_recursive_def_vars(self.program, self.cfg, *id, self.opaque_cache) {
                    Some(vars) => {
                        for v in vars {
                            self.invalidate(v);
                        }
                    }
                    None => {
                        self.invalidate_all();
                        return;
                    }
                }
                for a in args {
                    self.require_counter_free(a);
                }
                return;
            }
            _ => {}
        }
        visit::children(e, &mut |c| self.require_counter_free(c));
    }

    fn mentions_any_candidate(&mut self, e: &Expr) -> bool {
        if !self.tick() {
            return true;
        }
        match &*e.kind {
            ExprKind::Var(v) => return self.candidates.contains_key(v),
            ExprKind::Builtin { op: B::Domain, args } if args.len() == 1 => {
                if let Some(v) = variable(&args[0], false) {
                    if matches!(self.candidates.get(&v).map(|c| &c.kind), Some(CounterKind::Map(_))) {
                        return false;
                    }
                }
            }
            ExprKind::Apply { op: OpRef::Def(id), args } => {
                match opaque_recursive_def_vars(self.program, self.cfg, *id, self.opaque_cache) {
                    Some(vars) => {
                        if vars.iter().any(|v| self.candidates.contains_key(v)) {
                            return true;
                        }
                    }
                    None => return true,
                }
                return args.iter().any(|a| self.mentions_any_candidate(a));
            }
            _ => {}
        }
        let mut found = false;
        visit::children(e, &mut |c| {
            if !found {
                found |= self.mentions_any_candidate(c);
            }
        });
        found
    }

    fn check_init_seed(&mut self, v: VarId, rhs: &Expr) -> bool {
        let kind = self.candidates[&v].kind.clone();
        match kind {
            CounterKind::Scalar => self.check_scalar_init(rhs),
            CounterKind::Map(keys) => self.check_map_init(&keys, rhs),
        }
    }

    fn check_scalar_init(&mut self, rhs: &Expr) -> bool {
        if !self.tick() {
            return false;
        }
        if atom_nat(self.domains, rhs).is_some() {
            return true;
        }
        if let ExprKind::If { cond, then, els } = &*rhs.kind {
            if self.mentions_any_candidate(cond) {
                return false;
            }
            return self.check_scalar_init(then) && self.check_scalar_init(els);
        }
        false
    }

    fn check_map_init(&mut self, keys: &BTreeSet<Atom>, rhs: &Expr) -> bool {
        if !self.tick() {
            return false;
        }
        match &*rhs.kind {
            ExprKind::FnConstruct { bounds, body } if bounds.len() == 1 => {
                matches!(&bounds[0].vars, BoundVars::Many(ids) if ids.len() == 1)
                    && self.domains.exact_set(&bounds[0].set).as_ref() == Some(keys)
                    && self.check_scalar_init(body)
            }
            ExprKind::If { cond, then, els } => {
                !self.mentions_any_candidate(cond) && self.check_map_init(keys, then) && self.check_map_init(keys, els)
            }
            _ => false,
        }
    }

    fn check_transfer(&mut self, v: VarId, rhs: &Expr, locals: &Locals) -> bool {
        let kind = self.candidates[&v].kind.clone();
        match kind {
            CounterKind::Scalar => self.check_scalar_transfer(v, rhs, locals),
            CounterKind::Map(keys) => self.check_map_transfer(v, &keys, rhs, locals),
        }
    }

    fn check_scalar_transfer(&mut self, v: VarId, rhs: &Expr, locals: &Locals) -> bool {
        if !self.tick() {
            return false;
        }
        if variable(rhs, false) == Some(v) {
            return true;
        }
        if atom_nat(self.domains, rhs).is_some() {
            return true;
        }
        match &*rhs.kind {
            ExprKind::Builtin { op: B::Plus, args } if args.len() == 2 => {
                for (lhs, delta_e) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                    if variable(lhs, false) == Some(v) {
                        if let Some(d) = atom_nat(self.domains, delta_e) {
                            if d > 0 {
                                if let Some(c) = self.candidates.get_mut(&v) {
                                    c.has_positive_add = true;
                                }
                            }
                            return true;
                        }
                    }
                }
                false
            }
            ExprKind::If { cond, then, els } => {
                self.check_pred(cond, locals);
                self.check_scalar_transfer(v, then, locals) && self.check_scalar_transfer(v, els, locals)
            }
            _ => false,
        }
    }

    fn check_map_transfer(&mut self, v: VarId, keys: &BTreeSet<Atom>, rhs: &Expr, locals: &Locals) -> bool {
        if !self.tick() {
            return false;
        }
        if variable(rhs, false) == Some(v) {
            return true;
        }
        match &*rhs.kind {
            ExprKind::FnConstruct { bounds, body } if bounds.len() == 1 => {
                let BoundVars::Many(ids) = &bounds[0].vars else { return false };
                if ids.len() != 1 || self.domains.exact_set(&bounds[0].set).as_ref() != Some(keys) {
                    return false;
                }
                let mut inner_locals = locals.clone();
                inner_locals.insert(ids[0], Domain::Atoms(keys.clone()));
                self.check_map_slot_transfer(v, &Expr::new(ExprKind::Local(ids[0]), body.span), body, &inner_locals)
            }
            ExprKind::Except { base, updates } if variable(base, false) == Some(v) => {
                if updates.is_empty() {
                    return true;
                }
                for (path, val) in updates {
                    let [ExceptKey::Index(indices)] = path.as_slice() else { return false };
                    let [idx] = indices.as_slice() else { return false };
                    if self.mentions_any_candidate(idx) || !is_index_in_domain(self.domains, idx, keys, locals) {
                        return false;
                    }
                    if !self.check_map_slot_transfer(v, idx, val, locals) {
                        return false;
                    }
                }
                true
            }
            ExprKind::If { cond, then, els } => {
                self.check_pred(cond, locals);
                self.check_map_transfer(v, keys, then, locals) && self.check_map_transfer(v, keys, els, locals)
            }
            _ => false,
        }
    }

    fn is_same_map_slot(&self, e: &Expr, v: VarId, expected_idx: &Expr) -> bool {
        let ExprKind::FnApp { func, args } = &*e.kind else { return false };
        args.len() == 1 && variable(func, false) == Some(v) && expr_structurally_eq(&args[0], expected_idx)
    }

    fn check_map_slot_transfer(&mut self, v: VarId, idx: &Expr, val: &Expr, locals: &Locals) -> bool {
        if !self.tick() {
            return false;
        }
        if self.is_same_map_slot(val, v, idx) {
            return true;
        }
        if atom_nat(self.domains, val).is_some() {
            return true;
        }
        match &*val.kind {
            ExprKind::Builtin { op: B::Plus, args } if args.len() == 2 => {
                for (lhs, delta_e) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                    if self.is_same_map_slot(lhs, v, idx) {
                        if let Some(d) = atom_nat(self.domains, delta_e) {
                            if d > 0 {
                                if let Some(c) = self.candidates.get_mut(&v) {
                                    c.has_positive_add = true;
                                }
                            }
                            return true;
                        }
                    }
                }
                false
            }
            ExprKind::If { cond, then, els } => {
                self.check_pred(cond, locals);
                self.check_map_slot_transfer(v, idx, then, locals) && self.check_map_slot_transfer(v, idx, els, locals)
            }
            _ => false,
        }
    }

    /// Match a single unprimed counter slot: `Var(v)` for scalar `v` or `FnApp(Var(v), [idx])`
    /// for map `v` where `idx` is counter-free and proved in `DOMAIN v`.
    fn match_slot(&mut self, e: &Expr, locals: &Locals) -> Option<VarId> {
        if let Some(v) = variable(e, false) {
            if matches!(self.candidates.get(&v).map(|c| &c.kind), Some(CounterKind::Scalar)) {
                return Some(v);
            }
        }
        if let ExprKind::FnApp { func, args } = &*e.kind {
            if args.len() == 1 {
                if let Some(v) = variable(func, false) {
                    if let Some(CounterKind::Map(keys)) = self.candidates.get(&v).map(|c| c.kind.clone()) {
                        if !self.mentions_any_candidate(&args[0]) && is_index_in_domain(self.domains, &args[0], &keys, locals) {
                            return Some(v);
                        }
                    }
                }
            }
        }
        None
    }

    fn check_pred(&mut self, e: &Expr, locals: &Locals) {
        if !self.tick() {
            return;
        }
        if !self.mentions_any_candidate(e) {
            // Still ensure no opaque recursive def with impure/invalid body slipped through.
            self.require_counter_free(e);
            return;
        }
        match &*e.kind {
            ExprKind::And(es) | ExprKind::Or(es) => {
                for item in es {
                    self.check_pred(item, locals);
                }
                return;
            }
            ExprKind::If { cond, then, els } => {
                self.check_pred(cond, locals);
                self.check_pred(then, locals);
                self.check_pred(els, locals);
                return;
            }
            ExprKind::Quant { bounds, body, .. } => {
                let mut scope = locals.clone();
                let mut total_combos = 1usize;
                let mut ok = true;
                for b in bounds {
                    if self.mentions_any_candidate(&b.set) {
                        ok = false;
                        break;
                    }
                    let BoundVars::Many(ids) = &b.vars else {
                        ok = false;
                        break;
                    };
                    let Some(atoms) = self.domains.exact_set(&b.set) else {
                        ok = false;
                        break;
                    };
                    if atoms.len() > MAX_MAP_KEYS {
                        ok = false;
                        break;
                    }
                    for _ in ids {
                        total_combos = total_combos.saturating_mul(atoms.len());
                    }
                    if total_combos > MAX_MAP_KEYS {
                        ok = false;
                        break;
                    }
                    let dom = if atoms.is_empty() { Domain::Bottom } else { Domain::Atoms(atoms) };
                    for id in ids {
                        scope.insert(*id, dom.clone());
                    }
                }
                if ok {
                    self.check_pred(body, &scope);
                    return;
                }
            }
            ExprKind::Builtin { op, args } => match (op, args.as_slice()) {
                (B::Not, [p]) => {
                    self.check_pred(p, locals);
                    return;
                }
                (B::Implies | B::Equiv, [p, q]) => {
                    self.check_pred(p, locals);
                    self.check_pred(q, locals);
                    return;
                }
                (B::Lt | B::Le | B::Gt | B::Ge | B::Eq | B::Neq, [a, b]) => {
                    for (slot_e, const_e, rev) in [(a, b, false), (b, a, true)] {
                        if let Some(v) = self.match_slot(slot_e, locals) {
                            if let Some(Atom::Num(t)) = self.domains.atom_value(const_e) {
                                match required_cap(*op, t, rev) {
                                    Some(req) => self.raise_cap(v, req),
                                    None => self.invalidate(v),
                                }
                                return;
                            }
                        }
                    }
                    // Allow retained equality/inequality branching on a threshold condition:
                    // `lhs = IF cond THEN t ELSE f` (and symmetric).
                    if matches!(op, B::Eq | B::Neq) {
                        if !self.mentions_any_candidate(a) && matches!(&*b.kind, ExprKind::If { .. }) {
                            self.check_eq_if(a, b, locals);
                            return;
                        }
                        if !self.mentions_any_candidate(b) && matches!(&*a.kind, ExprKind::If { .. }) {
                            self.check_eq_if(b, a, locals);
                            return;
                        }
                    }
                }
                (B::In | B::NotIn, [a, b]) => {
                    if self.check_membership(a, b, locals) {
                        return;
                    }
                }
                _ => {}
            },
            _ => {}
        }
        // Fallback: any candidate mentioned in an unsupported construct is invalidated.
        self.require_counter_free(e);
    }

    fn check_eq_if(&mut self, other: &Expr, expr: &Expr, locals: &Locals) {
        if !self.tick() {
            return;
        }
        if let ExprKind::If { cond, then, els } = &*expr.kind {
            self.check_pred(cond, locals);
            self.check_eq_if(other, then, locals);
            self.check_eq_if(other, els, locals);
        } else {
            self.require_counter_free(other);
            self.require_counter_free(expr);
        }
    }

    fn check_membership(&mut self, elem: &Expr, set: &Expr, locals: &Locals) -> bool {
        if let Some(v) = self.match_slot(elem, locals) {
            return self.check_nat_set_membership(v, set);
        }
        if let Some(v) = variable(elem, false) {
            if let Some(CounterKind::Map(keys)) = self.candidates.get(&v).map(|c| c.kind.clone()) {
                if let ExprKind::FnSet { domain, range } = &*set.kind {
                    if self.domains.exact_set(domain).as_ref() == Some(&keys) {
                        return self.check_nat_set_membership(v, range);
                    }
                }
            }
        }
        false
    }

    fn check_nat_set_membership(&mut self, v: VarId, set: &Expr) -> bool {
        match &*set.kind {
            ExprKind::Builtin { op: B::Nat | B::Int, args } if args.is_empty() => true,
            ExprKind::Builtin { op: B::DotDot, args } if args.len() == 2 => {
                let (Some(Atom::Num(lo)), Some(Atom::Num(hi))) = (self.domains.atom_value(&args[0]), self.domains.atom_value(&args[1]))
                else {
                    return false;
                };
                if lo > hi || hi < 0 {
                    return true;
                }
                match hi.checked_add(1).filter(|&r| r <= MAX_CAP) {
                    Some(req) => {
                        self.raise_cap(v, req);
                        true
                    }
                    None => {
                        self.invalidate(v);
                        true
                    }
                }
            }
            ExprKind::SetEnum(es) => {
                let mut req = 0i128;
                for item in es {
                    let Some(Atom::Num(n)) = self.domains.atom_value(item) else {
                        return false;
                    };
                    if n >= 0 {
                        let Some(r) = n.checked_add(1).filter(|&r| r <= MAX_CAP) else {
                            self.invalidate(v);
                            return true;
                        };
                        req = req.max(r);
                    }
                }
                self.raise_cap(v, req);
                true
            }
            _ => false,
        }
    }
}

pub(super) fn expr_structurally_eq(a: &Expr, b: &Expr) -> bool {
    match (&*a.kind, &*b.kind) {
        (ExprKind::Var(x), ExprKind::Var(y)) => x == y,
        (ExprKind::Local(x), ExprKind::Local(y)) => x == y,
        (ExprKind::Const(x), ExprKind::Const(y)) => x == y,
        (ExprKind::Num(x), ExprKind::Num(y)) => x == y,
        (ExprKind::Str(x), ExprKind::Str(y)) => x == y,
        (ExprKind::Bool(x), ExprKind::Bool(y)) => x == y,
        (ExprKind::Tuple(xs), ExprKind::Tuple(ys)) | (ExprKind::SetEnum(xs), ExprKind::SetEnum(ys)) => {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| expr_structurally_eq(x, y))
        }
        (ExprKind::Field { record: r1, field: f1 }, ExprKind::Field { record: r2, field: f2 }) => f1 == f2 && expr_structurally_eq(r1, r2),
        (ExprKind::FnApp { func: f1, args: a1 }, ExprKind::FnApp { func: f2, args: a2 }) => {
            a1.len() == a2.len() && expr_structurally_eq(f1, f2) && a1.iter().zip(a2).all(|(x, y)| expr_structurally_eq(x, y))
        }
        (ExprKind::Builtin { op: o1, args: a1 }, ExprKind::Builtin { op: o2, args: a2 }) => {
            o1 == o2 && a1.len() == a2.len() && a1.iter().zip(a2).all(|(x, y)| expr_structurally_eq(x, y))
        }
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Static upper-bound analysis (profitability gate + arithmeticSemantics label)
// ---------------------------------------------------------------------------

/// Compute two static upper bounds for `counter`:
/// 1. `reachable_ub`: upper bound on every slot's value in admitted reachable
///    states (may use every guard in each `Next` branch, since only enabled
///    transitions produce successors). Used for the static profitability gate.
/// 2. `eval_ub`: upper bound on every arithmetic result computed **when each
///    addition is evaluated**, including disabled branches. Only global
///    admitted-state bounds (`reachable_ub` and `CONSTRAINT`) and guards
///    strictly preceding the counter's primed binding in left-to-right branch
///    order (plus enclosing `IF` conditions inside the transfer RHS) may bound
///    the operands of `c + d`. Used to decide checked vs. mathematical counter
///    arithmetic.
fn compute_bounds(
    domains: &Domains,
    counter: &CounterSpec,
    initial: &[Branch],
    steps: &[Branch],
    constraints: &[Expr],
) -> (Option<i128>, Option<i128>) {
    // 1. Seed upper bounds from Init.
    let mut init_ub: i128 = 0;
    for b in initial {
        let Some(rhs) = binding(b, counter.var, false) else {
            return (None, None);
        };
        let Some(u) = max_init_value(domains, &rhs) else {
            return (None, None);
        };
        init_ub = init_ub.max(u);
    }

    // 2. Global pre-state upper bounds from CONSTRAINTs (hold on every admitted
    //    state before Next is evaluated).
    let mut global_pre_ub: Option<i128> = None;
    for c in constraints {
        if let Some(u) = extract_universal_ub(domains, counter, c, false) {
            global_pre_ub = Some(global_pre_ub.map_or(u, |old| old.min(u)));
        }
    }

    // 3. Reachable-state upper bound: all branch guards hold on any successor.
    let mut reachable_ub = Some(init_ub);
    for b in steps {
        let Some(rhs) = binding(b, counter.var, true) else {
            reachable_ub = None;
            break;
        };
        let mut branch_univ_ub = global_pre_ub;
        for t in &b.terms {
            if let Some(u) = extract_universal_ub(domains, counter, t, false) {
                branch_univ_ub = Some(branch_univ_ub.map_or(u, |old| old.min(u)));
            }
        }
        let Some(branch_ub) = scan_transfer_ub(domains, counter, &rhs, &b.terms, branch_univ_ub) else {
            reachable_ub = None;
            break;
        };
        reachable_ub = reachable_ub.map(|u| u.max(branch_ub));
    }

    // 4. Evaluation-time upper bound: only global admitted-state bounds and
    //    guards evaluated strictly BEFORE the counter's primed binding hold
    //    when additions inside `rhs` execute (including on disabled branches).
    let admitted_pre_ub = tighten_ub(reachable_ub, global_pre_ub);
    let mut eval_ub = Some(init_ub);
    for b in steps {
        let Some((bind_idx, rhs)) = binding_with_index(b, counter.var, true) else {
            eval_ub = None;
            break;
        };
        let preceding = &b.terms[..bind_idx];
        let mut eval_univ_ub = admitted_pre_ub;
        for t in preceding {
            if let Some(u) = extract_universal_ub(domains, counter, t, false) {
                eval_univ_ub = Some(eval_univ_ub.map_or(u, |old| old.min(u)));
            }
        }
        let Some(branch_eval_ub) = scan_transfer_ub(domains, counter, &rhs, preceding, eval_univ_ub) else {
            eval_ub = None;
            break;
        };
        eval_ub = eval_ub.map(|u| u.max(branch_eval_ub));
    }

    (reachable_ub, eval_ub)
}

fn max_init_value(domains: &Domains, e: &Expr) -> Option<i128> {
    if let Some(n) = atom_nat(domains, e) {
        return Some(n);
    }
    match &*e.kind {
        ExprKind::FnConstruct { body, .. } => max_init_value(domains, body),
        ExprKind::If { then, els, .. } => Some(max_init_value(domains, then)?.max(max_init_value(domains, els)?)),
        _ => None,
    }
}

fn scan_transfer_ub(domains: &Domains, counter: &CounterSpec, rhs: &Expr, branch_terms: &[Expr], univ_ub: Option<i128>) -> Option<i128> {
    match &counter.kind {
        CounterKind::Scalar => scan_scalar_transfer_ub(domains, counter, rhs, univ_ub),
        CounterKind::Map(_) => scan_map_transfer_ub(domains, counter, rhs, branch_terms, univ_ub),
    }
}

fn scan_scalar_transfer_ub(domains: &Domains, counter: &CounterSpec, rhs: &Expr, pre_ub: Option<i128>) -> Option<i128> {
    if variable(rhs, false) == Some(counter.var) {
        return Some(0);
    }
    if let Some(r) = atom_nat(domains, rhs) {
        return Some(r);
    }
    match &*rhs.kind {
        ExprKind::Builtin { op: B::Plus, args } if args.len() == 2 => {
            for (lhs, delta_e) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                if variable(lhs, false) == Some(counter.var) {
                    let d = atom_nat(domains, delta_e)?;
                    if d == 0 {
                        return Some(0);
                    }
                    return pre_ub?.checked_add(d);
                }
            }
            None
        }
        ExprKind::If { cond, then, els } => {
            let then_ub = tighten_ub(pre_ub, extract_universal_ub(domains, counter, cond, false));
            let els_ub = tighten_ub(pre_ub, extract_universal_ub(domains, counter, cond, true));
            let a = scan_scalar_transfer_ub(domains, counter, then, then_ub)?;
            let b = scan_scalar_transfer_ub(domains, counter, els, els_ub)?;
            Some(a.max(b))
        }
        _ => None,
    }
}

fn scan_map_transfer_ub(
    domains: &Domains,
    counter: &CounterSpec,
    rhs: &Expr,
    branch_terms: &[Expr],
    univ_ub: Option<i128>,
) -> Option<i128> {
    if variable(rhs, false) == Some(counter.var) {
        return Some(0);
    }
    match &*rhs.kind {
        ExprKind::FnConstruct { bounds, body } if bounds.len() == 1 => {
            let BoundVars::Many(ids) = &bounds[0].vars else { return None };
            let idx = Expr::new(ExprKind::Local(ids[0]), body.span);
            scan_map_slot_transfer_ub(domains, counter, &idx, body, univ_ub)
        }
        ExprKind::Except { base, updates } if variable(base, false) == Some(counter.var) => {
            let mut max_val = 0i128;
            for (path, val) in updates {
                let [ExceptKey::Index(indices)] = path.as_slice() else { return None };
                let [idx] = indices.as_slice() else { return None };
                let mut slot_ub = univ_ub;
                for t in branch_terms {
                    slot_ub = tighten_ub(slot_ub, extract_slot_ub(domains, counter.var, Some(idx), t, false));
                }
                let u = scan_map_slot_transfer_ub(domains, counter, idx, val, slot_ub)?;
                max_val = max_val.max(u);
            }
            Some(max_val)
        }
        ExprKind::If { cond, then, els } => {
            let then_ub = tighten_ub(univ_ub, extract_universal_ub(domains, counter, cond, false));
            let els_ub = tighten_ub(univ_ub, extract_universal_ub(domains, counter, cond, true));
            let a = scan_map_transfer_ub(domains, counter, then, branch_terms, then_ub)?;
            let b = scan_map_transfer_ub(domains, counter, els, branch_terms, els_ub)?;
            Some(a.max(b))
        }
        _ => None,
    }
}

fn scan_map_slot_transfer_ub(domains: &Domains, counter: &CounterSpec, idx: &Expr, val: &Expr, pre_ub: Option<i128>) -> Option<i128> {
    if matches!(&*val.kind, ExprKind::FnApp { func, args } if args.len() == 1 && variable(func, false) == Some(counter.var) && expr_structurally_eq(&args[0], idx))
    {
        return Some(0);
    }
    if let Some(r) = atom_nat(domains, val) {
        return Some(r);
    }
    match &*val.kind {
        ExprKind::Builtin { op: B::Plus, args } if args.len() == 2 => {
            for (lhs, delta_e) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                if matches!(&*lhs.kind, ExprKind::FnApp { func, args } if args.len() == 1 && variable(func, false) == Some(counter.var) && expr_structurally_eq(&args[0], idx))
                {
                    let d = atom_nat(domains, delta_e)?;
                    if d == 0 {
                        return Some(0);
                    }
                    return pre_ub?.checked_add(d);
                }
            }
            None
        }
        ExprKind::If { cond, then, els } => {
            let then_ub = tighten_ub(pre_ub, extract_slot_ub(domains, counter.var, Some(idx), cond, false));
            let els_ub = tighten_ub(pre_ub, extract_slot_ub(domains, counter.var, Some(idx), cond, true));
            let a = scan_map_slot_transfer_ub(domains, counter, idx, then, then_ub)?;
            let b = scan_map_slot_transfer_ub(domains, counter, idx, els, els_ub)?;
            Some(a.max(b))
        }
        _ => None,
    }
}

fn tighten_ub(cur: Option<i128>, extra: Option<i128>) -> Option<i128> {
    match (cur, extra) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, b) => a.or(b),
    }
}

fn extract_universal_ub(domains: &Domains, counter: &CounterSpec, e: &Expr, negated: bool) -> Option<i128> {
    match &counter.kind {
        CounterKind::Scalar => extract_slot_ub(domains, counter.var, None, e, negated),
        CounterKind::Map(keys) => {
            if negated {
                return None;
            }
            match &*e.kind {
                ExprKind::And(es) => es.iter().filter_map(|x| extract_universal_ub(domains, counter, x, false)).min(),
                ExprKind::Quant { kind: QuantKind::Forall, bounds, body } if bounds.len() == 1 => {
                    let BoundVars::Many(ids) = &bounds[0].vars else { return None };
                    if ids.len() != 1 || domains.exact_set(&bounds[0].set).as_ref() != Some(keys) {
                        return None;
                    }
                    let idx = Expr::new(ExprKind::Local(ids[0]), body.span);
                    extract_slot_ub(domains, counter.var, Some(&idx), body, false)
                }
                ExprKind::Builtin { op: B::In, args } if args.len() == 2 && variable(&args[0], false) == Some(counter.var) => {
                    if let ExprKind::FnSet { domain, range } = &*args[1].kind {
                        if domains.exact_set(domain).as_ref() == Some(keys) {
                            return set_upper_bound(domains, range);
                        }
                    }
                    None
                }
                _ => None,
            }
        }
    }
}

fn matches_target_slot(e: &Expr, var: VarId, idx: Option<&Expr>) -> bool {
    match idx {
        None => variable(e, false) == Some(var),
        Some(expected) => {
            matches!(&*e.kind, ExprKind::FnApp { func, args } if args.len() == 1 && variable(func, false) == Some(var) && expr_structurally_eq(&args[0], expected))
        }
    }
}

fn extract_slot_ub(domains: &Domains, var: VarId, idx: Option<&Expr>, e: &Expr, negated: bool) -> Option<i128> {
    match &*e.kind {
        ExprKind::And(es) if !negated => es.iter().filter_map(|x| extract_slot_ub(domains, var, idx, x, false)).min(),
        ExprKind::Or(es) if negated => es.iter().filter_map(|x| extract_slot_ub(domains, var, idx, x, true)).min(),
        ExprKind::Builtin { op: B::Not, args } if args.len() == 1 => extract_slot_ub(domains, var, idx, &args[0], !negated),
        ExprKind::Builtin { op, args } if args.len() == 2 && matches!(op, B::Lt | B::Le | B::Gt | B::Ge | B::Eq) => {
            for (slot_e, const_e, rev) in [(&args[0], &args[1], false), (&args[1], &args[0], true)] {
                if matches_target_slot(slot_e, var, idx) {
                    let Some(Atom::Num(t)) = domains.atom_value(const_e) else { continue };
                    let mut norm_op = if rev {
                        match op {
                            B::Lt => B::Gt,
                            B::Le => B::Ge,
                            B::Gt => B::Lt,
                            B::Ge => B::Le,
                            x => *x,
                        }
                    } else {
                        *op
                    };
                    if negated {
                        norm_op = match norm_op {
                            B::Lt => B::Ge,
                            B::Le => B::Gt,
                            B::Gt => B::Le,
                            B::Ge => B::Lt,
                            _ => return None,
                        };
                    }
                    return match norm_op {
                        B::Lt => Some((t - 1).max(0)),
                        B::Le | B::Eq => Some(t.max(0)),
                        _ => None,
                    };
                }
            }
            None
        }
        ExprKind::Builtin { op: B::In, args } if !negated && args.len() == 2 && matches_target_slot(&args[0], var, idx) => {
            set_upper_bound(domains, &args[1])
        }
        _ => None,
    }
}

fn set_upper_bound(domains: &Domains, set: &Expr) -> Option<i128> {
    match &*set.kind {
        ExprKind::Builtin { op: B::DotDot, args } if args.len() == 2 => {
            let (Atom::Num(lo), Atom::Num(hi)) = (domains.atom_value(&args[0])?, domains.atom_value(&args[1])?) else {
                return None;
            };
            if lo > hi {
                return Some(0);
            }
            Some(hi.max(0))
        }
        ExprKind::SetEnum(es) => {
            let mut max_n = 0i128;
            for item in es {
                let Atom::Num(n) = domains.atom_value(item)? else { return None };
                max_n = max_n.max(n);
            }
            Some(max_n)
        }
        _ => None,
    }
}
