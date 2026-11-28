//! Apply frontend state-reduction proofs through the existing VIEW machinery.

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::atomic::Ordering;

use tlx_front::cfg::ConstBinding;
use tlx_sema::hir::*;
use tlx_value::Value;

use crate::{env::Env, error::EResult, eval::Ctx};

use super::{behavior, Behavior, FpMode, InterpModel, State};

/// Bounded BFS summary of a model's reduced state space, used to compare
/// mutually exclusive certified reductions (such as `phase-field-projection`
/// vs. automatic symmetry) without guessing from static counts alone.
#[derive(Clone, Debug)]
pub struct ReducedProbe {
    /// Total distinct reduced states discovered (including initial states).
    pub distinct: usize,
    /// Whether the entire reachable reduced graph finished within the budget.
    pub completed: bool,
    /// Cumulative distinct reduced states after each completed BFS level `0..=d`.
    pub cumulative_by_depth: Vec<usize>,
}

/// One admitted state's verdict in the merge probe (`projection_merges`).
enum ProbeStep {
    /// Two distinct admitted states share a projected key.
    Merge,
    /// Admitted, not a merge (possibly a duplicate concrete state).
    Continue,
    /// Budget exhausted or evaluation failed before a witness.
    Decline,
}

impl InterpModel {
    fn cfg_constants_allow_certification(&self) -> bool {
        let cfg = &self.ip.cfg;
        tlx_sema::optimize::cfg_constants_supported(&self.ip.prog, cfg)
            && cfg.constants.iter().all(|b| match b {
                // `Def = value` still needs a value-override certificate.
                ConstBinding::Value { name, module: None, .. } => self.ip.root_def(name).is_none(),
                // Pure definition and parameterized-constant substitutions are
                // resolved and certified by `cfg_constants_supported`.
                ConstBinding::Subst { module: None, .. } => true,
                _ => false,
            })
    }

    fn init_prop_exprs(&self) -> Vec<Expr> {
        self.init_props.iter().map(|(_, e)| e.clone()).collect()
    }

    fn check_spec<'a>(&'a self, init_props: &'a [Expr]) -> tlx_sema::optimize::CheckSpec<'a> {
        tlx_sema::optimize::CheckSpec {
            invariants: &self.invariants,
            init_props,
            constraints: &self.constraints,
            action_constraints: &self.action_constraints,
            action_props: &self.action_props,
        }
    }

    /// Bound on the merge probe: admitted states and enumerated states (initial
    /// states plus generated successors). Both budgets are charged during
    /// enumeration, so no batch is queued before its states are checked.
    const MERGE_PROBE_STATES: usize = 4096;
    const MERGE_PROBE_ENUM: usize = 65_536;

    /// Whether the candidate projection identifies at least two distinct
    /// admitted states within a bounded exploration.
    ///
    /// A certified projection that merges no admitted state cannot reduce the
    /// search, so a rule whose action-check support made it applicable declines
    /// instead of installing a reduction that changes nothing. Initial states
    /// and successors share one admission path, both budgets are charged while
    /// enumerating, and every admitted state's projected key is compared as soon
    /// as it is generated (only unseen concrete states are queued), so a merge
    /// in a large fan-out is witnessed before the enumeration budget runs out.
    /// The bound is conservative in one direction: a merge beyond it is not
    /// observed and the projection declines. An evaluation error before a
    /// witness also declines the candidate, leaving the ordinary search to
    /// report the error. The probe suppresses `-stats` collection and restores
    /// the generated-state counter, so it changes no report.
    fn projection_merges(&self, projection: &tlx_sema::optimize::FieldProjection) -> bool {
        let mut reduced = self.clone();
        reduced.view = Some(projection.view.clone());
        reduced.ordered_projection = projection.ordered.clone().map(std::sync::Arc::new);
        reduced.state_projection = true;
        reduced.fp_mode = FpMode::Reduced;
        let plain = self.with_fp_mode(FpMode::Plain);
        let generated = self.ip.composed_states.load(Ordering::Relaxed);
        let stats_on = tlx_runtime::stats::suspend();
        let merges = self.merge_probe(&plain, &reduced, &projection.view);
        tlx_runtime::stats::resume(stats_on);
        self.ip.composed_states.store(generated, Ordering::Relaxed);
        merges
    }

    /// Bounded level-by-level BFS of this model's reduced state space (`VIEW`
    /// and/or symmetry). Suspends `-stats` and restores `composed_states` so
    /// probing never alters search metrics; returns `None` on evaluation error.
    pub fn probe_reduced_size(
        &self,
        max_states: usize,
        max_depth: u32,
        max_edges: usize,
        max_time: std::time::Duration,
    ) -> Option<ReducedProbe> {
        use tlx_runtime::Model;
        let started = std::time::Instant::now();
        let mut m = self.with_fp_mode(FpMode::Reduced);
        m.claim = None;
        let generated = self.ip.composed_states.load(Ordering::Relaxed);
        let stats_on = tlx_runtime::stats::suspend();
        let result = (|| {
            let mut seen: HashSet<u64> = HashSet::new();
            let mut frontier: Vec<State> = Vec::new();
            let mut cumulative_by_depth: Vec<usize> = Vec::new();
            let mut hit_budget = false;
            let mut failed = false;

            if m.init_states_while(&mut |s| {
                if started.elapsed() >= max_time {
                    hit_budget = true;
                    return false;
                }
                match m.constraint(&s) {
                    Ok(true) => {}
                    Ok(false) => return true,
                    Err(_) => {
                        failed = true;
                        return false;
                    }
                }
                if seen.insert(s.fp) {
                    frontier.push(s);
                    if seen.len() > max_states {
                        hit_budget = true;
                        return false;
                    }
                }
                true
            })
            .is_err()
                || failed
            {
                return None;
            }
            if hit_budget {
                return Some(ReducedProbe { distinct: seen.len(), completed: false, cumulative_by_depth });
            }
            cumulative_by_depth.push(seen.len());
            if frontier.is_empty() {
                return Some(ReducedProbe { distinct: seen.len(), completed: true, cumulative_by_depth });
            }

            let mut total_edges = 0usize;
            for _depth in 0..max_depth {
                let mut next_frontier = Vec::new();
                for s in &frontier {
                    if started.elapsed() >= max_time {
                        hit_budget = true;
                        break;
                    }
                    if m.successors(s, &mut |t, _| {
                        total_edges += 1;
                        if total_edges > max_edges || started.elapsed() >= max_time {
                            hit_budget = true;
                            return false;
                        }
                        if seen.contains(&t.fp) {
                            return true;
                        }
                        let admitted = match m.constraint(&t) {
                            Ok(true) => match m.action_constraint(s, &t) {
                                Ok(ok) => ok,
                                Err(_) => {
                                    failed = true;
                                    return false;
                                }
                            },
                            Ok(false) => false,
                            Err(_) => {
                                failed = true;
                                return false;
                            }
                        };
                        if admitted && seen.insert(t.fp) {
                            next_frontier.push(t);
                            if seen.len() > max_states {
                                hit_budget = true;
                                return false;
                            }
                        }
                        true
                    })
                    .is_err()
                        || failed
                    {
                        return None;
                    }
                    if hit_budget {
                        break;
                    }
                }
                if hit_budget {
                    return Some(ReducedProbe { distinct: seen.len(), completed: false, cumulative_by_depth });
                }
                cumulative_by_depth.push(seen.len());
                if next_frontier.is_empty() {
                    return Some(ReducedProbe { distinct: seen.len(), completed: true, cumulative_by_depth });
                }
                frontier = next_frontier;
            }
            Some(ReducedProbe { distinct: seen.len(), completed: false, cumulative_by_depth })
        })();
        tlx_runtime::stats::resume(stats_on);
        self.ip.composed_states.store(generated, Ordering::Relaxed);
        result
    }

    #[allow(clippy::too_many_arguments)] // one admission path shared by initial states and successors
    fn probe_admit(
        plain: &InterpModel,
        reduced: &InterpModel,
        view: &Expr,
        s: State,
        parent: Option<&State>,
        keys: &mut HashMap<u64, u64>,
        seen: &mut HashSet<u64>,
        queue: &mut VecDeque<State>,
        admitted: &mut usize,
        enumerated: &mut usize,
    ) -> ProbeStep {
        use tlx_runtime::Model;
        *enumerated += 1;
        if *enumerated > Self::MERGE_PROBE_ENUM {
            return ProbeStep::Decline;
        }
        match plain.constraint(&s) {
            Ok(true) => {}
            Ok(false) => return ProbeStep::Continue,
            Err(_) => return ProbeStep::Decline,
        }
        if let Some(parent) = parent {
            match plain.action_constraint(parent, &s) {
                Ok(true) => {}
                Ok(false) => return ProbeStep::Continue,
                Err(_) => return ProbeStep::Decline,
            }
        }
        *admitted += 1;
        if *admitted > Self::MERGE_PROBE_STATES {
            return ProbeStep::Decline;
        }
        let projected = match reduced.projected_value(view, &s.vals, s.level) {
            Ok(v) => v,
            Err(_) => return ProbeStep::Decline,
        };
        let key = match tlx_value::fingerprint::fingerprint(&projected) {
            Ok(k) => k,
            Err(_) => return ProbeStep::Decline,
        };
        match keys.get(&key) {
            Some(&full) if full != s.fp => return ProbeStep::Merge,
            Some(_) => {}
            None => {
                keys.insert(key, s.fp);
            }
        }
        if seen.insert(s.fp) {
            queue.push_back(s);
        }
        ProbeStep::Continue
    }

    fn merge_probe(&self, plain: &InterpModel, reduced: &InterpModel, view: &Expr) -> bool {
        use tlx_runtime::Model;
        let mut queue = VecDeque::new();
        let mut seen = HashSet::new();
        let mut keys: HashMap<u64, u64> = HashMap::new();
        let mut enumerated = 0usize;
        let mut admitted = 0usize;
        let mut witness = false;
        let mut decline = false;
        let init = plain.init_states_while(&mut |s| match Self::probe_admit(
            plain,
            reduced,
            view,
            s,
            None,
            &mut keys,
            &mut seen,
            &mut queue,
            &mut admitted,
            &mut enumerated,
        ) {
            ProbeStep::Merge => {
                witness = true;
                false
            }
            ProbeStep::Decline => {
                decline = true;
                false
            }
            ProbeStep::Continue => true,
        });
        if witness {
            return true;
        }
        if decline || init.is_err() {
            return false;
        }
        while let Some(s) = queue.pop_front() {
            let result = plain.successors(&s, &mut |t, _| match Self::probe_admit(
                plain,
                reduced,
                view,
                t,
                Some(&s),
                &mut keys,
                &mut seen,
                &mut queue,
                &mut admitted,
                &mut enumerated,
            ) {
                ProbeStep::Merge => {
                    witness = true;
                    false
                }
                ProbeStep::Decline => {
                    decline = true;
                    false
                }
                ProbeStep::Continue => true,
            });
            if witness {
                return true;
            }
            if decline || result.is_err() {
                return false;
            }
        }
        false
    }

    /// Forget proved irrelevant values in fingerprints, retaining concrete
    /// values and original actions for execution and counterexample replay.
    /// Certified mathematical allocation may eliminate eventual overflow.
    /// Safety only. Existing VIEWs and symmetry exclude automatic projection.
    pub fn project_state(&mut self) -> Option<(&'static str, Vec<String>)> {
        self.project_state_with_sym_keys(&std::collections::BTreeSet::new())
    }

    /// Like [`Self::project_state`], while avoiding any model value in `sym_keys`
    /// as a dead-field sentinel so a phase-field `VIEW` stays equivariant under
    /// permutations moving `sym_keys`.
    pub fn project_state_with_sym_keys(
        &mut self,
        sym_keys: &std::collections::BTreeSet<std::sync::Arc<str>>,
    ) -> Option<(&'static str, Vec<String>)> {
        let cfg = &self.ip.cfg;
        if !self.live.is_empty()
            || self.has_view()
            || !self.possible.is_empty()
            || !self.postconditions.is_empty()
            || !self.cfg_constants_allow_certification()
            || self.alias.is_some()
            || !self.group.is_empty()
            || cfg.symmetry.is_some()
        {
            return None;
        }
        let Ok(Behavior::Full { next, .. }) = behavior(&self.ip, cfg) else { return None };
        let init_props = self.init_prop_exprs();
        let spec = self.check_spec(&init_props);
        use tlx_sema::optimize as opt;
        let candidates = std::iter::once_with(|| {
            ("unobserved-state-projection", opt::unobserved_projection_with_spec(&self.ip.prog, cfg, &self.init, &next, spec))
        })
        .chain(std::iter::once_with(|| {
            ("relative-age-projection", opt::age_projection_with_spec(&self.ip.prog, cfg, &self.init, &next, spec))
        }))
        .chain(std::iter::once_with(|| {
            ("history-summary-projection", opt::history_projection_with_spec(&self.ip.prog, cfg, &self.init, &next, spec))
        }))
        .chain(std::iter::once_with(|| {
            ("ordered-allocation-projection", opt::ordered_projection_with_spec(&self.ip.prog, cfg, &self.init, &next, spec))
        }))
        .chain(std::iter::once_with(|| {
            ("threshold-counter-projection", opt::threshold_counter_projection_with_spec(&self.ip.prog, cfg, &self.init, &next, spec))
        }))
        .chain(std::iter::once_with(|| {
            ("phase-field-projection", opt::phase_projection_with_spec_avoiding(&self.ip.prog, cfg, &self.init, &next, spec, sym_keys))
        }))
        .chain(std::iter::once_with(|| {
            ("sequence-length-projection", opt::sequence_length_projection_with_spec(&self.ip.prog, cfg, &self.init, &next, spec))
        }));
        for (rule, candidate) in candidates {
            let Some(projection) = candidate else { continue };
            if projection.certificate.is_none() {
                continue;
            }
            // The projections this rule change newly enables with action checks
            // additionally require that the quotient actually merges admitted
            // states: one that merges nothing cannot reduce the search. Rules
            // that already supported action checks keep their selection.
            let newly_enabled = matches!(rule, "phase-field-projection" | "ordered-allocation-projection" | "threshold-counter-projection");
            // A saturation whose caps no reachable counter value exceeds merges
            // nothing, so its `VIEW` is pure overhead. The static bound on Init,
            // `Next` and `CONSTRAINT` cannot see guards that bound a counter only
            // in some control phases, so this rule additionally requires a
            // bounded merge witness instead of trusting the static estimate.
            let needs_merge_witness = (newly_enabled && spec.has_action_checks()) || rule == "threshold-counter-projection";
            if needs_merge_witness && !self.projection_merges(&projection) {
                continue;
            }
            let Some(certificate) = projection.certificate else { continue };
            self.projection_certificate = Some(certificate.into());
            self.mathematical_counter_arithmetic = projection.mathematical_counter_arithmetic;
            self.ordered_projection = projection.ordered.map(Into::into);
            self.view = Some(projection.view);
            self.state_projection = true;
            return Some((rule, projection.fields));
        }
        None
    }

    fn symmetry_cert_next(&self) -> Option<Expr> {
        self.symmetry_cert_next_with(false)
    }

    /// The next-state relation a symmetry certificate covers. `declared`
    /// permits a group installed from the cfg's `SYMMETRY` declaration: the
    /// caller certifies the combined product that includes the declared one
    /// (`augmented_symmetry_certificate`).
    fn symmetry_cert_next_with(&self, declared: bool) -> Option<Expr> {
        let cfg = &self.ip.cfg;
        if !self.live.is_empty()
            || (self.has_view() && !self.state_projection && self.tuple_view_vars().is_none())
            || self.ordered_projection.is_some()
            || (!declared && (!self.group.is_empty() || cfg.symmetry.is_some()))
            || !self.possible.is_empty()
            || !self.postconditions.is_empty()
            || self.alias.is_some()
            || !self.cfg_constants_allow_certification()
        {
            return None;
        }
        let Ok(Behavior::Full { next, .. }) = behavior(&self.ip, cfg) else { return None };
        Some(next)
    }

    /// The maximum nesting of `VIEW` variable-group definitions resolved
    /// before the declared view fails closed.
    const VIEW_GROUP_RESOLUTION_LIMIT: usize = 64;

    /// Flatten the declared cfg `VIEW` when it is exactly an unprimed state
    /// variable or a (possibly nested) tuple of distinct state variables, in
    /// the order the user wrote them. Zero-arity variable-group definitions
    /// (`serverVars == <<pc, log>>`, `View == <<serverVars, logVars>>`) expand
    /// recursively after `.cfg` `Def <- OtherDef` redirects. This is the single
    /// cfg-aware resolver: the certificate emitter is handed the retained list
    /// it returns, so eligibility and emission cannot disagree.
    ///
    /// Any other `VIEW` returns `None`, so automatic symmetry fails closed
    /// while the declared `VIEW` search stays exactly as it was: computed or
    /// primed subexpressions, repeated variables (including across groups),
    /// empty tuples, parameterized or function definitions, builtins, a
    /// definition assigned a `.cfg` value (`serverVars = <<1, 2>>`), and a
    /// definition-reference cycle.
    pub fn tuple_view_vars(&self) -> Option<Vec<VarId>> {
        let mut retained = Vec::new();
        let mut stack = Vec::new();
        self.flatten_view_var(self.view.as_ref()?, &mut retained, &mut stack, 0)?;
        (!retained.is_empty()).then_some(retained)
    }

    fn flatten_view_var(&self, e: &Expr, retained: &mut Vec<VarId>, stack: &mut Vec<DefId>, depth: usize) -> Option<()> {
        if depth > Self::VIEW_GROUP_RESOLUTION_LIMIT {
            return None;
        }
        match &*e.kind {
            ExprKind::Var(v) => {
                if v.idx() >= self.ip.prog.vars.len() || retained.contains(v) {
                    return None;
                }
                retained.push(*v);
            }
            ExprKind::Tuple(es) => {
                if es.is_empty() {
                    return None;
                }
                for e in es {
                    self.flatten_view_var(e, retained, stack, depth + 1)?;
                }
            }
            ExprKind::Apply { op: OpRef::Def(d), args } if args.is_empty() => {
                // `name = value` in the cfg replaces the definition with a
                // value; it is not a variable group, before or after redirect.
                if self.ip.has_def_value(*d) {
                    return None;
                }
                let d = self.ip.redirect_def(*d);
                if self.ip.has_def_value(d) || stack.contains(&d) {
                    return None;
                }
                let def = &self.ip.prog.defs[d.idx()];
                if !def.params.is_empty() || def.builtin.is_some() {
                    return None;
                }
                let DefKind::Op(body) = &def.kind else { return None };
                stack.push(d);
                let flattened = self.flatten_view_var(body, retained, stack, depth + 1);
                stack.pop();
                flattened?;
            }
            _ => return None,
        }
        Some(())
    }

    /// Whether the declared tuple `VIEW` retains every state variable (a
    /// permutation of them), so a plain symmetry certificate covers it: the
    /// view is then a bijection on states and the orbit quotient is unchanged.
    pub fn view_retains_all(&self) -> bool {
        self.tuple_view_vars().is_some_and(|retained| retained.len() == self.ip.prog.vars.len())
    }

    /// Canonicalize the declared tuple `VIEW`'s projected value at the
    /// fingerprint boundary after a certified erasure+symmetry group is
    /// installed. The composed certificate's key is exactly the orbit of the
    /// projected value, whereas the plain `VIEW`-with-symmetry fingerprint
    /// picks a whole-state least representative first, which would refine the
    /// certified quotient and can lose counterexample replay.
    pub fn install_view_projection(&mut self) {
        self.view_projection = true;
    }

    /// Certify a disjoint product of full key permutation groups. This does not install it.
    pub fn symmetry_certificate(&self, groups: &[Vec<String>]) -> Option<String> {
        let next = self.symmetry_cert_next()?;
        let cfg = &self.ip.cfg;
        let init_props = self.init_prop_exprs();
        let spec = self.check_spec(&init_props);
        if self.state_projection {
            tlx_sema::optimize::symmetry_projection_certificate_with_spec(
                &self.ip.prog,
                cfg,
                &self.init,
                &next,
                spec,
                groups,
                self.view.as_ref()?,
            )
        } else if let Some(retained) = self.tuple_view_vars() {
            // A declared tuple `VIEW`: a full-retention view is a bijection on
            // states (plain symmetry certificate); an omitting view composes
            // certified erasure with the orbit quotient over the exact
            // retained tuple.
            let span = self.view.as_ref()?.span;
            tlx_sema::optimize::symmetry_view_certificate_with_spec(&self.ip.prog, cfg, &self.init, &next, spec, groups, &retained, span)
        } else {
            tlx_sema::optimize::symmetry_certificate_with_spec(&self.ip.prog, cfg, &self.init, &next, spec, groups)
        }
    }

    /// Certify `combined` — the declared `.cfg` `SYMMETRY` factors plus extra
    /// disjoint full symmetric groups — as one connected product. Fails closed
    /// unless the declared group factors into full symmetric groups and every
    /// one of those factors appears verbatim in `combined`, so the certificate
    /// covers the group actually installed. This does not install it.
    pub fn augmented_symmetry_certificate(&self, combined: &[Vec<String>]) -> Option<String> {
        if self.state_projection || self.has_view() || self.ip.cfg.symmetry.is_none() {
            return None;
        }
        let declared: Vec<Vec<String>> =
            self.symmetry_factors()?.into_iter().map(|keys| keys.iter().map(|m| m.sym().as_str().to_owned()).collect()).collect();
        if !declared.iter().all(|factor| combined.contains(factor)) {
            return None;
        }
        let next = self.symmetry_cert_next_with(true)?;
        let init_props = self.init_prop_exprs();
        let spec = self.check_spec(&init_props);
        tlx_sema::optimize::symmetry_certificate_with_spec(&self.ip.prog, &self.ip.cfg, &self.init, &next, spec, combined)
    }

    /// Certify a disjoint product of full key permutation groups via the
    /// choice-symmetry certificate (`ChooseSymCertificate`), which proves
    /// `Init` equivariance as well as `CHOOSE` invariance. This does not install it.
    pub fn choose_symmetry_certificate(&self, groups: &[Vec<String>]) -> Option<String> {
        if self.state_projection {
            return None;
        }
        // Choice symmetry has no erasure counterpart, so a declared `VIEW` that
        // omits a variable cannot use it; a full-retention tuple view is a
        // bijection on states and the plain certificate still covers it.
        if self.has_view() && !self.view_retains_all() {
            return None;
        }
        let next = self.symmetry_cert_next()?;
        let init_props = self.init_prop_exprs();
        let spec = self.check_spec(&init_props);
        tlx_sema::optimize::choose_symmetry_certificate_with_spec(&self.ip.prog, &self.ip.cfg, &self.init, &next, spec, groups)
    }

    /// Retain the proof of the automatic group actually installed by the caller.
    pub fn record_symmetry_certificate(&mut self, certificate: String) {
        self.projection_certificate = Some(certificate.into());
    }

    /// The accepted pass's generated proof; generation never invokes Lean.
    pub fn projection_certificate(&self) -> Option<&str> {
        self.projection_certificate.as_deref()
    }

    pub fn mathematical_counter_arithmetic(&self) -> bool {
        self.mathematical_counter_arithmetic
    }

    pub fn ordered_projection(&self) -> Option<&tlx_sema::optimize::OrderedPlan> {
        self.ordered_projection.as_deref()
    }

    pub(super) fn projected_value(&self, view: &Expr, values: &[Value], level: u32) -> EResult<Value> {
        if let Some(plan) = &self.ordered_projection {
            super::ordered::project(plan, values)
        } else if let ExprKind::Tuple(es) = &*view.kind {
            if es.iter().all(|e| matches!(&*e.kind, ExprKind::Var(_))) {
                let parts: Vec<Value> = es
                    .iter()
                    .map(|e| match &*e.kind {
                        ExprKind::Var(v) => values[v.idx()].clone(),
                        _ => unreachable!(),
                    })
                    .collect();
                return Ok(Value::tuple(parts));
            }
            Ok(self.ip.eval(view, &Env::default(), &Ctx::state(values, level))?.normalize()?)
        } else {
            Ok(self.ip.eval(view, &Env::default(), &Ctx::state(values, level))?.normalize()?)
        }
    }

    /// An automatically certified projection, distinct from a declared VIEW.
    pub fn has_automatic_projection(&self) -> bool {
        self.state_projection
    }

    pub fn has_projected_symmetry(&self) -> bool {
        (self.state_projection || self.view_projection) && !self.group.is_empty()
    }

    /// Canonicalize the projected value, so forgotten fields cannot decide
    /// which permutation represents its orbit. Internal sentinels may have
    /// different types from retained values; use the total structural order.
    pub(super) fn projected_orbit(&self, projected: Value) -> EResult<Value> {
        let Some(p) = self.group.least_total_perm(&projected)? else {
            return Ok(projected);
        };
        Ok(p.apply(&projected)?.unwrap_or(projected))
    }

    /// Fast fingerprint for projected symmetry when `view` is a pure tuple of
    /// retained state variables: compares permutations in-place via
    /// `Group::least_perm` (building only the winning permutation's image) and
    /// falls back to `projected_orbit` if TLC comparison encounters mixed types.
    pub(super) fn projected_orbit_fp(&self, view: &Expr, vals: &[Value], level: u32) -> EResult<u64> {
        if self.ordered_projection.is_none() {
            if let ExprKind::Tuple(es) = &*view.kind {
                if !es.is_empty() && es.iter().all(|e| matches!(&*e.kind, ExprKind::Var(_))) {
                    let retained: Vec<Value> = es
                        .iter()
                        .map(|e| match &*e.kind {
                            ExprKind::Var(v) => vals[v.idx()].clone(),
                            _ => unreachable!(),
                        })
                        .collect();
                    let order: Vec<usize> = (0..retained.len()).collect();
                    if let Ok(opt_p) = self.group.least_perm(&mut super::symmetry::StateVals::Given(&retained), &order) {
                        let mut fps = Vec::with_capacity(retained.len());
                        match opt_p {
                            None => {
                                for v in &retained {
                                    fps.push(tlx_value::fingerprint::fingerprint(v)?);
                                }
                            }
                            Some(perm) => {
                                for v in &retained {
                                    let fp = match perm.apply(v)? {
                                        Some(img) => tlx_value::fingerprint::fingerprint(&img)?,
                                        None => tlx_value::fingerprint::fingerprint(v)?,
                                    };
                                    fps.push(fp);
                                }
                            }
                        }
                        return super::symmetry::combine_fps(&fps);
                    }
                }
            }
        }
        let projected = self.projected_value(view, vals, level)?;
        let canonical = self.projected_orbit(projected)?;
        Ok(tlx_value::fingerprint::fingerprint(&canonical)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Interp;
    use tlx_sema::Program;

    const AGE: &str = r#"---- MODULE Age ----
EXTENDS Naturals, Sequences
VARIABLE clock, records, h
Empty == [status |-> "empty", payload |-> ""]
Init == /\ clock = 0 /\ records = [k \in {1} |-> Empty] /\ h = <<>>
Tick == /\ clock' = clock + 1 /\ UNCHANGED <<records, h>>
Put == /\ records' = [records EXCEPT ![1] = [created |-> clock, payload |-> "x"]]
       /\ h' = Append(h, "put") /\ UNCHANGED clock
Drop == /\ records[1] # Empty /\ records[1].created + 2 <= clock
        /\ records' = [records EXCEPT ![1] = Empty]
        /\ h' = Append(h, "drop") /\ UNCHANGED clock
Next == Tick \/ Put \/ Drop
Inv == /\ clock \in Nat /\ records \in [{1} -> [created: Nat, payload: {"x"}] \cup {Empty}]
       /\ h \in Seq({"put", "drop"})
====
"#;

    #[test]
    fn age_installs_a_connected_composition_certificate() {
        let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
        let dir = tlx_testkit::TempDir::with_spec("age-eval", AGE, cfg);
        let p = Program::load(&dir.join("Age.tla"), &[]).unwrap();
        let ip = Interp::new(p, tlx_front::cfg::parse_cfg(cfg).unwrap()).unwrap();
        let mut m = InterpModel::new(ip).unwrap();
        let (rule, _) = m.project_state().unwrap();
        assert_eq!(rule, "relative-age-projection");
        assert!(m.projection_certificate().unwrap().contains("GeneratedAgeHistory"));
    }

    const DECLARED: &str = r#"---- MODULE Declared ----
EXTENDS TLC, Naturals, FiniteSets
CONSTANTS TxId, Key
VARIABLES tx, key
Init == tx = [t \in TxId |-> 0] /\ key = [k \in Key |-> 0]
Next == \/ \E t \in TxId : tx[t] < 1 /\ tx' = [tx EXCEPT ![t] = 1] /\ UNCHANGED key
        \/ \E k \in Key : key[k] < 1 /\ key' = [key EXCEPT ![k] = 1] /\ UNCHANGED tx
Inv == \A t \in TxId : tx[t] <= 1 /\ \A k \in Key : key[k] <= 1
Syn == Permutations(TxId)
====
"#;

    #[test]
    fn an_augmented_certificate_must_cover_the_declared_factors() {
        let cfg =
            "CONSTANTS\n  TxId = {t1, t2}\n  Key = {k1, k2}\nSYMMETRY Syn\nINIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
        let dir = tlx_testkit::TempDir::with_spec("declared-augment", DECLARED, cfg);
        let p = Program::load(&dir.join("Declared.tla"), &[]).unwrap();
        let ip = Interp::new(p, tlx_front::cfg::parse_cfg(cfg).unwrap()).unwrap();
        let m = InterpModel::new(ip).unwrap();
        let declared: Vec<Vec<String>> = m
            .symmetry_factors()
            .expect("the declared group factors")
            .into_iter()
            .map(|keys| keys.iter().map(|k| k.sym().as_str().to_owned()).collect())
            .collect();
        assert_eq!(declared.len(), 1);
        assert_eq!(declared[0].len(), 2);
        let mut combined = declared.clone();
        combined.push(vec!["k1".to_owned(), "k2".to_owned()]);
        assert!(m.augmented_symmetry_certificate(&combined).is_some());
        // The certificate must cover every declared factor: dropping one is refused.
        assert!(m.augmented_symmetry_certificate(&combined[1..]).is_none());
        // Without a declared SYMMETRY the certificate is refused outright.
        let plain = "INIT Init\nNEXT Next\nINVARIANT Inv\nCONSTANTS TxId = {t1, t2} Key = {k1, k2}\n";
        let p = Program::load(&dir.join("Declared.tla"), &[]).unwrap();
        let ip = Interp::new(p, tlx_front::cfg::parse_cfg(plain).unwrap()).unwrap();
        assert!(InterpModel::new(ip).unwrap().augmented_symmetry_certificate(&combined[1..]).is_none());
    }

    const NESTED_VIEW: &str = r#"---- MODULE NestedView ----
EXTENDS TLC, Naturals, FiniteSets
CONSTANT Proc
VARIABLES pc, phase, ghost
serverVars == <<pc>>
logVars == <<phase>>
ghostVars == <<ghost>>
Init == pc = [p \in Proc |-> 0] /\ phase = FALSE /\ ghost = FALSE
Next == UNCHANGED <<pc, phase, ghost>>
Inv == TRUE
View == <<logVars, serverVars>>
====
"#;

    fn nested_view_model(cfg: &str) -> InterpModel {
        let dir = tlx_testkit::TempDir::with_spec("nested-view", NESTED_VIEW, cfg);
        let program = Program::load(&dir.join("NestedView.tla"), &[]).unwrap();
        let ip = Interp::new(program, tlx_front::cfg::parse_cfg(cfg).unwrap()).unwrap();
        InterpModel::new(ip).unwrap()
    }

    #[test]
    fn declared_view_group_definitions_resolve_recursively_and_fail_closed() {
        let cfg = "CONSTANT Proc = {p1, p2}\nINIT Init\nNEXT Next\nVIEW View\n";
        // `<<logVars, serverVars>>` expands to `<<phase, pc>>` in that order.
        assert_eq!(nested_view_model(cfg).tuple_view_vars(), Some(vec![VarId(1), VarId(0)]));
        // A `.cfg` value assignment replaces the group with a value.
        let value = "CONSTANT Proc = {p1, p2}\nCONSTANT serverVars = <<1, 2>>\nINIT Init\nNEXT Next\nVIEW View\n";
        assert!(nested_view_model(value).tuple_view_vars().is_none());
        // A `.cfg` `Def <- OtherDef` redirect is followed to the replacement group.
        let redirect = "CONSTANT Proc = {p1, p2}\nCONSTANT serverVars <- ghostVars\nINIT Init\nNEXT Next\nVIEW View\n";
        assert_eq!(nested_view_model(redirect).tuple_view_vars(), Some(vec![VarId(1), VarId(2)]));
    }

    #[test]
    #[ignore = "requires the local external pragmatic corpus; analysis only"]
    fn external_cleaner_age_filter_has_a_connected_certificate() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../third_party/external/pragmatic/database-blob/storage-cleaner-improved/storagecleanerimproved.tla");
        let cfg = "SPECIFICATION Spec\nCONSTANTS SERVERS = {s1} CLEANERS = {c1}\n\
            METADATAS = {m1} USERIDS = {u1} IMAGES = {i1} UUIDS = {ui1}\nINVARIANTS TypeOk ConsistentReads\n";
        let ip = Interp::new(Program::load(&path, &[]).unwrap(), tlx_front::cfg::parse_cfg(cfg).unwrap()).unwrap();
        let mut model = InterpModel::new(ip).unwrap();
        // CleanerStartGetBlobKeys stores a set filtered by timestamp age.
        // Its predicate and selected keys are explicit in the certificate.
        let (rule, _) = model.project_state().expect("certified relative-age filtering");
        assert_eq!(rule, "relative-age-projection");
        assert!(model.projection_certificate().unwrap().contains("Test.select"));
        assert!(model.projection_certificate().unwrap().contains("GeneratedAgeHistory"));
    }
}
