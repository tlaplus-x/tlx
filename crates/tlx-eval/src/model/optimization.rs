//! Apply frontend state-reduction proofs through the existing VIEW machinery.

use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::atomic::Ordering;

use tlx_front::cfg::ConstBinding;
use tlx_sema::hir::*;
use tlx_value::Value;

use crate::{env::Env, error::EResult, eval::Ctx};

use super::{behavior, Behavior, FpMode, InterpModel, State};

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
                ConstBinding::Value { name, module: None, .. } | ConstBinding::Subst { name, module: None, .. } => {
                    self.ip.root_def(name).is_none()
                }
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

    /// Forget proved irrelevant values in fingerprints, retaining concrete    /// Forget proved irrelevant values in fingerprints, retaining concrete
    /// values and original actions for execution and counterexample replay.
    /// Certified mathematical allocation may eliminate eventual overflow.
    /// Safety only. Existing VIEWs and symmetry exclude automatic projection.
    pub fn project_state(&mut self) -> Option<(&'static str, Vec<String>)> {
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
            ("phase-field-projection", opt::phase_projection_with_spec(&self.ip.prog, cfg, &self.init, &next, spec))
        }))
        .chain(std::iter::once_with(|| {
            ("sequence-length-projection", opt::sequence_length_projection_with_spec(&self.ip.prog, cfg, &self.init, &next, spec))
        }))
        .chain(std::iter::once_with(|| {
            ("ordered-allocation-projection", opt::ordered_projection_with_spec(&self.ip.prog, cfg, &self.init, &next, spec))
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
            let newly_enabled = matches!(rule, "phase-field-projection" | "ordered-allocation-projection");
            if newly_enabled && spec.has_action_checks() && !self.projection_merges(&projection) {
                continue;
            }
            let Some(certificate) = projection.certificate else { continue };
            self.projection_certificate = Some(certificate.into());
            self.ordered_projection = projection.ordered.map(Into::into);
            self.view = Some(projection.view);
            self.state_projection = true;
            return Some((rule, projection.fields));
        }
        None
    }

    fn symmetry_cert_next(&self) -> Option<Expr> {
        let cfg = &self.ip.cfg;
        if !self.live.is_empty()
            || (self.has_view() && !self.state_projection)
            || self.ordered_projection.is_some()
            || !self.group.is_empty()
            || cfg.symmetry.is_some()
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
        } else {
            tlx_sema::optimize::symmetry_certificate_with_spec(&self.ip.prog, cfg, &self.init, &next, spec, groups)
        }
    }

    /// Certify a disjoint product of full key permutation groups via the
    /// choice-symmetry certificate (`ChooseSymCertificate`), which proves
    /// `Init` equivariance as well as `CHOOSE` invariance. This does not install it.
    pub fn choose_symmetry_certificate(&self, groups: &[Vec<String>]) -> Option<String> {
        if self.state_projection {
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
        self.state_projection && !self.group.is_empty()
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
