//! Apply frontend state-reduction proofs through the existing VIEW machinery.

use tlx_front::cfg::ConstBinding;
use tlx_sema::hir::*;
use tlx_value::{ops, Value};

use crate::{env::Env, error::EResult, eval::Ctx};

use super::{behavior, Behavior, InterpModel};

impl InterpModel {
    /// Forget proved irrelevant values in fingerprints, retaining concrete
    /// values and original actions for execution and counterexample replay.
    /// Opt-in mathematical clock semantics may eliminate eventual overflow.
    /// Safety only. Existing VIEWs take precedence. Symmetry composes only
    /// when every constant introduced by the projection is fixed by it.
    pub fn project_state(&mut self) -> Option<(&'static str, Vec<String>)> {
        let cfg = &self.ip.cfg;
        if !self.live.is_empty()
            || self.has_view()
            || !self.possible.is_empty()
            || !self.postconditions.is_empty()
            || !cfg.constants.iter().all(|b| {
                matches!(b, ConstBinding::Value { name, module: None, .. }
                if self.ip.root_def(name).is_none())
            })
        {
            return None;
        }
        let Ok(Behavior::Full { next, .. }) = behavior(&self.ip, cfg) else { return None };
        let observations: Vec<_> = self
            .invariants
            .iter()
            .chain(&self.constraints)
            .chain(&self.action_constraints)
            .chain(&self.action_props)
            .chain(self.init_props.iter().map(|(_, e)| e))
            .chain(&self.alias)
            .cloned()
            .collect();
        let omitted = tlx_sema::optimize::unobserved_variables(&self.ip.prog, &self.init, &next, &observations);
        if omitted.is_empty() {
            let (rule, projection) =
                if let Some(p) = tlx_sema::optimize::age_projection(&self.ip.prog, cfg, &self.init, &next, &observations) {
                    ("relative-age-projection", p)
                } else if let Some(p) = tlx_sema::optimize::history_projection(&self.ip.prog, cfg, &self.init, &next, &observations) {
                    ("history-summary-projection", p)
                } else if let Some(p) = tlx_sema::optimize::phase_projection(&self.ip.prog, cfg, &self.init, &next, &observations) {
                    ("phase-field-projection", p)
                } else {
                    (
                        "sequence-length-projection",
                        tlx_sema::optimize::sequence_length_projection(&self.ip.prog, cfg, &self.init, &next, &observations)?,
                    )
                };
            if !self.projection_equivariant(&projection.view) {
                return None;
            }
            // The generated rule model currently represents state invariants,
            // not constraints, action properties or trace aliases.
            if self.constraints.is_empty()
                && self.action_constraints.is_empty()
                && self.action_props.is_empty()
                && self.init_props.is_empty()
                && self.alias.is_none()
            {
                self.projection_certificate = projection.certificate.map(Into::into);
            }
            self.view = Some(projection.view);
            self.state_projection = true;
            return Some((rule, projection.fields));
        }
        let retained = self
            .ip
            .prog
            .vars
            .iter()
            .enumerate()
            .filter(|(i, _)| !omitted.contains(&VarId(*i as u32)))
            .map(|(i, v)| Expr::new(ExprKind::Var(VarId(i as u32)), v.span))
            .collect();
        self.view = Some(Expr::new(ExprKind::Tuple(retained), self.init.span));
        self.state_projection = true;
        Some(("unobserved-state-projection", omitted.iter().map(|v| self.ip.prog.vars[v.idx()].name.to_string()).collect()))
    }

    /// The accepted pass's generated proof; generation never invokes Lean.
    pub fn projection_certificate(&self) -> Option<&str> {
        self.projection_certificate.as_deref()
    }

    pub fn has_projected_symmetry(&self) -> bool {
        self.state_projection && !self.symmetry.is_empty()
    }

    fn projection_equivariant(&self, e: &Expr) -> bool {
        if self.symmetry.is_empty() {
            return true;
        }
        if matches!(&*e.kind, ExprKind::Const(_)) {
            let Ok(value) = self.ip.eval(e, &Env::default(), &Ctx::NONE) else { return false };
            return self.symmetry.iter().all(|p| ops::permute(&value, &|s| p.get(&s).cloned()).is_ok_and(|v| v == value));
        }
        let mut valid = true;
        tlx_sema::visit::children(e, &mut |child| valid &= self.projection_equivariant(child));
        valid
    }

    /// Canonicalize the projected value, so forgotten fields cannot decide
    /// which permutation represents its orbit. Internal sentinels may have
    /// different types from retained values; use the total structural order.
    pub(super) fn projected_orbit(&self, projected: Value) -> EResult<Value> {
        let mut least = projected.clone();
        for permutation in &self.symmetry {
            let image = ops::permute(&projected, &|s| permutation.get(&s).cloned())?;
            if tlx_value::order::try_total_cmp(&image, &least)?.is_lt() {
                least = image;
            }
        }
        Ok(least)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Interp;
    use tlx_runtime::{explore, Options, Outcome};
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
    fn mathematical_age_finishes_an_unbounded_clock_and_history() {
        let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
        let dir = tlx_testkit::TempDir::with_spec("age-eval", AGE, cfg);
        let p = Program::load(&dir.join("Age.tla"), &[]).unwrap();
        let ip = Interp::new(p, tlx_front::cfg::parse_cfg(cfg).unwrap()).unwrap();
        let mut m = InterpModel::new(ip).unwrap();
        let (rule, fields) = m.project_state().unwrap();
        assert_eq!(rule, "relative-age-projection");
        assert!(fields.contains(&"h.history".into()));
        let report = explore(&m, &Options { workers: 1, fp: tlx_runtime::FpConfig::fixed(4096), ..Default::default() });
        assert_eq!(report.outcome, Outcome::Ok);
        assert_eq!(report.stats.distinct, 8);
    }

    #[test]
    #[ignore = "requires the local external pragmatic corpus"]
    fn external_cleaner_mathematical_age() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../third_party/external/pragmatic/database-blob/storage-cleaner-improved/storagecleanerimproved.tla");
        let cfg = "SPECIFICATION Spec\nCONSTANTS SERVERS = {s1} CLEANERS = {c1}\n\
            METADATAS = {m1} USERIDS = {u1} IMAGES = {i1} UUIDS = {ui1}\nINVARIANTS TypeOk ConsistentReads\n";
        for check_consistency in [true, false] {
            let ip = Interp::new(Program::load(&path, &[]).unwrap(), tlx_front::cfg::parse_cfg(cfg).unwrap()).unwrap();
            let mut m = InterpModel::new(ip).unwrap();
            let (rule, fields) = m.project_state().unwrap();
            assert_eq!(rule, "relative-age-projection");
            assert!(fields.contains(&"blobStoreState.created.age<=2".into()));
            assert!(fields.contains(&"operations.history".into()));
            if !check_consistency {
                // Explore the entire quotient separately from the known
                // failing property. Keep its monitor in the generated key.
                m.invariants.truncate(1);
            }
            let report = explore(&m, &Options { workers: 1, fp: tlx_runtime::FpConfig::fixed(4096), ..Default::default() });
            if check_consistency {
                assert_eq!(report.outcome, Outcome::InvariantViolated("ConsistentReads".into()));
                assert!(!report.trace.is_empty());
            } else {
                assert_eq!(report.outcome, Outcome::Ok);
                assert_eq!((report.stats.generated, report.stats.distinct, report.stats.depth), (3083, 820, 27));
            }
        }
    }
}
