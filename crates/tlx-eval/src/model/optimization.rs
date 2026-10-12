//! Apply frontend state-reduction proofs through the existing VIEW machinery.

use tlx_front::cfg::ConstBinding;
use tlx_sema::hir::*;
use tlx_value::{ops, Value};

use crate::{env::Env, error::EResult, eval::Ctx};

use super::{behavior, Behavior, InterpModel};

impl InterpModel {
    /// Forget proved irrelevant values in fingerprints, retaining concrete
    /// values and original actions for execution and counterexample replay.
    /// Certified mathematical allocation may eliminate eventual overflow.
    /// Safety only. Existing VIEWs and symmetry exclude automatic projection.
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
        // Certificates currently cover state invariants and deadlocks only.
        // No candidate may bypass this gate, including legacy reductions.
        if !self.constraints.is_empty()
            || !self.action_constraints.is_empty()
            || !self.action_props.is_empty()
            || !self.init_props.is_empty()
            || self.alias.is_some()
            || !self.symmetry.is_empty()
            || cfg.symmetry.is_some()
        {
            return None;
        }
        let observations = &self.invariants;
        use tlx_sema::optimize as opt;
        let candidates = std::iter::once_with(|| {
            ("unobserved-state-projection", opt::unobserved_projection(&self.ip.prog, &self.init, &next, observations))
        })
        .chain(std::iter::once_with(|| {
            ("relative-age-projection", opt::age_projection(&self.ip.prog, cfg, &self.init, &next, observations))
        }))
        .chain(std::iter::once_with(|| {
            ("history-summary-projection", opt::history_projection(&self.ip.prog, cfg, &self.init, &next, observations))
        }))
        .chain(std::iter::once_with(|| {
            ("ordered-allocation-projection", opt::ordered_projection(&self.ip.prog, cfg, &self.init, &next, observations))
        }));
        for (rule, candidate) in candidates {
            let Some(projection) = candidate else { continue };
            let Some(certificate) = projection.certificate else { continue };
            self.projection_certificate = Some(certificate.into());
            self.ordered_projection = projection.ordered.map(Into::into);
            self.view = Some(projection.view);
            self.state_projection = true;
            return Some((rule, projection.fields));
        }
        None
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
        } else {
            Ok(self.ip.eval(view, &Env::default(), &Ctx::state(values, level))?.normalize()?)
        }
    }

    pub fn has_projected_symmetry(&self) -> bool {
        self.state_projection && !self.symmetry.is_empty()
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
    fn age_installs_a_connected_certificate_without_history_composition() {
        let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
        let dir = tlx_testkit::TempDir::with_spec("age-eval", AGE, cfg);
        let p = Program::load(&dir.join("Age.tla"), &[]).unwrap();
        let ip = Interp::new(p, tlx_front::cfg::parse_cfg(cfg).unwrap()).unwrap();
        let mut m = InterpModel::new(ip).unwrap();
        // Age is bounded but history remains concrete. Do not explore this
        // still-infinite graph: composition needs a separate certificate.
        let (rule, _) = m.project_state().unwrap();
        assert_eq!(rule, "relative-age-projection");
        assert!(m.projection_certificate().unwrap().contains("GeneratedAge"));
    }

    #[test]
    #[ignore = "requires the local external pragmatic corpus; analysis only"]
    fn external_cleaner_age_dependent_filter_remains_uncertified() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../third_party/external/pragmatic/database-blob/storage-cleaner-improved/storagecleanerimproved.tla");
        let cfg = "SPECIFICATION Spec\nCONSTANTS SERVERS = {s1} CLEANERS = {c1}\n\
            METADATAS = {m1} USERIDS = {u1} IMAGES = {i1} UUIDS = {ui1}\nINVARIANTS TypeOk ConsistentReads\n";
        let ip = Interp::new(Program::load(&path, &[]).unwrap(), tlx_front::cfg::parse_cfg(cfg).unwrap()).unwrap();
        let mut model = InterpModel::new(ip).unwrap();
        // CleanerStartGetBlobKeys stores a set filtered by timestamp age.
        // That retained update is outside the current relative-age Test IR.
        let (rule, _) = model.project_state().expect("certified history fallback");
        assert_eq!(rule, "history-summary-projection");
        assert!(model.projection_certificate().unwrap().contains("GeneratedHistory"));
    }
}
