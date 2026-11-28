//! Lean certificate bodies: the shared constrained-theorem boilerplate opened by
//! every emitter and the automatic-symmetry dispatch across the specialized IRs.

use tlx_front::cfg::Config;

use crate::hir::Expr;
use crate::Program;

use super::spec::{model_groups, CheckSpec, SymGroup};
use super::{choose_sym, equiv_sym, keyed, liveness, threshold};

/// An emitted Lean certificate body whose `TlxOptimization.<namespace>` section
/// remains open until optional constrained and constant-substitution obligations
/// are appended and the namespace is closed once.
#[derive(Clone)]
pub(in crate::optimize::phase) struct OpenCert {
    pub(in crate::optimize::phase) body: String,
    pub(in crate::optimize::phase) namespace: &'static str,
    pub(in crate::optimize::phase) constrained: bool,
}

impl OpenCert {
    pub(in crate::optimize::phase) fn new(
        mut body: String,
        tail: &str,
        namespace: &'static str,
        constrained: bool,
        include_erasure_cert: bool,
        is_choose: bool,
    ) -> Self {
        body.push_str(tail);
        if !body.is_empty() && !body.ends_with('\n') {
            body.push('\n');
        }
        if constrained {
            push_constrained_theorems(&mut body, include_erasure_cert, is_choose);
        }
        Self { body, namespace, constrained }
    }

    pub(in crate::optimize::phase) fn new_composed(
        mut body: String,
        tail: &str,
        namespace: &'static str,
        constrained: bool,
        stage_prefix: &'static str,
        stage_project: &'static str,
    ) -> Self {
        body.push_str(tail);
        if !body.is_empty() && !body.ends_with('\n') {
            body.push('\n');
        }
        if constrained {
            push_composed_constrained_theorems(&mut body, stage_prefix, stage_project);
        }
        Self { body, namespace, constrained }
    }
}

fn push_composed_constrained_theorems(out: &mut String, stage_prefix: &str, stage_project: &str) {
    out.push_str(&format!(
        "def constrainedBefore := (model sem).constrainedConcrete\n\
         def constrainedIntermediate := (model sem).constrainedIntermediate\n\
         def constrainedAfter := (model sem).constrainedReduced\n\
         theorem {stage_prefix}_constrained_certificate :\n\
         \x20 ConstrainedCertificate (constrainedBefore sem) (constrainedIntermediate sem) ({stage_project} sem) :=\n\
         \x20 (model sem).{stage_prefix}_constrained_certificate\n\
         theorem symmetry_constrained_certificate :\n\
         \x20 ConstrainedCertificate (constrainedIntermediate sem) (constrainedAfter sem) (symProject sem) :=\n\
         \x20 (model sem).symmetry_constrained_certificate\n\
         theorem constrained_certificate :\n\
         \x20 ConstrainedCertificate (constrainedBefore sem) (constrainedAfter sem) (project sem) :=\n\
         \x20 (model sem).constrained_certificate\n\
         theorem constrained_optimization_correct :\n\
         \x20 ConstrainedSafe (constrainedBefore sem) ↔ ConstrainedSafe (constrainedAfter sem) :=\n\
         \x20 TlxOptimization.constrained_safety_iff (constrained_certificate sem)\n\
         theorem constrained_init_counterexample_lifts {{a}}\n\
         \x20 (ha : (constrainedAfter sem).initial a)\n\
         \x20 (bad : ¬ ((constrainedAfter sem).safe a ∧ (constrainedAfter sem).initSafe a)) :\n\
         \x20 ∃ s, (constrainedBefore sem).initial s ∧ project sem s = a ∧\n\
         \x20   ¬ ((constrainedBefore sem).safe s ∧ (constrainedBefore sem).initSafe s) :=\n\
         \x20 TlxOptimization.constrained_init_counterexample_lifts (constrained_certificate sem) ha bad\n\
         theorem constrained_step_counterexample_lifts {{a b}}\n\
         \x20 (ha : AdmittedReachable (constrainedAfter sem) a)\n\
         \x20 (hab : (constrainedAfter sem).next a b)\n\
         \x20 (bad : ¬ ((constrainedAfter sem).safe b ∧ (constrainedAfter sem).actionSafe a b)) :\n\
         \x20 ∃ s t, AdmittedReachable (constrainedBefore sem) s ∧ (constrainedBefore sem).next s t ∧\n\
         \x20   project sem s = a ∧ project sem t = b ∧\n\
         \x20   ¬ ((constrainedBefore sem).safe t ∧ (constrainedBefore sem).actionSafe s t) :=\n\
         \x20 TlxOptimization.constrained_step_counterexample_lifts (constrained_certificate sem) ha hab bad\n\
         theorem admitted_deadlock_preserved :\n\
         \x20 (∃ s, AdmittedReachable (constrainedBefore sem) s ∧ ¬ ∃ t, (constrainedBefore sem).next s t) ↔\n\
         \x20 (∃ a, AdmittedReachable (constrainedAfter sem) a ∧ ¬ ∃ b, (constrainedAfter sem).next a b) :=\n\
         \x20 TlxOptimization.constrained_deadlock_iff (constrained_certificate sem)\n\
         #print axioms {stage_prefix}_constrained_certificate\n\
         #print axioms symmetry_constrained_certificate\n\
         #print axioms constrained_certificate\n\
         #print axioms constrained_optimization_correct\n\
         #print axioms constrained_init_counterexample_lifts\n\
         #print axioms constrained_step_counterexample_lifts\n\
         #print axioms admitted_deadlock_preserved\n"
    ));
}

fn push_constrained_theorems(out: &mut String, include_erasure_cert: bool, is_choose: bool) {
    if is_choose {
        out.push_str(
            "def rawConstrainedBefore := (model sem).rawConstrained\n\
             def constrainedBefore := (model sem).validConstrained\n\
             def constrainedAfter := (model sem).constrainedReduced\n\
             theorem constrained_certificate :\n\
             \x20 ConstrainedCertificate (constrainedBefore sem) (constrainedAfter sem) (project sem) :=\n\
             \x20 (model sem).constrained_certificate\n\
             theorem constrained_optimization_correct :\n\
             \x20 ConstrainedSafe (rawConstrainedBefore sem) ↔ ConstrainedSafe (constrainedAfter sem) :=\n\
             \x20 (model sem).constrained_optimization_correct\n\
             theorem constrained_init_counterexample_lifts {a}\n\
             \x20 (ha : (constrainedAfter sem).initial a)\n\
             \x20 (bad : ¬ ((constrainedAfter sem).safe a ∧ (constrainedAfter sem).initSafe a)) :\n\
             \x20 ∃ s : (model sem).ValidState, (rawConstrainedBefore sem).initial s.val ∧ project sem s = a ∧\n\
             \x20   ¬ ((rawConstrainedBefore sem).safe s.val ∧ (rawConstrainedBefore sem).initSafe s.val) :=\n\
             \x20 (model sem).constrained_init_counterexample_lifts ha bad\n\
             theorem constrained_step_counterexample_lifts {a b}\n\
             \x20 (ha : AdmittedReachable (constrainedAfter sem) a)\n\
             \x20 (hab : (constrainedAfter sem).next a b)\n\
             \x20 (bad : ¬ ((constrainedAfter sem).safe b ∧ (constrainedAfter sem).actionSafe a b)) :\n\
             \x20 ∃ s t : (model sem).ValidState, AdmittedReachable (rawConstrainedBefore sem) s.val ∧ (rawConstrainedBefore sem).next s.val t.val ∧\n\
             \x20   project sem s = a ∧ project sem t = b ∧\n\
             \x20   ¬ ((rawConstrainedBefore sem).safe t.val ∧ (rawConstrainedBefore sem).actionSafe s.val t.val) :=\n\
             \x20 (model sem).constrained_step_counterexample_lifts ha hab bad\n\
             theorem admitted_deadlock_preserved :\n\
             \x20 (∃ s : (model sem).RState, AdmittedReachable (rawConstrainedBefore sem) s ∧ ¬ ∃ t : (model sem).RState, (rawConstrainedBefore sem).next s t) ↔\n\
             \x20 (∃ a, AdmittedReachable (constrainedAfter sem) a ∧ ¬ ∃ b, (constrainedAfter sem).next a b) :=\n\
             \x20 (model sem).admitted_deadlock_preserved\n\
             #print axioms constrained_certificate\n\
             #print axioms constrained_optimization_correct\n\
             #print axioms constrained_init_counterexample_lifts\n\
             #print axioms constrained_step_counterexample_lifts\n\
             #print axioms admitted_deadlock_preserved\n",
        );
    } else {
        out.push_str(
            "def constrainedBefore := (model sem).constrainedConcrete\n\
             def constrainedAfter := (model sem).constrainedReduced\n",
        );
        if include_erasure_cert {
            out.push_str(
                "def constrainedIntermediate := (model sem).erased.constrainedConcrete\n\
                 theorem erasure_constrained_certificate :\n\
                 \x20 ConstrainedCertificate (constrainedBefore sem) (constrainedIntermediate sem) (erase sem) :=\n\
                 \x20 (model sem).erasure_constrained_certificate\n",
            );
        }
        out.push_str(
            "theorem constrained_certificate :\n\
             \x20 ConstrainedCertificate (constrainedBefore sem) (constrainedAfter sem) (project sem) :=\n\
             \x20 (model sem).constrained_certificate\n\
             theorem constrained_optimization_correct :\n\
             \x20 ConstrainedSafe (constrainedBefore sem) ↔ ConstrainedSafe (constrainedAfter sem) :=\n\
             \x20 TlxOptimization.constrained_safety_iff (constrained_certificate sem)\n\
             theorem constrained_init_counterexample_lifts {a}\n\
             \x20 (ha : (constrainedAfter sem).initial a)\n\
             \x20 (bad : ¬ ((constrainedAfter sem).safe a ∧ (constrainedAfter sem).initSafe a)) :\n\
             \x20 ∃ s, (constrainedBefore sem).initial s ∧ project sem s = a ∧\n\
             \x20   ¬ ((constrainedBefore sem).safe s ∧ (constrainedBefore sem).initSafe s) :=\n\
             \x20 TlxOptimization.constrained_init_counterexample_lifts (constrained_certificate sem) ha bad\n\
             theorem constrained_step_counterexample_lifts {a b}\n\
             \x20 (ha : AdmittedReachable (constrainedAfter sem) a)\n\
             \x20 (hab : (constrainedAfter sem).next a b)\n\
             \x20 (bad : ¬ ((constrainedAfter sem).safe b ∧ (constrainedAfter sem).actionSafe a b)) :\n\
             \x20 ∃ s t, AdmittedReachable (constrainedBefore sem) s ∧ (constrainedBefore sem).next s t ∧\n\
             \x20   project sem s = a ∧ project sem t = b ∧\n\
             \x20   ¬ ((constrainedBefore sem).safe t ∧ (constrainedBefore sem).actionSafe s t) :=\n\
             \x20 TlxOptimization.constrained_step_counterexample_lifts (constrained_certificate sem) ha hab bad\n\
             theorem admitted_deadlock_preserved :\n\
             \x20 (∃ s, AdmittedReachable (constrainedBefore sem) s ∧ ¬ ∃ t, (constrainedBefore sem).next s t) ↔\n\
             \x20 (∃ a, AdmittedReachable (constrainedAfter sem) a ∧ ¬ ∃ b, (constrainedAfter sem).next a b) :=\n\
             \x20 TlxOptimization.constrained_deadlock_iff (constrained_certificate sem)\n",
        );
        if include_erasure_cert {
            out.push_str("#print axioms erasure_constrained_certificate\n");
        }
        out.push_str(
            "#print axioms constrained_certificate\n\
             #print axioms constrained_optimization_correct\n\
             #print axioms constrained_init_counterexample_lifts\n\
             #print axioms constrained_step_counterexample_lifts\n\
             #print axioms admitted_deadlock_preserved\n",
        );
    }
}

/// Generate a connected Lean symmetry certificate for a disjoint product of full
/// permutation groups. Prefers the specialized keyed-state IR, then falls back
/// to the generic recursive equivariant value & expression IR, and finally to
/// certified choice-irrelevant symmetry when `CHOOSE` expressions are present.
pub fn symmetry_certificate(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    observations: &[Expr],
    groups: &[Vec<String>],
) -> Option<String> {
    symmetry_certificate_with_spec(program, cfg, init, next, CheckSpec::invariants_only(observations), groups)
}

/// Generate a connected Lean symmetry certificate covering invariants, init properties,
/// constraints, action constraints, and action properties for `ModelValue` groups.
pub fn symmetry_certificate_with_spec(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: CheckSpec<'_>,
    groups: &[Vec<String>],
) -> Option<String> {
    let typed = model_groups(groups);
    symmetry_certificate_with_typed_groups(program, cfg, init, next, spec, &typed)
}

/// Generate a connected Lean symmetry certificate covering invariants, init properties,
/// constraints, action constraints, and action properties for typed `Model` / `Str` groups.
/// Non-`EquivSym` emitters decline `SymGroupKind::Str` groups.
pub fn symmetry_certificate_with_typed_groups(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: CheckSpec<'_>,
    groups: &[SymGroup],
) -> Option<String> {
    keyed::symmetry_certificate_with_typed_groups(program, cfg, init, next, spec, groups)
        .or_else(|| equiv_sym::symmetry_certificate_with_typed_groups(program, cfg, init, next, spec, groups))
        .or_else(|| choose_sym::choose_symmetry_certificate_with_typed_groups(program, cfg, init, next, spec, groups))
}

/// Certify unobserved-variable erasure followed by symmetry for the exact
/// installed retained-variable tuple, preferring `ErasedKeyedCertificate` and
/// falling back to `ErasedEquivCertificate`.
pub fn symmetry_projection_certificate(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    observations: &[Expr],
    groups: &[Vec<String>],
    view: &Expr,
) -> Option<String> {
    symmetry_projection_certificate_with_spec(program, cfg, init, next, CheckSpec::invariants_only(observations), groups, view)
}

/// Certify a structural projection followed by symmetry covering invariants,
/// init properties, constraints, action constraints, and action properties:
/// unobserved-variable erasure (`ErasedKeyedCertificate` / `ErasedEquivCertificate`),
/// phase-dependent field masking (`FieldSymCertificate`), or in-place
/// threshold-counter saturation (`ThresholdSymCertificate`).
pub fn symmetry_projection_certificate_with_spec(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: CheckSpec<'_>,
    groups: &[Vec<String>],
    view: &Expr,
) -> Option<String> {
    let typed = model_groups(groups);
    symmetry_projection_certificate_with_typed_groups(program, cfg, init, next, spec, &typed, view)
}

/// Typed-group counterpart of [`symmetry_projection_certificate_with_spec`].
/// Currently all composed projection+symmetry emitters decline `SymGroupKind::Str` groups.
pub fn symmetry_projection_certificate_with_typed_groups(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: CheckSpec<'_>,
    groups: &[SymGroup],
    view: &Expr,
) -> Option<String> {
    keyed::symmetry_projection_certificate_with_typed_groups(program, cfg, init, next, spec, groups, view)
        .or_else(|| equiv_sym::symmetry_projection_certificate_with_typed_groups(program, cfg, init, next, spec, groups, view))
        .or_else(|| liveness::sym::symmetry_projection_certificate_with_typed_groups(program, cfg, init, next, spec, groups, view))
        .or_else(|| threshold::sym::symmetry_projection_certificate_with_typed_groups(program, cfg, init, next, spec, groups, view))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::{ExprKind, OpRef, RootSymbol};
    use tlx_front::cfg::parse_cfg;

    #[test]
    fn non_equiv_sym_emitters_explicitly_decline_str_groups() {
        let spec = r#"---- MODULE StrDecline ----
CONSTANTS K
VARIABLES x, dead
Init == x \in K /\ dead = 0
Next == x' \in K /\ dead' = dead
Inv == x \in K
View == <<x>>
====
"#;
        let cfg = parse_cfg("CONSTANTS K = {\"k1\", \"k2\"}\nINIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap();
        let dir = tlx_testkit::TempDir::new("str-decline");
        let path = dir.write("StrDecline.tla", spec);
        let mut p = Program::load(&path, &[]).unwrap();
        p.resolve_all_root();
        let mut resolve = |name: &str| {
            let Some(RootSymbol::Def(id)) = p.lookup_root(name) else { panic!("missing {name}") };
            Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
        };
        let init = resolve("Init");
        let next = resolve("Next");
        let inv = [resolve("Inv")];
        let view = resolve("View");
        let check = CheckSpec::invariants_only(&inv);
        let str_groups = [SymGroup::str(vec!["k1".into(), "k2".into()])];

        assert!(keyed::symmetry_certificate_with_typed_groups(&p, &cfg, &init, &next, check, &str_groups).is_none());
        assert!(keyed::symmetry_projection_certificate_with_typed_groups(&p, &cfg, &init, &next, check, &str_groups, &view).is_none());
        assert!(choose_sym::choose_symmetry_certificate_with_typed_groups(&p, &cfg, &init, &next, check, &str_groups).is_none());
        assert!(equiv_sym::symmetry_projection_certificate_with_typed_groups(&p, &cfg, &init, &next, check, &str_groups, &view).is_none());
        assert!(
            liveness::sym::symmetry_projection_certificate_with_typed_groups(&p, &cfg, &init, &next, check, &str_groups, &view).is_none()
        );
        assert!(
            threshold::sym::symmetry_projection_certificate_with_typed_groups(&p, &cfg, &init, &next, check, &str_groups, &view).is_none()
        );
        // Meanwhile, EquivSym DOES certify the exact same Str group directly and via top-level dispatch.
        assert!(equiv_sym::symmetry_certificate_with_typed_groups(&p, &cfg, &init, &next, check, &str_groups).is_some());
        let dispatched = symmetry_certificate_with_typed_groups(&p, &cfg, &init, &next, check, &str_groups)
            .expect("top-level typed dispatch should route Str groups to EquivSym");
        assert!(dispatched.contains("namespace TlxOptimization.GeneratedEquivSymmetry"));
    }
}
