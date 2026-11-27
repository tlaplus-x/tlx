//! Structural state projections: field liveness, sequence length and finite
//! history summaries. These reuse normalized branches and forward domains.
//!
//! The module root keeps the projection entry points and re-exports the
//! supporting items its children import from `super`: check specifications and
//! retained views (`spec`), `.cfg` substitutions and definition-override redirects (`const_subst`), Lean
//! certificate bodies and symmetry dispatch (`cert`), disjunctive branch
//! splitting (`branch`), and shared structural HIR walkers (`hir_util`).

mod age;
mod branch;
mod cert;
mod choose_sym;
mod const_subst;
mod domain;
mod equiv_sym;
mod erasure;
mod hir_util;
mod history;
mod keyed;
mod liveness;
mod normalize;
mod ordered;
mod sequence;
mod spec;
mod sym_groups;
pub(crate) mod sym_norm;
mod sym_totality;
mod threshold;

pub use age::{age_projection, age_projection_with_spec};
pub use cert::{
    symmetry_certificate, symmetry_certificate_with_spec, symmetry_projection_certificate, symmetry_projection_certificate_with_spec,
};
pub use choose_sym::{choose_symmetry_certificate, choose_symmetry_certificate_with_spec};
pub use equiv_sym::{
    symmetry_certificate as equiv_symmetry_certificate, symmetry_certificate_with_spec as equiv_symmetry_certificate_with_spec,
};
pub use erasure::{unobserved_projection, unobserved_projection_with_spec};
pub use history::{history_projection, history_projection_with_spec};
pub use ordered::{ordered_projection, ordered_projection_with_spec, OrderedHistory, OrderedPlan, OrderedShape};
pub use sequence::{sequence_length_projection, sequence_length_projection_with_spec};
pub use spec::{CheckSpec, FieldProjection, AUTOSYM_MAX_GROUPS, AUTOSYM_MAX_KEYS, AUTOSYM_MAX_ORDER};
pub use sym_norm::{infer_var_domains, proves_var_membership, SymNormalizer};
pub use sym_totality::cfg_constants_supported;

pub use threshold::{threshold_counter_projection, threshold_counter_projection_with_spec};

// Supporting items the `phase` submodules import from `super`.
pub(in crate::optimize::phase) use branch::{
    binding, binding_with_index, branches, branches_positioned, branches_with_if, branches_with_if_positioned, mentions_phase_var,
    unchanged, variable, Branch, BranchBindings,
};
pub(in crate::optimize::phase) use cert::OpenCert;
pub(in crate::optimize::phase) use const_subst::{
    attach_const_subst_obligation, canonical_expr_repr, cfg_def_redirects, resolve_const_subst_chain, resolve_const_subst_name,
    resolve_const_subst_target, resolve_override_name, syntactic_expr_repr, AppliedOverride, CfgRedirects, ConstSubstTarget,
    OverrideObligations,
};
pub(in crate::optimize::phase) use hir_util::{
    atom_nat, collect_unchanged_excluding, expr_alpha_eq, expr_alpha_eq_with_locals, expr_structurally_eq, max_local, mentions_local,
    mentions_var, mentions_var_where, mentions_vars, ordinary_unchanged,
};
pub(in crate::optimize::phase) use spec::{parse_retained_view, ObsBundle, OwnedCheckSpec};

use std::collections::BTreeSet;
use std::sync::Arc;

use tlx_front::cfg::Config;

use crate::hir::Expr;
use crate::Program;

use domain::Domains;

/// Derive one field projection. An unknown transfer, observation, effect or
/// exhausted analysis budget cannot authorize dropping information. The caller
/// supplies all observations, excludes overrides and liveness, and checks
/// equivariance before composing the result with symmetry.
pub fn phase_projection(program: &Program, cfg: &Config, init: &Expr, next: &Expr, observations: &[Expr]) -> Option<FieldProjection> {
    phase_projection_with_spec(program, cfg, init, next, CheckSpec::invariants_only(observations))
}

/// Derive one field projection covering invariants, state constraints, and init properties.
pub fn phase_projection_with_spec(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: CheckSpec<'_>,
) -> Option<FieldProjection> {
    phase_projection_with_spec_avoiding(program, cfg, init, next, spec, &BTreeSet::new())
}

/// Derive one field projection while avoiding any model value in `avoid_keys`
/// as a dead-field sentinel, so the resulting `VIEW` remains equivariant under
/// permutations moving `avoid_keys`.
pub fn phase_projection_with_spec_avoiding(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: CheckSpec<'_>,
    avoid_keys: &BTreeSet<Arc<str>>,
) -> Option<FieldProjection> {
    if !cfg_constants_supported(program, cfg) {
        return None;
    }
    let mut expand = normalize::Normalizer::with_config(program, cfg);
    let init_norm = expand.root(init)?;
    let next_norm = expand.root(next)?;
    let init_pos = branches_with_if_positioned(&init_norm).or_else(|| branches_positioned(&init_norm))?;
    let step_pos = branches_with_if_positioned(&next_norm).or_else(|| branches_positioned(&next_norm))?;
    let initial: Vec<Branch> = init_pos.iter().map(|(b, _)| b.clone()).collect();
    let steps: Vec<Branch> = step_pos.iter().map(|(b, _)| b.clone()).collect();
    let norm = spec.try_map(|e| expand.root(e))?;
    let norm_spec = norm.as_spec();
    let domains = Domains::infer(program, cfg, &initial, &steps)?;
    let avoid = (!avoid_keys.is_empty()).then_some(avoid_keys);
    let mut best: Option<(FieldProjection, Option<OpenCert>)> = None;
    for (control, phases, keys) in liveness::control_candidates(&domains, init.span) {
        if let Some((projection, cert)) =
            liveness::derive(program, &domains, control, phases, keys, (&initial, &step_pos), norm_spec, avoid)
        {
            // A Boolean flag can be a valid but unhelpful control field.
            // Prefer certified candidates, then more forgotten fields;
            // the proof is independent of this selection heuristic.
            if best
                .as_ref()
                .is_none_or(|(old, old_cert)| (cert.is_some(), projection.fields.len()) > (old_cert.is_some(), old.fields.len()))
            {
                best = Some((projection, cert));
            }
        }
    }
    let (mut p, cert) = best?;
    if spec.is_constrained() && !sym_totality::check_projection_observations_total(program, cfg, init, next, spec) {
        return None;
    }
    if let Some(c) = cert {
        p.certificate = Some(expand.attach_const_subst(c)?);
    }
    Some(p)
}
