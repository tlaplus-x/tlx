//! Structural state projections: field liveness, sequence length and finite
//! history summaries. These reuse normalized branches and forward domains.
//!
//! The module root keeps the projection entry points and re-exports the
//! supporting items its children import from `super`: check specifications and
//! retained views (`spec`), `.cfg` constant substitutions (`const_subst`), Lean
//! certificate bodies and symmetry dispatch (`cert`), and disjunctive branch
//! splitting (`branch`).

mod age;
mod branch;
mod cert;
mod choose_sym;
mod const_subst;
mod domain;
mod equiv_sym;
mod erasure;
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
    binding, binding_with_index, branches, branches_positioned, branches_with_if, branches_with_if_positioned, max_local,
    mentions_phase_var, unchanged, variable, Branch, BranchBindings,
};
pub(in crate::optimize::phase) use cert::OpenCert;
pub(in crate::optimize::phase) use const_subst::{
    attach_const_subst_obligation, canonical_expr_repr, resolve_const_subst_chain, resolve_const_subst_name, resolve_const_subst_target,
    ConstSubstTarget,
};
pub(in crate::optimize::phase) use spec::{parse_retained_view, ObsBundle, OwnedCheckSpec};

use tlx_front::cfg::Config;

use crate::hir::{Expr, VarId};
use crate::Program;

use domain::{Domain, Domains};

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
    let mut best: Option<(FieldProjection, Option<OpenCert>)> = None;
    let mut consider = |candidate: Option<(FieldProjection, Option<OpenCert>)>| {
        if let Some((projection, cert)) = candidate {
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
    };
    for (i, d) in domains.vars.iter().enumerate() {
        let var = VarId(i as u32);
        match d {
            Domain::Record(fs) if fs.len() <= 32 => {
                for (control, values) in fs {
                    let Some(phases) = values.atoms() else { continue };
                    if phases.is_empty()
                        || phases.len() > 32
                        || !domain::compatible(phases)
                        || phases.iter().any(|p| domains.atom_expr(p, init.span).is_none())
                    {
                        continue;
                    }
                    consider(liveness::derive(
                        program,
                        &domains,
                        liveness::Control::RecordField { var, field: control.clone() },
                        phases,
                        None,
                        (&initial, &step_pos),
                        norm_spec,
                    ));
                }
            }
            Domain::Function(keys, range) if !keys.is_empty() && keys.len() <= 256 && domain::compatible(keys) => match &**range {
                Domain::Record(fs) if fs.len() <= 32 => {
                    for (control, values) in fs {
                        let Some(phases) = values.atoms() else { continue };
                        if phases.is_empty()
                            || phases.len() > 32
                            || !domain::compatible(phases)
                            || phases.iter().any(|p| domains.atom_expr(p, init.span).is_none())
                        {
                            continue;
                        }
                        consider(liveness::derive(
                            program,
                            &domains,
                            liveness::Control::RecordField { var, field: control.clone() },
                            phases,
                            Some(keys),
                            (&initial, &step_pos),
                            norm_spec,
                        ));
                    }
                }
                _ => {
                    let Some(phases) = range.atoms() else { continue };
                    if phases.len() < 2
                        || phases.len() > 32
                        || !domain::compatible(phases)
                        || phases.iter().any(|p| domains.atom_expr(p, init.span).is_none())
                    {
                        continue;
                    }
                    consider(liveness::derive(
                        program,
                        &domains,
                        liveness::Control::Var { var },
                        phases,
                        Some(keys),
                        (&initial, &step_pos),
                        norm_spec,
                    ));
                }
            },
            Domain::Atoms(phases)
                if (2..=32).contains(&phases.len())
                    && domain::compatible(phases)
                    && phases.iter().all(|p| domains.atom_expr(p, init.span).is_some()) =>
            {
                consider(liveness::derive(
                    program,
                    &domains,
                    liveness::Control::Var { var },
                    phases,
                    None,
                    (&initial, &step_pos),
                    norm_spec,
                ));
            }
            _ => {}
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
