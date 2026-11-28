//! Connected `FieldSymRule` certificate emitter composing phase-dependent field
//! masking (`FieldCertificate.lean`) with generic recursive equivariant symmetry
//! (`EquivSymCertificate.lean`, `OrbitQuotient.lean`) over one shared concrete
//! source model.
//!
//! Responsibilities are split across:
//! - this module: entry point, installed-`VIEW` candidate matching, and custom
//!   dead-field sentinel extraction;
//! - [`lower`]: HIR seed/step-case lowering, witness-bound read collection,
//!   state/action observation lowering, and liveness validation;
//! - [`output`]: standalone `GeneratedFieldSymmetry` Lean rendering.

mod lower;
mod output;

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use tlx_front::cfg::Config;

use crate::{hir::*, Program};

use super::super::{
    branches_positioned, branches_with_if_positioned,
    domain::{Atom, Domains},
    equiv_sym::{collect_const_bindings, validate_typed_groups},
    expr_alpha_eq, expr_alpha_eq_with_locals, has_str_group,
    sym_norm::{desugar_except_at, SymNormalizer},
    sym_totality, Branch, CheckSpec, SymGroup,
};
use super::{control_candidates, derive_analysis, Analysis, Control, Slot};

pub(super) struct Reads {
    pub(super) actor: Vec<bool>,
    pub(super) global: Vec<bool>,
}

impl Reads {
    pub(super) fn new(n: usize) -> Self {
        Self { actor: vec![false; n], global: vec![false; n] }
    }
}

pub(super) struct SeedData {
    pub(super) bounds: Vec<String>,
    pub(super) guard: String,
    pub(super) phase: usize,
    pub(super) values: Vec<String>,
}

pub(super) struct StepCase {
    pub(super) source: usize,
    pub(super) target: usize,
    pub(super) has_actor: bool,
    pub(super) reads: Reads,
    pub(super) writes: Vec<bool>,
    pub(super) bounds: Vec<String>,
    pub(super) guard: String,
    pub(super) values: Vec<String>,
}

/// Certify phase-dependent field masking followed by generic equivariant
/// symmetry for the exact installed `VIEW` expression. Fails closed (`None`)
/// whenever any step, sentinel, phase, key set, or observation falls outside
/// the certified composed IR. Declines `SymGroupKind::Str` groups.
pub(in crate::optimize::phase) fn symmetry_projection_certificate_with_typed_groups(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: CheckSpec<'_>,
    groups: &[SymGroup],
    installed_view: &Expr,
) -> Option<String> {
    if has_str_group(groups) {
        return None;
    }
    if !super::super::cfg_constants_supported(program, cfg) {
        return None;
    }
    let (groups, all_keys) = validate_typed_groups(groups)?;
    let const_bindings = collect_const_bindings(program, cfg)?;
    let mut norm = SymNormalizer::for_equiv_with_config(program, cfg);
    let init_norm = norm.normalize(init)?;
    let next_norm = norm.normalize(next)?;
    let owned_spec = spec.try_map(|e| norm.normalize(e))?;
    let norm_spec = owned_spec.as_spec();

    let const_info = sym_totality::collect_const_info(program, cfg);
    let totality = sym_totality::TotalityChecker::with_const_info(program, &groups, &all_keys, const_info, &init_norm, &next_norm, None);
    if !totality.check_all_with_spec(&init_norm, &next_norm, norm_spec, &[]) {
        return None;
    }

    let init_desugared = desugar_except_at(&init_norm)?;
    let next_desugared = desugar_except_at(&next_norm)?;
    let owned_spec = norm_spec.try_map(desugar_except_at)?;
    let norm_spec = owned_spec.as_spec();

    let init_pos = branches_with_if_positioned(&init_desugared).or_else(|| branches_positioned(&init_desugared))?;
    let step_pos = branches_with_if_positioned(&next_desugared).or_else(|| branches_positioned(&next_desugared))?;
    let initial: Vec<Branch> = init_pos.iter().map(|(b, _)| b.clone()).collect();
    let steps: Vec<Branch> = step_pos.iter().map(|(b, _)| b.clone()).collect();
    if initial.is_empty() || steps.is_empty() {
        return None;
    }
    let domains = Domains::infer(program, cfg, &initial, &steps)?;

    // Re-derive every candidate liveness analysis and pick the one whose `VIEW`
    // matches `installed_view` (allowing any equivariant key-free dead-field
    // sentinels actually installed in `installed_view`).
    let (matched, installed_sentinels) =
        find_matching_analysis(program, &domains, (&initial, &step_pos), norm_spec, &all_keys.model, installed_view, init.span)?;

    let cert = lower::emit_composed(
        program,
        &groups,
        &all_keys,
        &const_bindings,
        &totality,
        &matched,
        &installed_sentinels,
        &initial,
        &steps,
        norm_spec,
        init,
    )?;
    norm.attach_const_subst(cert)
}

fn find_matching_analysis<'a>(
    program: &Program,
    domains: &'a Domains,
    branches: (&[Branch], &[(Branch, Vec<usize>)]),
    spec: CheckSpec<'_>,
    all_keys: &BTreeSet<Arc<str>>,
    installed_view: &Expr,
    span: Span,
) -> Option<(Analysis<'a>, BTreeMap<Slot, Expr>)> {
    let (initial, _) = branches;
    let try_candidate =
        |control: Control, phases: &'a BTreeSet<Atom>, keys: Option<&'a BTreeSet<Atom>>| -> Option<(Analysis<'a>, BTreeMap<Slot, Expr>)> {
            let a = derive_analysis(domains, control, phases, keys, branches, spec)?;
            let proj = a.view(program, initial, Some(all_keys))?;
            if expr_alpha_eq(&proj.view, installed_view) {
                return Some((a, BTreeMap::new()));
            }
            let sentinels = match_view_with_custom_sentinels(program, &a, &proj.view, installed_view)?;
            Some((a, sentinels))
        };
    for (control, phases, keys) in control_candidates(domains, span) {
        if let Some(a) = try_candidate(control, phases, keys) {
            return Some(a);
        }
    }
    None
}

/// Verify that `installed` matches `expected` identically everywhere except
/// dead-field sentinel expressions, returning the exact per-slot sentinels
/// installed in `installed` so `ctx.lower_empty_var_expr` certifies them.
fn match_view_with_custom_sentinels(
    program: &Program,
    a: &Analysis<'_>,
    expected: &Expr,
    installed: &Expr,
) -> Option<BTreeMap<Slot, Expr>> {
    let (ExprKind::Tuple(exp_vars), ExprKind::Tuple(inst_vars)) = (&*expected.kind, &*installed.kind) else {
        return None;
    };
    if exp_vars.len() != program.vars.len() || inst_vars.len() != program.vars.len() {
        return None;
    }
    let mut sentinels = BTreeMap::new();
    match &a.control {
        Control::RecordField { var, .. } => {
            for (i, (ev, iv)) in exp_vars.iter().zip(inst_vars).enumerate() {
                if i != var.idx() {
                    if !expr_alpha_eq(ev, iv) {
                        return None;
                    }
                    continue;
                }
                let (e_exc, i_exc, locals) = unwrap_optional_keyed_fn(ev, iv, a.keys.is_some())?;
                let (ExprKind::Except { base: eb, updates: eu }, ExprKind::Except { base: ib, updates: iu }) = (&*e_exc.kind, &*i_exc.kind)
                else {
                    return None;
                };
                if !expr_alpha_eq_with_locals(eb, ib, &locals) || eu.len() != iu.len() {
                    return None;
                }
                for ((ep, eval), (ip, ival)) in eu.iter().zip(iu) {
                    let ([ExceptKey::Field(ef)], [ExceptKey::Field(ifld)]) = (ep.as_slice(), ip.as_slice()) else {
                        return None;
                    };
                    if ef != ifld {
                        return None;
                    }
                    let slot = Slot::RecordField(ef.clone());
                    let live = a.live.get(&slot)?;
                    let s = extract_masked_sentinel(eval, ival, live, a.phases, &locals)?;
                    sentinels.insert(slot, s);
                }
            }
        }
        Control::Var { .. } => {
            for (i, (ev, iv)) in exp_vars.iter().zip(inst_vars).enumerate() {
                let vid = VarId(i as u32);
                let slot = Slot::CompanionVar(vid);
                let Some(live) = a.live.get(&slot).filter(|ps| ps.len() < a.phases.len()) else {
                    if !expr_alpha_eq(ev, iv) {
                        return None;
                    }
                    continue;
                };
                if expr_alpha_eq(ev, iv) {
                    continue;
                }
                let (ebody, ibody, locals) = unwrap_optional_keyed_fn(ev, iv, a.keys.is_some())?;
                let s = extract_masked_sentinel(ebody, ibody, live, a.phases, &locals)?;
                sentinels.insert(slot, s);
            }
        }
    }
    Some(sentinels)
}

fn unwrap_optional_keyed_fn<'a>(ev: &'a Expr, iv: &'a Expr, keyed: bool) -> Option<(&'a Expr, &'a Expr, Vec<(LocalId, LocalId)>)> {
    if !keyed {
        return Some((ev, iv, Vec::new()));
    }
    let (ExprKind::FnConstruct { bounds: eb, body: ebody }, ExprKind::FnConstruct { bounds: ib, body: ibody }) = (&*ev.kind, &*iv.kind)
    else {
        return None;
    };
    let ([eb0], [ib0]) = (eb.as_slice(), ib.as_slice()) else { return None };
    if !expr_alpha_eq(&eb0.set, &ib0.set) {
        return None;
    }
    let (BoundVars::Many(el), BoundVars::Many(il)) = (&eb0.vars, &ib0.vars) else { return None };
    let ([e_id], [i_id]) = (el.as_slice(), il.as_slice()) else { return None };
    Some((ebody, ibody, vec![(*e_id, *i_id)]))
}

fn extract_masked_sentinel(
    expected: &Expr,
    installed: &Expr,
    live: &BTreeSet<Atom>,
    phases: &BTreeSet<Atom>,
    locals: &[(LocalId, LocalId)],
) -> Option<Expr> {
    if live.is_empty() {
        return Some(installed.clone());
    }
    let (ExprKind::If { cond: ec, then: et, els: ee }, ExprKind::If { cond: ic, then: it, els: ie }) = (&*expected.kind, &*installed.kind)
    else {
        return None;
    };
    if !expr_alpha_eq_with_locals(ec, ic, locals) {
        return None;
    }
    let dead_len = phases.len().saturating_sub(live.len());
    if live.len() <= dead_len {
        expr_alpha_eq_with_locals(et, it, locals).then(|| ie.clone())
    } else {
        expr_alpha_eq_with_locals(ee, ie, locals).then(|| it.clone())
    }
}
