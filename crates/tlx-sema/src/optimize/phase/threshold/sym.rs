//! Connected `ThresholdSymRule` certificate emitter composing in-place
//! threshold-counter saturation (`ThresholdCounterCertificate.lean`) with
//! generic recursive equivariant symmetry (`EquivSymCertificate.lean`,
//! `OrbitQuotient.lean`) over one shared concrete source model.
//!
//! Responsibilities are split across:
//! - this module: entry point, installed-`VIEW` verification, totality check,
//!   and flat counter-slot / template layout construction;
//! - [`lower`]: HIR init/step branch, guard, `SymTest`, `SymTransfer`, and
//!   state/action observation lowering;
//! - [`output`]: standalone `GeneratedThresholdSymmetry` Lean rendering.

mod lower;
mod output;

use std::collections::{BTreeMap, BTreeSet, HashMap};

use tlx_front::cfg::Config;

use crate::{hir::*, Program};

use super::super::{
    branches_with_if,
    domain::Atom,
    equiv_sym::{
        classify_key_set, collect_const_bindings, lower::LowerCtx, validate_typed_groups, AtomKey, GroupInfo, GroupMask, MovedKeys,
    },
    expr_alpha_eq, has_str_group,
    sym_norm::{desugar_except_at, SymNormalizer},
    sym_totality, CheckSpec, SymGroup,
};
use super::{analyze_counters, build_view, CounterKind, CounterSpec};

#[derive(Clone, Debug)]
pub(super) enum SlotInfo {
    Fixed { cap: i128, atom_id: usize, template: usize, desc: String },
    Sym { cap: i128, off: usize, group: usize, elem: usize, template: usize, desc: String },
}

#[derive(Clone, Debug)]
pub(super) enum SlotEntrySpec {
    FixedKey { slot: usize, atom_id: usize },
    SymGroup { off: usize, group: usize },
}

#[derive(Clone, Debug)]
pub(super) enum TemplateSpec {
    Scalar { var: VarId },
    MapFixed { var: VarId, key: Atom },
    MapSym { var: VarId },
}

pub(super) struct SlotLayout {
    pub(super) slots: Vec<SlotInfo>,
    pub(super) templates: Vec<TemplateSpec>,
    pub(super) scalar_slot: BTreeMap<VarId, usize>,
    pub(super) map_entries: BTreeMap<VarId, Vec<SlotEntrySpec>>,
}

pub(super) struct InitBranchData {
    pub(super) bounds: Vec<String>,
    pub(super) guard: String,
    pub(super) seeds: Vec<String>,
}

pub(super) struct StepBranchData {
    pub(super) bounds: Vec<String>,
    pub(super) guard: String,
    pub(super) transfers: Vec<String>,
}

fn build_slots_and_templates(
    program: &Program,
    counters: &[CounterSpec],
    groups: &[GroupInfo],
    all_keys: &MovedKeys,
    ctx: &mut LowerCtx<'_>,
) -> Option<SlotLayout> {
    let mut slots: Vec<SlotInfo> = Vec::new();
    let mut templates: Vec<TemplateSpec> = Vec::new();
    let mut scalar_slot: BTreeMap<VarId, usize> = BTreeMap::new();
    let mut map_entries: BTreeMap<VarId, Vec<SlotEntrySpec>> = BTreeMap::new();

    for c in counters {
        let var_name = &program.vars[c.var.idx()].name;
        match &c.kind {
            CounterKind::Scalar => {
                let t = templates.len();
                templates.push(TemplateSpec::Scalar { var: c.var });
                let k = slots.len();
                slots.push(SlotInfo::Fixed {
                    cap: c.cap,
                    atom_id: 0,
                    template: t,
                    desc: format!("slot {k}: scalar {var_name} (cap {})", c.cap),
                });
                scalar_slot.insert(c.var, k);
            }
            CounterKind::Map(keys) => {
                let (sym_groups, fixed_keys) = classify_key_set(keys, groups, all_keys)?;
                let mut entries = Vec::new();
                for fk in fixed_keys {
                    let ak = AtomKey::from_key_free_atom(&fk, all_keys)?;
                    let aid = ctx.atom_id_of(ak);
                    let t = templates.len();
                    templates.push(TemplateSpec::MapFixed { var: c.var, key: fk.clone() });
                    let k = slots.len();
                    slots.push(SlotInfo::Fixed {
                        cap: c.cap,
                        atom_id: aid,
                        template: t,
                        desc: format!("slot {k}: map {var_name}[{fk:?}] (cap {})", c.cap),
                    });
                    entries.push(SlotEntrySpec::FixedKey { slot: k, atom_id: aid });
                }
                if !sym_groups.is_empty() {
                    let t = templates.len();
                    templates.push(TemplateSpec::MapSym { var: c.var });
                    for gi in sym_groups {
                        ctx.mark_group_used(1u16 << gi);
                        let off = slots.len();
                        for (j, key_name) in groups[gi].keys.iter().enumerate() {
                            let k = slots.len();
                            slots.push(SlotInfo::Sym {
                                cap: c.cap,
                                off,
                                group: gi,
                                elem: j,
                                template: t,
                                desc: format!("slot {k}: sym map {var_name}[{key_name}] (group {gi}, elem {j}, cap {})", c.cap),
                            });
                        }
                        entries.push(SlotEntrySpec::SymGroup { off, group: gi });
                    }
                }
                if entries.is_empty() {
                    return None;
                }
                map_entries.insert(c.var, entries);
            }
        }
    }
    if slots.is_empty() || slots.len() > 256 || templates.is_empty() {
        return None;
    }
    Some(SlotLayout { slots, templates, scalar_slot, map_entries })
}

/// Certify in-place threshold-counter saturation followed by generic equivariant
/// symmetry for the exact installed `VIEW` expression. Fails closed (`None`)
/// whenever any counter cap, key set, transfer, test, or observation falls
/// outside the certified composed IR. Declines `SymGroupKind::Str` groups.
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

    let init_desugared = desugar_except_at(&init_norm)?;
    let next_desugared = desugar_except_at(&next_norm)?;
    let owned_spec_desugared = norm_spec.try_map(desugar_except_at)?;
    let norm_spec_desugared = owned_spec_desugared.as_spec();

    let initial = branches_with_if(&init_desugared)?;
    let steps = branches_with_if(&next_desugared)?;
    if initial.is_empty() || steps.is_empty() {
        return None;
    }

    let mut opaque_cache: HashMap<DefId, Option<BTreeSet<VarId>>> = HashMap::new();
    let (domains, counters) = analyze_counters(program, cfg, &initial, &steps, norm_spec_desugared, &mut opaque_cache)?;
    let expected_view = build_view(program, &counters, init.span);
    if !expr_alpha_eq(&expected_view, installed_view) {
        return None;
    }

    let counter_vars: BTreeSet<VarId> = counters.iter().map(|c| c.var).collect();
    let const_info = sym_totality::collect_const_info(program, cfg);
    let mut totality =
        sym_totality::TotalityChecker::with_const_info(program, &groups, &all_keys, const_info, &init_norm, &next_norm, None);
    totality.set_threshold_counters(counter_vars);
    if !totality.check_all_with_spec(&init_norm, &next_norm, norm_spec, &[]) {
        return None;
    }

    let counter_map: BTreeMap<VarId, CounterSpec> = counters.iter().map(|c| (c.var, c.clone())).collect();
    let core_vars: Vec<VarId> = (0..program.vars.len()).map(|i| VarId(i as u32)).filter(|v| !counter_map.contains_key(v)).collect();

    let mut ctx = LowerCtx::with_retained(program, &groups, &all_keys, &const_bindings, &totality, &core_vars);
    let layout = build_slots_and_templates(program, &counters, &groups, &all_keys, &mut ctx)?;

    let lowered = lower::lower_all(
        program,
        cfg,
        &domains,
        &groups,
        &all_keys,
        &counter_map,
        &layout,
        &initial,
        &steps,
        norm_spec_desugared,
        &mut ctx,
        &mut opaque_cache,
    )?;

    // Require every symmetric group in the product to be referenced by the spec.
    let full_mask: GroupMask = ((1u32 << groups.len()) - 1) as GroupMask;
    if ctx.used_groups != full_mask {
        return None;
    }

    let branch_count = lowered.init_branches.len().max(lowered.step_branches.len());
    let cert = output::render(&output::RenderSpec {
        groups: &groups,
        ctx: &ctx,
        orig_init: init,
        core_count: core_vars.len(),
        slots: &layout.slots,
        template_count: layout.templates.len(),
        branch_count,
        init_branches: &lowered.init_branches,
        step_branches: &lowered.step_branches,
        obs_test: &lowered.obs_test,
        init_obs_test: &lowered.init_obs_test,
        constraint_test: &lowered.constraint_test,
        action_constraint_form: &lowered.action_constraint_form,
        action_obs_form: &lowered.action_obs_form,
        constrained: norm_spec_desugared.is_constrained(),
    });
    norm.attach_const_subst(cert)
}
