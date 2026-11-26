//! Connected `FieldSymRule` certificate emitter composing phase-dependent field
//! masking (`FieldCertificate.lean`) with generic recursive equivariant symmetry
//! (`EquivSymCertificate.lean`) over one shared concrete source model.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write;
use std::sync::Arc;

use tlx_front::cfg::Config;

use crate::{builtins::Builtin as B, hir::*, optimize::lean::literal, visit, Program};

use super::super::{
    binding, branches_positioned, branches_with_if_positioned,
    domain::{Atom, Domains},
    equiv_sym::{collect_const_bindings, lower::LowerCtx, output::write_common_header, validate_groups, AtomKey, GroupInfo, GroupMask},
    sym_norm::{desugar_except_at, SymNormalizer},
    sym_totality, variable, Branch, CheckSpec, OpenCert,
};
use super::{control_candidates, derive_analysis, mentions_local, ActionRead, Analysis, Control, ObsContext, ObsSink, Slot};

const MAX_CASES: usize = 128;

/// Certify phase-dependent field masking followed by generic equivariant
/// symmetry for the exact installed `VIEW` expression. Fails closed (`None`)
/// whenever any step, sentinel, phase, key set, or observation falls outside
/// the certified composed IR.
pub(in crate::optimize::phase) fn symmetry_projection_certificate_with_spec(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: CheckSpec<'_>,
    groups: &[Vec<String>],
    installed_view: &Expr,
) -> Option<String> {
    if !super::super::cfg_constants_supported(program, cfg) {
        return None;
    }
    let (groups, all_keys) = validate_groups(groups)?;
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
        find_matching_analysis(program, &domains, (&initial, &step_pos), norm_spec, &all_keys, installed_view, init.span)?;

    let cert = emit_composed(
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

struct Reads {
    actor: Vec<bool>,
    global: Vec<bool>,
}

impl Reads {
    fn new(n: usize) -> Self {
        Self { actor: vec![false; n], global: vec![false; n] }
    }
}

struct SeedData {
    bounds: Vec<String>,
    guard: String,
    phase: usize,
    values: Vec<String>,
}

struct StepCase {
    source: usize,
    target: usize,
    has_actor: bool,
    reads: Reads,
    writes: Vec<bool>,
    bounds: Vec<String>,
    guard: String,
    values: Vec<String>,
}

#[allow(clippy::too_many_arguments)]
fn emit_composed(
    program: &Program,
    groups: &[GroupInfo],
    all_keys: &BTreeSet<Arc<str>>,
    const_bindings: &BTreeMap<ConstId, &tlx_front::cfg::CfgValue>,
    totality: &sym_totality::TotalityChecker<'_>,
    a: &Analysis<'_>,
    installed_sentinels: &BTreeMap<Slot, Expr>,
    initial: &[Branch],
    steps: &[Branch],
    spec: CheckSpec<'_>,
    orig_init: &Expr,
) -> Option<OpenCert> {
    let fields: Vec<Slot> = a.data_slots();
    let phases: Vec<Atom> = a.phases.iter().cloned().collect();
    if fields.is_empty() || phases.is_empty() || a.keys.is_some_and(|ks| ks.len() > 256) {
        return None;
    }

    let mut ctx = LowerCtx::new(program, groups, all_keys, const_bindings, totality);

    // Phases must be key-free atoms so `phaseVal` is invariant under `GroupPerm`.
    let mut phase_atom_ids = Vec::with_capacity(phases.len());
    for p in &phases {
        let ak = atom_to_key_free(p, all_keys)?;
        phase_atom_ids.push(ctx.atom_id_of(ak));
    }

    // Classify the control/map key set into `(fixed_atom_ids, key_mask)`.
    let (is_keyed, fixed_atom_ids, key_mask, default_key_lean) = match a.keys {
        None => {
            let dummy_id = ctx.atom_id_of(AtomKey::Bool(false));
            (false, vec![dummy_id], 0u16, "Sum.inl ⟨0, by decide⟩".to_string())
        }
        Some(ks) => {
            let mut mask: GroupMask = 0;
            let mut covered_keys: BTreeSet<Arc<str>> = BTreeSet::new();
            for (gi, g) in groups.iter().enumerate() {
                let present = g.keys.iter().filter(|k| ks.contains(&Atom::Model((*k).clone()))).count();
                if present == g.keys.len() {
                    mask |= 1u16 << gi;
                    covered_keys.extend(g.keys.iter().cloned());
                } else if present != 0 {
                    // Key domain partially overlaps a symmetric group — cannot compose.
                    return None;
                }
            }
            let mut fixed_ids = Vec::new();
            for k in ks {
                if let Atom::Model(m) = k {
                    if covered_keys.contains(m) {
                        continue;
                    }
                    if all_keys.contains(m) {
                        return None;
                    }
                }
                let ak = atom_to_key_free(k, all_keys)?;
                fixed_ids.push(ctx.atom_id_of(ak));
            }
            if mask != 0 {
                ctx.mark_group_used(mask);
            }
            let default_key = if !fixed_ids.is_empty() {
                "Sum.inl ⟨0, by decide⟩".to_string()
            } else {
                let first_g = (0..groups.len()).find(|gi| (mask & (1u16 << gi)) != 0)?;
                format!("Sum.inr ⟨⟨⟨{first_g}, by decide⟩, ⟨0, by decide⟩⟩, by decide⟩")
            };
            (true, fixed_ids, mask, default_key)
        }
    };

    // Lower sentinel expressions as closed key-free `Expr d Empty`.
    let fallback_atom_id = ctx.atom_id_of(AtomKey::Bool(false));
    let fallback_expr = format!("(Expr.atom {fallback_atom_id})");
    let mut sentinel_exprs = Vec::with_capacity(fields.len());
    for slot in &fields {
        let is_dead_somewhere = a.live.get(slot).is_some_and(|ps| ps.len() < phases.len());
        let sentinel = match installed_sentinels.get(slot) {
            Some(s) => s.clone(),
            None => a.sentinel_for_slot(slot, initial, Some(all_keys), orig_init.span)?,
        };
        match ctx.lower_empty_var_expr(&sentinel) {
            Some(expr) => sentinel_exprs.push(expr),
            None if !is_dead_somewhere => sentinel_exprs.push(fallback_expr.clone()),
            None => return None,
        }
    }

    // Lower Init seeds.
    let mut seeds = Vec::with_capacity(initial.len());
    for b in initial {
        seeds.push(lower_seed(&mut ctx, a, &fields, &phases, b)?);
    }

    // Lower Next step cases.
    let mut cases = Vec::new();
    for b in steps {
        cases.extend(lower_step_cases(&mut ctx, a, &fields, &phases, b, &fallback_expr)?);
        if cases.len() > MAX_CASES {
            return None;
        }
    }
    if seeds.is_empty() || cases.is_empty() {
        return None;
    }

    // Lower observations, init props, constraints, and action checks while
    // populating the `observed` matrix through the shared `Analysis` walkers.
    let mut observed = vec![vec![false; fields.len()]; phases.len()];
    let root_ctx = ObsContext::all(a.phases, a.keys.is_some());
    let obs_form = lower_state_preds(&mut ctx, a, &fields, &phases, spec.invariants, &root_ctx, &mut observed)?;
    let init_obs_form = lower_state_preds(&mut ctx, a, &fields, &phases, spec.init_props, &root_ctx, &mut observed)?;
    let constraint_form = lower_state_preds(&mut ctx, a, &fields, &phases, spec.constraints, &root_ctx, &mut observed)?;
    let action_constraint_form = lower_action_preds(&mut ctx, a, &fields, spec.action_constraints, &mut observed)?;
    let action_obs_form = lower_action_preds(&mut ctx, a, &fields, spec.action_props, &mut observed)?;

    // Validate all four FieldRule liveness conditions before rendering Lean.
    validate_liveness(a, &fields, &phases, &cases, &observed)?;

    // Require every symmetric group in the product to be referenced by the spec.
    let full_mask: GroupMask = ((1u32 << groups.len()) - 1) as GroupMask;
    if ctx.used_groups != full_mask {
        return None;
    }

    // Map `VarRole` for every program variable.
    let mut core_count = 0usize;
    let mut var_roles = Vec::with_capacity(program.vars.len());
    let ctrl_field_atom = match &a.control {
        Control::RecordField { field, .. } => Some(ctx.atom_id_of(AtomKey::Str(field.clone()))),
        Control::Var { .. } => None,
    };
    let rec_field_atoms: Vec<usize> = fields
        .iter()
        .map(|s| match s {
            Slot::RecordField(f) => ctx.atom_id_of(AtomKey::Str(f.clone())),
            Slot::CompanionVar(_) => 0,
        })
        .collect();
    for i in 0..program.vars.len() {
        let vid = VarId(i as u32);
        let role = match &a.control {
            Control::RecordField { var, .. } if *var == vid => {
                let cfa = ctrl_field_atom.unwrap();
                format!("VarRole.recordMap {is_keyed} {cfa} recordFieldAtom")
            }
            Control::Var { var } if *var == vid => format!("VarRole.controlVar {is_keyed}"),
            Control::Var { .. } if a.is_projected_var(vid) => {
                let fi = fields.iter().position(|s| matches!(s, Slot::CompanionVar(v) if *v == vid))?;
                format!("VarRole.companionVar {is_keyed} ⟨{fi}, by decide⟩")
            }
            _ => {
                let ci = core_count;
                core_count += 1;
                format!("VarRole.core ⟨{ci}, by decide⟩")
            }
        };
        var_roles.push(role);
    }

    let branch_count = seeds.len().max(cases.len());
    Some(render(
        program,
        groups,
        &ctx,
        orig_init,
        a,
        &fields,
        &phases,
        &phase_atom_ids,
        &fixed_atom_ids,
        key_mask,
        &default_key_lean,
        is_keyed,
        core_count,
        &var_roles,
        &rec_field_atoms,
        &sentinel_exprs,
        branch_count,
        &seeds,
        &cases,
        &observed,
        &obs_form,
        &init_obs_form,
        &constraint_form,
        &action_constraint_form,
        &action_obs_form,
        &fallback_expr,
        spec.is_constrained(),
    ))
}

fn atom_to_key_free(a: &Atom, all_keys: &BTreeSet<Arc<str>>) -> Option<AtomKey> {
    match a {
        Atom::Num(n) => Some(AtomKey::Int(*n)),
        Atom::Bool(b) => Some(AtomKey::Bool(*b)),
        Atom::Str(s) => Some(AtomKey::Str(s.clone())),
        Atom::Model(m) => (!all_keys.contains(m)).then(|| AtomKey::Model(m.clone())),
    }
}

fn clean_bounds(
    a: &Analysis<'_>,
    fields: &[Slot],
    bounds: &[Bound],
    allow_managed: bool,
    actor: Option<LocalId>,
    reads: &mut Reads,
) -> Option<Vec<Bound>> {
    let mut cleaned = Vec::with_capacity(bounds.len());
    for bd in bounds {
        let BoundVars::Many(ids) = &bd.vars else { return None };
        let only_actor = actor.is_some() && ids.iter().all(|id| Some(*id) == actor);
        let set = if only_actor { bd.set.clone() } else { clean_expr(a, fields, &bd.set, allow_managed, actor, reads)? };
        cleaned.push(Bound { vars: bd.vars.clone(), set });
    }
    Some(cleaned)
}

fn lower_seed(ctx: &mut LowerCtx<'_>, a: &Analysis<'_>, fields: &[Slot], phases: &[Atom], b: &Branch) -> Option<SeedData> {
    let mut reads = Reads::new(fields.len());
    let cleaned_bounds = clean_bounds(a, fields, &b.bounds, false, None, &mut reads)?;
    let (bounds, pushed) = ctx.lower_witness_bounds(&cleaned_bounds, false, None)?;
    let res = (|| {
        let (phase, values) = match &a.control {
            Control::RecordField { var, field: ctrl_field } => {
                let rhs = binding(b, *var, false)?;
                let (record, key_bound) = if let Some(keys) = a.keys {
                    let ExprKind::FnConstruct { bounds, body } = &*rhs.kind else { return None };
                    let [bound] = bounds.as_slice() else { return None };
                    let BoundVars::Many(ids) = &bound.vars else { return None };
                    let [id] = ids.as_slice() else { return None };
                    if a.domains.exact_set(&bound.set).as_ref() != Some(keys) {
                        return None;
                    }
                    (body, Some((*id, &bound.set)))
                } else {
                    (&rhs, None)
                };
                let ExprKind::Record(fs) = &*record.kind else { return None };
                if fs.len() != fields.len() + 1 {
                    return None;
                }
                let phase = a.domains.atom_value(&fs.iter().find(|(f, _)| f == ctrl_field)?.1)?;
                let phase = phases.iter().position(|p| *p == phase)?;
                let mut values = Vec::with_capacity(fields.len());
                for slot in fields {
                    let Slot::RecordField(field) = slot else { return None };
                    let val = &fs.iter().find(|(f, _)| f == field)?.1;
                    if a.mentions_any_managed(val) {
                        return None;
                    }
                    if let Some((kid, kset)) = key_bound {
                        ctx.push_bound_local(kid, Some(kset));
                    } else {
                        ctx.push_temp_local();
                    }
                    let lowered = ctx.lower_expr(val, false);
                    if let Some((kid, _)) = key_bound {
                        ctx.pop_bound_local(kid);
                    } else {
                        ctx.pop_temp_local();
                    }
                    values.push(lowered?);
                }
                (phase, values)
            }
            Control::Var { var: ctrl } => {
                let ctrl_rhs = binding(b, *ctrl, false)?;
                let phase_expr = if let Some(keys) = a.keys {
                    let ExprKind::FnConstruct { bounds, body } = &*ctrl_rhs.kind else { return None };
                    let [bound] = bounds.as_slice() else { return None };
                    let BoundVars::Many(ids) = &bound.vars else { return None };
                    let [id] = ids.as_slice() else { return None };
                    if a.domains.exact_set(&bound.set).as_ref() != Some(keys) || mentions_local(body, *id) {
                        return None;
                    }
                    body
                } else {
                    &ctrl_rhs
                };
                let phase = a.domains.atom_value(phase_expr)?;
                let phase = phases.iter().position(|p| *p == phase)?;
                let mut values = Vec::with_capacity(fields.len());
                for slot in fields {
                    let Slot::CompanionVar(v) = *slot else { return None };
                    let rhs = binding(b, v, false)?;
                    let (val, key_bound) = if let Some(keys) = a.keys {
                        let ExprKind::FnConstruct { bounds, body } = &*rhs.kind else { return None };
                        let [bound] = bounds.as_slice() else { return None };
                        let BoundVars::Many(ids) = &bound.vars else { return None };
                        let [id] = ids.as_slice() else { return None };
                        if a.domains.exact_set(&bound.set).as_ref() != Some(keys) {
                            return None;
                        }
                        (body, Some((*id, &bound.set)))
                    } else {
                        (&rhs, None)
                    };
                    if a.mentions_any_managed(val) {
                        return None;
                    }
                    if let Some((kid, kset)) = key_bound {
                        ctx.push_bound_local(kid, Some(kset));
                    } else {
                        ctx.push_temp_local();
                    }
                    let lowered = ctx.lower_expr(val, false);
                    if let Some((kid, _)) = key_bound {
                        ctx.pop_bound_local(kid);
                    } else {
                        ctx.pop_temp_local();
                    }
                    values.push(lowered?);
                }
                (phase, values)
            }
        };

        let mut forms = Vec::new();
        for term in &b.terms {
            if matches!(
                &*term.kind,
                ExprKind::Builtin { op: B::Eq, args }
                    if args.len() == 2 && variable(&args[0], false).is_some_and(|v| a.is_control_or_projected_var(v))
            ) {
                continue;
            }
            let cleaned = clean_expr(a, fields, term, false, None, &mut reads)?;
            forms.push(ctx.lower_form(&cleaned, false)?);
        }
        Some(SeedData { bounds, guard: fold_form_conj(forms), phase, values })
    })();
    for id in pushed.into_iter().rev() {
        ctx.pop_bound_local(id);
    }
    res
}

fn lower_step_cases(
    ctx: &mut LowerCtx<'_>,
    a: &Analysis<'_>,
    fields: &[Slot],
    phases: &[Atom],
    b: &Branch,
    fallback_expr: &str,
) -> Option<Vec<StepCase>> {
    let transfer = a.transfer_branch(b)?;
    let mut allowed = a.phases.clone();
    for term in &b.terms {
        if let Some(ps) = a.guard(term, transfer.actor) {
            allowed.retain(|p| ps.contains(p));
        }
    }
    // Locate the actor's bound set expression if keyed with an explicit actor.
    let actor_set = if let Some(actor_id) = transfer.actor {
        let keys = a.keys?;
        let mut found = None;
        for bound in &b.bounds {
            if let BoundVars::Many(ids) = &bound.vars {
                if ids.contains(&actor_id) {
                    if a.domains.exact_set(&bound.set).as_ref() != Some(keys) {
                        return None;
                    }
                    found = Some(&bound.set);
                    break;
                }
            }
        }
        Some(found?)
    } else {
        None
    };

    let mut out = Vec::new();
    for source_atom in allowed {
        let source = phases.iter().position(|p| *p == source_atom)?;
        let target = transfer.target.as_ref().map(|t| phases.iter().position(|p| p == t)).unwrap_or(Some(source))?;

        let mut reads = Reads::new(fields.len());
        let cleaned_bounds = clean_bounds(a, fields, &b.bounds, true, transfer.actor, &mut reads)?;
        if let Some(actor_id) = transfer.actor {
            ctx.push_bound_local(actor_id, actor_set);
        }
        let bounds_res = ctx.lower_witness_bounds(&cleaned_bounds, true, transfer.actor);
        let Some((bounds, pushed)) = bounds_res else {
            if let Some(actor_id) = transfer.actor {
                ctx.pop_bound_local(actor_id);
            }
            return None;
        };

        let case_res = (|| {
            let mut guard_forms = Vec::new();
            for term in &b.terms {
                if a.guard(term, transfer.actor).is_some() {
                    continue;
                }
                if matches!(
                    &*term.kind,
                    ExprKind::Builtin { op: B::Eq, args }
                        if args.len() == 2 && variable(&args[0], true).is_some_and(|v| a.is_control_or_projected_var(v))
                ) {
                    continue;
                }
                if let ExprKind::Builtin { op: B::Unchanged, args } = &*term.kind {
                    if args.len() != 1 {
                        return None;
                    }
                    let mut retained = Vec::new();
                    collect_retained_unchanged(a, &args[0], &mut retained)?;
                    for v_expr in retained {
                        let frame = Expr::new(ExprKind::Builtin { op: B::Unchanged, args: vec![v_expr] }, term.span);
                        guard_forms.push(ctx.lower_form(&frame, true)?);
                    }
                    continue;
                }
                let cleaned = clean_expr(a, fields, term, true, transfer.actor, &mut reads)?;
                guard_forms.push(ctx.lower_form(&cleaned, true)?);
            }
            let mut writes = vec![false; fields.len()];
            let mut values = Vec::with_capacity(fields.len());
            for (f, slot) in fields.iter().enumerate() {
                if let Some(rhs) = transfer.writes.get(slot) {
                    let cleaned = clean_expr(a, fields, rhs, true, transfer.actor, &mut reads)?;
                    values.push(ctx.lower_expr(&cleaned, true)?);
                    writes[f] = true;
                } else {
                    values.push(fallback_expr.to_string());
                }
            }
            Some(StepCase {
                source,
                target,
                has_actor: transfer.actor.is_some(),
                reads,
                writes,
                bounds,
                guard: fold_form_conj(guard_forms),
                values,
            })
        })();

        for id in pushed.into_iter().rev() {
            ctx.pop_bound_local(id);
        }
        if let Some(actor_id) = transfer.actor {
            ctx.pop_bound_local(actor_id);
        }
        out.push(case_res?);
    }
    Some(out)
}

fn collect_retained_unchanged(a: &Analysis<'_>, e: &Expr, out: &mut Vec<Expr>) -> Option<()> {
    match &*e.kind {
        ExprKind::Var(v) => {
            if !a.is_control_or_projected_var(*v) {
                out.push(e.clone());
            }
            Some(())
        }
        ExprKind::Tuple(es) => {
            for x in es {
                collect_retained_unchanged(a, x, out)?;
            }
            Some(())
        }
        _ => None,
    }
}

/// Record actor/global slot reads and replace `ProvedMembership` subexpressions
/// with `Bool(true)`, failing closed on bare projected vars or primed managed
/// vars — mirroring `liveness/lean/leaves.rs::mask`.
fn clean_expr(a: &Analysis<'_>, fields: &[Slot], e: &Expr, allow_managed: bool, actor: Option<LocalId>, reads: &mut Reads) -> Option<Expr> {
    if a.is_proved_membership(e) {
        return Some(Expr::new(ExprKind::Bool(true), e.span));
    }
    if a.is_fixed_domain_read(e) {
        return allow_managed.then(|| e.clone());
    }
    if let Some(index) = a.control_read(e) {
        if !allow_managed {
            return None;
        }
        if let Some(idx) = index {
            let _ = clean_expr(a, fields, idx, allow_managed, actor, reads)?;
        }
        return replace_proved_in_children(a, fields, e, allow_managed, actor, reads);
    }
    if let Some((slot, index)) = a.slot_read(e) {
        if !allow_managed {
            return None;
        }
        let f = fields.iter().position(|x| x == &slot)?;
        let actor_read = a.keys.is_none() || index.is_some_and(|i| matches!(&*i.kind, ExprKind::Local(l) if Some(*l) == actor));
        if actor_read {
            reads.actor[f] = true;
        } else {
            reads.global[f] = true;
        }
        // Clean index subexpression if present without re-recording the outer slot.
        let mut out = e.clone();
        match &mut *Arc::make_mut(&mut out.kind) {
            ExprKind::Field { record, .. } => {
                if let ExprKind::FnApp { args, .. } = &mut *Arc::make_mut(&mut record.kind) {
                    if args.len() == 1 {
                        args[0] = clean_expr(a, fields, &args[0], allow_managed, actor, reads)?;
                    }
                }
            }
            ExprKind::FnApp { args, .. } if args.len() == 1 => {
                args[0] = clean_expr(a, fields, &args[0], allow_managed, actor, reads)?;
            }
            _ => {}
        }
        return Some(out);
    }
    if matches!(&*e.kind, ExprKind::Var(v) if a.is_projected_var(*v))
        || matches!(&*e.kind, ExprKind::Builtin { op: B::Prime, .. } if a.mentions_any_managed(e))
    {
        return None;
    }
    if matches!(&*e.kind, ExprKind::Var(v) if matches!(&a.control, Control::Var { var } if *v == *var)) {
        return allow_managed.then(|| e.clone());
    }
    replace_proved_in_children(a, fields, e, allow_managed, actor, reads)
}

fn replace_proved_in_children(
    a: &Analysis<'_>,
    fields: &[Slot],
    e: &Expr,
    allow_managed: bool,
    actor: Option<LocalId>,
    reads: &mut Reads,
) -> Option<Expr> {
    let mut out = e.clone();
    let mut ok = true;
    visit::children_mut(&mut out, &mut |child| {
        if let Some(c) = clean_expr(a, fields, child, allow_managed, actor, reads) {
            *child = c;
        } else {
            ok = false;
        }
    });
    ok.then_some(out)
}

fn lower_state_preds(
    ctx: &mut LowerCtx<'_>,
    a: &Analysis<'_>,
    fields: &[Slot],
    phases: &[Atom],
    preds: &[Expr],
    root_ctx: &ObsContext,
    observed: &mut [Vec<bool>],
) -> Option<String> {
    struct CleanObsSink<'a> {
        fields: &'a [Slot],
        phases: &'a [Atom],
        observed: &'a mut [Vec<bool>],
    }
    impl ObsSink for CleanObsSink<'_> {
        fn proved_membership(&mut self, e: &Expr) -> Option<Option<Expr>> {
            Some(Some(Expr::new(ExprKind::Bool(true), e.span)))
        }
        fn fixed_domain(&mut self, e: &Expr) -> Option<Option<Expr>> {
            Some(Some(e.clone()))
        }
        fn control_read(&mut self, e: &Expr, index: Option<Expr>) -> Option<Option<Expr>> {
            let mut out = e.clone();
            if let Some(idx) = index {
                match &mut *Arc::make_mut(&mut out.kind) {
                    ExprKind::Field { record, .. } => {
                        if let ExprKind::FnApp { args, .. } = &mut *Arc::make_mut(&mut record.kind) {
                            if args.len() == 1 {
                                args[0] = idx;
                            }
                        }
                    }
                    ExprKind::FnApp { args, .. } if args.len() == 1 => {
                        args[0] = idx;
                    }
                    _ => {}
                }
            }
            Some(Some(out))
        }
        fn slot_read(&mut self, e: &Expr, slot: &Slot, index: Option<Expr>, allowed: &BTreeSet<Atom>) -> Option<Option<Expr>> {
            let f = self.fields.iter().position(|x| x == slot)?;
            for (p_idx, p) in self.phases.iter().enumerate() {
                if allowed.contains(p) {
                    self.observed[p_idx][f] = true;
                }
            }
            let mut out = e.clone();
            if let Some(idx) = index {
                match &mut *Arc::make_mut(&mut out.kind) {
                    ExprKind::Field { record, .. } => {
                        if let ExprKind::FnApp { args, .. } = &mut *Arc::make_mut(&mut record.kind) {
                            if args.len() == 1 {
                                args[0] = idx;
                            }
                        }
                    }
                    ExprKind::FnApp { args, .. } if args.len() == 1 => {
                        args[0] = idx;
                    }
                    _ => {}
                }
            }
            Some(Some(out))
        }
        fn bare_projected_var(&mut self, _e: &Expr, _var: VarId) -> Option<Option<Expr>> {
            None
        }
        fn bare_control_var(&mut self, e: &Expr) -> Option<Option<Expr>> {
            Some(Some(e.clone()))
        }
    }

    let mut forms = Vec::with_capacity(preds.len());
    for p in preds {
        let mut sink = CleanObsSink { fields, phases, observed };
        let cleaned = a.walk_obs(p, root_ctx, &mut sink, true)??;
        forms.push(ctx.lower_form(&cleaned, false)?);
    }
    Some(fold_form_conj(forms))
}

fn lower_action_preds(
    ctx: &mut LowerCtx<'_>,
    a: &Analysis<'_>,
    fields: &[Slot],
    preds: &[Expr],
    observed: &mut [Vec<bool>],
) -> Option<String> {
    let mut forms = Vec::with_capacity(preds.len());
    for p in preds {
        let cleaned = clean_action_expr(a, fields, p, observed, false)?;
        forms.push(ctx.lower_action_pred(&cleaned)?);
    }
    Some(fold_form_conj(forms))
}

fn clean_action_expr(a: &Analysis<'_>, fields: &[Slot], e: &Expr, observed: &mut [Vec<bool>], ambient: bool) -> Option<Expr> {
    match a.classify_action_read(e) {
        ActionRead::Slot { slot, key, map_primed, key_primed } => {
            if map_primed && ambient {
                return None;
            }
            if let Some(slot) = slot {
                let f = fields.iter().position(|x| x == &slot)?;
                for row in observed.iter_mut() {
                    row[f] = true;
                }
            }
            let key_scope = ambient || key_primed;
            if key_primed && ambient {
                return None;
            }
            if let Some(key) = key {
                let _ = clean_action_expr(a, fields, key, observed, key_scope)?;
            }
            // Replace any proved memberships inside key subexpressions while preserving the outer slot AST.
            let mut out = e.clone();
            if key.is_some() {
                clean_action_key_in_place(a, fields, &mut out, observed, key_scope)?;
            }
            Some(out)
        }
        ActionRead::ProvedMembership => Some(Expr::new(ExprKind::Bool(true), e.span)),
        ActionRead::FixedDomain | ActionRead::ControlMap | ActionRead::Unchanged(_) => Some(e.clone()),
        ActionRead::BoxAction { action, sub } => {
            let action = clean_action_expr(a, fields, action, observed, ambient)?;
            Some(Expr::new(ExprKind::BoxAction { action, sub: sub.clone() }, e.span))
        }
        ActionRead::Unsupported => None,
        ActionRead::Recurse => {
            let mut out = e.clone();
            let mut ok = true;
            visit::children_mut(&mut out, &mut |child| {
                if let Some(c) = clean_action_expr(a, fields, child, observed, ambient) {
                    *child = c;
                } else {
                    ok = false;
                }
            });
            ok.then_some(out)
        }
    }
}

fn clean_action_key_in_place(a: &Analysis<'_>, fields: &[Slot], e: &mut Expr, observed: &mut [Vec<bool>], key_scope: bool) -> Option<()> {
    match &mut *Arc::make_mut(&mut e.kind) {
        ExprKind::Builtin { op: B::Prime, args } if args.len() == 1 => {
            clean_action_key_in_place(a, fields, &mut args[0], observed, key_scope)
        }
        ExprKind::Field { record, .. } => clean_action_key_in_place(a, fields, record, observed, key_scope),
        ExprKind::FnApp { args, .. } if args.len() == 1 => {
            args[0] = clean_action_expr(a, fields, &args[0], observed, key_scope)?;
            Some(())
        }
        _ => Some(()),
    }
}

fn validate_liveness(a: &Analysis<'_>, fields: &[Slot], phases: &[Atom], cases: &[StepCase], observed: &[Vec<bool>]) -> Option<()> {
    for (f, slot) in fields.iter().enumerate() {
        let live = &a.live[slot];
        for (p_idx, p) in phases.iter().enumerate() {
            if observed[p_idx][f] && !live.contains(p) {
                return None;
            }
        }
        for c in cases {
            if (c.reads.actor[f] && !live.contains(&phases[c.source]))
                || (c.reads.global[f] && !phases.iter().all(|p| live.contains(p)))
                || (!c.writes[f] && live.contains(&phases[c.target]) && !live.contains(&phases[c.source]))
            {
                return None;
            }
        }
    }
    Some(())
}

fn fold_form_conj(forms: Vec<String>) -> String {
    let mut it = forms.into_iter();
    let Some(first) = it.next() else {
        return "(Form.truth true)".to_string();
    };
    it.fold(first, |acc, f| format!("(Form.conj {acc} {f})"))
}

#[allow(clippy::too_many_arguments)]
fn render(
    program: &Program,
    groups: &[GroupInfo],
    ctx: &LowerCtx<'_>,
    orig_init: &Expr,
    a: &Analysis<'_>,
    fields: &[Slot],
    phases: &[Atom],
    phase_atom_ids: &[usize],
    fixed_atom_ids: &[usize],
    key_mask: GroupMask,
    default_key_lean: &str,
    is_keyed: bool,
    core_count: usize,
    var_roles: &[String],
    rec_field_atoms: &[usize],
    sentinel_exprs: &[String],
    branch_count: usize,
    seeds: &[SeedData],
    cases: &[StepCase],
    observed: &[Vec<bool>],
    obs_form: &str,
    init_obs_form: &str,
    constraint_form: &str,
    action_constraint_form: &str,
    action_obs_form: &str,
    fallback_expr: &str,
    constrained: bool,
) -> OpenCert {
    let mut out = String::from(include_str!("../../FieldCertificate.lean"));
    out.push_str(include_str!("../../EquivSymCertificate.lean"));
    out.push_str(include_str!("../../FieldSymCertificate.lean"));
    out.push_str("\nnamespace TlxOptimization.GeneratedFieldSymmetry\n");
    out.push_str(
        "open TlxOptimization FieldRule EquivRule FieldSymRule\n\
         noncomputable section\n\
         set_option linter.unusedVariables false\n\
         set_option maxRecDepth 20000\n",
    );
    write_common_header(&mut out, groups, program.vars.len(), ctx, orig_init);
    writeln!(out, "abbrev FullVar := VarId").unwrap();
    writeln!(out, "abbrev CoreVar := Fin {core_count}").unwrap();
    writeln!(out, "abbrev FixedCount : Nat := {}", fixed_atom_ids.len()).unwrap();
    writeln!(out, "abbrev PhaseCount : Nat := {}", phases.len()).unwrap();
    writeln!(out, "abbrev FieldCount : Nat := {}", fields.len()).unwrap();
    writeln!(out, "abbrev BranchCount : Nat := {branch_count}").unwrap();

    // Key mask and fixed atom IDs.
    let mask_parts: Vec<String> =
        (0..groups.len()).filter(|gi| (key_mask & (1u16 << gi)) != 0).map(|gi| format!("g.val == {gi}")).collect();
    let key_mask_lean = if mask_parts.is_empty() { "fun _ => false".to_string() } else { format!("fun g => {}", mask_parts.join(" || ")) };
    writeln!(out, "def keyMask : GroupMask GroupCount := {key_mask_lean}").unwrap();
    out.push_str("def fixedAtomId (i : Fin FixedCount) : Nat :=\n  match i.val with\n");
    for (i, aid) in fixed_atom_ids.iter().enumerate() {
        writeln!(out, "  | {i} => {aid}").unwrap();
    }
    out.push_str("  | _ => 0\n");
    writeln!(out, "def defaultKey : KeyElem groupSizes FixedCount keyMask := {default_key_lean}").unwrap();

    out.push_str("def phaseAtom (p : Fin PhaseCount) : Nat :=\n  match p.val with\n");
    for (i, aid) in phase_atom_ids.iter().enumerate() {
        writeln!(out, "  | {i} => {aid}").unwrap();
    }
    out.push_str("  | _ => 0\n");

    out.push_str("def recordFieldAtom (f : Fin FieldCount) : Nat :=\n  match f.val with\n");
    for (i, aid) in rec_field_atoms.iter().enumerate() {
        writeln!(out, "  | {i} => {aid}").unwrap();
    }
    out.push_str("  | _ => 0\n");

    out.push_str("def varRole (v : FullVar) : VarRole CoreVar (Fin FieldCount) :=\n  match v.val, v.isLt with\n");
    for (i, role) in var_roles.iter().enumerate() {
        writeln!(out, "  | {i}, _ => {role}").unwrap();
    }
    writeln!(out, "  | _ + {}, h => absurd h (by omega)", var_roles.len()).unwrap();

    out.push_str("def sentinelExpr (f : Fin FieldCount) : EquivRule.Expr GroupCount Empty :=\n  match f.val with\n");
    for (i, se) in sentinel_exprs.iter().enumerate() {
        writeln!(out, "  | {i} => {se}").unwrap();
    }
    writeln!(out, "  | _ => {fallback_expr}").unwrap();

    // Liveness and branch tables.
    out.push_str("def live (p : Fin PhaseCount) (f : Fin FieldCount) : Bool :=\n  match p.val, f.val with\n");
    for (pi, p) in phases.iter().enumerate() {
        for (fi, slot) in fields.iter().enumerate() {
            if a.live[slot].contains(p) {
                writeln!(out, "  | {pi}, {fi} => true").unwrap();
            }
        }
    }
    out.push_str("  | _, _ => false\n");

    out.push_str("def source (b : Fin BranchCount) : Fin PhaseCount :=\n  match b.val with\n");
    for (bi, c) in cases.iter().enumerate() {
        writeln!(out, "  | {bi} => ⟨{}, by decide⟩", c.source).unwrap();
    }
    out.push_str("  | _ => ⟨0, by decide⟩\n");

    out.push_str("def target (b : Fin BranchCount) : Fin PhaseCount :=\n  match b.val with\n");
    for (bi, c) in cases.iter().enumerate() {
        writeln!(out, "  | {bi} => ⟨{}, by decide⟩", c.target).unwrap();
    }
    out.push_str("  | _ => ⟨0, by decide⟩\n");

    out.push_str("def readsActor (b : Fin BranchCount) (f : Fin FieldCount) : Bool :=\n  match b.val, f.val with\n");
    for (bi, c) in cases.iter().enumerate() {
        for (fi, &r) in c.reads.actor.iter().enumerate() {
            if r {
                writeln!(out, "  | {bi}, {fi} => true").unwrap();
            }
        }
    }
    out.push_str("  | _, _ => false\n");

    out.push_str("def readsGlobal (b : Fin BranchCount) (f : Fin FieldCount) : Bool :=\n  match b.val, f.val with\n");
    for (bi, c) in cases.iter().enumerate() {
        for (fi, &r) in c.reads.global.iter().enumerate() {
            if r {
                writeln!(out, "  | {bi}, {fi} => true").unwrap();
            }
        }
    }
    out.push_str("  | _, _ => false\n");

    out.push_str("def writes (b : Fin BranchCount) (f : Fin FieldCount) : Bool :=\n  match b.val, f.val with\n");
    for (bi, c) in cases.iter().enumerate() {
        for (fi, &w) in c.writes.iter().enumerate() {
            if w {
                writeln!(out, "  | {bi}, {fi} => true").unwrap();
            }
        }
    }
    out.push_str("  | _, _ => false\n");

    out.push_str("def observed (p : Fin PhaseCount) (f : Fin FieldCount) : Bool :=\n  match p.val, f.val with\n");
    for (pi, row) in observed.iter().enumerate() {
        for (fi, &o) in row.iter().enumerate() {
            if o {
                writeln!(out, "  | {pi}, {fi} => true").unwrap();
            }
        }
    }
    out.push_str("  | _, _ => false\n");

    // Seed tables.
    out.push_str("def seedValid (b : Fin BranchCount) : Bool :=\n  match b.val with\n");
    for bi in 0..seeds.len() {
        writeln!(out, "  | {bi} => true").unwrap();
    }
    out.push_str("  | _ => false\n");

    out.push_str("def seedBounds (b : Fin BranchCount) : List (SetPred GroupCount FullVar) :=\n  match b.val with\n");
    for (bi, s) in seeds.iter().enumerate() {
        writeln!(out, "  | {bi} => [{}]", s.bounds.join(", ")).unwrap();
    }
    out.push_str("  | _ => []\n");

    out.push_str("def seedGuard (b : Fin BranchCount) : Form GroupCount FullVar :=\n  match b.val with\n");
    for (bi, s) in seeds.iter().enumerate() {
        writeln!(out, "  | {bi} => {}", s.guard).unwrap();
    }
    out.push_str("  | _ => Form.truth false\n");

    out.push_str("def seedPhase (b : Fin BranchCount) : Fin PhaseCount :=\n  match b.val with\n");
    for (bi, s) in seeds.iter().enumerate() {
        writeln!(out, "  | {bi} => ⟨{}, by decide⟩", s.phase).unwrap();
    }
    out.push_str("  | _ => ⟨0, by decide⟩\n");

    out.push_str(
        "def seedValueExpr (b : Fin BranchCount) (f : Fin FieldCount) : EquivRule.Expr GroupCount FullVar :=\n  match b.val, f.val with\n",
    );
    for (bi, s) in seeds.iter().enumerate() {
        for (fi, v) in s.values.iter().enumerate() {
            writeln!(out, "  | {bi}, {fi} => {v}").unwrap();
        }
    }
    writeln!(out, "  | _, _ => {fallback_expr}").unwrap();

    // Step tables.
    out.push_str("def stepValid (b : Fin BranchCount) : Bool :=\n  match b.val with\n");
    for bi in 0..cases.len() {
        writeln!(out, "  | {bi} => true").unwrap();
    }
    out.push_str("  | _ => false\n");

    out.push_str("def stepHasActor (b : Fin BranchCount) : Bool :=\n  match b.val with\n");
    for (bi, c) in cases.iter().enumerate() {
        if c.has_actor {
            writeln!(out, "  | {bi} => true").unwrap();
        }
    }
    out.push_str("  | _ => false\n");

    out.push_str("def stepBounds (b : Fin BranchCount) : List (SetPred GroupCount FullVar) :=\n  match b.val with\n");
    for (bi, c) in cases.iter().enumerate() {
        writeln!(out, "  | {bi} => [{}]", c.bounds.join(", ")).unwrap();
    }
    out.push_str("  | _ => []\n");

    out.push_str("def stepGuard (b : Fin BranchCount) : Form GroupCount FullVar :=\n  match b.val with\n");
    for (bi, c) in cases.iter().enumerate() {
        writeln!(out, "  | {bi} => {}", c.guard).unwrap();
    }
    out.push_str("  | _ => Form.truth false\n");

    out.push_str(
        "def stepValueExpr (b : Fin BranchCount) (f : Fin FieldCount) : EquivRule.Expr GroupCount FullVar :=\n  match b.val, f.val with\n",
    );
    for (bi, c) in cases.iter().enumerate() {
        for (fi, v) in c.values.iter().enumerate() {
            writeln!(out, "  | {bi}, {fi} => {v}").unwrap();
        }
    }
    writeln!(out, "  | _, _ => {fallback_expr}").unwrap();

    writeln!(out, "def obsForm : Form GroupCount FullVar := {obs_form}").unwrap();
    if constrained {
        writeln!(out, "def initObsForm : Form GroupCount FullVar := {init_obs_form}").unwrap();
        writeln!(out, "def constraintForm : Form GroupCount FullVar := {constraint_form}").unwrap();
        writeln!(out, "def actionConstraintForm : Form GroupCount FullVar := {action_constraint_form}").unwrap();
        writeln!(out, "def actionObsForm : Form GroupCount FullVar := {action_obs_form}").unwrap();
    }
    writeln!(
        out,
        "def fieldSummary : String := {}",
        literal(&format!("control={:?}; fields={:?}; phases={:?}; keyed={is_keyed}", a.control, fields, phases))
    )
    .unwrap();

    out.push_str(
        "abbrev Semantics (A : Type) := EquivRule.AtomOps A\n\
         variable {A : Type} [HasNatAtom A] (sem : Semantics A)\n\
         def model : FieldSymRule.Model GroupCount groupSizes FixedCount keyMask CoreVar FullVar PhaseCount FieldCount BranchCount A where\n\
         \x20 ops := sem\n\
         \x20 fixedAtom := fun i => sem.atomVal (fixedAtomId i)\n\
         \x20 defaultKey := defaultKey\n\
         \x20 phaseAtom := phaseAtom\n\
         \x20 varRole := varRole\n\
         \x20 sentinelExpr := sentinelExpr\n\
         \x20 live := live\n\
         \x20 source := source\n\
         \x20 target := target\n\
         \x20 readsActor := readsActor\n\
         \x20 readsGlobal := readsGlobal\n\
         \x20 writes := writes\n\
         \x20 observed := observed\n\
         \x20 actorLive := by decide\n\
         \x20 globalLive := by decide\n\
         \x20 frameLive := by decide\n\
         \x20 observedLive := by decide\n\
         \x20 seedValid := seedValid\n\
         \x20 seedBounds := seedBounds\n\
         \x20 seedGuard := seedGuard\n\
         \x20 seedPhase := seedPhase\n\
         \x20 seedValueExpr := seedValueExpr\n\
         \x20 stepValid := stepValid\n\
         \x20 stepHasActor := stepHasActor\n\
         \x20 stepBounds := stepBounds\n\
         \x20 stepGuard := stepGuard\n\
         \x20 stepValueExpr := stepValueExpr\n\
         \x20 obsForm := obsForm\n",
    );
    if constrained {
        out.push_str(
            "  initObsForm := initObsForm\n\
             \x20 constraintForm := constraintForm\n\
             \x20 actionConstraintForm := actionConstraintForm\n\
             \x20 actionObsForm := actionObsForm\n",
        );
    }
    // Prove `defaultKeyFixed` cleanly for both keyed (all `isKeyed = true`) and
    // scalar (`defaultKey = Sum.inl ⟨0, _⟩`, invariant by `rfl`).
    out.push_str("  defaultKeyFixed := by\n    intro p v\n    rcases v with ⟨v, hv⟩\n    match v, hv with\n");
    for (i, role) in var_roles.iter().enumerate() {
        let tactic = if is_keyed || role.starts_with("VarRole.core") { "trivial" } else { "rfl" };
        writeln!(out, "    | {i}, _ => {tactic}").unwrap();
    }
    writeln!(out, "    | _ + {}, h => exact absurd h (by omega)", var_roles.len()).unwrap();

    OpenCert::new_composed(out, include_str!("sym.lean"), "GeneratedFieldSymmetry", constrained, "field", "fieldProject")
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

fn expr_alpha_eq_with_locals(a: &Expr, b: &Expr, locals: &[(LocalId, LocalId)]) -> bool {
    let mut map = locals.to_vec();
    expr_alpha_eq_rec(a, b, &mut map)
}

/// Alpha-equivalent structural equality on HIR expressions (ignoring spans).
pub(in crate::optimize::phase) fn expr_alpha_eq(a: &Expr, b: &Expr) -> bool {
    let mut map = Vec::new();
    expr_alpha_eq_rec(a, b, &mut map)
}

fn expr_alpha_eq_rec(a: &Expr, b: &Expr, locals: &mut Vec<(LocalId, LocalId)>) -> bool {
    match (&*a.kind, &*b.kind) {
        (ExprKind::Bool(x), ExprKind::Bool(y)) => x == y,
        (ExprKind::Num(x), ExprKind::Num(y)) => x == y,
        (ExprKind::Str(x), ExprKind::Str(y)) => x == y,
        (ExprKind::Decimal(x), ExprKind::Decimal(y)) => x == y,
        (ExprKind::Var(x), ExprKind::Var(y)) => x == y,
        (ExprKind::Const(x), ExprKind::Const(y)) => x == y,
        (ExprKind::Local(x), ExprKind::Local(y)) => {
            if let Some((_, mapped)) = locals.iter().rev().find(|(l, _)| l == x) {
                mapped == y
            } else {
                x == y
            }
        }
        (ExprKind::Tuple(xs), ExprKind::Tuple(ys)) | (ExprKind::SetEnum(xs), ExprKind::SetEnum(ys)) => {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| expr_alpha_eq_rec(x, y, locals))
        }
        (ExprKind::Record(xs), ExprKind::Record(ys)) => {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|((k1, v1), (k2, v2))| k1 == k2 && expr_alpha_eq_rec(v1, v2, locals))
        }
        (ExprKind::Field { record: r1, field: f1 }, ExprKind::Field { record: r2, field: f2 }) => {
            f1 == f2 && expr_alpha_eq_rec(r1, r2, locals)
        }
        (ExprKind::FnApp { func: f1, args: a1 }, ExprKind::FnApp { func: f2, args: a2 }) => {
            expr_alpha_eq_rec(f1, f2, locals) && a1.len() == a2.len() && a1.iter().zip(a2).all(|(x, y)| expr_alpha_eq_rec(x, y, locals))
        }
        (ExprKind::Builtin { op: o1, args: a1 }, ExprKind::Builtin { op: o2, args: a2 }) => {
            o1 == o2 && a1.len() == a2.len() && a1.iter().zip(a2).all(|(x, y)| expr_alpha_eq_rec(x, y, locals))
        }
        (ExprKind::If { cond: c1, then: t1, els: e1 }, ExprKind::If { cond: c2, then: t2, els: e2 }) => {
            expr_alpha_eq_rec(c1, c2, locals) && expr_alpha_eq_rec(t1, t2, locals) && expr_alpha_eq_rec(e1, e2, locals)
        }
        (ExprKind::Except { base: b1, updates: u1 }, ExprKind::Except { base: b2, updates: u2 }) => {
            expr_alpha_eq_rec(b1, b2, locals)
                && u1.len() == u2.len()
                && u1.iter().zip(u2).all(|((p1, v1), (p2, v2))| {
                    p1.len() == p2.len()
                        && p1.iter().zip(p2).all(|(k1, k2)| match (k1, k2) {
                            (ExceptKey::Field(f1), ExceptKey::Field(f2)) => f1 == f2,
                            (ExceptKey::Index(i1), ExceptKey::Index(i2)) => {
                                i1.len() == i2.len() && i1.iter().zip(i2).all(|(x, y)| expr_alpha_eq_rec(x, y, locals))
                            }
                            _ => false,
                        })
                        && expr_alpha_eq_rec(v1, v2, locals)
                })
        }
        (ExprKind::FnConstruct { bounds: b1, body: body1 }, ExprKind::FnConstruct { bounds: b2, body: body2 }) => {
            if b1.len() != b2.len() {
                return false;
            }
            let saved = locals.len();
            let mut ok = true;
            for (x, y) in b1.iter().zip(b2) {
                if !expr_alpha_eq_rec(&x.set, &y.set, locals) {
                    ok = false;
                    break;
                }
                match (&x.vars, &y.vars) {
                    (BoundVars::Many(l1), BoundVars::Many(l2)) | (BoundVars::Tuple(l1), BoundVars::Tuple(l2)) if l1.len() == l2.len() => {
                        for (&id1, &id2) in l1.iter().zip(l2) {
                            locals.push((id1, id2));
                        }
                    }
                    _ => {
                        ok = false;
                        break;
                    }
                }
            }
            let res = ok && expr_alpha_eq_rec(body1, body2, locals);
            locals.truncate(saved);
            res
        }
        _ => false,
    }
}
