//! HIR seed, step-case, witness-bound, and state/action observation lowering
//! into the composed `FieldSymRule` Lean IR, plus pre-emission liveness checks.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::{builtins::Builtin as B, hir::*, visit, Program};

use super::super::super::{
    binding,
    domain::Atom,
    equiv_sym::{fold_form_conj, lower::LowerCtx, AtomKey, GroupInfo, GroupMask},
    mentions_local, sym_totality, variable, Branch, CheckSpec, OpenCert,
};
use super::super::{ActionRead, Analysis, Control, ObsContext, ObsSink, Slot};
use super::output::{self, RenderSpec};
use super::{Reads, SeedData, StepCase};

const MAX_CASES: usize = 128;

#[allow(clippy::too_many_arguments)]
pub(super) fn emit_composed(
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
        let ak = AtomKey::from_key_free_atom(p, all_keys)?;
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
                let ak = AtomKey::from_key_free_atom(k, all_keys)?;
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
    Some(output::render(&RenderSpec {
        program,
        groups,
        ctx: &ctx,
        orig_init,
        analysis: a,
        fields: &fields,
        phases: &phases,
        phase_atom_ids: &phase_atom_ids,
        fixed_atom_ids: &fixed_atom_ids,
        key_mask,
        default_key_lean: &default_key_lean,
        is_keyed,
        core_count,
        var_roles: &var_roles,
        rec_field_atoms: &rec_field_atoms,
        sentinel_exprs: &sentinel_exprs,
        branch_count,
        seeds: &seeds,
        cases: &cases,
        observed: &observed,
        obs_form: &obs_form,
        init_obs_form: &init_obs_form,
        constraint_form: &constraint_form,
        action_constraint_form: &action_constraint_form,
        action_obs_form: &action_obs_form,
        fallback_expr: &fallback_expr,
        constrained: spec.is_constrained(),
    }))
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
