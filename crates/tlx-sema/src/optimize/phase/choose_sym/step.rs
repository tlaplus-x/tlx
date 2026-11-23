//! Step-branch lowering (`preGuard`, hoisted `BranchChoice` sequence, `postGuard`,
//! `Write` / `ChoiceSlotExpr` / `FlagStep` / `MsgStep` emission) for `choose_sym`.

use super::super::sym_totality::IntBoundHint;
use super::super::{variable, Branch};
use super::bounds::{eval_elem_bound, LocalBounds, ValBound};
use super::domain_infer::{collect_primed_vars, exact_k_subset_family, group_mask_exact, independent, mentions_primed_var, VarShape};
use super::expressions::{find_first_choice_node, replace_cached_choices, ExtractedChoice};
use super::invariant::{record_empty_guards, FlagStepKind, MsgStepKind};
use super::pure_expr::{bounded, AuxScope};
use super::{mentions_any_local, mentions_any_var, mentions_local, Emitter, GroupMask, KeyRef, Locals};
use crate::{builtins::Builtin as B, hir::*};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

pub(super) struct StepCase {
    pub(super) pre_guard: String,
    pub(super) empty_flag_guards: Vec<(usize, GroupMask)>,
    pub(super) empty_msg_guards: Vec<usize>,
    pub(super) uniform_guards: Vec<(usize, String)>,
    pub(super) choices: Vec<String>,
    pub(super) post_guard: String,
    pub(super) writes: Vec<String>,
    pub(super) slot_writes: Vec<String>,
    pub(super) flag_steps: Vec<FlagStepKind>,
    pub(super) msg_steps: Vec<MsgStepKind>,
    pub(super) keys: Vec<(LocalId, GroupMask)>,
}

#[derive(Clone)]
enum StepVarSource {
    Unchanged,
    Eq(Expr),
    SlotIn { local: LocalId },
    FlagCard { card: usize },
}

struct PreparedStepGuards {
    keys: Vec<(LocalId, GroupMask)>,
    var_sources: Vec<Option<StepVarSource>>,
    pre_guard: String,
    empty_flag_guards: Vec<(usize, GroupMask)>,
    empty_msg_guards: Vec<usize>,
    uniform_guards: Vec<(usize, String)>,
    choice_guard_exprs: Vec<Expr>,
}

impl Emitter<'_> {
    pub(super) fn lower_step_branch(&mut self, b: &Branch) -> Option<StepCase> {
        let mut step_locals = self.domains.locals(&b.bounds);
        let mut step_local_bounds = LocalBounds::new();
        let mut step_hints = HashMap::new();
        for bnd in &b.bounds {
            let eb = eval_elem_bound(
                &bnd.set,
                &self.model_bounds,
                &step_local_bounds,
                None,
                self.domains,
                self.fold_vars,
                self.groups,
                &self.shapes,
                0,
            );
            for l in bnd.vars.locals() {
                let lb = if matches!(bnd.vars, BoundVars::Many(_)) { eb.clone() } else { ValBound::Top };
                if let Some(h) = val_bound_to_hint(&lb) {
                    step_hints.insert(*l, h);
                }
                step_local_bounds.insert(*l, lb);
            }
        }
        let mut step_check_env = self.totality.bind_step_bounds(&b.bounds, &step_hints)?;
        std::mem::swap(&mut self.step_locals, &mut step_locals);
        std::mem::swap(&mut self.step_local_bounds, &mut step_local_bounds);
        std::mem::swap(&mut self.step_check_env, &mut step_check_env);
        let res = self.lower_step_branch_inner(b);
        self.step_locals = step_locals;
        self.step_local_bounds = step_local_bounds;
        self.step_check_env = step_check_env;
        res
    }

    fn lower_step_branch_inner(&mut self, b: &Branch) -> Option<StepCase> {
        let prep = self.prepare_step_guards(b)?;
        let allow_branch_hoist = prep.choice_guard_exprs.is_empty();
        let mut choices: Vec<String> = Vec::new();
        let mut cur_keys = prep.keys.clone();
        let mut cur_aux = AuxScope::default();
        let mut hoisted_cache: Vec<(Expr, Expr)> = Vec::new();

        // Pass 1: hoist ALL branch-level choices before lowering postGuard or any variable
        // writes so every KeyRef.bound and AuxEnv slot reflects the final post-choice layout.
        let mut prepared_rhs: Vec<Option<Expr>> = vec![None; self.shapes.len()];
        for (vi, slot) in prepared_rhs.iter_mut().enumerate() {
            let var = VarId(vi as u32);
            if let Some(StepVarSource::Eq(rhs)) = &prep.var_sources[vi] {
                if variable(rhs, false) == Some(var) {
                    continue;
                }
                let rewritten = if self.contains_any_choose(rhs) {
                    match self.shapes[vi] {
                        VarShape::KeySetFlag { .. } | VarShape::BoolMapFlag { .. } | VarShape::MsgSet { .. } => {
                            if !allow_branch_hoist {
                                return None;
                            }
                            self.hoist_branch_choices(rhs, &mut cur_keys, &mut cur_aux, &mut choices, &mut hoisted_cache)?
                        }
                        VarShape::FixedMap { .. } | VarShape::ScalarSlot { .. } => {
                            if allow_branch_hoist {
                                self.hoist_branch_choices(rhs, &mut cur_keys, &mut cur_aux, &mut choices, &mut hoisted_cache)?
                            } else {
                                rhs.clone()
                            }
                        }
                        VarShape::Core => rhs.clone(),
                    }
                } else {
                    rhs.clone()
                };
                *slot = Some(rewritten);
            }
        }

        // Pass 2: lower postGuard and every variable update against the final post-choice scope.
        let post_guard = self.choice_tests(&prep.choice_guard_exprs, &cur_keys, &cur_aux)?;

        let mut writes = Vec::new();
        let mut slot_writes = Vec::new();
        let mut flag_steps = vec![FlagStepKind::Keep; self.num_flags];
        let mut msg_steps = vec![MsgStepKind::Keep; self.num_msgs];
        let no_choices = choices.is_empty();

        for (vi, rhs_opt) in prepared_rhs.iter().enumerate() {
            let var = VarId(vi as u32);
            self.lower_var_step_update(
                var,
                &prep,
                rhs_opt.as_ref(),
                &cur_keys,
                &cur_aux,
                no_choices,
                &mut writes,
                &mut slot_writes,
                &mut flag_steps,
                &mut msg_steps,
            )?;
        }

        Some(StepCase {
            pre_guard: prep.pre_guard,
            empty_flag_guards: prep.empty_flag_guards,
            empty_msg_guards: prep.empty_msg_guards,
            uniform_guards: prep.uniform_guards,
            choices,
            post_guard,
            writes,
            slot_writes,
            flag_steps,
            msg_steps,
            keys: prep.keys,
        })
    }

    fn prepare_step_guards(&mut self, b: &Branch) -> Option<PreparedStepGuards> {
        let locals = self.domains.locals(&b.bounds);
        let mut keys: Vec<(LocalId, GroupMask)> = Vec::new();
        let mut pure_guard_exprs: Vec<Expr> = Vec::new();
        let mut choice_guard_exprs: Vec<Expr> = Vec::new();

        for bound in &b.bounds {
            let BoundVars::Many(ids) = &bound.vars else { return None };
            if let Some(exact) = self.domains.exact_set(&bound.set) {
                let (mask, fixed) = group_mask_exact(self.groups, &exact)?;
                if mask != 0 && fixed.is_empty() {
                    for &id in ids {
                        keys.insert(0, (id, mask));
                    }
                    continue;
                }
            }
            if let Some(v) = variable(&bound.set, false) {
                if let VarShape::KeySetFlag { mask, .. } = self.shapes[v.idx()] {
                    for &id in ids {
                        keys.insert(0, (id, mask));
                        pure_guard_exprs.push(Expr::new(
                            ExprKind::Builtin { op: B::In, args: vec![Expr::new(ExprKind::Local(id), bound.set.span), bound.set.clone()] },
                            bound.set.span,
                        ));
                    }
                    continue;
                }
            }
            for id in ids {
                if !independent(locals.get(id)?, self.all_keys) {
                    return None;
                }
                pure_guard_exprs.push(Expr::new(
                    ExprKind::Builtin { op: B::In, args: vec![Expr::new(ExprKind::Local(*id), bound.set.span), bound.set.clone()] },
                    bound.set.span,
                ));
            }
        }

        let mut consumed_terms = vec![false; b.terms.len()];
        let mut var_sources: Vec<Option<StepVarSource>> = vec![None; self.shapes.len()];
        for (vi, src_slot) in var_sources.iter_mut().enumerate() {
            if matches!(self.shapes[vi], VarShape::Core) {
                continue;
            }
            let var = VarId(vi as u32);
            let (eqs, ins, unchanged) = self.collect_var_terms(b, var, true);
            if eqs.len() + unchanged > 1 {
                return None;
            }
            if let [(idx, rhs)] = eqs.as_slice() {
                consumed_terms[*idx] = true;
                *src_slot = Some(StepVarSource::Eq(rhs.clone()));
            } else if unchanged == 1 {
                *src_slot = Some(StepVarSource::Unchanged);
            } else {
                match self.shapes[vi] {
                    VarShape::ScalarSlot { mask, .. } => {
                        let [(idx, set_expr)] = ins.as_slice() else { return None };
                        let exact = self.domains.exact_set(set_expr)?;
                        let (smask, fixed) = group_mask_exact(self.groups, &exact)?;
                        if smask == 0 || !fixed.is_empty() || (smask & !mask) != 0 {
                            return None;
                        }
                        let fresh = self.alloc_local();
                        keys.insert(0, (fresh, smask));
                        consumed_terms[*idx] = true;
                        *src_slot = Some(StepVarSource::SlotIn { local: fresh });
                    }
                    VarShape::KeySetFlag { mask, .. } => {
                        let [(idx, set_expr)] = ins.as_slice() else { return None };
                        let (fmask, card) = exact_k_subset_family(self.program, self.cfg, set_expr, self.groups)?;
                        if fmask != mask {
                            return None;
                        }
                        consumed_terms[*idx] = true;
                        *src_slot = Some(StepVarSource::FlagCard { card });
                    }
                    _ => return None,
                }
            }
        }

        let mut pre_guard_parts: Vec<String> = Vec::new();
        for (idx, &(_, mask)) in keys.iter().enumerate() {
            pre_guard_parts.push(format!("(PureTest.inGroup (KeyRef.bound {idx}) {})", self.mask_lean(mask)));
        }

        let mut seen_choose = false;
        let mut seen_choose_assign = false;
        let mut primed_mentioned: BTreeSet<VarId> = BTreeSet::new();
        for (idx, term) in b.terms.iter().enumerate() {
            let has_choose = self.contains_any_choose(term);
            if consumed_terms[idx] {
                if has_choose {
                    seen_choose = true;
                    seen_choose_assign = true;
                }
                collect_primed_vars(term, false, &mut primed_mentioned);
                continue;
            }
            let term = if let ExprKind::Builtin { op: B::Unchanged, args } = &*term.kind {
                let [arg] = args.as_slice() else { return None };
                match self.core_frames(arg)? {
                    Some(core_arg) => Expr::new(ExprKind::Builtin { op: B::Unchanged, args: vec![core_arg] }, term.span),
                    None => continue,
                }
            } else {
                term.clone()
            };
            // A first primed LHS equality `v' = rhs` or fresh `UNCHANGED` frame on `VarShape::Core`
            // variables (with no `CHOOSE` and `v'` never constrained earlier) always binds `v'` and
            // cannot suppress an earlier `CHOOSE` error. Any guard after a choice-bearing assignment
            // (even if the guard itself contains `CHOOSE`) must be refused because `preGuard` and
            // `postGuard` run before `writes`/`slotWrites`.
            let is_fresh_core_assign = !has_choose
                && match &*term.kind {
                    ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 => variable(&args[0], true).is_some_and(|v| {
                        matches!(self.shapes.get(v.idx()), Some(VarShape::Core))
                            && !primed_mentioned.contains(&v)
                            && !mentions_primed_var(&args[1], false, v)
                    }),
                    ExprKind::Builtin { op: B::Unchanged, args } if args.len() == 1 => {
                        let mut frame_vars = Vec::new();
                        collect_unchanged_vars(&args[0], &mut frame_vars);
                        let unique: BTreeSet<VarId> = frame_vars.iter().copied().collect();
                        !frame_vars.is_empty()
                            && unique.len() == frame_vars.len()
                            && unique
                                .iter()
                                .all(|v| matches!(self.shapes.get(v.idx()), Some(VarShape::Core)) && !primed_mentioned.contains(v))
                    }
                    _ => false,
                };
            collect_primed_vars(&term, false, &mut primed_mentioned);
            if seen_choose_assign && !is_fresh_core_assign {
                return None;
            }
            if has_choose {
                seen_choose = true;
                choice_guard_exprs.push(term);
            } else if seen_choose && !is_fresh_core_assign {
                return None;
            } else {
                pure_guard_exprs.push(term);
            }
        }

        let base_aux = AuxScope::default();
        let mut empty_flag_guards = Vec::new();
        let mut empty_msg_guards = Vec::new();
        let mut uniform_guards = Vec::new();

        for gexpr in &pure_guard_exprs {
            let mut flat = Vec::new();
            flatten_top_and(gexpr, &mut flat);
            for sub in flat {
                self.inspect_uniform_guard(sub, &keys, &base_aux, &mut uniform_guards);
                let pt = self.pure_test(sub, &keys, &base_aux)?;
                record_empty_guards(&pt, self.groups.len(), &mut empty_flag_guards, &mut empty_msg_guards);
                pre_guard_parts.push(pt);
            }
        }

        let mut pre_guard = "(PureTest.truth true)".to_owned();
        for part in pre_guard_parts {
            pre_guard = if pre_guard == "(PureTest.truth true)" { part } else { bounded(format!("(PureTest.conj {pre_guard} {part})"))? };
        }

        Some(PreparedStepGuards { keys, var_sources, pre_guard, empty_flag_guards, empty_msg_guards, uniform_guards, choice_guard_exprs })
    }

    #[allow(clippy::too_many_arguments)] // updates the per-shape step accumulators against the final post-choice scope
    fn lower_var_step_update(
        &mut self,
        var: VarId,
        prep: &PreparedStepGuards,
        rhs_opt: Option<&Expr>,
        cur_keys: &[(LocalId, GroupMask)],
        cur_aux: &AuxScope,
        no_choices: bool,
        writes: &mut Vec<String>,
        slot_writes: &mut Vec<String>,
        flag_steps: &mut [FlagStepKind],
        msg_steps: &mut [MsgStepKind],
    ) -> Option<()> {
        match self.shapes[var.idx()].clone() {
            VarShape::Core => {}
            VarShape::FixedMap { mask, map_id } => {
                if let Some(rhs) = rhs_opt {
                    self.emit_map_step(var, map_id, mask, rhs, cur_keys, cur_aux, writes)?;
                }
            }
            VarShape::ScalarSlot { mask, has_fixed, slot_id } => match prep.var_sources[var.idx()].as_ref()? {
                StepVarSource::Unchanged => {}
                StepVarSource::Eq(_) => {
                    if let Some(rhs) = rhs_opt {
                        let cse = self.choice_slot_expr(rhs, mask, has_fixed, cur_keys, cur_aux)?;
                        slot_writes.push(format!("⟨⟨{slot_id}, by decide⟩, {cse}⟩"));
                    }
                }
                StepVarSource::SlotIn { local } => {
                    let cur_pos = cur_keys.iter().position(|(l, _)| l == local)?;
                    slot_writes.push(format!("⟨⟨{slot_id}, by decide⟩, (ChoiceSlotExpr.ref (KeyRef.bound {cur_pos}))⟩"));
                }
                StepVarSource::FlagCard { .. } => return None,
            },
            VarShape::KeySetFlag { mask, flag_id } => match prep.var_sources[var.idx()].as_ref()? {
                StepVarSource::Unchanged => {}
                StepVarSource::Eq(_) => {
                    if let Some(rhs) = rhs_opt {
                        flag_steps[flag_id] = self.lower_keyset_flag_step(var, mask, rhs, cur_keys, cur_aux)?;
                    }
                }
                StepVarSource::FlagCard { card } => {
                    flag_steps[flag_id] = FlagStepKind::Cardinal { mask, card: *card };
                }
                StepVarSource::SlotIn { .. } => return None,
            },
            VarShape::BoolMapFlag { mask, flag_id } => {
                if let Some(rhs) = rhs_opt {
                    flag_steps[flag_id] = self.lower_bool_map_flag_step(var, mask, flag_id, rhs, cur_keys, cur_aux)?;
                }
            }
            VarShape::MsgSet { mask, msg_id, fields, key_field, val_field } => {
                if let Some(rhs) = rhs_opt {
                    msg_steps[msg_id] = self.lower_msg_step(
                        var,
                        mask,
                        msg_id,
                        &fields,
                        &key_field,
                        val_field.as_ref(),
                        rhs,
                        cur_keys,
                        cur_aux,
                        &prep.empty_msg_guards,
                        &prep.uniform_guards,
                        no_choices,
                    )?;
                }
            }
        }
        Some(())
    }

    fn hoist_branch_choices(
        &mut self,
        e: &Expr,
        cur_keys: &mut Vec<(LocalId, GroupMask)>,
        cur_aux: &mut AuxScope,
        choices: &mut Vec<String>,
        cache: &mut Vec<(Expr, Expr)>,
    ) -> Option<Expr> {
        let mut cur = replace_cached_choices(e, cache, self.fold_vars);
        while self.contains_any_choose(&cur) {
            let orig_sub = find_first_choice_node(&cur, self.fold_vars)?;
            match self.extract_one_choice(&cur, cur_keys, cur_aux)? {
                ExtractedChoice::Fold { mask, filter, term, hole, replaced } => {
                    choices.push(format!("(BranchChoice.foldInt {} {filter} {term})", self.mask_lean(mask)));
                    cur_aux.fold_ints.insert(0, hole);
                    cache.push((orig_sub, Expr::new(ExprKind::Local(hole), e.span)));
                    cur = replace_cached_choices(&replaced, cache, self.fold_vars);
                }
                ExtractedChoice::Proj { pk, hole, replaced } => {
                    choices.push(format!("(BranchChoice.projVal {pk})"));
                    cur_aux.proj_vals.insert(0, hole);
                    cache.push((orig_sub, Expr::new(ExprKind::Local(hole), e.span)));
                    cur = replace_cached_choices(&replaced, cache, self.fold_vars);
                }
                ExtractedChoice::Unique { uk, mask, hole, replaced } => {
                    choices.push(format!("(BranchChoice.uniqueKey {uk})"));
                    cur_keys.insert(0, (hole, mask));
                    cache.push((orig_sub, Expr::new(ExprKind::Local(hole), e.span)));
                    cur = replace_cached_choices(&replaced, cache, self.fold_vars);
                }
            }
            if choices.len() > 32 {
                return None;
            }
        }
        Some(cur)
    }

    #[allow(clippy::too_many_arguments)] // lowers a FixedMap whole-map or multi-key EXCEPT assignment into Write items
    fn emit_map_step(
        &mut self,
        var: VarId,
        map_id: usize,
        mask: GroupMask,
        rhs: &Expr,
        keys: &[(LocalId, GroupMask)],
        aux: &AuxScope,
        writes: &mut Vec<String>,
    ) -> Option<()> {
        match &*rhs.kind {
            ExprKind::FnConstruct { bounds, body } => {
                let [Bound { vars: BoundVars::Many(ids), set }] = bounds.as_slice() else { return None };
                let [id] = ids.as_slice() else { return None };
                let exact = self.domains.exact_set(set)?;
                let (bmask, fixed) = group_mask_exact(self.groups, &exact)?;
                if bmask != mask || !fixed.is_empty() {
                    return None;
                }
                let mut scope = keys.to_vec();
                scope.insert(0, (*id, mask));
                let cexpr = self.choice_expr(body, &scope, aux)?;
                writes.push(format!("(Write.all ⟨{map_id}, by decide⟩ {} {cexpr})", self.mask_lean(mask)));
                Some(())
            }
            ExprKind::Except { base, updates } => {
                if variable(base, false) != Some(var) || updates.is_empty() {
                    return None;
                }
                let mut grouped: Vec<(KeyRef, Vec<(Vec<ExceptKey>, Expr)>)> = Vec::new();
                for (path, val) in updates {
                    let (ExceptKey::Index(args), rest) = path.split_first()? else { return None };
                    let [idx_expr] = args.as_slice() else { return None };
                    let (kref, kmask, _) = self.key_ref(idx_expr, keys, aux)?;
                    if (kmask & !mask) != 0 {
                        return None;
                    }
                    if rest.is_empty() {
                        grouped.push((kref, vec![(vec![], val.clone())]));
                    } else if let Some((_, existing)) = grouped.iter_mut().find(|(k, _)| *k == kref) {
                        existing.push((rest.to_vec(), val.clone()));
                    } else {
                        grouped.push((kref, vec![(rest.to_vec(), val.clone())]));
                    }
                }
                if grouped.len() > 1 && grouped.iter().any(|(_, patches)| patches.iter().any(|(r, _)| !r.is_empty())) {
                    return None;
                }
                for (kref, patches) in grouped {
                    let full_val = if patches.len() == 1 && patches[0].0.is_empty() {
                        patches[0].1.clone()
                    } else {
                        let kexpr = self.key_ref_expr(kref, keys, rhs.span)?;
                        let entry =
                            Expr::new(ExprKind::FnApp { func: Expr::new(ExprKind::Var(var), rhs.span), args: vec![kexpr] }, rhs.span);
                        Expr::new(ExprKind::Except { base: entry, updates: patches }, rhs.span)
                    };
                    let cexpr = self.choice_expr(&full_val, keys, aux)?;
                    writes.push(format!("(Write.point ⟨{map_id}, by decide⟩ {} {cexpr})", kref.lean()));
                }
                Some(())
            }
            _ => None,
        }
    }

    fn lower_keyset_flag_step(
        &mut self,
        var: VarId,
        mask: GroupMask,
        rhs: &Expr,
        keys: &[(LocalId, GroupMask)],
        aux: &AuxScope,
    ) -> Option<FlagStepKind> {
        match &*rhs.kind {
            ExprKind::SetEnum(es) if es.is_empty() => return Some(FlagStepKind::Clear),
            ExprKind::SetEnum(es) if es.len() == 1 => {
                let (kref, kmask, _) = self.key_ref(&es[0], keys, aux)?;
                if (kmask & !mask) != 0 {
                    return None;
                }
                return Some(FlagStepKind::Singleton { mask: kmask, target: kref });
            }
            ExprKind::Builtin { op: B::Cup, args } if args.len() == 2 => {
                let single_opt = if variable(&args[0], false) == Some(var) {
                    Some(&args[1])
                } else if variable(&args[1], false) == Some(var) {
                    Some(&args[0])
                } else {
                    None
                };
                if let Some(s) = single_opt {
                    if let ExprKind::SetEnum(es) = &*s.kind {
                        if let [item] = es.as_slice() {
                            let (kref, kmask, _) = self.key_ref(item, keys, aux)?;
                            if (kmask & !mask) == 0 {
                                return Some(FlagStepKind::SetPoint { mask: kmask, target: kref });
                            }
                        }
                    }
                }
            }
            ExprKind::Builtin { op: B::SetMinus, args } if args.len() == 2 => {
                if variable(&args[0], false) == Some(var) {
                    if let ExprKind::SetEnum(es) = &*args[1].kind {
                        if let [item] = es.as_slice() {
                            let (kref, _, _) = self.key_ref(item, keys, aux)?;
                            return Some(FlagStepKind::ClearPoint { target: kref });
                        }
                    }
                }
            }
            _ => {}
        }
        let fresh = self.alloc_local();
        let mut scope = keys.to_vec();
        scope.insert(0, (fresh, mask));
        let pred = self.key_in_set_pure(KeyRef::Bound(0), mask, rhs, &scope, aux)?;
        Some(FlagStepKind::GeneralAll { mask, pred })
    }

    fn lower_bool_map_flag_step(
        &mut self,
        var: VarId,
        mask: GroupMask,
        flag_id: usize,
        rhs: &Expr,
        keys: &[(LocalId, GroupMask)],
        aux: &AuxScope,
    ) -> Option<FlagStepKind> {
        match &*rhs.kind {
            ExprKind::FnConstruct { bounds, body } => {
                let [Bound { vars: BoundVars::Many(ids), set }] = bounds.as_slice() else { return None };
                let [id] = ids.as_slice() else { return None };
                let exact = self.domains.exact_set(set)?;
                let (bmask, fixed) = group_mask_exact(self.groups, &exact)?;
                if bmask != mask || !fixed.is_empty() {
                    return None;
                }
                if matches!(&*body.kind, ExprKind::Bool(false)) {
                    return Some(FlagStepKind::Clear);
                }
                let mut scope = keys.to_vec();
                scope.insert(0, (*id, mask));
                let pred = self.pure_test(body, &scope, aux)?;
                Some(FlagStepKind::GeneralAll { mask, pred })
            }
            ExprKind::Except { base, updates } if variable(base, false) == Some(var) && updates.len() == 1 => {
                let (path, val) = &updates[0];
                let [ExceptKey::Index(args)] = path.as_slice() else { return None };
                let [idx_expr] = args.as_slice() else { return None };
                let (kref, kmask, _) = self.key_ref(idx_expr, keys, aux)?;
                if (kmask & !mask) != 0 {
                    return None;
                }
                match &*val.kind {
                    ExprKind::Bool(false) => Some(FlagStepKind::ClearPoint { target: kref }),
                    ExprKind::Bool(true) => Some(FlagStepKind::SetPoint { mask: kmask, target: kref }),
                    _ => {
                        let _ = self.pure_test(val, keys, aux)?;
                        let shifted_kref = match kref {
                            KeyRef::Bound(i) => KeyRef::Bound(i + 1),
                            other => other,
                        };
                        let mut scope = keys.to_vec();
                        let fresh = self.alloc_local();
                        scope.insert(0, (fresh, mask));
                        let val_pt_shifted = self.pure_test(val, &scope, aux)?;
                        let eq = format!("(PureTest.equal (KeyRef.bound 0) {})", shifted_kref.lean());
                        let old = format!("(PureTest.flag ⟨{flag_id}, by decide⟩ (KeyRef.bound 0))");
                        let pred =
                            format!("(PureTest.disj (PureTest.conj {eq} {val_pt_shifted}) (PureTest.conj (PureTest.neg {eq}) {old}))");
                        Some(FlagStepKind::GeneralAll { mask, pred })
                    }
                }
            }
            _ => None,
        }
    }

    #[allow(clippy::too_many_arguments)] // lowers MsgSet clear, comprehension, or singleton union against branch guard facts
    fn lower_msg_step(
        &mut self,
        var: VarId,
        mask: GroupMask,
        msg_id: usize,
        fields: &[Arc<str>],
        key_field: &Arc<str>,
        val_field: Option<&Arc<str>>,
        rhs: &Expr,
        keys: &[(LocalId, GroupMask)],
        aux: &AuxScope,
        empty_msg_guards: &[usize],
        uniform_guards: &[(usize, String)],
        no_choices: bool,
    ) -> Option<MsgStepKind> {
        match &*rhs.kind {
            ExprKind::SetEnum(es) if es.is_empty() => return Some(MsgStepKind::Clear),
            ExprKind::SetMap { expr: rec_expr, bounds } => {
                let [Bound { vars: BoundVars::Many(ids), set: dom_set }] = bounds.as_slice() else { return None };
                let [p_id] = ids.as_slice() else { return None };
                let exact = self.domains.exact_set(dom_set)?;
                let (smask, fixed) = group_mask_exact(self.groups, &exact)?;
                if smask == 0 || !fixed.is_empty() || (smask & !mask) != 0 {
                    return None;
                }
                let ExprKind::Record(fs) = &*rec_expr.kind else { return None };
                let mut fnames: Vec<Arc<str>> = fs.iter().map(|(k, _)| k.clone()).collect();
                fnames.sort();
                if fnames != fields {
                    return None;
                }
                let (_, kexpr) = fs.iter().find(|(k, _)| k == key_field)?;
                if !matches!(&*kexpr.kind, ExprKind::Local(l) if l == p_id) {
                    return None;
                }
                let val_pure = match val_field {
                    None => self.dummy_pure_expr(),
                    Some(vf) => {
                        let (_, vexpr) = fs.iter().find(|(k, _)| k == vf)?;
                        if mentions_local(vexpr, *p_id) {
                            return None;
                        }
                        self.pure_expr(vexpr, keys, aux)?
                    }
                };
                let meta_rec = build_meta_record(fs, key_field, val_field, rec_expr.span);
                let mut scope = keys.to_vec();
                scope.insert(0, (*p_id, smask));
                let meta_pure = self.pure_expr(&meta_rec, &scope, aux)?;
                return Some(MsgStepKind::ComprehensionAll { mask: smask, meta_expr: meta_pure, val_expr: val_pure });
            }
            ExprKind::Builtin { op: B::Cup, args } if args.len() == 2 => {
                let single_opt = if variable(&args[0], false) == Some(var) {
                    Some(&args[1])
                } else if variable(&args[1], false) == Some(var) {
                    Some(&args[0])
                } else {
                    None
                };
                let ExprKind::SetEnum(es) = &*single_opt?.kind else { return None };
                let [rec_expr] = es.as_slice() else { return None };
                let ExprKind::Record(fs) = &*rec_expr.kind else { return None };
                let mut fnames: Vec<Arc<str>> = fs.iter().map(|(k, _)| k.clone()).collect();
                fnames.sort();
                if fnames != fields {
                    return None;
                }
                let (_, kexpr) = fs.iter().find(|(k, _)| k == key_field)?;
                let (kref, kmask, _) = self.key_ref(kexpr, keys, aux)?;
                if (kmask & !mask) != 0 {
                    return None;
                }
                let meta_rec = build_meta_record(fs, key_field, val_field, rec_expr.span);
                let meta_pure = self.pure_expr(&meta_rec, keys, aux)?;
                match val_field {
                    None => {
                        let const_id = self.intern_const_val(None, "unit".into());
                        return Some(MsgStepKind::AddConst { mask: kmask, target: kref, meta_expr: meta_pure, const_id });
                    }
                    Some(vf) => {
                        let (_, vexpr) = fs.iter().find(|(k, _)| k == vf)?;
                        if !mentions_any_var(vexpr)
                            && !mentions_any_local(vexpr)
                            && independent(&self.eval_expr_domain(vexpr, &Locals::new()), self.all_keys)
                        {
                            let const_id = self.intern_const_val(Some(vexpr), format!("{vexpr:#?}"));
                            return Some(MsgStepKind::AddConst { mask: kmask, target: kref, meta_expr: meta_pure, const_id });
                        }
                        let val_pure = self.pure_expr(vexpr, keys, aux)?;
                        if empty_msg_guards.contains(&msg_id) {
                            return Some(MsgStepKind::AddWhenEmpty { mask: kmask, target: kref, meta_expr: meta_pure, val_expr: val_pure });
                        }
                        if no_choices {
                            if let Some(ug_idx) = uniform_guards.iter().position(|(m, vp)| *m == msg_id && vp == &val_pure) {
                                return Some(MsgStepKind::AddMatchingGuard { mask: kmask, target: kref, meta_expr: meta_pure, ug_idx });
                            }
                        }
                        return Some(MsgStepKind::AddGeneral { mask: kmask, target: kref, meta_expr: meta_pure, val_expr: val_pure });
                    }
                }
            }
            _ => {}
        }
        None
    }

    fn dummy_pure_expr(&mut self) -> String {
        let id = self.atoms.len();
        self.atoms.push("Dummy unit payload PureExpr".into());
        format!("(PureExpr.leaf ⟨{id}, [], [], [], []⟩)")
    }

    fn core_frames(&self, e: &Expr) -> Option<Option<Expr>> {
        match &*e.kind {
            ExprKind::Var(v) => {
                if self.is_non_core(*v) {
                    Some(None)
                } else {
                    Some(Some(e.clone()))
                }
            }
            ExprKind::Tuple(es) => {
                let mut kept = Vec::new();
                for item in es {
                    if let Some(c) = self.core_frames(item)? {
                        kept.push(c);
                    }
                }
                if kept.is_empty() {
                    Some(None)
                } else {
                    Some(Some(Expr::new(ExprKind::Tuple(kept), e.span)))
                }
            }
            _ => None,
        }
    }
}

fn flatten_top_and<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
    match &*e.kind {
        ExprKind::And(es) => es.iter().for_each(|x| flatten_top_and(x, out)),
        _ => out.push(e),
    }
}

fn build_meta_record(fs: &[(Arc<str>, Expr)], key_field: &Arc<str>, val_field: Option<&Arc<str>>, span: Span) -> Expr {
    let kept: Vec<(Arc<str>, Expr)> = fs.iter().filter(|(k, _)| k != key_field && val_field != Some(k)).cloned().collect();
    if kept.is_empty() {
        Expr::new(ExprKind::Num(0), span)
    } else {
        Expr::new(ExprKind::Record(kept), span)
    }
}

fn collect_unchanged_vars(e: &Expr, out: &mut Vec<VarId>) {
    match &*e.kind {
        ExprKind::Var(v) => out.push(*v),
        ExprKind::Tuple(es) => {
            for item in es {
                collect_unchanged_vars(item, out);
            }
        }
        _ => {}
    }
}

pub(super) fn val_bound_to_hint(b: &ValBound) -> Option<IntBoundHint> {
    match b {
        ValBound::Int(ib) => {
            let (lo, hi) = ib.fits_i32()?;
            Some(IntBoundHint::Int(lo as i32, hi as i32))
        }
        ValBound::Map(inner) => Some(IntBoundHint::Map(Box::new(val_bound_to_hint(inner)?))),
        ValBound::Set(inner) => Some(IntBoundHint::Set(Box::new(val_bound_to_hint(inner)?))),
        ValBound::Record(fs) => {
            let map: BTreeMap<Arc<str>, IntBoundHint> = fs.iter().filter_map(|(k, v)| Some((k.clone(), val_bound_to_hint(v)?))).collect();
            (!map.is_empty()).then_some(IntBoundHint::Record(map))
        }
        ValBound::Bottom | ValBound::Top => None,
    }
}
