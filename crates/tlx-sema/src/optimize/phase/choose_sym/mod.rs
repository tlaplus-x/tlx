//! Certified choice-irrelevant automatic symmetry (`ChooseSymCertificate.lean`).
//!
//! Proves symmetry for `CHOOSE`-bearing TLA+ specifications whose choices are:
//! 1. Unique-witness key choices (`x = target`, `ChooseOne` `Q(x) /\ \A y : Q(y) => y = x`,
//!    or inductively proved at-most-one active key in a `KeySet` / boolean flag map),
//! 2. Projected value-invariant choices (`proj(CHOOSE x \in S : P(x))` over key-free-value
//!    record comprehensions, predicate-pinned `.val`, or inductively proved constant/uniform
//!    `.val` message sets),
//! 3. Commutative-associative recursive `CHOOSE` integer set-sum folds (`chooseFoldAdd`),
//!
//! while preserving empty-witness `CHOOSE` errors (`none`) and refusing partial/unsound choices.

mod bounds;
mod domain_infer;
mod expressions;
mod invariant;
mod output;
mod pure_expr;
mod step;

use super::domain::{Atom, Domain, Domains, Locals};
use super::sym_groups::{subst_local, ActionKeyRef, GroupInfo, GroupMask, KeyRef};
use super::sym_norm::SymNormalizer;
use super::{max_local, mentions_local, variable, Branch};
use crate::{builtins::Builtin as B, hir::*, visit, Program};
use bounds::{infer_model_bounds, LocalBounds, ModelBounds};
use domain_infer::{
    classify_var, collect_projected_fields, exact_k_subset_family, expr_has_choose, group_mask_exact, independent, mask_atoms_domain,
    max_local_in_branches, split_branches, validate_groups, VarShape,
};
use expressions::ast_equiv;
use invariant::{FlagInitKind, InvPlan, MsgInitKind};
use pure_expr::AuxScope;
use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;
use step::{val_bound_to_hint, StepCase};
use tlx_front::cfg::Config;

struct InitCase {
    flag_inits: Vec<FlagInitKind>,
    msg_inits: Vec<MsgInitKind>,
}

struct Emitter<'a> {
    program: &'a Program,
    cfg: &'a Config,
    domains: &'a Domains,
    model_bounds: ModelBounds,
    totality: &'a super::sym_totality::TotalityChecker<'a>,
    step_locals: Locals,
    step_local_bounds: LocalBounds,
    step_check_env: super::sym_totality::CheckEnv,
    fold_vars: &'a HashMap<LocalId, Option<Expr>>,
    groups: &'a [GroupInfo],
    all_keys: &'a BTreeSet<Atom>,
    shapes: Vec<VarShape>,
    num_maps: usize,
    num_slots: usize,
    num_flags: usize,
    num_msgs: usize,
    atoms: Vec<String>,
    fixed_atoms: Vec<String>,
    const_vals: Vec<(Option<Expr>, String)>,
    init_metas: usize,
    init_core_vals: usize,
    next_local: u32,
    used_choose: bool,
    req_at_most_one_flags: BTreeSet<(usize, GroupMask)>,
    req_uniform_msgs: BTreeSet<usize>,
}

/// Generate a connected `ChooseSymCertificate.lean` proof for a disjoint product
/// of full permutation groups on a `CHOOSE`-bearing model. Returns `None` if no
/// `CHOOSE` is used or if any choice, invariant, or operation is unsupported.
pub fn choose_symmetry_certificate(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    observations: &[Expr],
    raw_groups: &[Vec<String>],
) -> Option<String> {
    choose_symmetry_certificate_with_spec(program, cfg, init, next, super::CheckSpec::invariants_only(observations), raw_groups)
}

/// Generate a connected `ChooseSymCertificate.lean` proof covering invariants,
/// init properties, state constraints, action constraints, and action properties.
pub fn choose_symmetry_certificate_with_spec(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: super::CheckSpec<'_>,
    raw_groups: &[Vec<String>],
) -> Option<String> {
    if !super::cfg_constants_supported(program, cfg) {
        return None;
    }
    let (groups, all_keys) = validate_groups(raw_groups)?;
    let mut norm = SymNormalizer::for_choose_with_config(program, cfg);
    let initial = norm.normalize(init)?;
    let init_branches = split_branches(&initial)?;
    let next_norm = norm.normalize(next)?;
    let steps = split_branches(&next_norm)?;
    let owned_spec = spec.try_map(|o| norm.normalize(o))?;
    let norm_spec = owned_spec.as_spec();

    if norm_spec.action_constraints.iter().chain(norm_spec.action_props).any(expr_has_choose) {
        return None;
    }
    if norm.fold_vars.is_empty()
        && !expr_has_choose(&initial)
        && !expr_has_choose(&next_norm)
        && !norm_spec.all_state_preds().any(expr_has_choose)
    {
        return None;
    }
    if init_branches.is_empty() || steps.is_empty() {
        return None;
    }

    let domains = Domains::infer_with_folds(program, cfg, &init_branches, &steps, &norm.fold_vars)?;

    let mut proj_fields: HashMap<VarId, BTreeSet<Arc<str>>> = HashMap::new();
    collect_projected_fields(&initial, &norm.fold_vars, &mut proj_fields);
    collect_projected_fields(&next_norm, &norm.fold_vars, &mut proj_fields);
    for o in norm_spec.all_exprs() {
        collect_projected_fields(o, &norm.fold_vars, &mut proj_fields);
    }

    let mut shapes = Vec::with_capacity(domains.vars.len());
    let mut num_maps = 0usize;
    let mut num_slots = 0usize;
    let mut num_flags = 0usize;
    let mut num_msgs = 0usize;
    let mut used_groups: GroupMask = 0;

    for (vi, d) in domains.vars.iter().enumerate() {
        let var = VarId(vi as u32);
        let shape = classify_var(
            &groups,
            &all_keys,
            d,
            proj_fields.get(&var),
            &mut num_maps,
            &mut num_slots,
            &mut num_flags,
            &mut num_msgs,
            &mut used_groups,
        )?;
        shapes.push(shape);
    }
    let all_mask: GroupMask = (1u16 << groups.len()) - 1;
    if (num_maps + num_slots + num_flags + num_msgs) == 0 || used_groups != all_mask {
        return None;
    }

    let (equiv_groups, equiv_all_keys) = super::equiv_sym::validate_groups(raw_groups)?;
    let model_bounds = infer_model_bounds(program, cfg, &domains, &shapes, &norm.fold_vars, &groups, &init_branches, &steps);
    let bound_hints: Vec<Option<super::sym_totality::IntBoundHint>> = model_bounds.vars.iter().map(val_bound_to_hint).collect();
    let totality = super::sym_totality::build_choose_totality_checker(
        program,
        cfg,
        &equiv_groups,
        &equiv_all_keys,
        &initial,
        &next_norm,
        norm_spec,
        &norm.fold_vars,
        &bound_hints,
    )?;

    let next_local = norm
        .local
        .max(max_local_in_branches(&init_branches))
        .max(max_local_in_branches(&steps))
        .max(norm_spec.all_exprs().map(max_local).max().unwrap_or(0))
        + 1;

    let mut e = Emitter {
        program,
        cfg,
        domains: &domains,
        model_bounds,
        totality: &totality,
        step_locals: Locals::new(),
        step_local_bounds: LocalBounds::new(),
        step_check_env: super::sym_totality::CheckEnv::default(),
        fold_vars: &norm.fold_vars,
        groups: &groups,
        all_keys: &all_keys,
        shapes,
        num_maps,
        num_slots,
        num_flags,
        num_msgs,
        atoms: vec![],
        fixed_atoms: vec![],
        const_vals: vec![],
        init_metas: 0,
        init_core_vals: 0,
        next_local,
        used_choose: false,
        req_at_most_one_flags: BTreeSet::new(),
        req_uniform_msgs: BTreeSet::new(),
    };

    norm.attach_const_subst(e.finish(&initial, &init_branches, &steps, norm_spec)?)
}

pub(super) fn mentions_any_var(e: &Expr) -> bool {
    if matches!(&*e.kind, ExprKind::Var(_)) {
        return true;
    }
    let mut found = false;
    visit::children(e, &mut |c| found |= mentions_any_var(c));
    found
}

pub(super) fn mentions_any_local(e: &Expr) -> bool {
    if matches!(&*e.kind, ExprKind::Local(_)) {
        return true;
    }
    let mut found = false;
    visit::children(e, &mut |c| found |= mentions_any_local(c));
    found
}

fn mentions_free_local(e: &Expr, bound: &BTreeSet<LocalId>) -> bool {
    match &*e.kind {
        ExprKind::Local(l) => !bound.contains(l),
        ExprKind::Quant { bounds, body, .. } | ExprKind::FnConstruct { bounds, body } | ExprKind::SetMap { expr: body, bounds } => {
            let mut scope = bound.clone();
            for b in bounds {
                if mentions_free_local(&b.set, &scope) {
                    return true;
                }
                scope.extend(b.vars.locals().iter().copied());
            }
            mentions_free_local(body, &scope)
        }
        ExprKind::SetFilter { bound: b, pred } => {
            if mentions_free_local(&b.set, bound) {
                return true;
            }
            let mut scope = bound.clone();
            scope.extend(b.vars.locals().iter().copied());
            mentions_free_local(pred, &scope)
        }
        ExprKind::Choose { vars, set, body } => {
            if set.as_ref().is_some_and(|s| mentions_free_local(s, bound)) {
                return true;
            }
            let mut scope = bound.clone();
            scope.extend(vars.locals().iter().copied());
            mentions_free_local(body, &scope)
        }
        ExprKind::Lambda { params, body } => {
            let mut scope = bound.clone();
            scope.extend(params.iter().copied());
            mentions_free_local(body, &scope)
        }
        _ => {
            let mut found = false;
            visit::children(e, &mut |c| found |= mentions_free_local(c, bound));
            found
        }
    }
}

fn count_unchanged_var(e: &Expr, v: VarId) -> usize {
    match &*e.kind {
        ExprKind::Var(x) => usize::from(*x == v),
        ExprKind::Tuple(es) => es.iter().map(|x| count_unchanged_var(x, v)).sum(),
        _ => 0,
    }
}

impl Emitter<'_> {
    fn is_non_core(&self, v: VarId) -> bool {
        !matches!(self.shapes[v.idx()], VarShape::Core)
    }

    fn alloc_local(&mut self) -> LocalId {
        let id = LocalId(self.next_local);
        self.next_local += 1;
        id
    }

    fn mask_lean(&self, mask: GroupMask) -> String {
        let all_mask: GroupMask = (1u16 << self.groups.len()) - 1;
        if mask == all_mask {
            return "(fun _ => true)".into();
        }
        if mask == 0 {
            return "(fun _ => false)".into();
        }
        let mut arms = String::new();
        for gi in 0..self.groups.len() {
            if (mask & (1 << gi)) != 0 {
                arms.push_str(&format!(" | {gi} => true"));
            }
        }
        format!("(fun g => match g.val with{arms} | _ => false)")
    }

    fn mask_domain(&self, mask: GroupMask) -> Domain {
        mask_atoms_domain(self.groups, mask)
    }

    fn eval_expr_domain(&self, e: &Expr, locals: &Locals) -> Domain {
        self.domains.value(e, locals)
    }

    fn eval_expr_element_domain(&self, e: &Expr, locals: &Locals) -> Domain {
        self.domains.element_domain(e, locals, 0)
    }

    fn key_ref_expr(&self, kref: KeyRef, keys: &[(LocalId, GroupMask)], span: Span) -> Option<Expr> {
        match kref {
            KeyRef::Bound(idx) => {
                let (lid, _) = keys.get(idx)?;
                Some(Expr::new(ExprKind::Local(*lid), span))
            }
            KeyRef::Slot(slot_id) => {
                let (vi, _) = self
                    .shapes
                    .iter()
                    .enumerate()
                    .find(|(_, sh)| matches!(sh, VarShape::ScalarSlot { slot_id: s, .. } if *s == slot_id))?;
                Some(Expr::new(ExprKind::Var(VarId(vi as u32)), span))
            }
            KeyRef::Fixed(_) => None,
        }
    }

    fn intern_const_val(&mut self, expr_opt: Option<&Expr>, doc: String) -> usize {
        let found = self.const_vals.iter().position(|(existing, _)| match (existing.as_ref(), expr_opt) {
            (None, None) => true,
            (Some(a), Some(b)) => ast_equiv(a, b, self.fold_vars),
            _ => false,
        });
        found.unwrap_or_else(|| {
            let idx = self.const_vals.len();
            self.const_vals.push((expr_opt.cloned(), doc));
            idx
        })
    }

    fn collect_var_terms(&self, b: &Branch, v: VarId, primed: bool) -> (Vec<(usize, Expr)>, Vec<(usize, Expr)>, usize) {
        let mut eqs = Vec::new();
        let mut ins = Vec::new();
        let mut unchanged = 0usize;
        for (idx, term) in b.terms.iter().enumerate() {
            match &*term.kind {
                ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 && variable(&args[0], primed) == Some(v) => {
                    eqs.push((idx, args[1].clone()));
                }
                ExprKind::Builtin { op: B::In, args } if args.len() == 2 && variable(&args[0], primed) == Some(v) => {
                    ins.push((idx, args[1].clone()));
                }
                ExprKind::Builtin { op: B::Unchanged, args } if primed && args.len() == 1 => {
                    unchanged += count_unchanged_var(&args[0], v);
                }
                _ => {}
            }
        }
        (eqs, ins, unchanged)
    }

    pub(super) fn lower_init_branch(&mut self, ib: &Branch) -> Option<InitCase> {
        let mut keys: Vec<(LocalId, GroupMask)> = Vec::new();
        let locals = self.domains.locals(&ib.bounds);
        for bnd in &ib.bounds {
            let BoundVars::Many(ids) = &bnd.vars else { return None };
            if let Some(exact) = self.domains.exact_set(&bnd.set) {
                let (mask, fixed) = group_mask_exact(self.groups, &exact)?;
                if mask != 0 && fixed.is_empty() {
                    for &id in ids {
                        keys.insert(0, (id, mask));
                    }
                    continue;
                }
            }
            for id in ids {
                if !independent(locals.get(id)?, self.all_keys) {
                    return None;
                }
            }
        }

        let mut flag_inits = vec![FlagInitKind::Empty; self.num_flags];
        let mut msg_inits = vec![MsgInitKind::Empty; self.num_msgs];
        let mut consumed_terms = vec![false; ib.terms.len()];
        let aux = AuxScope::default();

        for vi in 0..self.shapes.len() {
            let var = VarId(vi as u32);
            let (eqs, ins, _) = self.collect_var_terms(ib, var, false);
            match self.shapes[vi].clone() {
                VarShape::Core => {
                    if eqs.len() == 1 {
                        let (idx, rhs) = &eqs[0];
                        let _ = self.pure_expr(rhs, &keys, &aux)?;
                        consumed_terms[*idx] = true;
                    }
                }
                VarShape::FixedMap { mask, map_id } => {
                    let [(idx, rhs)] = eqs.as_slice() else { return None };
                    let mut dummy_writes = Vec::new();
                    self.emit_map_init(map_id, mask, rhs, &keys, &aux, &mut dummy_writes)?;
                    consumed_terms[*idx] = true;
                }
                VarShape::ScalarSlot { mask, has_fixed, .. } => {
                    if eqs.len() > 1 {
                        return None;
                    }
                    if let [(idx, rhs)] = eqs.as_slice() {
                        let _ = self.choice_slot_expr(rhs, mask, has_fixed, &keys, &aux)?;
                        if self.contains_any_choose(rhs) {
                            return None;
                        }
                        consumed_terms[*idx] = true;
                    } else {
                        let [(idx, set_expr)] = ins.as_slice() else { return None };
                        let exact = self.domains.exact_set(set_expr)?;
                        let (smask, fixed) = group_mask_exact(self.groups, &exact)?;
                        if smask == 0 || (!fixed.is_empty() && !has_fixed) || (smask & !mask) != 0 {
                            return None;
                        }
                        consumed_terms[*idx] = true;
                    }
                }
                VarShape::KeySetFlag { mask, flag_id } => {
                    if eqs.len() > 1 {
                        return None;
                    }
                    if let [(idx, rhs)] = eqs.as_slice() {
                        flag_inits[flag_id] = self.lower_keyset_flag_init(mask, rhs, &keys)?;
                        consumed_terms[*idx] = true;
                    } else {
                        let [(idx, set_expr)] = ins.as_slice() else { return None };
                        let (fmask, card) = exact_k_subset_family(self.program, self.cfg, set_expr, self.groups)?;
                        if fmask != mask {
                            return None;
                        }
                        flag_inits[flag_id] = FlagInitKind::Cardinal { mask, card };
                        consumed_terms[*idx] = true;
                    }
                }
                VarShape::BoolMapFlag { mask, flag_id } => {
                    let [(idx, rhs)] = eqs.as_slice() else { return None };
                    flag_inits[flag_id] = self.lower_bool_map_flag_init(mask, rhs, &keys)?;
                    consumed_terms[*idx] = true;
                }
                VarShape::MsgSet { mask, msg_id, fields, key_field, val_field } => {
                    let [(idx, rhs)] = eqs.as_slice() else { return None };
                    msg_inits[msg_id] = self.lower_msg_init(mask, &fields, &key_field, val_field.as_ref(), rhs)?;
                    consumed_terms[*idx] = true;
                }
            }
        }

        for (idx, term) in ib.terms.iter().enumerate() {
            if consumed_terms[idx] || matches!(&*term.kind, ExprKind::Bool(true)) {
                continue;
            }
            // `initSetup` only encodes per-variable initializers and cannot represent extra
            // cross-variable guards (e.g. `~(owner \notin leaders)` on nondeterministic flags).
            return None;
        }

        Some(InitCase { flag_inits, msg_inits })
    }

    fn emit_map_init(
        &mut self,
        map_id: usize,
        mask: GroupMask,
        rhs: &Expr,
        keys: &[(LocalId, GroupMask)],
        aux: &AuxScope,
        writes: &mut Vec<String>,
    ) -> Option<()> {
        let ExprKind::FnConstruct { bounds, body } = &*rhs.kind else { return None };
        let [Bound { vars: BoundVars::Many(ids), set }] = bounds.as_slice() else { return None };
        let [id] = ids.as_slice() else { return None };
        let exact = self.domains.exact_set(set)?;
        let (bmask, fixed) = group_mask_exact(self.groups, &exact)?;
        if bmask != mask || !fixed.is_empty() {
            return None;
        }
        let mut scope = keys.to_vec();
        scope.insert(0, (*id, mask));
        let val = self.pure_expr(body, &scope, aux)?;
        writes.push(format!("(Write.all ⟨{map_id}, by decide⟩ {} (ChoiceExpr.pure {val}))", self.mask_lean(mask)));
        Some(())
    }

    fn lower_keyset_flag_init(&self, mask: GroupMask, rhs: &Expr, keys: &[(LocalId, GroupMask)]) -> Option<FlagInitKind> {
        if let ExprKind::SetEnum(es) = &*rhs.kind {
            if es.is_empty() {
                return Some(FlagInitKind::Empty);
            }
            if let [single] = es.as_slice() {
                if let ExprKind::Local(id) = &*single.kind {
                    let (idx, (_, kmask)) = keys.iter().enumerate().find(|(_, (k, _))| k == id)?;
                    if (*kmask & !mask) == 0 {
                        return Some(FlagInitKind::Singleton { mask: *kmask, key_idx: idx });
                    }
                }
            }
            return None;
        }
        if let Some(exact) = self.domains.exact_set(rhs) {
            let (m, fixed) = group_mask_exact(self.groups, &exact)?;
            if m != 0 && fixed.is_empty() && (m & !mask) == 0 {
                return Some(FlagInitKind::All { mask: m });
            }
        }
        None
    }

    fn lower_bool_map_flag_init(&self, mask: GroupMask, rhs: &Expr, keys: &[(LocalId, GroupMask)]) -> Option<FlagInitKind> {
        let ExprKind::FnConstruct { bounds, body } = &*rhs.kind else { return None };
        let [Bound { vars: BoundVars::Many(ids), set }] = bounds.as_slice() else { return None };
        let [id] = ids.as_slice() else { return None };
        let exact = self.domains.exact_set(set)?;
        let (bmask, fixed) = group_mask_exact(self.groups, &exact)?;
        if bmask != mask || !fixed.is_empty() {
            return None;
        }
        match &*body.kind {
            ExprKind::Bool(false) => Some(FlagInitKind::Empty),
            ExprKind::Bool(true) => Some(FlagInitKind::All { mask }),
            ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 => {
                let other = if matches!(&*args[0].kind, ExprKind::Local(l) if l == id) {
                    &args[1]
                } else if matches!(&*args[1].kind, ExprKind::Local(l) if l == id) {
                    &args[0]
                } else {
                    return None;
                };
                let ExprKind::Local(tid) = &*other.kind else { return None };
                let (idx, (_, kmask)) = keys.iter().enumerate().find(|(_, (k, _))| k == tid)?;
                if (*kmask & !mask) == 0 {
                    Some(FlagInitKind::Singleton { mask: *kmask, key_idx: idx })
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn lower_msg_init(
        &mut self,
        mask: GroupMask,
        fields: &[Arc<str>],
        key_field: &Arc<str>,
        val_field: Option<&Arc<str>>,
        rhs: &Expr,
    ) -> Option<MsgInitKind> {
        if let ExprKind::SetEnum(es) = &*rhs.kind {
            return es.is_empty().then_some(MsgInitKind::Empty);
        }
        let ExprKind::SetMap { expr: rec_expr, bounds } = &*rhs.kind else { return None };
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
        let no_bound = BTreeSet::new();
        for (fname, fexpr) in fs {
            if fname == key_field {
                continue;
            }
            // `MsgInit.eval` (`initMeta` / `initCoreVal`) is a function of `st.core` alone,
            // so neither the comprehension binder `p_id` nor any enclosing `Init` existential
            // witness may occur free in message initialization fields.
            if mentions_free_local(fexpr, &no_bound)
                || self.mentions_non_core(fexpr)
                || self.contains_any_choose(fexpr)
                || !independent(&self.eval_expr_domain(fexpr, &Locals::new()), self.all_keys)
            {
                return None;
            }
        }
        let meta_id = self.init_metas;
        self.init_metas += 1;
        match val_field {
            None => {
                let const_id = self.intern_const_val(None, "unit".into());
                Some(MsgInitKind::ComprehensionConst { mask: smask, meta_id, const_id })
            }
            Some(vf) => {
                let (_, vexpr) = fs.iter().find(|(k, _)| k == vf)?;
                if !mentions_any_var(vexpr) && !mentions_any_local(vexpr) {
                    let const_id = self.intern_const_val(Some(vexpr), format!("{vexpr:#?}"));
                    Some(MsgInitKind::ComprehensionConst { mask: smask, meta_id, const_id })
                } else {
                    let core_id = self.init_core_vals;
                    self.init_core_vals += 1;
                    Some(MsgInitKind::ComprehensionCore { mask: smask, meta_id, core_id })
                }
            }
        }
    }
}
