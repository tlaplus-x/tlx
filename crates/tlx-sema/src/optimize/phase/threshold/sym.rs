//! Connected `ThresholdSymRule` certificate emitter composing in-place
//! threshold-counter saturation (`ThresholdCounterCertificate.lean`) with
//! generic recursive equivariant symmetry (`EquivSymCertificate.lean`) over
//! one shared concrete source model.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Write;
use std::sync::Arc;

use tlx_front::cfg::Config;

use crate::{builtins::Builtin as B, hir::*, optimize::lean::literal, visit, Program};

use super::super::{
    binding, branches_with_if,
    domain::{Atom, Domains},
    equiv_sym::{collect_const_bindings, lower::LowerCtx, output::write_common_header, validate_groups, AtomKey, GroupInfo, GroupMask},
    liveness::sym::expr_alpha_eq,
    normalize::opaque_recursive_def_vars,
    sym_norm::{desugar_except_at, SymNormalizer},
    sym_totality, variable, Branch, CheckSpec, OpenCert,
};
use super::{analyze_counters, atom_nat, build_view, expr_structurally_eq, ordinary_unchanged, required_cap, CounterKind, CounterSpec};

const MAX_TEST_WORK: usize = 200_000;

#[derive(Clone, Debug)]
enum SlotInfo {
    Fixed { cap: i128, atom_id: usize, template: usize, desc: String },
    Sym { cap: i128, off: usize, group: usize, elem: usize, template: usize, desc: String },
}

#[derive(Clone, Debug)]
enum SlotEntrySpec {
    FixedKey { slot: usize, atom_id: usize },
    SymGroup { off: usize, group: usize },
}

#[derive(Clone, Debug)]
enum TemplateSpec {
    Scalar { var: VarId },
    MapFixed { var: VarId, key: Atom },
    MapSym { var: VarId },
}

/// Certify in-place threshold-counter saturation followed by generic equivariant
/// symmetry for the exact installed `VIEW` expression. Fails closed (`None`)
/// whenever any counter cap, key set, transfer, test, or observation falls
/// outside the certified composed IR.
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
    let norm_spec = norm_spec_desugared;

    let counter_map: BTreeMap<VarId, CounterSpec> = counters.iter().map(|c| (c.var, c.clone())).collect();
    let core_vars: Vec<VarId> = (0..program.vars.len()).map(|i| VarId(i as u32)).filter(|v| !counter_map.contains_key(v)).collect();

    let mut ctx = LowerCtx::with_retained(program, &groups, &all_keys, &const_bindings, &totality, &core_vars);

    // Build flat slot and template tables.
    let mut slots: Vec<SlotInfo> = Vec::new();
    let mut templates: Vec<TemplateSpec> = Vec::new();
    let mut scalar_slot: BTreeMap<VarId, usize> = BTreeMap::new();
    let mut map_entries: BTreeMap<VarId, Vec<SlotEntrySpec>> = BTreeMap::new();

    for c in &counters {
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
                let mut sym_groups = Vec::new();
                let mut covered_keys: BTreeSet<Arc<str>> = BTreeSet::new();
                for (gi, g) in groups.iter().enumerate() {
                    let present = g.keys.iter().filter(|k| keys.contains(&Atom::Model((*k).clone()))).count();
                    if present == g.keys.len() {
                        sym_groups.push(gi);
                        covered_keys.extend(g.keys.iter().cloned());
                    } else if present != 0 {
                        // Partial overlap with a symmetric group cannot compose.
                        return None;
                    }
                }
                let mut fixed_keys = Vec::new();
                for k in keys {
                    if let Atom::Model(m) = k {
                        if covered_keys.contains(m) {
                            continue;
                        }
                        if all_keys.contains(m) {
                            return None;
                        }
                    }
                    fixed_keys.push(k.clone());
                }
                let mut entries = Vec::new();
                for fk in fixed_keys {
                    let ak = atom_to_key_free(&fk, &all_keys)?;
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

    let mut e = Emitter {
        program,
        cfg,
        domains: &domains,
        groups: &groups,
        all_keys: &all_keys,
        counters: &counter_map,
        scalar_slot: &scalar_slot,
        map_entries: &map_entries,
        templates: &templates,
        ctx: &mut ctx,
        opaque_cache: &mut opaque_cache,
        remaining: MAX_TEST_WORK,
    };

    let mut init_branches = Vec::with_capacity(initial.len());
    for b in &initial {
        init_branches.push(e.lower_init_branch(b)?);
    }

    let mut step_branches = Vec::with_capacity(steps.len());
    for b in &steps {
        step_branches.push(e.lower_step_branch(b)?);
    }

    let obs_test = e.lower_test_conj(norm_spec.invariants, false)?;
    let init_obs_test = e.lower_test_conj(norm_spec.init_props, false)?;
    let constraint_test = e.lower_test_conj(norm_spec.constraints, false)?;
    let action_constraint_form = e.lower_action_conj(norm_spec.action_constraints)?;
    let action_obs_form = e.lower_action_conj(norm_spec.action_props)?;

    // Require every symmetric group in the product to be referenced by the spec.
    let full_mask: GroupMask = ((1u32 << groups.len()) - 1) as GroupMask;
    if e.ctx.used_groups != full_mask {
        return None;
    }

    let branch_count = init_branches.len().max(step_branches.len());
    let cert = render(
        &groups,
        &ctx,
        init,
        core_vars.len(),
        &slots,
        templates.len(),
        branch_count,
        &init_branches,
        &step_branches,
        &obs_test,
        &init_obs_test,
        &constraint_test,
        &action_constraint_form,
        &action_obs_form,
        norm_spec.is_constrained(),
    );
    norm.attach_const_subst(cert)
}

struct InitBranchData {
    bounds: Vec<String>,
    guard: String,
    seeds: Vec<String>,
}

struct StepBranchData {
    bounds: Vec<String>,
    guard: String,
    transfers: Vec<String>,
}

struct Emitter<'a, 'c> {
    program: &'a Program,
    cfg: &'a Config,
    domains: &'a Domains,
    groups: &'a [GroupInfo],
    all_keys: &'a BTreeSet<Arc<str>>,
    counters: &'a BTreeMap<VarId, CounterSpec>,
    scalar_slot: &'a BTreeMap<VarId, usize>,
    map_entries: &'a BTreeMap<VarId, Vec<SlotEntrySpec>>,
    templates: &'a [TemplateSpec],
    ctx: &'c mut LowerCtx<'a>,
    opaque_cache: &'c mut HashMap<DefId, Option<BTreeSet<VarId>>>,
    remaining: usize,
}

impl Emitter<'_, '_> {
    fn tick(&mut self, cost: usize) -> Option<()> {
        self.remaining = self.remaining.checked_sub(cost.max(1))?;
        Some(())
    }

    fn independent(&mut self, e: &Expr) -> bool {
        match &*e.kind {
            ExprKind::Var(v) => return !self.counters.contains_key(v),
            ExprKind::Builtin { op: B::Domain, args } if args.len() == 1 => {
                if let Some(v) = variable(&args[0], false) {
                    if matches!(self.counters.get(&v).map(|c| &c.kind), Some(CounterKind::Map(_))) {
                        return false;
                    }
                }
            }
            ExprKind::Apply { op: OpRef::Def(id), args } => {
                let Some(vars) = opaque_recursive_def_vars(self.program, self.cfg, *id, self.opaque_cache) else {
                    return false;
                };
                if vars.iter().any(|v| self.counters.contains_key(v)) {
                    return false;
                }
                return args.iter().all(|a| self.independent(a));
            }
            _ => {}
        }
        let mut ok = true;
        visit::children(e, &mut |c| {
            if ok {
                ok &= self.independent(c);
            }
        });
        ok
    }

    fn lower_init_branch(&mut self, b: &Branch) -> Option<InitBranchData> {
        let (bounds, pushed) = self.ctx.lower_witness_bounds(&b.bounds, false, None)?;
        let res = (|| {
            let mut guards = Vec::new();
            for term in &b.terms {
                if matches!(
                    &*term.kind,
                    ExprKind::Builtin { op: B::Eq, args }
                        if args.len() == 2 && variable(&args[0], false).is_some_and(|v| self.counters.contains_key(&v))
                ) {
                    continue;
                }
                guards.push(self.ctx.lower_form(term, false)?);
            }
            let mut seeds = Vec::with_capacity(self.templates.len());
            for tmpl in self.templates {
                let seed = match tmpl {
                    TemplateSpec::Scalar { var } => {
                        let rhs = binding(b, *var, false)?;
                        self.lower_scalar_seed(&rhs)?
                    }
                    TemplateSpec::MapFixed { var, key } => {
                        let rhs = binding(b, *var, false)?;
                        self.lower_map_seed(Some(key), &rhs)?
                    }
                    TemplateSpec::MapSym { var } => {
                        let rhs = binding(b, *var, false)?;
                        self.lower_map_seed(None, &rhs)?
                    }
                };
                seeds.push(seed);
            }
            Some(InitBranchData { bounds, guard: fold_form_conj(guards), seeds })
        })();
        for id in pushed.into_iter().rev() {
            self.ctx.pop_bound_local(id);
        }
        res
    }

    fn lower_scalar_seed(&mut self, rhs: &Expr) -> Option<String> {
        self.tick(1)?;
        if let Some(n) = atom_nat(self.domains, rhs) {
            return Some(format!("(SymSeed.const {n})"));
        }
        if let ExprKind::If { cond, then, els } = &*rhs.kind {
            let c = self.ctx.lower_form(cond, false)?;
            let t = self.lower_scalar_seed(then)?;
            let f = self.lower_scalar_seed(els)?;
            return Some(format!("(SymSeed.ite {c} {t} {f})"));
        }
        None
    }

    fn lower_map_seed(&mut self, fixed_key: Option<&Atom>, rhs: &Expr) -> Option<String> {
        self.tick(1)?;
        match &*rhs.kind {
            ExprKind::FnConstruct { bounds, body } => {
                let [bound] = bounds.as_slice() else { return None };
                let BoundVars::Many(ids) = &bound.vars else { return None };
                let [local] = ids.as_slice() else { return None };
                if super::super::liveness::mentions_local(body, *local) {
                    let key = fixed_key?;
                    let key_expr = self.domains.atom_expr(key, body.span)?;
                    let subst = subst_local(body, *local, &key_expr);
                    return self.lower_scalar_seed(&subst);
                }
                self.lower_scalar_seed(body)
            }
            ExprKind::If { cond, then, els } => {
                let c = self.ctx.lower_form(cond, false)?;
                let t = self.lower_map_seed(fixed_key, then)?;
                let f = self.lower_map_seed(fixed_key, els)?;
                Some(format!("(SymSeed.ite {c} {t} {f})"))
            }
            _ => None,
        }
    }

    fn lower_step_branch(&mut self, b: &Branch) -> Option<StepBranchData> {
        let (bounds, pushed) = self.ctx.lower_witness_bounds(&b.bounds, true, None)?;
        let res = (|| {
            let mut guards = Vec::new();
            for term in &b.terms {
                if matches!(
                    &*term.kind,
                    ExprKind::Builtin { op: B::Eq, args }
                        if args.len() == 2 && variable(&args[0], true).is_some_and(|v| self.counters.contains_key(&v))
                ) {
                    continue;
                }
                if let ExprKind::Builtin { op: B::Unchanged, args } = &*term.kind {
                    if args.len() == 1 && ordinary_unchanged(&args[0]) {
                        let mut retained = Vec::new();
                        self.collect_retained_unchanged(&args[0], &mut retained)?;
                        for v_expr in retained {
                            let frame = Expr::new(ExprKind::Builtin { op: B::Unchanged, args: vec![v_expr] }, term.span);
                            guards.push(format!("(SymTest.pure {})", self.ctx.lower_form(&frame, true)?));
                        }
                        continue;
                    }
                }
                guards.push(self.lower_sym_test(term, true)?);
            }
            let mut transfers = Vec::with_capacity(self.templates.len());
            for tmpl in self.templates {
                let tr = match tmpl {
                    TemplateSpec::Scalar { var } => {
                        let rhs = binding(b, *var, true)?;
                        self.lower_scalar_transfer(*var, &rhs)?
                    }
                    TemplateSpec::MapFixed { var, key } => {
                        let rhs = binding(b, *var, true)?;
                        self.lower_map_transfer(*var, Some(key), &rhs)?
                    }
                    TemplateSpec::MapSym { var } => {
                        let rhs = binding(b, *var, true)?;
                        self.lower_map_transfer(*var, None, &rhs)?
                    }
                };
                transfers.push(tr);
            }
            Some(StepBranchData { bounds, guard: fold_sym_test(guards, "conj", "true"), transfers })
        })();
        for id in pushed.into_iter().rev() {
            self.ctx.pop_bound_local(id);
        }
        res
    }

    fn collect_retained_unchanged(&self, e: &Expr, out: &mut Vec<Expr>) -> Option<()> {
        match &*e.kind {
            ExprKind::Var(v) => {
                if !self.counters.contains_key(v) {
                    out.push(e.clone());
                }
                Some(())
            }
            ExprKind::Tuple(es) => {
                for x in es {
                    self.collect_retained_unchanged(x, out)?;
                }
                Some(())
            }
            _ => None,
        }
    }

    fn lower_scalar_transfer(&mut self, var: VarId, rhs: &Expr) -> Option<String> {
        self.tick(1)?;
        if variable(rhs, false) == Some(var) {
            return Some("SymTransfer.keep".to_string());
        }
        if let Some(r) = atom_nat(self.domains, rhs) {
            return Some(format!("(SymTransfer.reset {r})"));
        }
        match &*rhs.kind {
            ExprKind::Builtin { op: B::Plus, args } if args.len() == 2 => {
                for (lhs, delta_e) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                    if variable(lhs, false) == Some(var) {
                        if let Some(d) = atom_nat(self.domains, delta_e) {
                            return Some(format!("(SymTransfer.add {d})"));
                        }
                    }
                }
                None
            }
            ExprKind::If { cond, then, els } => {
                let c = self.lower_sym_test(cond, true)?;
                let t = self.lower_scalar_transfer(var, then)?;
                let f = self.lower_scalar_transfer(var, els)?;
                self.tick(c.len() + t.len() + f.len())?;
                Some(format!("(SymTransfer.ite {c} {t} {f})"))
            }
            _ => None,
        }
    }

    fn lower_map_transfer(&mut self, var: VarId, fixed_key: Option<&Atom>, rhs: &Expr) -> Option<String> {
        self.tick(1)?;
        if variable(rhs, false) == Some(var) {
            return Some("SymTransfer.keep".to_string());
        }
        match &*rhs.kind {
            ExprKind::FnConstruct { bounds, body } => {
                let [bound] = bounds.as_slice() else { return None };
                let BoundVars::Many(ids) = &bound.vars else { return None };
                let [local] = ids.as_slice() else { return None };
                let idx = Expr::new(ExprKind::Local(*local), body.span);
                self.lower_map_slot_transfer(var, &idx, body, Some(*local), fixed_key)
            }
            ExprKind::Except { base, updates } if variable(base, false) == Some(var) => {
                let mut result = "SymTransfer.keep".to_string();
                for (path, val) in updates {
                    let [ExceptKey::Index(indices)] = path.as_slice() else { return None };
                    let [idx] = indices.as_slice() else { return None };
                    let upd = self.lower_map_slot_transfer(var, idx, val, None, fixed_key)?;
                    let key_expr = self.ctx.lower_expr(idx, true)?;
                    self.tick(key_expr.len() + upd.len() + result.len())?;
                    result = format!("(SymTransfer.ifKeyEq {key_expr} {upd} {result})");
                }
                Some(result)
            }
            ExprKind::If { cond, then, els } => {
                let c = self.lower_sym_test(cond, true)?;
                let t = self.lower_map_transfer(var, fixed_key, then)?;
                let f = self.lower_map_transfer(var, fixed_key, els)?;
                self.tick(c.len() + t.len() + f.len())?;
                Some(format!("(SymTransfer.ite {c} {t} {f})"))
            }
            _ => None,
        }
    }

    fn lower_map_slot_transfer(
        &mut self,
        var: VarId,
        idx: &Expr,
        val: &Expr,
        ctor_local: Option<LocalId>,
        fixed_key: Option<&Atom>,
    ) -> Option<String> {
        self.tick(1)?;
        if matches!(
            &*val.kind,
            ExprKind::FnApp { func, args }
                if args.len() == 1 && variable(func, false) == Some(var) && expr_structurally_eq(&args[0], idx)
        ) {
            return Some("SymTransfer.keep".to_string());
        }
        if let Some(r) = atom_nat(self.domains, val) {
            return Some(format!("(SymTransfer.reset {r})"));
        }
        match &*val.kind {
            ExprKind::Builtin { op: B::Plus, args } if args.len() == 2 => {
                for (lhs, delta_e) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                    if matches!(
                        &*lhs.kind,
                        ExprKind::FnApp { func, args }
                            if args.len() == 1 && variable(func, false) == Some(var) && expr_structurally_eq(&args[0], idx)
                    ) {
                        if let Some(d) = atom_nat(self.domains, delta_e) {
                            return Some(format!("(SymTransfer.add {d})"));
                        }
                    }
                }
                None
            }
            ExprKind::If { cond, then, els } => {
                // Handle `IF local = keyExpr THEN ... ELSE ...` inside `[local \in D |-> ...]`.
                if let Some(l) = ctor_local {
                    if let ExprKind::Builtin { op: B::Eq, args } = &*cond.kind {
                        if args.len() == 2 {
                            let other = if matches!(&*args[0].kind, ExprKind::Local(x) if *x == l) {
                                Some(&args[1])
                            } else if matches!(&*args[1].kind, ExprKind::Local(x) if *x == l) {
                                Some(&args[0])
                            } else {
                                None
                            };
                            if let Some(key_e) = other {
                                if !super::super::liveness::mentions_local(key_e, l) {
                                    let key_expr = self.ctx.lower_expr(key_e, true)?;
                                    let t = self.lower_map_slot_transfer(var, idx, then, ctor_local, fixed_key)?;
                                    let f = self.lower_map_slot_transfer(var, idx, els, ctor_local, fixed_key)?;
                                    self.tick(key_expr.len() + t.len() + f.len())?;
                                    return Some(format!("(SymTransfer.ifKeyEq {key_expr} {t} {f})"));
                                }
                            }
                        }
                    }
                    if super::super::liveness::mentions_local(cond, l) {
                        let key = fixed_key?;
                        let key_expr = self.domains.atom_expr(key, cond.span)?;
                        let subst_cond = subst_local(cond, l, &key_expr);
                        let c = self.lower_sym_test(&subst_cond, true)?;
                        let t = self.lower_map_slot_transfer(var, idx, then, ctor_local, fixed_key)?;
                        let f = self.lower_map_slot_transfer(var, idx, els, ctor_local, fixed_key)?;
                        self.tick(c.len() + t.len() + f.len())?;
                        return Some(format!("(SymTransfer.ite {c} {t} {f})"));
                    }
                }
                let c = self.lower_sym_test(cond, true)?;
                let t = self.lower_map_slot_transfer(var, idx, then, ctor_local, fixed_key)?;
                let f = self.lower_map_slot_transfer(var, idx, els, ctor_local, fixed_key)?;
                self.tick(c.len() + t.len() + f.len())?;
                Some(format!("(SymTransfer.ite {c} {t} {f})"))
            }
            _ => None,
        }
    }

    fn lower_test_conj(&mut self, preds: &[Expr], allow_prime: bool) -> Option<String> {
        let parts = preds.iter().map(|p| self.lower_sym_test(p, allow_prime)).collect::<Option<Vec<_>>>()?;
        Some(fold_sym_test(parts, "conj", "true"))
    }

    fn lower_action_conj(&mut self, preds: &[Expr]) -> Option<String> {
        let mut forms = Vec::with_capacity(preds.len());
        for p in preds {
            if !self.independent(p) {
                return None;
            }
            forms.push(self.ctx.lower_action_pred(p)?);
        }
        Some(fold_form_conj(forms))
    }

    fn lower_sym_test(&mut self, e: &Expr, allow_prime: bool) -> Option<String> {
        self.tick(1)?;
        if self.independent(e) {
            let f = self.ctx.lower_form(e, allow_prime)?;
            return Some(format!("(SymTest.pure {f})"));
        }
        match &*e.kind {
            ExprKind::And(es) | ExprKind::Or(es) => {
                let is_and = matches!(&*e.kind, ExprKind::And(_));
                let parts = es.iter().map(|x| self.lower_sym_test(x, allow_prime)).collect::<Option<Vec<_>>>()?;
                Some(fold_sym_test(parts, if is_and { "conj" } else { "disj" }, if is_and { "true" } else { "false" }))
            }
            ExprKind::If { cond, then, els } => {
                let c = self.lower_sym_test(cond, allow_prime)?;
                let t = self.lower_sym_test(then, allow_prime)?;
                let f = self.lower_sym_test(els, allow_prime)?;
                self.tick(c.len() * 2 + t.len() + f.len())?;
                Some(format!("(SymTest.disj (SymTest.conj {c} {t}) (SymTest.conj (SymTest.neg {c}) {f}))"))
            }
            ExprKind::Quant { kind, bounds, body } => self.lower_quant(*kind, bounds, body, allow_prime),
            ExprKind::Builtin { op, args } => match (op, args.as_slice()) {
                (B::Not, [p]) => Some(format!("(SymTest.neg {})", self.lower_sym_test(p, allow_prime)?)),
                (B::Implies, [p, q]) => Some(format!(
                    "(SymTest.disj (SymTest.neg {}) {})",
                    self.lower_sym_test(p, allow_prime)?,
                    self.lower_sym_test(q, allow_prime)?
                )),
                (B::Equiv, [p, q]) => {
                    let lp = self.lower_sym_test(p, allow_prime)?;
                    let lq = self.lower_sym_test(q, allow_prime)?;
                    self.tick(lp.len() * 2 + lq.len() * 2)?;
                    Some(format!("(SymTest.disj (SymTest.conj {lp} {lq}) (SymTest.conj (SymTest.neg {lp}) (SymTest.neg {lq})))"))
                }
                (B::Lt | B::Le | B::Gt | B::Ge | B::Eq | B::Neq, [a, b]) => {
                    if let Some(cmp) = self.lower_comparison(*op, a, b, allow_prime) {
                        return Some(cmp);
                    }
                    if matches!(op, B::Eq | B::Neq) {
                        let neg = *op == B::Neq;
                        if self.independent(a) && matches!(&*b.kind, ExprKind::If { .. }) {
                            let eq = self.lower_eq_if(a, b, false, allow_prime)?;
                            return Some(if neg { format!("(SymTest.neg {eq})") } else { eq });
                        }
                        if self.independent(b) && matches!(&*a.kind, ExprKind::If { .. }) {
                            let eq = self.lower_eq_if(b, a, true, allow_prime)?;
                            return Some(if neg { format!("(SymTest.neg {eq})") } else { eq });
                        }
                    }
                    None
                }
                (B::In | B::NotIn, [a, b]) => {
                    let mem = self.lower_membership(a, b, allow_prime)?;
                    Some(if *op == B::NotIn { format!("(SymTest.neg {mem})") } else { mem })
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn lower_quant(&mut self, kind: QuantKind, bounds: &[Bound], body: &Expr, allow_prime: bool) -> Option<String> {
        let mut flat: Vec<(LocalId, &Expr, Vec<usize>, Vec<usize>)> = Vec::new();
        for b in bounds {
            let BoundVars::Many(ids) = &b.vars else { return None };
            let set_atoms = self.domains.exact_set(&b.set)?;
            let (sym_groups, fixed_ids) = self.classify_domain_set(&set_atoms)?;
            for &id in ids {
                flat.push((id, &b.set, sym_groups.clone(), fixed_ids.clone()));
            }
        }
        self.expand_quant_sym(kind, &flat, body, allow_prime)
    }

    fn classify_domain_set(&mut self, set_atoms: &BTreeSet<Atom>) -> Option<(Vec<usize>, Vec<usize>)> {
        let mut sym_groups = Vec::new();
        let mut covered_keys: BTreeSet<Arc<str>> = BTreeSet::new();
        for (gi, g) in self.groups.iter().enumerate() {
            let present = g.keys.iter().filter(|k| set_atoms.contains(&Atom::Model((*k).clone()))).count();
            if present == g.keys.len() {
                sym_groups.push(gi);
                self.ctx.mark_group_used(1u16 << gi);
                covered_keys.extend(g.keys.iter().cloned());
            } else if present != 0 {
                return None;
            }
        }
        let mut fixed_ids = Vec::new();
        for a in set_atoms {
            if let Atom::Model(m) = a {
                if covered_keys.contains(m) {
                    continue;
                }
                if self.all_keys.contains(m) {
                    return None;
                }
            }
            let ak = atom_to_key_free(a, self.all_keys)?;
            fixed_ids.push(self.ctx.atom_id_of(ak));
        }
        Some((sym_groups, fixed_ids))
    }

    fn expand_quant_sym(
        &mut self,
        kind: QuantKind,
        rest: &[(LocalId, &Expr, Vec<usize>, Vec<usize>)],
        body: &Expr,
        allow_prime: bool,
    ) -> Option<String> {
        let Some(((id, set_expr, sym_groups, fixed_ids), tail)) = rest.split_first() else {
            return self.lower_sym_test(body, allow_prime);
        };
        let is_all = matches!(kind, QuantKind::Forall);
        let mut parts = Vec::new();
        for &gi in sym_groups {
            self.ctx.push_bound_local(*id, Some(set_expr));
            let inner = self.expand_quant_sym(kind, tail, body, allow_prime);
            self.ctx.pop_bound_local(*id);
            let inner = inner?;
            let ctor = if is_all { "allGroup" } else { "someGroup" };
            parts.push(format!("(SymTest.{ctor} ⟨{gi}, by decide⟩ {inner})"));
        }
        if !fixed_ids.is_empty() {
            self.ctx.push_bound_local(*id, Some(set_expr));
            let inner = self.expand_quant_sym(kind, tail, body, allow_prime);
            self.ctx.pop_bound_local(*id);
            let inner = inner?;
            let ids_str = fixed_ids.iter().map(usize::to_string).collect::<Vec<_>>().join(", ");
            let ctor = if is_all { "allFixed" } else { "someFixed" };
            parts.push(format!("(SymTest.{ctor} [{ids_str}] {inner})"));
        }
        Some(fold_sym_test(parts, if is_all { "conj" } else { "disj" }, if is_all { "true" } else { "false" }))
    }

    fn lower_eq_if(&mut self, other: &Expr, expr: &Expr, other_on_right: bool, allow_prime: bool) -> Option<String> {
        self.tick(1)?;
        if let ExprKind::If { cond, then, els } = &*expr.kind {
            let c = self.lower_sym_test(cond, allow_prime)?;
            let t = self.lower_eq_if(other, then, other_on_right, allow_prime)?;
            let f = self.lower_eq_if(other, els, other_on_right, allow_prime)?;
            self.tick(c.len() * 2 + t.len() + f.len())?;
            Some(format!("(SymTest.disj (SymTest.conj {c} {t}) (SymTest.conj (SymTest.neg {c}) {f}))"))
        } else {
            let args = if other_on_right { vec![expr.clone(), other.clone()] } else { vec![other.clone(), expr.clone()] };
            let eq = Expr::new(ExprKind::Builtin { op: B::Eq, args }, expr.span);
            let f = self.ctx.lower_form(&eq, allow_prime)?;
            Some(format!("(SymTest.pure {f})"))
        }
    }

    fn lower_comparison(&mut self, op: B, a: &Expr, b: &Expr, allow_prime: bool) -> Option<String> {
        for (slot_e, const_e, rev) in [(a, b, false), (b, a, true)] {
            let Some(Atom::Num(thresh)) = self.domains.atom_value(const_e) else { continue };
            let norm_op = if rev {
                match op {
                    B::Lt => B::Gt,
                    B::Le => B::Ge,
                    B::Gt => B::Lt,
                    B::Ge => B::Le,
                    x => x,
                }
            } else {
                op
            };
            if let Some(v) = variable(slot_e, false) {
                if let Some(&k) = self.scalar_slot.get(&v) {
                    return self.emit_scalar_cmp(v, k, norm_op, thresh);
                }
            }
            if let ExprKind::FnApp { func, args } = &*slot_e.kind {
                if args.len() == 1 {
                    if let Some(v) = variable(func, false) {
                        if self.map_entries.contains_key(&v) {
                            let key_expr = self.ctx.lower_expr(&args[0], allow_prime)?;
                            return self.emit_map_cmp(v, &key_expr, norm_op, thresh);
                        }
                    }
                }
            }
        }
        None
    }

    fn emit_scalar_cmp(&mut self, var: VarId, k: usize, op: B, thresh: i128) -> Option<String> {
        self.tick(1)?;
        if thresh < 0 {
            let truth = matches!(op, B::Gt | B::Ge | B::Neq);
            return Some(format!("(SymTest.pure (Form.truth {truth}))"));
        }
        let req = required_cap(op, thresh, false)?;
        if req > self.counters.get(&var)?.cap {
            return None;
        }
        let cmp_ctor = cmp_ctor_name(op)?;
        Some(format!("(SymTest.cmpScalar ⟨{k}, by decide⟩ {cmp_ctor} {thresh} (by decide))"))
    }

    fn emit_map_cmp(&mut self, var: VarId, key_expr: &str, op: B, thresh: i128) -> Option<String> {
        self.tick(1)?;
        if thresh < 0 {
            let truth = matches!(op, B::Gt | B::Ge | B::Neq);
            return Some(format!("(SymTest.pure (Form.truth {truth}))"));
        }
        let req = required_cap(op, thresh, false)?;
        if req > self.counters.get(&var)?.cap {
            return None;
        }
        let cmp_ctor = cmp_ctor_name(op)?;
        let entries = self.map_entries.get(&var)?;
        let entries_str = entries
            .iter()
            .map(|e| match e {
                SlotEntrySpec::FixedKey { slot, atom_id } => format!("(SlotEntry.fixedKey ⟨{slot}, by decide⟩ {atom_id})"),
                SlotEntrySpec::SymGroup { off, group } => format!("(SlotEntry.symGroup {off} ⟨{group}, by decide⟩)"),
            })
            .collect::<Vec<_>>()
            .join(", ");
        Some(format!("(SymTest.cmpMap [{entries_str}] {key_expr} {cmp_ctor} {thresh})"))
    }

    fn lower_membership(&mut self, elem: &Expr, set: &Expr, allow_prime: bool) -> Option<String> {
        if let Some(v) = variable(elem, false) {
            if let Some(&k) = self.scalar_slot.get(&v) {
                return self.lower_scalar_nat_set(v, k, set);
            }
            if let Some(entries) = self.map_entries.get(&v).cloned() {
                if let ExprKind::FnSet { domain, range } = &*set.kind {
                    let CounterKind::Map(expected_keys) = &self.counters.get(&v)?.kind else { return None };
                    if self.domains.exact_set(domain).as_ref() != Some(expected_keys) {
                        return None;
                    }
                    let mut parts = Vec::new();
                    for entry in entries {
                        match entry {
                            SlotEntrySpec::FixedKey { slot, .. } => {
                                parts.push(self.lower_scalar_nat_set(v, slot, range)?);
                            }
                            SlotEntrySpec::SymGroup { group, .. } => {
                                self.ctx.push_temp_local();
                                let inner = self.lower_map_entry_nat_set(v, "(Expr.localVar 0)", range);
                                self.ctx.pop_temp_local();
                                let inner = inner?;
                                parts.push(format!("(SymTest.allGroup ⟨{group}, by decide⟩ {inner})"));
                            }
                        }
                    }
                    return Some(fold_sym_test(parts, "conj", "true"));
                }
            }
        }
        if let ExprKind::FnApp { func, args } = &*elem.kind {
            if args.len() == 1 {
                if let Some(v) = variable(func, false) {
                    if self.map_entries.contains_key(&v) {
                        let key_expr = self.ctx.lower_expr(&args[0], allow_prime)?;
                        return self.lower_map_entry_nat_set(v, &key_expr, set);
                    }
                }
            }
        }
        None
    }

    fn lower_scalar_nat_set(&mut self, var: VarId, k: usize, set: &Expr) -> Option<String> {
        match &*set.kind {
            ExprKind::Builtin { op: B::Nat | B::Int, args } if args.is_empty() => Some("(SymTest.pure (Form.truth true))".to_string()),
            ExprKind::Builtin { op: B::DotDot, args } if args.len() == 2 => {
                let (Atom::Num(lo), Atom::Num(hi)) = (self.domains.atom_value(&args[0])?, self.domains.atom_value(&args[1])?) else {
                    return None;
                };
                if lo > hi || hi < 0 {
                    return Some("(SymTest.pure (Form.truth false))".to_string());
                }
                let lo_cmp = self.emit_scalar_cmp(var, k, B::Ge, lo.max(0))?;
                let hi_cmp = self.emit_scalar_cmp(var, k, B::Le, hi)?;
                Some(format!("(SymTest.conj {lo_cmp} {hi_cmp})"))
            }
            ExprKind::SetEnum(es) => {
                let mut eqs = Vec::new();
                for item in es {
                    let Atom::Num(n) = self.domains.atom_value(item)? else { return None };
                    if n >= 0 {
                        eqs.push(self.emit_scalar_cmp(var, k, B::Eq, n)?);
                    }
                }
                Some(fold_sym_test(eqs, "disj", "false"))
            }
            _ => None,
        }
    }

    fn lower_map_entry_nat_set(&mut self, var: VarId, key_expr: &str, set: &Expr) -> Option<String> {
        match &*set.kind {
            ExprKind::Builtin { op: B::Nat | B::Int, args } if args.is_empty() => Some("(SymTest.pure (Form.truth true))".to_string()),
            ExprKind::Builtin { op: B::DotDot, args } if args.len() == 2 => {
                let (Atom::Num(lo), Atom::Num(hi)) = (self.domains.atom_value(&args[0])?, self.domains.atom_value(&args[1])?) else {
                    return None;
                };
                if lo > hi || hi < 0 {
                    return Some("(SymTest.pure (Form.truth false))".to_string());
                }
                let lo_cmp = self.emit_map_cmp(var, key_expr, B::Ge, lo.max(0))?;
                let hi_cmp = self.emit_map_cmp(var, key_expr, B::Le, hi)?;
                Some(format!("(SymTest.conj {lo_cmp} {hi_cmp})"))
            }
            ExprKind::SetEnum(es) => {
                let mut eqs = Vec::new();
                for item in es {
                    let Atom::Num(n) = self.domains.atom_value(item)? else { return None };
                    if n >= 0 {
                        eqs.push(self.emit_map_cmp(var, key_expr, B::Eq, n)?);
                    }
                }
                Some(fold_sym_test(eqs, "disj", "false"))
            }
            _ => None,
        }
    }
}

fn cmp_ctor_name(op: B) -> Option<&'static str> {
    match op {
        B::Lt => Some("Cmp.lt"),
        B::Le => Some("Cmp.le"),
        B::Eq => Some("Cmp.eq"),
        B::Neq => Some("Cmp.ne"),
        B::Gt => Some("Cmp.gt"),
        B::Ge => Some("Cmp.ge"),
        _ => None,
    }
}

fn atom_to_key_free(a: &Atom, all_keys: &BTreeSet<Arc<str>>) -> Option<AtomKey> {
    match a {
        Atom::Num(n) => Some(AtomKey::Int(*n)),
        Atom::Bool(b) => Some(AtomKey::Bool(*b)),
        Atom::Str(s) => Some(AtomKey::Str(s.clone())),
        Atom::Model(m) => (!all_keys.contains(m)).then(|| AtomKey::Model(m.clone())),
    }
}

fn subst_local(e: &Expr, target: LocalId, replacement: &Expr) -> Expr {
    if matches!(&*e.kind, ExprKind::Local(l) if *l == target) {
        return replacement.clone();
    }
    let mut out = e.clone();
    visit::children_mut(&mut out, &mut |child| {
        *child = subst_local(child, target, replacement);
    });
    out
}

fn fold_form_conj(forms: Vec<String>) -> String {
    let mut it = forms.into_iter();
    let Some(first) = it.next() else {
        return "(Form.truth true)".to_string();
    };
    it.fold(first, |acc, f| format!("(Form.conj {acc} {f})"))
}

fn fold_sym_test(tests: Vec<String>, op: &str, identity: &str) -> String {
    let mut it = tests.into_iter();
    let Some(first) = it.next() else {
        return format!("(SymTest.pure (Form.truth {identity}))");
    };
    it.fold(first, |acc, t| format!("(SymTest.{op} {acc} {t})"))
}

#[allow(clippy::too_many_arguments)]
fn render(
    groups: &[GroupInfo],
    ctx: &LowerCtx<'_>,
    orig_init: &Expr,
    core_count: usize,
    slots: &[SlotInfo],
    template_count: usize,
    branch_count: usize,
    init_branches: &[InitBranchData],
    step_branches: &[StepBranchData],
    obs_test: &str,
    init_obs_test: &str,
    constraint_test: &str,
    action_constraint_form: &str,
    action_obs_form: &str,
    constrained: bool,
) -> OpenCert {
    let mut out = String::from(include_str!("../../ThresholdCounterCertificate.lean"));
    out.push_str(include_str!("../../EquivSymCertificate.lean"));
    out.push_str(include_str!("../../ThresholdSymCertificate.lean"));
    out.push_str("\nnamespace TlxOptimization.GeneratedThresholdSymmetry\n");
    out.push_str(
        "open TlxOptimization ThresholdCounterRule EquivRule ThresholdSymRule\n\
         noncomputable section\n\
         set_option linter.unusedVariables false\n\
         set_option maxRecDepth 20000\n",
    );
    write_common_header(&mut out, groups, core_count, ctx, orig_init);
    writeln!(out, "abbrev CoreVar := VarId").unwrap();
    writeln!(out, "abbrev SlotCount : Nat := {}", slots.len()).unwrap();
    writeln!(out, "abbrev TemplateCount : Nat := {template_count}").unwrap();
    writeln!(out, "abbrev BranchCount : Nat := {branch_count}").unwrap();

    for (k, s) in slots.iter().enumerate() {
        let desc = match s {
            SlotInfo::Fixed { desc, .. } | SlotInfo::Sym { desc, .. } => desc,
        };
        writeln!(out, "def slot{k}Desc : String := {}", literal(desc)).unwrap();
    }

    out.push_str("def cap (k : Fin SlotCount) : Nat :=\n  match k.val with\n");
    for (k, s) in slots.iter().enumerate() {
        let c = match s {
            SlotInfo::Fixed { cap, .. } | SlotInfo::Sym { cap, .. } => *cap,
        };
        writeln!(out, "  | {k} => {c}").unwrap();
    }
    out.push_str("  | _ => 0\n");

    out.push_str(
        "def slotInfo (k : Fin SlotCount) : Option (Nat × Sigma (fun g : Fin GroupCount => Fin (groupSizes g))) :=\n  match k.val with\n",
    );
    for (k, s) in slots.iter().enumerate() {
        match s {
            SlotInfo::Fixed { .. } => writeln!(out, "  | {k} => none").unwrap(),
            SlotInfo::Sym { off, group, elem, .. } => {
                writeln!(out, "  | {k} => some ({off}, ⟨⟨{group}, by decide⟩, ⟨{elem}, by decide⟩⟩)").unwrap();
            }
        }
    }
    out.push_str("  | _ => none\n");

    out.push_str("def fixedSlotAtom (k : Fin SlotCount) : Nat :=\n  match k.val with\n");
    for (k, s) in slots.iter().enumerate() {
        if let SlotInfo::Fixed { atom_id, .. } = s {
            if *atom_id != 0 {
                writeln!(out, "  | {k} => {atom_id}").unwrap();
            }
        }
    }
    out.push_str("  | _ => 0\n");

    out.push_str("def slotTemplate (k : Fin SlotCount) : Fin TemplateCount :=\n  match k.val with\n");
    for (k, s) in slots.iter().enumerate() {
        let t = match s {
            SlotInfo::Fixed { template, .. } | SlotInfo::Sym { template, .. } => *template,
        };
        writeln!(out, "  | {k} => ⟨{t}, by decide⟩").unwrap();
    }
    out.push_str("  | _ => ⟨0, by decide⟩\n");

    // Init branch tables.
    out.push_str("def initValid (b : Fin BranchCount) : Bool :=\n  match b.val with\n");
    for bi in 0..init_branches.len() {
        writeln!(out, "  | {bi} => true").unwrap();
    }
    out.push_str("  | _ => false\n");

    out.push_str("def initBounds (b : Fin BranchCount) : List (SetPred GroupCount CoreVar) :=\n  match b.val with\n");
    for (bi, b) in init_branches.iter().enumerate() {
        writeln!(out, "  | {bi} => [{}]", b.bounds.join(", ")).unwrap();
    }
    out.push_str("  | _ => []\n");

    out.push_str("def initGuard (b : Fin BranchCount) : Form GroupCount CoreVar :=\n  match b.val with\n");
    for (bi, b) in init_branches.iter().enumerate() {
        writeln!(out, "  | {bi} => {}", b.guard).unwrap();
    }
    out.push_str("  | _ => Form.truth false\n");

    out.push_str("def initSeed (b : Fin BranchCount) (t : Fin TemplateCount) : SymSeed GroupCount CoreVar :=\n  match b.val, t.val with\n");
    for (bi, b) in init_branches.iter().enumerate() {
        for (ti, seed) in b.seeds.iter().enumerate() {
            writeln!(out, "  | {bi}, {ti} => {seed}").unwrap();
        }
    }
    out.push_str("  | _, _ => SymSeed.const 0\n");

    // Step branch tables.
    out.push_str("def stepValid (b : Fin BranchCount) : Bool :=\n  match b.val with\n");
    for bi in 0..step_branches.len() {
        writeln!(out, "  | {bi} => true").unwrap();
    }
    out.push_str("  | _ => false\n");

    out.push_str("def stepBounds (b : Fin BranchCount) : List (SetPred GroupCount CoreVar) :=\n  match b.val with\n");
    for (bi, b) in step_branches.iter().enumerate() {
        writeln!(out, "  | {bi} => [{}]", b.bounds.join(", ")).unwrap();
    }
    out.push_str("  | _ => []\n");

    out.push_str("def stepGuard (b : Fin BranchCount) : SymTest GroupCount cap CoreVar :=\n  match b.val with\n");
    for (bi, b) in step_branches.iter().enumerate() {
        writeln!(out, "  | {bi} => {}", b.guard).unwrap();
    }
    out.push_str("  | _ => SymTest.pure (Form.truth false)\n");

    out.push_str("def stepTransfer (b : Fin BranchCount) (t : Fin TemplateCount) : SymTransfer GroupCount cap CoreVar :=\n  match b.val, t.val with\n");
    for (bi, b) in step_branches.iter().enumerate() {
        for (ti, tr) in b.transfers.iter().enumerate() {
            writeln!(out, "  | {bi}, {ti} => {tr}").unwrap();
        }
    }
    out.push_str("  | _, _ => SymTransfer.keep\n");

    writeln!(out, "def obsTest : SymTest GroupCount cap CoreVar := {obs_test}").unwrap();
    if constrained {
        writeln!(out, "def initObsTest : SymTest GroupCount cap CoreVar := {init_obs_test}").unwrap();
        writeln!(out, "def constraintTest : SymTest GroupCount cap CoreVar := {constraint_test}").unwrap();
        writeln!(out, "def actionConstraintForm : Form GroupCount CoreVar := {action_constraint_form}").unwrap();
        writeln!(out, "def actionObsForm : Form GroupCount CoreVar := {action_obs_form}").unwrap();
    }

    out.push_str(
        "abbrev Semantics (A : Type) := EquivRule.AtomOps A\n\
         variable {A : Type} [HasNatAtom A] (sem : Semantics A)\n\
         def model : ThresholdSymRule.Model GroupCount groupSizes CoreVar SlotCount TemplateCount BranchCount A where\n\
         \x20 ops := sem\n\
         \x20 cap := cap\n\
         \x20 slotInfo := slotInfo\n\
         \x20 fixedSlotAtom := fixedSlotAtom\n\
         \x20 slotTemplate := slotTemplate\n\
         \x20 slotBounds := by decide\n\
         \x20 slotClosed := by decide\n\
         \x20 capUniform := by decide\n\
         \x20 templateUniform := by decide\n\
         \x20 initValid := initValid\n\
         \x20 initBounds := initBounds\n\
         \x20 initGuard := initGuard\n\
         \x20 initSeed := initSeed\n\
         \x20 stepValid := stepValid\n\
         \x20 stepBounds := stepBounds\n\
         \x20 stepGuard := stepGuard\n\
         \x20 stepTransfer := stepTransfer\n\
         \x20 obsTest := obsTest\n",
    );
    if constrained {
        out.push_str(
            "  initObsTest := initObsTest\n\
             \x20 constraintTest := constraintTest\n\
             \x20 actionConstraintForm := actionConstraintForm\n\
             \x20 actionObsForm := actionObsForm\n",
        );
    }
    out.push_str(
        "  stepGuardValid := by decide\n\
         \x20 stepTransferValid := by decide\n\
         \x20 obsValid := by decide\n\
         \x20 initObsValid := by decide\n\
         \x20 constraintValid := by decide\n",
    );

    OpenCert::new_composed(out, include_str!("sym.lean"), "GeneratedThresholdSymmetry", constrained, "threshold", "thresholdProject")
}
