//! HIR init/step branch, guard, `SymTest`, `SymTransfer`, and state/action
//! observation lowering into the composed `ThresholdSymRule` Lean IR.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use tlx_front::cfg::Config;

use crate::{builtins::Builtin as B, hir::*, visit, Program};

use super::super::super::{
    binding, collect_unchanged_excluding,
    domain::{Atom, Domains},
    equiv_sym::{classify_key_set, fold_form_conj, lower::LowerCtx, AtomKey, GroupInfo, MovedKeys},
    mentions_local,
    normalize::opaque_recursive_def_vars,
    ordinary_unchanged,
    sym_groups::subst_local,
    variable, Branch, CheckSpec,
};
use super::super::{
    required_cap,
    shape::{self, MapSeedShape, MapTransferShape, SeedShape, SlotUpdate},
    CounterKind, CounterSpec,
};
use super::{InitBranchData, SlotEntrySpec, SlotLayout, StepBranchData, TemplateSpec};

const MAX_TEST_WORK: usize = 200_000;

pub(super) struct LoweredModel {
    pub(super) init_branches: Vec<InitBranchData>,
    pub(super) step_branches: Vec<StepBranchData>,
    pub(super) obs_test: String,
    pub(super) init_obs_test: String,
    pub(super) constraint_test: String,
    pub(super) action_constraint_form: String,
    pub(super) action_obs_form: String,
}

#[derive(Clone, Copy)]
enum CmpTarget<'a> {
    Scalar(usize),
    Map(&'a str),
}

#[allow(clippy::too_many_arguments)]
pub(super) fn lower_all<'a>(
    program: &'a Program,
    cfg: &'a Config,
    domains: &'a Domains,
    groups: &'a [GroupInfo],
    all_keys: &'a MovedKeys,
    counters: &'a BTreeMap<VarId, CounterSpec>,
    layout: &'a SlotLayout,
    initial: &[Branch],
    steps: &[Branch],
    spec: CheckSpec<'_>,
    ctx: &mut LowerCtx<'a>,
    opaque_cache: &mut HashMap<DefId, Option<BTreeSet<VarId>>>,
) -> Option<LoweredModel> {
    let mut e = Emitter {
        program,
        cfg,
        domains,
        groups,
        all_keys,
        counters,
        scalar_slot: &layout.scalar_slot,
        map_entries: &layout.map_entries,
        templates: &layout.templates,
        ctx,
        opaque_cache,
        remaining: MAX_TEST_WORK,
    };

    let mut init_branches = Vec::with_capacity(initial.len());
    for b in initial {
        init_branches.push(e.lower_init_branch(b)?);
    }

    let mut step_branches = Vec::with_capacity(steps.len());
    for b in steps {
        step_branches.push(e.lower_step_branch(b)?);
    }

    let obs_test = e.lower_test_conj(spec.invariants, false)?;
    let init_obs_test = e.lower_test_conj(spec.init_props, false)?;
    let constraint_test = e.lower_test_conj(spec.constraints, false)?;
    let action_constraint_form = e.lower_action_conj(spec.action_constraints)?;
    let action_obs_form = e.lower_action_conj(spec.action_props)?;

    Some(LoweredModel { init_branches, step_branches, obs_test, init_obs_test, constraint_test, action_constraint_form, action_obs_form })
}

struct Emitter<'a, 'c> {
    program: &'a Program,
    cfg: &'a Config,
    domains: &'a Domains,
    groups: &'a [GroupInfo],
    all_keys: &'a MovedKeys,
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
        match shape::seed_shape(self.domains, rhs)? {
            SeedShape::Const(n) => Some(format!("(SymSeed.const {n})")),
            SeedShape::Ite { cond, then, els } => {
                let c = self.ctx.lower_form(cond, false)?;
                let t = self.lower_scalar_seed(then)?;
                let f = self.lower_scalar_seed(els)?;
                Some(format!("(SymSeed.ite {c} {t} {f})"))
            }
        }
    }

    fn lower_map_seed(&mut self, fixed_key: Option<&Atom>, rhs: &Expr) -> Option<String> {
        self.tick(1)?;
        match shape::map_seed_shape(rhs)? {
            MapSeedShape::FnConstruct { local, body, .. } => {
                if mentions_local(body, local) {
                    let key = fixed_key?;
                    let key_expr = self.domains.atom_expr(key, body.span)?;
                    let subst = subst_local(body, local, &key_expr);
                    return self.lower_scalar_seed(&subst);
                }
                self.lower_scalar_seed(body)
            }
            MapSeedShape::Ite { cond, then, els } => {
                let c = self.ctx.lower_form(cond, false)?;
                let t = self.lower_map_seed(fixed_key, then)?;
                let f = self.lower_map_seed(fixed_key, els)?;
                Some(format!("(SymSeed.ite {c} {t} {f})"))
            }
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
                        collect_unchanged_excluding(&args[0], &mut |v| self.counters.contains_key(&v), &mut retained)?;
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

    fn lower_scalar_transfer(&mut self, var: VarId, rhs: &Expr) -> Option<String> {
        self.tick(1)?;
        match shape::scalar_update(self.domains, var, rhs)? {
            SlotUpdate::Keep => Some("SymTransfer.keep".to_string()),
            SlotUpdate::Reset(r) => Some(format!("(SymTransfer.reset {r})")),
            SlotUpdate::Add(d) => Some(format!("(SymTransfer.add {d})")),
            SlotUpdate::Ite { cond, then, els } => {
                let c = self.lower_sym_test(cond, true)?;
                let t = self.lower_scalar_transfer(var, then)?;
                let f = self.lower_scalar_transfer(var, els)?;
                self.tick(c.len() + t.len() + f.len())?;
                Some(format!("(SymTransfer.ite {c} {t} {f})"))
            }
        }
    }

    fn lower_map_transfer(&mut self, var: VarId, fixed_key: Option<&Atom>, rhs: &Expr) -> Option<String> {
        self.tick(1)?;
        match shape::map_transfer_shape(var, rhs)? {
            MapTransferShape::Keep => Some("SymTransfer.keep".to_string()),
            MapTransferShape::FnConstruct { local, body, .. } => {
                let idx = Expr::new(ExprKind::Local(local), body.span);
                self.lower_map_slot_transfer(var, &idx, body, Some(local), fixed_key)
            }
            MapTransferShape::Except(updates) => {
                let mut result = "SymTransfer.keep".to_string();
                for (idx, val) in updates {
                    let upd = self.lower_map_slot_transfer(var, idx, val, None, fixed_key)?;
                    let key_expr = self.ctx.lower_expr(idx, true)?;
                    self.tick(key_expr.len() + upd.len() + result.len())?;
                    result = format!("(SymTransfer.ifKeyEq {key_expr} {upd} {result})");
                }
                Some(result)
            }
            MapTransferShape::Ite { cond, then, els } => {
                let c = self.lower_sym_test(cond, true)?;
                let t = self.lower_map_transfer(var, fixed_key, then)?;
                let f = self.lower_map_transfer(var, fixed_key, els)?;
                self.tick(c.len() + t.len() + f.len())?;
                Some(format!("(SymTransfer.ite {c} {t} {f})"))
            }
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
        match shape::map_slot_update(self.domains, var, idx, val)? {
            SlotUpdate::Keep => Some("SymTransfer.keep".to_string()),
            SlotUpdate::Reset(r) => Some(format!("(SymTransfer.reset {r})")),
            SlotUpdate::Add(d) => Some(format!("(SymTransfer.add {d})")),
            SlotUpdate::Ite { cond, then, els } => {
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
                                if !mentions_local(key_e, l) {
                                    let key_expr = self.ctx.lower_expr(key_e, true)?;
                                    let t = self.lower_map_slot_transfer(var, idx, then, ctor_local, fixed_key)?;
                                    let f = self.lower_map_slot_transfer(var, idx, els, ctor_local, fixed_key)?;
                                    self.tick(key_expr.len() + t.len() + f.len())?;
                                    return Some(format!("(SymTransfer.ifKeyEq {key_expr} {t} {f})"));
                                }
                            }
                        }
                    }
                    if mentions_local(cond, l) {
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
            let (sym_groups, fixed_atoms) = classify_key_set(&set_atoms, self.groups, self.all_keys)?;
            for &gi in &sym_groups {
                self.ctx.mark_group_used(1u16 << gi);
            }
            let mut fixed_ids = Vec::with_capacity(fixed_atoms.len());
            for a in &fixed_atoms {
                let ak = AtomKey::from_key_free_atom(a, self.all_keys)?;
                fixed_ids.push(self.ctx.atom_id_of(ak));
            }
            for &id in ids {
                flat.push((id, &b.set, sym_groups.clone(), fixed_ids.clone()));
            }
        }
        self.expand_quant_sym(kind, &flat, body, allow_prime)
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
                    return self.emit_cmp(v, CmpTarget::Scalar(k), norm_op, thresh);
                }
            }
            if let ExprKind::FnApp { func, args } = &*slot_e.kind {
                if args.len() == 1 {
                    if let Some(v) = variable(func, false) {
                        if self.map_entries.contains_key(&v) {
                            let key_expr = self.ctx.lower_expr(&args[0], allow_prime)?;
                            return self.emit_cmp(v, CmpTarget::Map(&key_expr), norm_op, thresh);
                        }
                    }
                }
            }
        }
        None
    }

    fn emit_cmp(&mut self, var: VarId, target: CmpTarget<'_>, op: B, thresh: i128) -> Option<String> {
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
        match target {
            CmpTarget::Scalar(k) => Some(format!("(SymTest.cmpScalar ⟨{k}, by decide⟩ {cmp_ctor} {thresh} (by decide))")),
            CmpTarget::Map(key_expr) => {
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
        }
    }

    fn lower_membership(&mut self, elem: &Expr, set: &Expr, allow_prime: bool) -> Option<String> {
        if let Some(v) = variable(elem, false) {
            if let Some(&k) = self.scalar_slot.get(&v) {
                return self.lower_nat_set(v, CmpTarget::Scalar(k), set);
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
                                parts.push(self.lower_nat_set(v, CmpTarget::Scalar(slot), range)?);
                            }
                            SlotEntrySpec::SymGroup { group, .. } => {
                                self.ctx.push_temp_local();
                                let inner = self.lower_nat_set(v, CmpTarget::Map("(Expr.localVar 0)"), range);
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
                        return self.lower_nat_set(v, CmpTarget::Map(&key_expr), set);
                    }
                }
            }
        }
        None
    }

    fn lower_nat_set(&mut self, var: VarId, target: CmpTarget<'_>, set: &Expr) -> Option<String> {
        match &*set.kind {
            ExprKind::Builtin { op: B::Nat | B::Int, args } if args.is_empty() => Some("(SymTest.pure (Form.truth true))".to_string()),
            ExprKind::Builtin { op: B::DotDot, args } if args.len() == 2 => {
                let (Atom::Num(lo), Atom::Num(hi)) = (self.domains.atom_value(&args[0])?, self.domains.atom_value(&args[1])?) else {
                    return None;
                };
                if lo > hi || hi < 0 {
                    return Some("(SymTest.pure (Form.truth false))".to_string());
                }
                let lo_cmp = self.emit_cmp(var, target, B::Ge, lo.max(0))?;
                let hi_cmp = self.emit_cmp(var, target, B::Le, hi)?;
                Some(format!("(SymTest.conj {lo_cmp} {hi_cmp})"))
            }
            ExprKind::SetEnum(es) => {
                let mut eqs = Vec::new();
                for item in es {
                    let Atom::Num(n) = self.domains.atom_value(item)? else { return None };
                    if n >= 0 {
                        eqs.push(self.emit_cmp(var, target, B::Eq, n)?);
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

fn fold_sym_test(tests: Vec<String>, op: &str, identity: &str) -> String {
    let mut it = tests.into_iter();
    let Some(first) = it.next() else {
        return format!("(SymTest.pure (Form.truth {identity}))");
    };
    it.fold(first, |acc, t| format!("(SymTest.{op} {acc} {t})"))
}
