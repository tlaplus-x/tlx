//! Connected rule-IR certificate emitter for threshold-counter saturation.
//!
//! Retained state `C` stays exact; every projected scalar counter or fixed-domain
//! map slot maps to `Fin SlotCount` with per-slot cap `cap : Fin SlotCount → Nat`.
//! Semantic leaves (`sem.test`, `sem.observe`, `sem.actionTest`) never receive
//! any projected counter value.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Write;

use tlx_front::cfg::Config;

use crate::{builtins::Builtin as B, hir::*, optimize::lean::literal, visit, Program};

use super::{atom_nat, expr_structurally_eq, ordinary_unchanged, required_cap, CounterKind, CounterSpec};
use crate::optimize::phase::{
    binding,
    domain::{Atom, Domains},
    normalize::opaque_recursive_def_vars,
    variable, Branch, CheckSpec, OpenCert,
};

#[derive(Clone, Debug)]
enum SlotKind {
    Scalar { var: VarId, cap: i128 },
    Map { var: VarId, key: Atom, cap: i128 },
}

impl SlotKind {
    fn var(&self) -> VarId {
        match self {
            Self::Scalar { var, .. } | Self::Map { var, .. } => *var,
        }
    }

    fn cap(&self) -> i128 {
        match self {
            Self::Scalar { cap, .. } | Self::Map { cap, .. } => *cap,
        }
    }
}

pub(super) struct EmitInput<'a> {
    pub program: &'a Program,
    pub cfg: &'a Config,
    pub domains: &'a Domains,
    pub counters: &'a [CounterSpec],
    pub initial: &'a [Branch],
    pub steps: &'a [Branch],
    pub spec: CheckSpec<'a>,
}

pub(super) fn emit(input: EmitInput<'_>, opaque_cache: &mut HashMap<DefId, Option<BTreeSet<VarId>>>) -> Option<OpenCert> {
    let EmitInput { program, cfg, domains, counters, initial, steps, spec } = input;
    let mut slots = Vec::new();
    let mut counter_map = BTreeMap::new();
    for c in counters {
        counter_map.insert(c.var, c.clone());
        match &c.kind {
            CounterKind::Scalar => slots.push(SlotKind::Scalar { var: c.var, cap: c.cap }),
            CounterKind::Map(keys) => {
                for key in keys {
                    slots.push(SlotKind::Map { var: c.var, key: key.clone(), cap: c.cap });
                }
            }
        }
    }
    if slots.is_empty() || slots.len() > 256 {
        return None;
    }

    let mut e = Emitter {
        program,
        cfg,
        domains,
        counters: counter_map,
        slots,
        atoms: Vec::new(),
        scope: Vec::new(),
        opaque_cache,
        remaining: 200_000,
    };

    // Lower Init branches: pure initial predicate + per-slot Nat seed.
    let mut init_preds = Vec::new();
    let mut init_seeds = Vec::new();
    for branch in initial {
        let (pred, seeds) = e.init_branch(branch)?;
        init_preds.push(pred);
        init_seeds.push(seeds);
    }

    // Lower Next branches: Test cap guard + per-slot Transfer cap.
    let mut step_guards = Vec::new();
    let mut step_transfers = Vec::new();
    for branch in steps {
        let (guard, transfers) = e.step_branch(branch)?;
        step_guards.push(guard);
        step_transfers.push(transfers);
    }

    // Lower state & action observations / constraints.
    let observations = spec.invariants.iter().map(|p| e.test(p, true)).collect::<Option<Vec<_>>>()?;
    let init_obs = spec.init_props.iter().map(|p| e.test(p, true)).collect::<Option<Vec<_>>>()?;
    let constraints = spec.constraints.iter().map(|p| e.test(p, true)).collect::<Option<Vec<_>>>()?;
    let action_constraints = spec.action_constraints.iter().map(|p| e.action_test(p)).collect::<Option<Vec<_>>>()?;
    let action_obs = spec.action_props.iter().map(|p| e.action_test(p)).collect::<Option<Vec<_>>>()?;
    let constrained = spec.is_constrained();

    let mut out = String::from(include_str!("../../ThresholdCounterCertificate.lean"));
    out.push_str(
        "\nnamespace TlxOptimization.GeneratedThresholdCounter\n\
         open TlxOptimization ThresholdCounterRule\n\
         noncomputable section\n\
         set_option linter.unusedVariables false\n\
         attribute [local instance] Classical.propDecidable\n",
    );
    writeln!(out, "abbrev SlotCount : Nat := {}", e.slots.len()).unwrap();
    out.push_str("def cap (k : Fin SlotCount) : Nat :=\n  match k.val with\n");
    for (k, slot) in e.slots.iter().enumerate() {
        writeln!(out, "  | {k} => {}", slot.cap()).unwrap();
    }
    out.push_str("  | _ => 0\n\n");
    out.push_str(
        "-- C contains exactly retained state; W supplies branch-local choices.\n\
         -- Semantic leaves never receive any projected counter value.\n\
         structure Semantics (C W : Type) where\n\
         \x20 test : Nat → C → C → W → Prop\n\
         \x20 observe : Nat → C → Prop\n\
         \x20 actionTest : Nat → C → C → Prop\n",
    );
    for (k, slot) in e.slots.iter().enumerate() {
        let desc = match slot {
            SlotKind::Scalar { var, cap } => format!("slot {k}: scalar {} (cap {cap})", program.vars[var.idx()].name),
            SlotKind::Map { var, key, cap } => format!("slot {k}: map {}[{key:#?}] (cap {cap})", program.vars[var.idx()].name),
        };
        writeln!(out, "def slot{k}Desc : String := {}", literal(&desc)).unwrap();
    }
    for (i, atom) in e.atoms.iter().enumerate() {
        writeln!(out, "def atom{i}HIR : String := {}", literal(atom)).unwrap();
    }

    let params = "{C W : Type} (sem : Semantics C W)";
    out.push_str("\nvariable {C W : Type} (sem : Semantics C W)\n");

    writeln!(out, "def initial {params} (c : C) (choice : Nat × W) : Prop :=\n  let d := c\n  match choice.1 with").unwrap();
    for (i, pred) in init_preds.iter().enumerate() {
        writeln!(out, "  | {i} => {pred}").unwrap();
    }
    out.push_str("  | _ => False\n");

    writeln!(out, "def seed {params} (c : C) (choice : Nat × W) (k : Fin SlotCount) : Nat :=\n  let d := c\n  match choice.1 with")
        .unwrap();
    for (i, seeds) in init_seeds.iter().enumerate() {
        writeln!(out, "  | {i} => match k.val with").unwrap();
        for (k, seed_expr) in seeds.iter().enumerate() {
            writeln!(out, "    | {k} => {seed_expr}").unwrap();
        }
        out.push_str("    | _ => 0\n");
    }
    out.push_str("  | _ => 0\n");

    writeln!(out, "def guard {params} (c d : C) (choice : Nat × W) : Test cap :=\n  match choice.1 with").unwrap();
    for (i, guard) in step_guards.iter().enumerate() {
        writeln!(out, "  | {i} => {guard}").unwrap();
    }
    out.push_str("  | _ => Test.pure False\n");

    writeln!(out, "def transfer {params} (c d : C) (choice : Nat × W) (k : Fin SlotCount) : Transfer cap :=\n  match choice.1 with")
        .unwrap();
    for (i, transfers) in step_transfers.iter().enumerate() {
        writeln!(out, "  | {i} => match k.val with").unwrap();
        for (k, tr) in transfers.iter().enumerate() {
            writeln!(out, "    | {k} => {tr}").unwrap();
        }
        out.push_str("    | _ => Transfer.keep\n");
    }
    out.push_str("  | _ => Transfer.keep\n");

    writeln!(out, "def observe {params} (c : C) : Test cap := {}", fold_test(observations, "conj", "True")).unwrap();
    if constrained {
        writeln!(out, "def initObserve {params} (c : C) : Test cap := {}", fold_test(init_obs, "conj", "True")).unwrap();
        writeln!(out, "def constraint {params} (c : C) : Test cap := {}", fold_test(constraints, "conj", "True")).unwrap();
        writeln!(out, "def actionConstraint {params} (c d : C) : Prop := {}", fold_prop(action_constraints)).unwrap();
        writeln!(out, "def actionObserve {params} (c d : C) : Prop := {}", fold_prop(action_obs)).unwrap();
    }

    out.push_str(
        "def model : ThresholdCounterRule.Model C (Nat × W) SlotCount where\n\
         \x20 cap := cap\n\
         \x20 initial := initial sem\n\
         \x20 seed := seed sem\n\
         \x20 guard := guard sem\n\
         \x20 transfer := transfer sem\n\
         \x20 observe := observe sem\n",
    );
    if constrained {
        out.push_str(
            "  initObserve := initObserve sem\n\
             \x20 constraint := constraint sem\n\
             \x20 actionConstraint := actionConstraint sem\n\
             \x20 actionObserve := actionObserve sem\n",
        );
    }

    Some(OpenCert::new(out, include_str!("certificate.lean"), "GeneratedThresholdCounter", constrained, false, false))
}

struct Emitter<'a> {
    program: &'a Program,
    cfg: &'a Config,
    domains: &'a Domains,
    counters: BTreeMap<VarId, CounterSpec>,
    slots: Vec<SlotKind>,
    atoms: Vec<String>,
    scope: Vec<(LocalId, Atom)>,
    opaque_cache: &'a mut HashMap<DefId, Option<BTreeSet<VarId>>>,
    remaining: usize,
}

impl Emitter<'_> {
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
                        return true;
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

    fn atom(&mut self, e: &Expr, observation: bool) -> Option<String> {
        self.tick(1)?;
        if !self.independent(e) {
            return None;
        }
        let id = self.atoms.len();
        if self.scope.is_empty() {
            self.atoms.push(format!("{e:#?}"));
        } else {
            self.atoms.push(format!("{e:#?}\nBound atoms: {:?}", self.scope));
        }
        Some(if observation { format!("sem.observe {id} c") } else { format!("sem.test {id} c d choice.2") })
    }

    fn action_test(&mut self, e: &Expr) -> Option<String> {
        self.tick(1)?;
        if !self.independent(e) {
            return None;
        }
        let id = self.atoms.len();
        self.atoms.push(format!("{e:#?}"));
        Some(format!("(sem.actionTest {id} c d)"))
    }

    fn slot_index_eq(&mut self, index: &Expr, key: &Atom, observation: bool) -> Option<String> {
        self.tick(1)?;
        if !self.independent(index) {
            return None;
        }
        let id = self.atoms.len();
        self.atoms.push(format!("Slot equality: index {index:#?} = atom {key:?}\nBound atoms: {:?}", self.scope));
        Some(if observation { format!("sem.observe {id} c") } else { format!("sem.test {id} c d choice.2") })
    }

    fn resolve_known_atom(&self, e: &Expr) -> Option<Atom> {
        if let ExprKind::Local(id) = &*e.kind {
            if let Some((_, a)) = self.scope.iter().rev().find(|(l, _)| l == id) {
                return Some(a.clone());
            }
        }
        self.domains.atom_value(e)
    }

    fn lower_branch_bounds(&mut self, bounds: &[Bound]) -> Option<Vec<String>> {
        let mut out = Vec::new();
        for bound in bounds {
            if !self.independent(&bound.set) {
                return None;
            }
            let span = bound.set.span;
            match &bound.vars {
                BoundVars::Many(ids) => {
                    for &l in ids {
                        let mem = Expr::new(
                            ExprKind::Builtin { op: B::In, args: vec![Expr::new(ExprKind::Local(l), span), bound.set.clone()] },
                            span,
                        );
                        out.push(self.atom(&mem, false)?);
                    }
                }
                BoundVars::Tuple(ids) => {
                    let elems = ids.iter().map(|&l| Expr::new(ExprKind::Local(l), span)).collect();
                    let mem = Expr::new(
                        ExprKind::Builtin { op: B::In, args: vec![Expr::new(ExprKind::Tuple(elems), span), bound.set.clone()] },
                        span,
                    );
                    out.push(self.atom(&mem, false)?);
                }
            }
        }
        Some(out)
    }

    fn with_map_ctor_slot<T>(&mut self, bounds: &[Bound], slot_key: &Atom, f: impl FnOnce(&mut Self, LocalId) -> Option<T>) -> Option<T> {
        let [bound] = bounds else { return None };
        let BoundVars::Many(ids) = &bound.vars else { return None };
        let [local] = ids.as_slice() else { return None };
        self.scope.push((*local, slot_key.clone()));
        let res = f(self, *local);
        self.scope.pop();
        res
    }

    fn init_branch(&mut self, b: &Branch) -> Option<(String, Vec<String>)> {
        let mut preds: Vec<String> = self.lower_branch_bounds(&b.bounds)?.into_iter().map(|a| format!("({a})")).collect();
        for term in &b.terms {
            if matches!(&*term.kind, ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 && variable(&args[0], false).is_some_and(|v| self.counters.contains_key(&v)))
            {
                continue;
            }
            preds.push(format!("({})", self.atom(term, false)?));
        }

        let mut seeds = Vec::with_capacity(self.slots.len());
        let slots_snapshot = self.slots.clone();
        for slot in &slots_snapshot {
            let rhs = binding(b, slot.var(), false)?;
            let seed_expr = match slot {
                SlotKind::Scalar { .. } => self.lower_scalar_init(&rhs)?,
                SlotKind::Map { key, .. } => self.lower_map_init(key, &rhs)?,
            };
            seeds.push(seed_expr);
        }
        Some((fold_prop(preds), seeds))
    }

    fn lower_scalar_init(&mut self, rhs: &Expr) -> Option<String> {
        self.tick(1)?;
        if let Some(n) = atom_nat(self.domains, rhs) {
            return Some(n.to_string());
        }
        if let ExprKind::If { cond, then, els } = &*rhs.kind {
            let c = self.atom(cond, false)?;
            let t = self.lower_scalar_init(then)?;
            let f = self.lower_scalar_init(els)?;
            return Some(format!("(if ({c}) then {t} else {f})"));
        }
        None
    }

    fn lower_map_init(&mut self, slot_key: &Atom, rhs: &Expr) -> Option<String> {
        self.tick(1)?;
        match &*rhs.kind {
            ExprKind::FnConstruct { bounds, body } => self.with_map_ctor_slot(bounds, slot_key, |this, _| this.lower_scalar_init(body)),
            ExprKind::If { cond, then, els } => {
                let c = self.atom(cond, false)?;
                let t = self.lower_map_init(slot_key, then)?;
                let f = self.lower_map_init(slot_key, els)?;
                Some(format!("(if ({c}) then {t} else {f})"))
            }
            _ => None,
        }
    }

    fn step_branch(&mut self, b: &Branch) -> Option<(String, Vec<String>)> {
        let mut guards: Vec<String> = self.lower_branch_bounds(&b.bounds)?.into_iter().map(|a| format!("(Test.pure ({a}))")).collect();
        for term in &b.terms {
            if matches!(&*term.kind, ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 && variable(&args[0], true).is_some_and(|v| self.counters.contains_key(&v)))
            {
                continue;
            }
            if let ExprKind::Builtin { op: B::Unchanged, args } = &*term.kind {
                if args.len() == 1 && ordinary_unchanged(&args[0]) {
                    let mut retained = Vec::new();
                    self.collect_retained_unchanged(&args[0], &mut retained)?;
                    for v_expr in retained {
                        let frame = Expr::new(ExprKind::Builtin { op: B::Unchanged, args: vec![v_expr] }, term.span);
                        guards.push(format!("(Test.pure ({}))", self.atom(&frame, false)?));
                    }
                    continue;
                }
            }
            guards.push(self.test(term, false)?);
        }

        let mut transfers = Vec::with_capacity(self.slots.len());
        let slots_snapshot = self.slots.clone();
        for slot in &slots_snapshot {
            let rhs = binding(b, slot.var(), true)?;
            let tr = match slot {
                SlotKind::Scalar { var, .. } => self.lower_scalar_transfer(*var, &rhs)?,
                SlotKind::Map { var, key, .. } => self.lower_map_transfer(*var, key, &rhs)?,
            };
            transfers.push(tr);
        }

        Some((fold_test(guards, "conj", "True"), transfers))
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
            return Some("Transfer.keep".into());
        }
        if let Some(r) = atom_nat(self.domains, rhs) {
            return Some(format!("(Transfer.reset {r})"));
        }
        match &*rhs.kind {
            ExprKind::Builtin { op: B::Plus, args } if args.len() == 2 => {
                for (lhs, delta_e) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                    if variable(lhs, false) == Some(var) {
                        if let Some(d) = atom_nat(self.domains, delta_e) {
                            return Some(format!("(Transfer.add {d})"));
                        }
                    }
                }
                None
            }
            ExprKind::If { cond, then, els } => {
                let c = self.test(cond, false)?;
                let t = self.lower_scalar_transfer(var, then)?;
                let f = self.lower_scalar_transfer(var, els)?;
                self.tick(c.len() + t.len() + f.len())?;
                Some(format!("(Transfer.ite {c} {t} {f})"))
            }
            _ => None,
        }
    }

    fn lower_map_transfer(&mut self, var: VarId, slot_key: &Atom, rhs: &Expr) -> Option<String> {
        self.tick(1)?;
        if variable(rhs, false) == Some(var) {
            return Some("Transfer.keep".into());
        }
        match &*rhs.kind {
            ExprKind::FnConstruct { bounds, body } => self.with_map_ctor_slot(bounds, slot_key, |this, local| {
                let idx = Expr::new(ExprKind::Local(local), body.span);
                this.lower_map_slot_transfer(var, &idx, body)
            }),
            ExprKind::Except { base, updates } if variable(base, false) == Some(var) => {
                let mut result = "Transfer.keep".to_owned();
                for (path, val) in updates {
                    let [ExceptKey::Index(indices)] = path.as_slice() else { return None };
                    let [idx] = indices.as_slice() else { return None };
                    if let Some(known) = self.resolve_known_atom(idx) {
                        if known == *slot_key {
                            result = self.lower_map_slot_transfer(var, idx, val)?;
                        }
                    } else {
                        let upd = self.lower_map_slot_transfer(var, idx, val)?;
                        let cond = self.slot_index_eq(idx, slot_key, false)?;
                        self.tick(cond.len() + upd.len() + result.len())?;
                        result = format!("(Transfer.ite (Test.pure ({cond})) {upd} {result})");
                    }
                }
                Some(result)
            }
            ExprKind::If { cond, then, els } => {
                let c = self.test(cond, false)?;
                let t = self.lower_map_transfer(var, slot_key, then)?;
                let f = self.lower_map_transfer(var, slot_key, els)?;
                self.tick(c.len() + t.len() + f.len())?;
                Some(format!("(Transfer.ite {c} {t} {f})"))
            }
            _ => None,
        }
    }

    fn lower_map_slot_transfer(&mut self, var: VarId, idx: &Expr, val: &Expr) -> Option<String> {
        self.tick(1)?;
        if matches!(&*val.kind, ExprKind::FnApp { func, args } if args.len() == 1 && variable(func, false) == Some(var) && expr_structurally_eq(&args[0], idx))
        {
            return Some("Transfer.keep".into());
        }
        if let Some(r) = atom_nat(self.domains, val) {
            return Some(format!("(Transfer.reset {r})"));
        }
        match &*val.kind {
            ExprKind::Builtin { op: B::Plus, args } if args.len() == 2 => {
                for (lhs, delta_e) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                    if matches!(&*lhs.kind, ExprKind::FnApp { func, args } if args.len() == 1 && variable(func, false) == Some(var) && expr_structurally_eq(&args[0], idx))
                    {
                        if let Some(d) = atom_nat(self.domains, delta_e) {
                            return Some(format!("(Transfer.add {d})"));
                        }
                    }
                }
                None
            }
            ExprKind::If { cond, then, els } => {
                let c = self.test(cond, false)?;
                let t = self.lower_map_slot_transfer(var, idx, then)?;
                let f = self.lower_map_slot_transfer(var, idx, els)?;
                self.tick(c.len() + t.len() + f.len())?;
                Some(format!("(Transfer.ite {c} {t} {f})"))
            }
            _ => None,
        }
    }

    fn test(&mut self, e: &Expr, observation: bool) -> Option<String> {
        self.tick(1)?;
        if self.independent(e) {
            return Some(format!("(Test.pure ({}))", self.atom(e, observation)?));
        }
        match &*e.kind {
            ExprKind::And(es) | ExprKind::Or(es) => {
                let and = matches!(&*e.kind, ExprKind::And(_));
                let parts = es.iter().map(|x| self.test(x, observation)).collect::<Option<Vec<_>>>()?;
                Some(fold_test(parts, if and { "conj" } else { "disj" }, if and { "True" } else { "False" }))
            }
            ExprKind::If { cond, then, els } => {
                let c = self.test(cond, observation)?;
                let t = self.test(then, observation)?;
                let f = self.test(els, observation)?;
                self.tick(c.len() * 2 + t.len() + f.len())?;
                Some(format!("(Test.disj (Test.conj {c} {t}) (Test.conj (Test.neg {c}) {f}))"))
            }
            ExprKind::Quant { kind, bounds, body } => self.lower_quant(*kind, bounds, body, observation),
            ExprKind::Builtin { op, args } => match (op, args.as_slice()) {
                (B::Not, [p]) => Some(format!("(Test.neg {})", self.test(p, observation)?)),
                (B::Implies, [p, q]) => {
                    Some(format!("(Test.disj (Test.neg {}) {})", self.test(p, observation)?, self.test(q, observation)?))
                }
                (B::Equiv, [p, q]) => {
                    let lp = self.test(p, observation)?;
                    let lq = self.test(q, observation)?;
                    self.tick(lp.len() * 2 + lq.len() * 2)?;
                    Some(format!("(Test.disj (Test.conj {lp} {lq}) (Test.conj (Test.neg {lp}) (Test.neg {lq})))"))
                }
                (B::Lt | B::Le | B::Gt | B::Ge | B::Eq | B::Neq, [a, b]) => {
                    if let Some(cmp) = self.lower_comparison(*op, a, b, observation) {
                        return Some(cmp);
                    }
                    if matches!(op, B::Eq | B::Neq) {
                        let neg = *op == B::Neq;
                        if self.independent(a) && matches!(&*b.kind, ExprKind::If { .. }) {
                            let eq = self.lower_eq_if(a, b, false, observation)?;
                            return Some(if neg { format!("(Test.neg {eq})") } else { eq });
                        }
                        if self.independent(b) && matches!(&*a.kind, ExprKind::If { .. }) {
                            let eq = self.lower_eq_if(b, a, true, observation)?;
                            return Some(if neg { format!("(Test.neg {eq})") } else { eq });
                        }
                    }
                    None
                }
                (B::In | B::NotIn, [a, b]) => {
                    let mem = self.lower_membership(a, b, observation)?;
                    Some(if *op == B::NotIn { format!("(Test.neg {mem})") } else { mem })
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn lower_quant(&mut self, kind: QuantKind, bounds: &[Bound], body: &Expr, observation: bool) -> Option<String> {
        let mut flat: Vec<(LocalId, Vec<Atom>)> = Vec::new();
        for b in bounds {
            let BoundVars::Many(ids) = &b.vars else { return None };
            let atoms: Vec<Atom> = self.domains.exact_set(&b.set)?.into_iter().collect();
            for &id in ids {
                flat.push((id, atoms.clone()));
            }
        }
        let mut results = Vec::new();
        self.expand_quant(&flat, body, observation, &mut results)?;
        let is_all = matches!(kind, QuantKind::Forall);
        Some(fold_test(results, if is_all { "conj" } else { "disj" }, if is_all { "True" } else { "False" }))
    }

    fn expand_quant(&mut self, rest: &[(LocalId, Vec<Atom>)], body: &Expr, observation: bool, out: &mut Vec<String>) -> Option<()> {
        let Some(((id, atoms), tail)) = rest.split_first() else {
            out.push(self.test(body, observation)?);
            return Some(());
        };
        for atom in atoms {
            self.scope.push((*id, atom.clone()));
            let res = self.expand_quant(tail, body, observation, out);
            self.scope.pop();
            res?;
        }
        Some(())
    }

    fn lower_eq_if(&mut self, other: &Expr, expr: &Expr, other_on_right: bool, observation: bool) -> Option<String> {
        self.tick(1)?;
        if let ExprKind::If { cond, then, els } = &*expr.kind {
            let c = self.test(cond, observation)?;
            let t = self.lower_eq_if(other, then, other_on_right, observation)?;
            let f = self.lower_eq_if(other, els, other_on_right, observation)?;
            self.tick(c.len() * 2 + t.len() + f.len())?;
            Some(format!("(Test.disj (Test.conj {c} {t}) (Test.conj (Test.neg {c}) {f}))"))
        } else {
            let args = if other_on_right { vec![expr.clone(), other.clone()] } else { vec![other.clone(), expr.clone()] };
            let eq = Expr::new(ExprKind::Builtin { op: B::Eq, args }, expr.span);
            Some(format!("(Test.pure ({}))", self.atom(&eq, observation)?))
        }
    }

    fn lower_comparison(&mut self, op: B, a: &Expr, b: &Expr, observation: bool) -> Option<String> {
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
            // Scalar counter slot.
            if let Some(v) = variable(slot_e, false) {
                if let Some(k) = self.slots.iter().position(|s| matches!(s, SlotKind::Scalar { var, .. } if *var == v)) {
                    return self.emit_slot_cmp(k, norm_op, thresh);
                }
            }
            // Map counter slot `v[idx]`.
            if let ExprKind::FnApp { func, args } = &*slot_e.kind {
                if args.len() == 1 {
                    if let Some(v) = variable(func, false) {
                        if matches!(self.counters.get(&v).map(|c| &c.kind), Some(CounterKind::Map(_))) {
                            return self.lower_map_slot_cmp(v, &args[0], norm_op, thresh, observation);
                        }
                    }
                }
            }
        }
        None
    }

    fn emit_slot_cmp(&mut self, k: usize, op: B, thresh: i128) -> Option<String> {
        self.tick(1)?;
        if thresh < 0 {
            let truth = matches!(op, B::Gt | B::Ge | B::Neq);
            return Some(format!("(Test.pure {})", if truth { "True" } else { "False" }));
        }
        let req = required_cap(op, thresh, false)?;
        if req > self.slots[k].cap() {
            return None;
        }
        let cmp_ctor = match op {
            B::Lt => "Cmp.lt",
            B::Le => "Cmp.le",
            B::Eq => "Cmp.eq",
            B::Neq => "Cmp.ne",
            B::Gt => "Cmp.gt",
            B::Ge => "Cmp.ge",
            _ => return None,
        };
        Some(format!("(Test.cmp ⟨{k}, by decide⟩ {cmp_ctor} {thresh} (by decide))"))
    }

    fn lower_map_slot_cmp(&mut self, var: VarId, idx: &Expr, op: B, thresh: i128, observation: bool) -> Option<String> {
        if let Some(known) = self.resolve_known_atom(idx) {
            let k = self.slots.iter().position(|s| matches!(s, SlotKind::Map { var: v, key, .. } if *v == var && *key == known))?;
            return self.emit_slot_cmp(k, op, thresh);
        }
        let matching: Vec<(usize, Atom)> = self
            .slots
            .iter()
            .enumerate()
            .filter_map(|(k, s)| match s {
                SlotKind::Map { var: v, key, .. } if *v == var => Some((k, key.clone())),
                _ => None,
            })
            .collect();
        if matching.is_empty() {
            return None;
        }
        let mut alts = Vec::with_capacity(matching.len());
        for (k, key) in matching {
            let eq = self.slot_index_eq(idx, &key, observation)?;
            let cmp = self.emit_slot_cmp(k, op, thresh)?;
            alts.push(format!("(Test.conj (Test.pure ({eq})) {cmp})"));
        }
        Some(fold_test(alts, "disj", "False"))
    }

    fn lower_membership(&mut self, elem: &Expr, set: &Expr, observation: bool) -> Option<String> {
        // Scalar counter membership.
        if let Some(v) = variable(elem, false) {
            if let Some(k) = self.slots.iter().position(|s| matches!(s, SlotKind::Scalar { var, .. } if *var == v)) {
                return self.lower_slot_nat_set(k, set);
            }
            // Whole-map membership `v \in [D -> R]`.
            if matches!(self.counters.get(&v).map(|c| &c.kind), Some(CounterKind::Map(_))) {
                if let ExprKind::FnSet { range, .. } = &*set.kind {
                    let ks: Vec<usize> = self.slots.iter().enumerate().filter_map(|(k, s)| (s.var() == v).then_some(k)).collect();
                    let parts = ks.into_iter().map(|k| self.lower_slot_nat_set(k, range)).collect::<Option<Vec<_>>>()?;
                    return Some(fold_test(parts, "conj", "True"));
                }
            }
        }
        // Map entry membership `v[idx] \in S`.
        if let ExprKind::FnApp { func, args } = &*elem.kind {
            if args.len() == 1 {
                if let Some(v) = variable(func, false) {
                    if matches!(self.counters.get(&v).map(|c| &c.kind), Some(CounterKind::Map(_))) {
                        if let Some(known) = self.resolve_known_atom(&args[0]) {
                            let k = self
                                .slots
                                .iter()
                                .position(|s| matches!(s, SlotKind::Map { var, key, .. } if *var == v && *key == known))?;
                            return self.lower_slot_nat_set(k, set);
                        }
                        let matching: Vec<(usize, Atom)> = self
                            .slots
                            .iter()
                            .enumerate()
                            .filter_map(|(k, s)| match s {
                                SlotKind::Map { var, key, .. } if *var == v => Some((k, key.clone())),
                                _ => None,
                            })
                            .collect();
                        let mut alts = Vec::with_capacity(matching.len());
                        for (k, key) in matching {
                            let eq = self.slot_index_eq(&args[0], &key, observation)?;
                            let mem = self.lower_slot_nat_set(k, set)?;
                            alts.push(format!("(Test.conj (Test.pure ({eq})) {mem})"));
                        }
                        return Some(fold_test(alts, "disj", "False"));
                    }
                }
            }
        }
        None
    }

    fn lower_slot_nat_set(&mut self, k: usize, set: &Expr) -> Option<String> {
        match &*set.kind {
            ExprKind::Builtin { op: B::Nat | B::Int, args } if args.is_empty() => Some("(Test.pure True)".into()),
            ExprKind::Builtin { op: B::DotDot, args } if args.len() == 2 => {
                let (Atom::Num(lo), Atom::Num(hi)) = (self.domains.atom_value(&args[0])?, self.domains.atom_value(&args[1])?) else {
                    return None;
                };
                if lo > hi || hi < 0 {
                    return Some("(Test.pure False)".into());
                }
                let lo_cmp = self.emit_slot_cmp(k, B::Ge, lo.max(0))?;
                let hi_cmp = self.emit_slot_cmp(k, B::Le, hi)?;
                Some(format!("(Test.conj {lo_cmp} {hi_cmp})"))
            }
            ExprKind::SetEnum(es) => {
                let mut eqs = Vec::new();
                for item in es {
                    let Atom::Num(n) = self.domains.atom_value(item)? else { return None };
                    if n >= 0 {
                        eqs.push(self.emit_slot_cmp(k, B::Eq, n)?);
                    }
                }
                Some(fold_test(eqs, "disj", "False"))
            }
            _ => None,
        }
    }
}

fn fold_test(tests: Vec<String>, op: &str, identity: &str) -> String {
    tests.into_iter().rev().fold(format!("(Test.pure {identity})"), |tail, head| format!("(Test.{op} {head} {tail})"))
}

fn fold_prop(props: Vec<String>) -> String {
    props.into_iter().rev().fold("True".to_owned(), |tail, head| format!("({head} ∧ {tail})"))
}
