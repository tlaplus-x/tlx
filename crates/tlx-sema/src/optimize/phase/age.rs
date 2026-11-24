//! Finite ages for a monotone logical clock and timestamped records in maps.
//! This rule has mathematical-natural clock semantics, not machine overflow
//! semantics. Concrete actions and timestamps are retained for trace replay.

use std::{collections::BTreeMap, sync::Arc};

use tlx_front::cfg::Config;

use crate::{builtins::Builtin as B, hir::*, visit, Program};

use super::{
    binding, branches,
    domain::{Atom, Domain, Domains},
    normalize::Normalizer,
    variable, Branch, FieldProjection,
};

mod lean;

struct Stamp {
    var: VarId,
    field: Arc<str>,
    cap: i128,
}

struct Proof<'a> {
    clock: VarId,
    stamps: Vec<Stamp>,
    domains: &'a Domains,
}

/// Prove a quotient for one logical clock. The caller must explicitly permit
/// mathematical clock semantics and apply the ordinary safety-only boundary.
pub fn age_projection(program: &Program, cfg: &Config, init: &Expr, next: &Expr, observations: &[Expr]) -> Option<FieldProjection> {
    age_projection_with_spec(program, cfg, init, next, super::CheckSpec::invariants_only(observations))
}

/// Prove a quotient for one logical clock covering invariants, state constraints,
/// and init properties.
pub fn age_projection_with_spec(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: super::CheckSpec<'_>,
) -> Option<FieldProjection> {
    let spec = spec.state_only()?;
    if !super::cfg_constants_supported(program, cfg) {
        return None;
    }
    let mut expand = Normalizer::with_config(program, cfg);
    let initial = branches(&expand.root(init)?)?;
    let steps = branches(&expand.root(next)?)?;
    let norm = spec.try_map(|e| expand.root(e))?;
    let norm_spec = norm.as_spec();
    let domains = Domains::infer(program, cfg, &initial, &steps)?;
    for i in 0..program.vars.len() {
        let clock = VarId(i as u32);
        if !initial.iter().all(|b| binding(b, clock, false).is_some_and(|e| matches!(&*e.kind, ExprKind::Num(0)))) {
            continue;
        }
        if !steps.iter().all(|b| binding(b, clock, true).is_some_and(|e| clock_transfer(&e, clock).is_some())) {
            continue;
        }
        let mut stamps = Vec::new();
        for (j, d) in domains.vars.iter().enumerate() {
            let Domain::Function(_, range) = d else { continue };
            let Some(records) = range.records() else { continue };
            let mut fields = BTreeMap::new();
            for r in records {
                for (k, d) in r {
                    if matches!(d, Domain::Integer(n) if n >= 0) {
                        fields.insert(k, ());
                    }
                }
            }
            // One timestamp field per map for now. Other shapes/fields stay
            // concrete; unsupported timestamp transfers refuse this clock.
            if fields.len() == 1 {
                stamps.push(Stamp { var: VarId(j as u32), field: fields.into_keys().next().unwrap(), cap: 0 });
            }
        }
        if stamps.is_empty() {
            continue;
        }
        let mut proof = Proof { clock, stamps, domains: &domains };
        if !initial.iter().all(|b| proof.branch(b, false))
            || !steps.iter().all(|b| proof.branch(b, true))
            || !norm_spec.all_state_preds().all(|e| proof.read(e))
            || (spec.is_constrained() && !super::sym_totality::check_age_observations_total(program, cfg, init, next, spec, clock))
        {
            continue;
        }
        let mut projection = proof.view(program);
        let mut combined = None;
        for (j, domain) in domains.vars.iter().enumerate() {
            let Some(history) = super::history::candidate(program, &domains, j, domain, &initial, &steps, norm_spec) else {
                continue;
            };
            if let Some(certificate) = lean::emit(&proof, &initial, &steps, norm_spec, Some(&history)) {
                let ExprKind::Tuple(values) = std::sync::Arc::make_mut(&mut projection.view.kind) else { unreachable!() };
                values[j] = history.summary;
                projection.fields.push(format!("{}.history", program.vars[j].name));
                combined = Some(certificate);
                break;
            }
        }
        let Some(certificate) = combined.or_else(|| lean::emit(&proof, &initial, &steps, norm_spec, None)) else { continue };
        let Some(certificate) = expand.attach_const_subst(certificate) else {
            continue;
        };
        projection.certificate = Some(certificate);
        return Some(projection);
    }
    None
}

fn clock_transfer(e: &Expr, clock: VarId) -> Option<bool> {
    if variable(e, false) == Some(clock) {
        return Some(false);
    }
    match &*e.kind {
        ExprKind::Builtin { op: B::Plus, args }
            if args.len() == 2 && variable(&args[0], false) == Some(clock) && matches!(&*args[1].kind, ExprKind::Num(1)) =>
        {
            Some(true)
        }
        _ => None,
    }
}

impl Proof<'_> {
    fn branch(&mut self, b: &Branch, primed: bool) -> bool {
        let Some(clock) = binding(b, self.clock, primed) else { return false };
        let tick = if primed { clock_transfer(&clock, self.clock) } else { Some(false) };
        let Some(tick) = tick else { return false };
        for i in 0..self.stamps.len() {
            let Some(rhs) = binding(b, self.stamps[i].var, primed) else { return false };
            if !self.transfer(&rhs, i, primed, tick) {
                return false;
            }
        }
        if !b.bounds.iter().all(|b| self.read(&b.set)) {
            return false;
        }
        b.terms.iter().all(|e| match &*e.kind {
            ExprKind::Builtin { op: B::Eq, args }
                if args.len() == 2
                    && variable(&args[0], primed).is_some_and(|v| v == self.clock || self.stamps.iter().any(|s| s.var == v)) =>
            {
                true
            }
            ExprKind::Builtin { op: B::Unchanged, args } if primed && args.len() == 1 => ordinary_unchanged(&args[0]),
            _ => self.read(e),
        })
    }

    fn transfer(&mut self, e: &Expr, i: usize, primed: bool, tick: bool) -> bool {
        let var = self.stamps[i].var;
        match &*e.kind {
            ExprKind::Var(v) => primed && *v == var,
            ExprKind::FnConstruct { bounds, body } if bounds.len() == 1 => {
                let Domain::Function(keys, _) = &self.domains.vars[var.idx()] else { return false };
                matches!(&bounds[0].vars, BoundVars::Many(ids) if ids.len() == 1)
                    && self.domains.exact_set(&bounds[0].set).as_ref() == Some(keys)
                    && self.record(body, i, primed, tick)
            }
            ExprKind::Except { base, updates } if primed && variable(base, false) == Some(var) => updates.iter().all(|(path, rhs)| {
                let Some((ExceptKey::Index(indices), rest)) = path.split_first() else { return false };
                if indices.len() != 1 || !self.read(&indices[0]) {
                    return false;
                }
                match rest {
                    [] => self.record(rhs, i, primed, tick),
                    [ExceptKey::Field(field)] if *field == self.stamps[i].field => !tick && variable(rhs, false) == Some(self.clock),
                    [ExceptKey::Field(_)] => self.read(rhs),
                    _ => false,
                }
            }),
            ExprKind::If { cond, then, els } => {
                self.read(cond) && self.transfer(then, i, primed, tick) && self.transfer(els, i, primed, tick)
            }
            _ => false,
        }
    }

    fn record(&mut self, e: &Expr, i: usize, primed: bool, tick: bool) -> bool {
        let ExprKind::Record(fields) = &*e.kind else { return false };
        fields.iter().all(|(k, e)| {
            if *k == self.stamps[i].field {
                if primed {
                    !tick && variable(e, false) == Some(self.clock)
                } else {
                    matches!(&*e.kind, ExprKind::Num(0))
                }
            } else {
                self.read(e)
            }
        })
    }

    fn entry<'a>(&self, e: &'a Expr) -> Option<(usize, &'a Expr)> {
        let ExprKind::FnApp { func, args } = &*e.kind else { return None };
        if args.len() != 1 {
            return None;
        }
        let v = variable(func, false)?;
        Some((self.stamps.iter().position(|s| s.var == v)?, &args[0]))
    }

    fn timestamp<'a>(&self, e: &'a Expr) -> Option<(usize, &'a Expr, i128)> {
        let (e, offset) = match &*e.kind {
            ExprKind::Builtin { op: B::Plus, args } if args.len() == 2 => {
                let Atom::Num(n) = self.domains.atom_value(&args[1])? else { return None };
                if !(0..=1_000_000).contains(&n) {
                    return None;
                }
                (&args[0], n)
            }
            _ => (e, 0),
        };
        let ExprKind::Field { record, field } = &*e.kind else { return None };
        let (i, index) = self.entry(record)?;
        (*field == self.stamps[i].field).then_some((i, index, offset))
    }

    fn read(&mut self, e: &Expr) -> bool {
        match &*e.kind {
            ExprKind::Var(v) if *v == self.clock || self.stamps.iter().any(|s| s.var == *v) => return false,
            ExprKind::Field { record, field } => {
                if let Some((i, index)) = self.entry(record) {
                    return *field != self.stamps[i].field && self.read(index);
                }
            }
            ExprKind::Builtin { op: B::In, args } if args.len() == 2 => {
                if let Some(v) = variable(&args[0], false) {
                    if (v == self.clock || self.stamps.iter().any(|s| s.var == v))
                        && self.domains.belongs(&self.domains.vars[v.idx()], &args[1])
                    {
                        return true;
                    }
                }
            }
            ExprKind::Builtin { op: B::Domain, args } if args.len() == 1 => {
                if variable(&args[0], false).is_some_and(|v| self.stamps.iter().any(|s| s.var == v)) {
                    return true;
                }
                if let Some((_, index)) = self.entry(&args[0]) {
                    return self.read(index);
                }
            }
            ExprKind::Builtin { op, args } if args.len() == 2 && matches!(op, B::Eq | B::Neq | B::Lt | B::Le | B::Gt | B::Ge) => {
                for (timestamp, clock, reversed) in [(&args[0], &args[1], false), (&args[1], &args[0], true)] {
                    if variable(clock, false) != Some(self.clock) {
                        continue;
                    }
                    if let Some((i, index, offset)) = self.timestamp(timestamp) {
                        if !self.read(index) {
                            return false;
                        }
                        let extra = match op {
                            B::Eq | B::Neq => true,
                            B::Lt | B::Ge => !reversed,
                            B::Le | B::Gt => reversed,
                            _ => unreachable!(),
                        };
                        self.stamps[i].cap = self.stamps[i].cap.max(offset + i128::from(extra));
                        return true;
                    }
                }
                if matches!(op, B::Eq | B::Neq) {
                    for (entry, literal) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                        if let Some((i, index)) = self.entry(entry) {
                            let ExprKind::Record(fs) = &*literal.kind else { continue };
                            // A literal without the timestamp has a different
                            // domain from every stamped record. Unstamped
                            // values and all their comparisons stay exact.
                            if fs.iter().all(|(k, _)| *k != self.stamps[i].field) {
                                return self.read(index) && self.read(literal);
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        let mut valid = true;
        visit::children(e, &mut |child| valid &= self.read(child));
        valid
    }

    fn view(&self, program: &Program) -> FieldProjection {
        let span = program.vars[self.clock.idx()].span;
        let make = |kind| Expr::new(kind, span);
        let builtin = |op, args| make(ExprKind::Builtin { op, args });
        let clock = make(ExprKind::Var(self.clock));
        let mut values: Vec<_> = (0..program.vars.len()).map(|i| make(ExprKind::Var(VarId(i as u32)))).collect();
        values[self.clock.idx()] = make(ExprKind::Num(0));
        for (i, stamp) in self.stamps.iter().enumerate() {
            let local = LocalId((program.locals.len() + i) as u32);
            let map = make(ExprKind::Var(stamp.var));
            let entry = make(ExprKind::FnApp { func: map.clone(), args: vec![make(ExprKind::Local(local))] });
            let field = make(ExprKind::Field { record: entry.clone(), field: stamp.field.clone() });
            let age = builtin(B::Minus, vec![clock.clone(), field]);
            let cap = make(ExprKind::Num(stamp.cap));
            let capped = make(ExprKind::If { cond: builtin(B::Ge, vec![age.clone(), cap.clone()]), then: cap, els: age });
            let projected =
                make(ExprKind::Except { base: entry.clone(), updates: vec![(vec![ExceptKey::Field(stamp.field.clone())], capped)] });
            let body = make(ExprKind::If {
                cond: builtin(B::In, vec![make(ExprKind::Str(stamp.field.clone())), builtin(B::Domain, vec![entry.clone()])]),
                then: projected,
                els: entry,
            });
            values[stamp.var.idx()] = make(ExprKind::FnConstruct {
                bounds: vec![Bound { vars: BoundVars::Many(vec![local]), set: builtin(B::Domain, vec![map]) }],
                body,
            });
        }
        FieldProjection {
            ordered: None,
            view: make(ExprKind::Tuple(values)),
            fields: self
                .stamps
                .iter()
                .map(|s| format!("{}.{}.age<={}", program.vars[s.var.idx()].name, s.field, s.cap))
                .chain(std::iter::once(format!("{}.logical-clock", program.vars[self.clock.idx()].name)))
                .collect(),
            certificate: None,
        }
    }
}

fn ordinary_unchanged(e: &Expr) -> bool {
    match &*e.kind {
        ExprKind::Var(_) => true,
        ExprKind::Tuple(es) => es.iter().all(ordinary_unchanged),
        _ => false,
    }
}
