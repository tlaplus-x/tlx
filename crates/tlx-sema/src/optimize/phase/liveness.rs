//! Backward liveness on (control value, record field) pairs. Reads are roots;
//! an untouched live successor field makes its predecessor field live.

mod lean;

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use crate::{builtins::Builtin as B, hir::*, visit, Program};

use super::domain::{Atom, Domain, Domains};
use super::{binding, variable, Branch, FieldProjection};

struct Analysis<'a> {
    domains: &'a Domains,
    var: VarId,
    control: &'a str,
    phases: &'a BTreeSet<Atom>,
    keys: Option<&'a BTreeSet<Atom>>,
    live: BTreeMap<Arc<str>, BTreeSet<Atom>>,
    remaining: usize,
}

struct Transfer {
    actor: Option<LocalId>,
    writes: BTreeMap<Arc<str>, Expr>,
    target: Option<Atom>,
}

pub(super) fn derive(
    program: &Program,
    domains: &Domains,
    var: VarId,
    control: &str,
    phases: &BTreeSet<Atom>,
    branches: (&[Branch], &[Branch]),
    spec: super::CheckSpec<'_>,
) -> Option<(FieldProjection, Option<super::OpenCert>)> {
    let (initial, steps) = branches;
    let (keys, fields) = match &domains.vars[var.idx()] {
        Domain::Record(fs) => (None, fs),
        Domain::Function(keys, range) => {
            let Domain::Record(fs) = &**range else { return None };
            (Some(keys), fs)
        }
        _ => return None,
    };
    let mut a = Analysis {
        domains,
        var,
        control,
        phases,
        keys,
        live: fields.keys().map(|f| (f.clone(), BTreeSet::new())).collect(),
        remaining: 100_000,
    };
    a.live.get_mut(control)?.extend(phases.iter().cloned());
    for e in spec.all_state_preds() {
        a.read(e, phases, None)?;
    }
    let mut edges = Vec::new();
    for branch in steps {
        let transfer = a.transfer(&binding(branch, var, true)?, branch)?;
        for bound in &branch.bounds {
            // Bounds moved out of conjunctions are conservatively read in all phases.
            a.read(&bound.set, phases, None)?;
        }
        let mut context = phases.clone();
        for term in &branch.terms {
            match &*term.kind {
                ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 && variable(&args[0], true) == Some(var) => {
                    for rhs in transfer.writes.values() {
                        a.read(rhs, &context, transfer.actor)?;
                    }
                }
                ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 && variable(&args[0], true).is_some() => {
                    a.read(&args[1], &context, transfer.actor)?;
                }
                ExprKind::Builtin { op: B::Unchanged, args } if args.len() == 1 => {
                    a.read_unchanged(&args[0])?;
                }
                _ => {
                    a.read(term, &context, transfer.actor)?;
                    if let Some(allowed) = a.guard(term, transfer.actor) {
                        context.retain(|p| allowed.contains(p));
                    }
                }
            }
        }
        for source in context {
            let target = transfer.target.as_ref().unwrap_or(&source).clone();
            edges.push((source, target, transfer.writes.keys().cloned().collect::<BTreeSet<_>>()));
        }
    }
    loop {
        let mut changed = false;
        for (source, target, writes) in &edges {
            for (field, live) in &mut a.live {
                if !writes.contains(field) && live.contains(target) {
                    changed |= live.insert(source.clone());
                }
            }
        }
        if !changed {
            break;
        }
    }
    let projection = a.view(program)?;
    let cert = lean::emit(&a, initial, steps, spec);
    Some((projection, cert))
}

impl Analysis<'_> {
    fn transfer(&self, rhs: &Expr, branch: &Branch) -> Option<Transfer> {
        let mut out = Transfer { actor: None, writes: BTreeMap::new(), target: None };
        if variable(rhs, false) == Some(self.var) {
            // An unchanged map can still have actor-specific guards. Using
            // one referenced actor keeps its phase context; other actors'
            // reads remain conservative in `read`.
            if self.keys.is_some() {
                out.actor = branch.terms.iter().find_map(|e| {
                    let ExprKind::Builtin { args, .. } = &*e.kind else { return None };
                    let (field, actor) = self.field(args.first()?)?;
                    (field == self.control).then_some(actor).flatten()
                });
            }
            return Some(out);
        }
        let ExprKind::Except { base, updates } = &*rhs.kind else { return None };
        if variable(base, false) != Some(self.var) {
            return None;
        }
        let locals = self.domains.locals(&branch.bounds);
        for (path, value) in updates {
            let field = match (self.keys, path.as_slice()) {
                (None, [ExceptKey::Field(f)]) => f,
                (Some(keys), [ExceptKey::Index(args), ExceptKey::Field(f)]) if args.len() == 1 => {
                    let ExprKind::Local(actor) = &*args[0].kind else { return None };
                    if out.actor.is_some_and(|old| old != *actor) {
                        return None;
                    }
                    // An EXCEPT outside the domain does not overwrite anything.
                    if !locals.get(actor)?.atoms()?.is_subset(keys) {
                        return None;
                    }
                    out.actor = Some(*actor);
                    f
                }
                _ => return None,
            };
            if !self.live.contains_key(field) || out.writes.insert(field.clone(), value.clone()).is_some() {
                return None;
            }
            if &**field == self.control {
                let phase = self.domains.atom_value(value)?;
                if !self.phases.contains(&phase) {
                    return None;
                }
                out.target = Some(phase);
            }
        }
        Some(out)
    }

    /// Recognize a field read without treating its structural base as a read
    /// of every field. Cross-actor reads conservatively apply in every phase.
    fn field<'e>(&self, e: &'e Expr) -> Option<(&'e str, Option<LocalId>)> {
        let ExprKind::Field { record, field } = &*e.kind else { return None };
        if self.keys.is_none() && variable(record, false) == Some(self.var) {
            return Some((field, None));
        }
        if self.keys.is_some() {
            if let ExprKind::FnApp { func, args } = &*record.kind {
                if variable(func, false) == Some(self.var) && args.len() == 1 {
                    if let ExprKind::Local(actor) = &*args[0].kind {
                        return Some((field, Some(*actor)));
                    }
                }
            }
        }
        None
    }

    fn read(&mut self, e: &Expr, context: &BTreeSet<Atom>, actor: Option<LocalId>) -> Option<()> {
        if self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        if let Some((field, reader)) = self.field(e) {
            let phases = if self.keys.is_some() && (actor.is_none() || actor != reader) { self.phases } else { context };
            // Missing fields can fail; the record shape is retained, so no
            // stored value can affect that error.
            if let Some(live) = self.live.get_mut(field) {
                live.extend(phases.iter().cloned());
            }
            return Some(());
        }
        if let ExprKind::Builtin { op: B::In, args } = &*e.kind {
            if args.len() == 2
                && variable(&args[0], false) == Some(self.var)
                && self.domains.belongs(&self.domains.vars[self.var.idx()], &args[1])
            {
                return Some(());
            }
        }
        match &*e.kind {
            ExprKind::Var(v) if *v == self.var => {
                for live in self.live.values_mut() {
                    live.extend(self.phases.iter().cloned());
                }
            }
            // These contexts change what a variable reference denotes. The
            // ordinary current-state read walk cannot justify a projection.
            ExprKind::Builtin { op: B::Prime, args } if args.len() == 1 && variable(&args[0], false).is_some_and(|v| v != self.var) => {}
            ExprKind::At | ExprKind::Builtin { op: B::Prime | B::Enabled, .. } => return None,
            _ => {
                let mut valid = true;
                visit::children(e, &mut |child| {
                    valid &= self.read(child, context, actor).is_some();
                });
                if !valid {
                    return None;
                }
            }
        }
        Some(())
    }

    fn read_unchanged(&mut self, e: &Expr) -> Option<()> {
        match &*e.kind {
            ExprKind::Var(_) => Some(()),
            ExprKind::Tuple(es) => {
                for e in es {
                    self.read_unchanged(e)?;
                }
                Some(())
            }
            _ => None,
        }
    }

    fn guard(&self, e: &Expr, actor: Option<LocalId>) -> Option<BTreeSet<Atom>> {
        let ExprKind::Builtin { op, args } = &*e.kind else { return None };
        if args.len() != 2 {
            return None;
        }
        let (field, reader) = self.field(&args[0])?;
        if field != self.control || reader != actor || (self.keys.is_some() && actor.is_none()) {
            return None;
        }
        let tested = match op {
            B::Eq | B::Neq => BTreeSet::from([self.domains.atom_value(&args[1])?]),
            B::In | B::NotIn => self.domains.exact_set(&args[1])?,
            _ => return None,
        };
        Some(if matches!(op, B::Neq | B::NotIn) { self.phases.difference(&tested).cloned().collect() } else { tested })
    }

    fn view(&self, program: &Program) -> Option<FieldProjection> {
        let span = program.vars[self.var.idx()].span;
        let var = Expr::new(ExprKind::Var(self.var), span);
        let local = LocalId(program.locals.len() as u32);
        let record = if self.keys.is_some() {
            Expr::new(ExprKind::FnApp { func: var.clone(), args: vec![Expr::new(ExprKind::Local(local), span)] }, span)
        } else {
            var.clone()
        };
        let mut updates = Vec::new();
        let mut fields = Vec::new();
        for (field, live) in &self.live {
            let dead: Vec<_> = self.phases.difference(live).map(|p| self.domains.atom_expr(p, span)).collect::<Option<_>>()?;
            if dead.is_empty() {
                continue;
            }
            let control = Expr::new(ExprKind::Field { record: record.clone(), field: self.control.into() }, span);
            let cond = Expr::new(ExprKind::Builtin { op: B::In, args: vec![control, Expr::new(ExprKind::SetEnum(dead), span)] }, span);
            let old = Expr::new(ExprKind::Field { record: record.clone(), field: field.clone() }, span);
            let value = Expr::new(ExprKind::If { cond, then: Expr::new(ExprKind::Bool(false), span), els: old }, span);
            updates.push((vec![ExceptKey::Field(field.clone())], value));
            fields.push(format!("{}{}.{field}", program.vars[self.var.idx()].name, if self.keys.is_some() { "[*]" } else { "" }));
        }
        if updates.is_empty() {
            return None;
        }
        let mut projected = Expr::new(ExprKind::Except { base: record, updates }, span);
        if self.keys.is_some() {
            let set = Expr::new(ExprKind::Builtin { op: B::Domain, args: vec![var] }, span);
            projected =
                Expr::new(ExprKind::FnConstruct { bounds: vec![Bound { vars: BoundVars::Many(vec![local]), set }], body: projected }, span);
        }
        let values = program
            .vars
            .iter()
            .enumerate()
            .map(|(i, v)| if i == self.var.idx() { projected.clone() } else { Expr::new(ExprKind::Var(VarId(i as u32)), v.span) })
            .collect();
        Some(FieldProjection { ordered: None, view: Expr::new(ExprKind::Tuple(values), span), fields, certificate: None })
    }
}
