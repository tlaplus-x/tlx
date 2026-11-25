//! Connect fixed nested numeric occurrences to explicit allocation transfers.
mod expressions;
mod live;
mod output;
mod schema;

use super::super::{
    domain::{Atom, Domains},
    max_local,
};
use super::{binding, syntax, variable, Branch, Family, OrderedPlan, OrderedShape};
use crate::{builtins::Builtin as B, hir::*, Program};
use schema::{Path, Schema, Slot};
use std::collections::{BTreeMap, BTreeSet};
use tlx_front::cfg::Config;

pub(super) fn emit(
    program: &Program,
    cfg: &Config,
    families: &[Family],
    plan: &OrderedPlan,
    initial: &[Branch],
    steps: &[Branch],
    spec: super::super::CheckSpec<'_>,
) -> Option<super::super::OpenCert> {
    if initial.is_empty() || steps.is_empty() {
        return None;
    }
    if let Some(h) = &plan.history {
        if plan.variables[h.variable].value.as_deref().is_some_and(schema::colored) {
            return None;
        }
    }
    let domains = Domains::infer(program, cfg, initial, steps)?;
    let mut fresh = program.locals.len() as u32;
    for b in initial.iter().chain(steps) {
        for bound in &b.bounds {
            for id in bound.vars.locals() {
                fresh = fresh.max(id.0);
            }
            fresh = fresh.max(max_local(&bound.set));
        }
        for term in &b.terms {
            fresh = fresh.max(max_local(term));
        }
    }
    for o in spec.all_state_preds() {
        fresh = fresh.max(max_local(o));
    }
    let mut context = Context { domains: &domains, schemas: vec![], aliases: BTreeMap::new(), fresh: fresh.checked_add(1)? };
    let initial = context.expand(initial)?;
    let mut schemas = vec![];
    for (i, shape) in plan.variables.iter().enumerate() {
        schemas.push(if plan.history.as_ref().is_some_and(|h| h.variable == i) {
            Schema::History
        } else {
            context.schema(&binding(&initial[0], VarId(i as u32), false)?, shape)?
        });
    }
    context.schemas = schemas;
    let steps = context.expand(steps)?;
    let mut slots = vec![];
    let mut plain = vec![];
    for (i, schema) in context.schemas.iter().enumerate() {
        schema.leaves(Path { var: VarId(i as u32), keys: vec![] }, &mut slots, &mut plain, families);
    }
    if slots.len() > 256 || plain.len() > 512 {
        return None;
    }
    let mut e = Emitter { context, families, plan, slots, plain, atoms: vec![], anchors: plan.anchors.clone(), targets: vec![] };
    let seeds = initial.iter().map(|b| e.seed(b)).collect::<Option<Vec<_>>>()?;
    let cases = steps.iter().map(|b| e.case(b)).collect::<Option<Vec<_>>>()?;
    let observation = e.tests(spec.invariants, Mode::Observe)?;
    let init_obs = e.tests(spec.init_props, Mode::Observe)?;
    let constraint = e.tests(spec.constraints, Mode::Observe)?;
    let action_constraint = e.action_tests(spec.action_constraints)?;
    let action_obs = e.action_tests(spec.action_props)?;
    Some(e.output(&seeds, &cases, &observation, &init_obs, &constraint, &action_constraint, &action_obs, spec.is_constrained()))
}

struct Context<'a> {
    domains: &'a Domains,
    schemas: Vec<Schema>,
    aliases: BTreeMap<LocalId, Atom>,
    fresh: u32,
}
impl Context<'_> {
    fn fresh(&mut self) -> Option<LocalId> {
        let id = LocalId(self.fresh);
        self.fresh = self.fresh.checked_add(1)?;
        Some(id)
    }
    fn atom(&self, e: &Expr) -> Option<Atom> {
        self.domains.state_atom_value(e, &self.aliases)
    }
    fn atom_expr(&mut self, a: &Atom, span: Span) -> Option<Expr> {
        if let Some(e) = self.domains.atom_expr(a, span) {
            return Some(e);
        }
        let id = if let Some((id, _)) = self.aliases.iter().find(|(_, v)| *v == a) {
            *id
        } else {
            let id = self.fresh()?;
            self.aliases.insert(id, a.clone());
            id
        };
        Some(Expr::new(ExprKind::Local(id), span))
    }
    fn keys(&self, e: &Expr) -> Option<BTreeSet<Atom>> {
        if let Some(keys) = self.domains.exact_set(e) {
            return Some(keys);
        }
        match &*e.kind {
            ExprKind::SetEnum(es) => es.iter().map(|e| self.atom(e)).collect(),
            ExprKind::Builtin { op: B::Cup, args } if args.len() == 2 => {
                let mut keys = self.keys(&args[0])?;
                keys.extend(self.keys(&args[1])?);
                Some(keys)
            }
            _ => None,
        }
    }
    fn expand(&mut self, branches: &[Branch]) -> Option<Vec<Branch>> {
        let mut out = vec![];
        for branch in branches {
            let mut pending = vec![branch.clone()];
            for _ in 0..branch.bounds.len() {
                let mut next = vec![];
                for b in pending {
                    let bound = b.bounds.first()?;
                    let BoundVars::Many(ids) = &bound.vars else { return None };
                    let mut alternatives = vec![Branch { bounds: b.bounds[1..].to_vec(), terms: b.terms.clone() }];
                    for id in ids {
                        let mut expanded = vec![];
                        for a in alternatives {
                            for key in self.keys(&bound.set)? {
                                let value = self.atom_expr(&key, bound.set.span)?;
                                let terms = a.terms.iter().map(|e| schema::substitute(e, *id, &value)).collect();
                                let bounds = a
                                    .bounds
                                    .iter()
                                    .map(|b| Bound { vars: b.vars.clone(), set: schema::substitute(&b.set, *id, &value) })
                                    .collect();
                                expanded.push(Branch { bounds, terms });
                                if expanded.len() > 512 {
                                    return None;
                                }
                            }
                        }
                        alternatives = expanded;
                    }
                    next.extend(alternatives);
                    if next.len() > 512 {
                        return None;
                    }
                }
                pending = next;
            }
            out.extend(pending);
            if out.len() > 512 {
                return None;
            }
        }
        (!out.is_empty()).then_some(out)
    }
}

#[derive(Clone, Copy)]
enum Mode {
    Initial,
    Step,
    Observe,
    Transfer(usize),
}
struct Seed {
    payload: Option<String>,
    guard: String,
    values: Vec<Vec<i128>>,
}
struct Case {
    payload: Option<String>,
    guard: String,
    deltas: Vec<i128>,
    values: Vec<Vec<String>>,
}
struct Emitter<'a, 'd> {
    context: Context<'d>,
    families: &'a [Family],
    plan: &'a OrderedPlan,
    slots: Vec<Slot>,
    plain: Vec<Path>,
    atoms: Vec<String>,
    anchors: Vec<Vec<i128>>,
    targets: Vec<String>,
}
impl Emitter<'_, '_> {
    fn validate_shapes(&mut self, b: &Branch, primed: bool) -> Option<()> {
        for (i, schema) in self.context.schemas.clone().iter().enumerate() {
            if !matches!(schema, Schema::History) {
                self.context.shape_matches(&binding(b, VarId(i as u32), primed)?, schema)?;
            }
        }
        Some(())
    }
    fn seed(&mut self, b: &Branch) -> Option<Seed> {
        self.validate_shapes(b, false)?;
        let mut values = vec![vec![]; self.families.len()];
        for slot in self.slots.clone() {
            let rhs = binding(b, slot.path.var, false)?;
            let e = self.context.select(&rhs, &slot.path.keys)?;
            let n = if let Some(Atom::Num(n)) = self.context.atom(&e) {
                n
            } else {
                let var = variable(&e, false)?;
                self.families.iter().find(|f| f.variable == var)?.initial
            };
            if n > self.families[slot.family].initial {
                return None;
            }
            values[slot.family].push(n);
        }
        Some(Seed { payload: self.history_payload(b, false)?, guard: self.guard(b, false)?, values })
    }
    fn case(&mut self, b: &Branch) -> Option<Case> {
        self.validate_shapes(b, true)?;
        let deltas = self
            .families
            .iter()
            .map(|f| {
                let e = syntax::increment(&binding(b, f.variable, true)?, f.variable)?;
                let Atom::Num(n) = self.context.atom(&e)? else { return None };
                (n >= 0).then_some(n)
            })
            .collect::<Option<Vec<_>>>()?;
        let mut values = vec![vec![]; self.families.len()];
        for slot in self.slots.clone() {
            let rhs = binding(b, slot.path.var, true)?;
            let value = self.context.select(&rhs, &slot.path.keys)?;
            values[slot.family].push(self.transfer(&value, slot.family, deltas[slot.family])?);
        }
        Some(Case { payload: self.history_payload(b, true)?, guard: self.guard(b, true)?, deltas, values })
    }
    fn guard(&mut self, b: &Branch, primed: bool) -> Option<String> {
        let mode = if primed { Mode::Step } else { Mode::Initial };
        let mut terms = vec![];
        for path in self.plain.clone() {
            let rhs = self.context.select(&binding(b, path.var, primed)?, &path.keys)?;
            let target = self.context.fresh()?;
            self.targets.push(format!("{target:?}: {} core leaf {path:?}", if primed { "next" } else { "initial" }));
            terms.push(Expr::new(
                ExprKind::Builtin { op: B::Eq, args: vec![Expr::new(ExprKind::Local(target), rhs.span), rhs] },
                Span::default(),
            ));
        }
        for term in &b.terms {
            if matches!(&*term.kind,ExprKind::Builtin{op:B::Eq,args} if args.len()==2 && variable(&args[0],primed).is_some()) {
                continue;
            }
            if matches!(&*term.kind,ExprKind::Builtin{op:B::Unchanged,args} if primed && args.len()==1 && syntax::frame(&args[0])) {
                continue;
            }
            terms.push(term.clone());
        }
        self.tests(&terms, mode)
    }
}
