//! Connect the inferred phase liveness table to explicit record and companion transfers.
mod leaves;
mod output;

use super::super::{binding, mentions_local, variable, Branch};
use super::{Analysis, Atom, Control, ObsContext, Slot};
use crate::{builtins::Builtin as B, hir::*};

pub(super) fn emit(
    a: &Analysis<'_>,
    initial: &[Branch],
    steps: &[Branch],
    spec: super::super::CheckSpec<'_>,
) -> Option<super::super::OpenCert> {
    let fields: Vec<Slot> = a.data_slots();
    let phases: Vec<Atom> = a.phases.iter().cloned().collect();
    let mut e = Emitter { a, fields, phases, atoms: vec![] };
    let seeds = initial.iter().map(|b| e.seed(b)).collect::<Option<Vec<_>>>()?;
    let mut cases = vec![];
    for (i, branch) in steps.iter().enumerate() {
        cases.extend(e.cases(i, branch)?);
        if cases.len() > 128 {
            return None;
        }
    }
    if cases.is_empty() || seeds.is_empty() || e.fields.is_empty() || a.keys.is_some_and(|keys| keys.len() > 256) {
        return None;
    }
    let mut observed = vec![vec![false; e.fields.len()]; e.phases.len()];
    let root_ctx = ObsContext::all(a.phases, a.keys.is_some());
    let observations = spec.invariants.iter().map(|o| e.obs_leaf(o, "observe", &root_ctx, &mut observed)).collect::<Option<Vec<_>>>()?;
    let init_obs = spec.init_props.iter().map(|o| e.obs_leaf(o, "observe", &root_ctx, &mut observed)).collect::<Option<Vec<_>>>()?;
    let constraints = spec.constraints.iter().map(|o| e.obs_leaf(o, "observe", &root_ctx, &mut observed)).collect::<Option<Vec<_>>>()?;
    let action_constraints =
        spec.action_constraints.iter().map(|o| e.action_leaf(o, "actionConstraint", &mut observed)).collect::<Option<Vec<_>>>()?;
    let action_props = spec.action_props.iter().map(|o| e.action_leaf(o, "actionObserve", &mut observed)).collect::<Option<Vec<_>>>()?;
    e.validate(&cases, &observed)?;
    Some(e.output(seeds, cases, observed, observations, init_obs, constraints, action_constraints, action_props, spec.is_constrained()))
}

struct Emitter<'a, 'd> {
    a: &'a Analysis<'d>,
    fields: Vec<Slot>,
    phases: Vec<Atom>,
    atoms: Vec<String>,
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
struct Case {
    branch: usize,
    actor: Option<LocalId>,
    source: usize,
    target: usize,
    reads: Reads,
    guard: String,
    values: Vec<Option<String>>,
}
struct Seed {
    guard: String,
    phase: usize,
    values: Vec<String>,
}

impl Emitter<'_, '_> {
    fn seed(&mut self, b: &Branch) -> Option<Seed> {
        let (phase, values) = match &self.a.control {
            Control::RecordField { var, field: ctrl_field } => {
                let rhs = binding(b, *var, false)?;
                let (record, key) = if let Some(keys) = self.a.keys {
                    let ExprKind::FnConstruct { bounds, body } = &*rhs.kind else { return None };
                    let [bound] = bounds.as_slice() else { return None };
                    let BoundVars::Many(ids) = &bound.vars else { return None };
                    let [id] = ids.as_slice() else { return None };
                    if self.a.domains.exact_set(&bound.set).as_ref() != Some(keys) {
                        return None;
                    }
                    (body, Some(*id))
                } else {
                    (&rhs, None)
                };
                let ExprKind::Record(fs) = &*record.kind else { return None };
                if fs.len() != self.fields.len() + 1 {
                    return None;
                }
                let phase = self.a.domains.atom_value(&fs.iter().find(|(f, _)| f == ctrl_field)?.1)?;
                let phase = self.phases.iter().position(|p| *p == phase)?;
                let mut values = vec![];
                for slot in &self.fields {
                    let Slot::RecordField(field) = slot else { return None };
                    let value = &fs.iter().find(|(f, _)| f == field)?.1;
                    if self.a.mentions_any_managed(value) {
                        return None;
                    }
                    let id = self.atoms.len();
                    self.atoms.push(format!("Seed field {field}: {value:#?}\nKey parameter: {key:?}"));
                    values.push(format!("(sem.seedValue {id} c choice.2 k)"));
                }
                (phase, values)
            }
            Control::Var { var: ctrl } => {
                let ctrl_rhs = binding(b, *ctrl, false)?;
                let phase_expr = if let Some(keys) = self.a.keys {
                    let ExprKind::FnConstruct { bounds, body } = &*ctrl_rhs.kind else { return None };
                    let [bound] = bounds.as_slice() else { return None };
                    let BoundVars::Many(ids) = &bound.vars else { return None };
                    let [id] = ids.as_slice() else { return None };
                    if self.a.domains.exact_set(&bound.set).as_ref() != Some(keys) || mentions_local(body, *id) {
                        return None;
                    }
                    body
                } else {
                    &ctrl_rhs
                };
                let phase = self.a.domains.atom_value(phase_expr)?;
                let phase = self.phases.iter().position(|p| *p == phase)?;
                let mut values = vec![];
                for slot in &self.fields {
                    let Slot::CompanionVar(v) = *slot else { return None };
                    let rhs = binding(b, v, false)?;
                    let (value, key) = if let Some(keys) = self.a.keys {
                        let ExprKind::FnConstruct { bounds, body } = &*rhs.kind else { return None };
                        let [bound] = bounds.as_slice() else { return None };
                        let BoundVars::Many(ids) = &bound.vars else { return None };
                        let [id] = ids.as_slice() else { return None };
                        if self.a.domains.exact_set(&bound.set).as_ref() != Some(keys) {
                            return None;
                        }
                        (body, Some(*id))
                    } else {
                        (&rhs, None)
                    };
                    if self.a.mentions_any_managed(value) {
                        return None;
                    }
                    let id = self.atoms.len();
                    self.atoms.push(format!("Seed companion {v:?}: {value:#?}\nKey parameter: {key:?}"));
                    values.push(format!("(sem.seedValue {id} c choice.2 k)"));
                }
                (phase, values)
            }
        };
        let mut reads = Reads::new(self.fields.len());
        let guard = self.guard(b, false, None, &mut reads)?;
        Some(Seed { guard, phase, values })
    }

    fn guard(&mut self, b: &Branch, primed: bool, actor: Option<LocalId>, reads: &mut Reads) -> Option<String> {
        let kind = if primed { "test" } else { "initial" };
        let mut terms = vec![];
        for bound in &b.bounds {
            let BoundVars::Many(ids) = &bound.vars else { return None };
            for id in ids {
                let member = Expr::new(
                    ExprKind::Builtin { op: B::In, args: vec![Expr::new(ExprKind::Local(*id), bound.set.span), bound.set.clone()] },
                    bound.set.span,
                );
                terms.push(self.leaf(&member, kind, actor, reads)?);
            }
        }
        for term in &b.terms {
            // These predicates are the explicit finite source-phase dispatch.
            if primed && self.a.guard(term, actor).is_some() {
                continue;
            }
            if matches!(
                &*term.kind,
                ExprKind::Builtin { op: B::Eq, args }
                    if args.len() == 2 && variable(&args[0], primed).is_some_and(|v| self.a.is_control_or_projected_var(v))
            ) {
                continue;
            }
            let term = if let ExprKind::Builtin { op: B::Unchanged, args } = &*term.kind {
                if !primed || args.len() != 1 {
                    return None;
                }
                Expr::new(ExprKind::Builtin { op: B::Unchanged, args: vec![self.frames(&args[0])?] }, term.span)
            } else {
                term.clone()
            };
            terms.push(self.leaf(&term, kind, actor, reads)?);
        }
        Some(conjunction(&terms))
    }

    fn frames(&self, e: &Expr) -> Option<Expr> {
        let kind = match &*e.kind {
            ExprKind::Var(v) if self.a.is_control_or_projected_var(*v) => ExprKind::Tuple(vec![]),
            ExprKind::Var(_) => return Some(e.clone()),
            ExprKind::Tuple(es) => ExprKind::Tuple(es.iter().map(|e| self.frames(e)).collect::<Option<_>>()?),
            _ => return None,
        };
        Some(Expr::new(kind, e.span))
    }

    fn cases(&mut self, branch: usize, b: &Branch) -> Option<Vec<Case>> {
        let transfer = self.a.transfer_branch(b)?;
        let mut allowed = self.a.phases.clone();
        for term in &b.terms {
            if let Some(phases) = self.a.guard(term, transfer.actor) {
                allowed.retain(|p| phases.contains(p));
            }
        }
        let mut out = vec![];
        for source in allowed {
            let source = self.phases.iter().position(|p| *p == source)?;
            let target = transfer.target.as_ref().map(|target| self.phases.iter().position(|p| p == target)).unwrap_or(Some(source))?;
            let mut reads = Reads::new(self.fields.len());
            let guard = self.guard(b, true, transfer.actor, &mut reads)?;
            let mut values = vec![];
            for f in 0..self.fields.len() {
                let value = if let Some(rhs) = transfer.writes.get(&self.fields[f]) {
                    Some(self.leaf(rhs, "value", transfer.actor, &mut reads)?)
                } else {
                    None
                };
                values.push(value);
            }
            out.push(Case { branch, actor: transfer.actor, source, target, reads, guard, values });
        }
        Some(out)
    }

    fn validate(&self, cases: &[Case], observed: &[Vec<bool>]) -> Option<()> {
        // These are also emitted as finite, closed Lean obligations.
        for (f, slot) in self.fields.iter().enumerate() {
            let live = &self.a.live[slot];
            for (p_idx, p) in self.phases.iter().enumerate() {
                if observed[p_idx][f] && !live.contains(p) {
                    return None;
                }
            }
            for c in cases {
                if (c.reads.actor[f] && !live.contains(&self.phases[c.source]))
                    || (c.reads.global[f] && !self.phases.iter().all(|p| live.contains(p)))
                    || (c.values[f].is_none() && live.contains(&self.phases[c.target]) && !live.contains(&self.phases[c.source]))
                {
                    return None;
                }
            }
        }
        Some(())
    }
}
fn conjunction(parts: &[String]) -> String {
    if parts.is_empty() {
        "True".into()
    } else {
        format!("({})", parts.join(" ∧ "))
    }
}
