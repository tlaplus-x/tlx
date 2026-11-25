//! Replace record reads by explicit phase/data inputs. No raw record reaches C.
use super::super::super::{max_local, variable};
use super::{Emitter, Reads};
use crate::{builtins::Builtin as B, hir::*, visit};

impl Emitter<'_, '_> {
    pub(super) fn leaf(&mut self, e: &Expr, kind: &str, actor: Option<LocalId>, reads: &mut Reads) -> Option<String> {
        let mut next = max_local(e).checked_add(1)?;
        let mut holes = vec![];
        let masked = self.mask(e, kind, actor, reads, &mut next, &mut holes)?;
        let id = self.atoms.len();
        self.atoms.push(format!("{kind} HIR: {masked:#?}\nRecord holes: {holes:#?}"));
        Some(match kind {
            "initial" => format!("(sem.initial {id} c choice.2)"),
            "observe" => format!("(sem.observe {id} c p input)"),
            _ => format!("(sem.{kind} {id} c d choice.2 p input)"),
        })
    }

    /// Lower one action check over both endpoints. Field reads become the
    /// explicit `p`/`q` phase and `input`/`input'` observed-value inputs; the
    /// whole predicate is a single opaque `sem.actionTest` atom.
    pub(super) fn action_leaf(&mut self, e: &Expr, kind: &str, reads: &mut Reads) -> Option<String> {
        let mut next = max_local(e).checked_add(1)?;
        let mut holes = vec![];
        let masked = self.action_mask(e, reads, &mut next, &mut holes, false)?;
        let id = self.atoms.len();
        self.atoms.push(format!("{kind} HIR: {masked:#?}\nRecord holes: {holes:#?}"));
        Some(format!("(sem.actionTest {id} c d p q input input')"))
    }

    /// Lower an action read. `ambient` says the enclosing read already selects
    /// the target endpoint (the key of a whole-lookup prime, or a key that is
    /// itself read through the target map), so an unprimed field read inside it
    /// still addresses the target endpoint.
    fn action_mask(&self, e: &Expr, reads: &mut Reads, next: &mut u32, holes: &mut Vec<String>, ambient: bool) -> Option<Expr> {
        if let Some((field, key, map_primed, key_primed)) = self.a.action_field(e) {
            if map_primed && ambient {
                return None;
            }
            let primed = map_primed || ambient;
            let slot = if field == self.a.control {
                if primed { "phase'" } else { "phase" }.to_owned()
            } else {
                let f = self.fields.iter().position(|x| &**x == field)?;
                reads.global[f] = true;
                format!("data field {f}")
            };
            // The key identifies which endpoint slot the read addresses and in
            // which endpoint it is evaluated; without both, two different keyed
            // reads would lower to the same atom.
            let key_scope = ambient || key_primed;
            if key_primed && ambient {
                return None;
            }
            let key = match key {
                Some(key) => Some(self.action_mask(key, reads, next, holes, key_scope)?),
                None => None,
            };
            let local = LocalId(*next);
            *next = next.checked_add(1)?;
            holes.push(format!("{local:?} = {slot}, source key {key:#?}; primed={primed}; key primed={key_scope}"));
            return Some(Expr::new(ExprKind::Local(local), e.span));
        }
        if let ExprKind::Builtin { op: B::In, args } = &*e.kind {
            if args.len() == 2
                && variable(&args[0], false) == Some(self.a.var)
                && self.a.domains.belongs(&self.a.domains.vars[self.a.var.idx()], &args[1])
            {
                return Some(Expr::new(ExprKind::Bool(true), e.span));
            }
        }
        if matches!(&*e.kind, ExprKind::Var(v) if *v == self.a.var) {
            return None;
        }
        if let ExprKind::BoxAction { action, sub } = &*e.kind {
            if mentions(sub, self.a.var) {
                return None;
            }
            let action = self.action_mask(action, reads, next, holes, ambient)?;
            return Some(Expr::new(ExprKind::BoxAction { action, sub: sub.clone() }, e.span));
        }
        if let ExprKind::Builtin { op: B::Unchanged, args } = &*e.kind {
            // The analysis admits `UNCHANGED` only over retained values, where
            // no projected field needs a hole.
            if args.iter().any(|a| mentions(a, self.a.var)) {
                return None;
            }
            return Some(e.clone());
        }
        if matches!(&*e.kind, ExprKind::AngleAction { .. } | ExprKind::At) || matches!(&*e.kind, ExprKind::Builtin { op: B::Enabled, .. }) {
            return None;
        }
        if let ExprKind::Builtin { op: B::Prime, args } = &*e.kind {
            if args.iter().any(|a| mentions(a, self.a.var)) {
                return None;
            }
        }
        let mut result = e.clone();
        let mut valid = true;
        visit::children_mut(&mut result, &mut |child| {
            if let Some(e) = self.action_mask(child, reads, next, holes, ambient) {
                *child = e;
            } else {
                valid = false;
            }
        });
        valid.then_some(result)
    }

    fn mask(
        &self,
        e: &Expr,
        kind: &str,
        actor: Option<LocalId>,
        reads: &mut Reads,
        next: &mut u32,
        holes: &mut Vec<String>,
    ) -> Option<Expr> {
        if let ExprKind::Builtin { op: B::In, args } = &*e.kind {
            if args.len() == 2
                && variable(&args[0], false) == Some(self.a.var)
                && self.a.domains.belongs(&self.a.domains.vars[self.a.var.idx()], &args[1])
            {
                return Some(Expr::new(ExprKind::Bool(true), e.span));
            }
        }
        if let ExprKind::Field { record, field } = &*e.kind {
            let index = if self.a.keys.is_none() && variable(record, false) == Some(self.a.var) {
                Some(None)
            } else if let ExprKind::FnApp { func, args } = &*record.kind {
                if variable(func, false) == Some(self.a.var) && args.len() == 1 {
                    Some(Some(&args[0]))
                } else {
                    None
                }
            } else {
                None
            };
            if let Some(index) = index {
                if kind == "initial" {
                    return None;
                }
                let actor_read = kind != "observe"
                    && (self.a.keys.is_none() || index.is_some_and(|i| matches!(&*i.kind, ExprKind::Local(l) if Some(*l) == actor)));
                let slot = if field.as_ref() == self.a.control {
                    "phase".to_owned()
                } else {
                    let f = self.fields.iter().position(|f| f == field)?;
                    if actor_read {
                        reads.actor[f] = true;
                    } else {
                        reads.global[f] = true;
                    }
                    format!("data field {f}")
                };
                let index = if let Some(e) = index { Some(self.mask(e, kind, actor, reads, next, holes)?) } else { None };
                let local = LocalId(*next);
                *next = next.checked_add(1)?;
                holes.push(format!("{local:?} = {slot}, source key {index:#?}; actor-relative={actor_read}"));
                return Some(Expr::new(ExprKind::Local(local), e.span));
            }
        }
        if matches!(&*e.kind, ExprKind::Var(v) if *v == self.a.var)
            || matches!(&*e.kind, ExprKind::Builtin { op: B::Prime, .. } if mentions(e, self.a.var))
        {
            return None;
        }
        let mut result = e.clone();
        let mut valid = true;
        visit::children_mut(&mut result, &mut |child| {
            if let Some(e) = self.mask(child, kind, actor, reads, next, holes) {
                *child = e;
            } else {
                valid = false;
            }
        });
        valid.then_some(result)
    }
}

pub(super) fn mentions(e: &Expr, var: VarId) -> bool {
    if matches!(&*e.kind, ExprKind::Var(v) if *v == var) {
        return true;
    }
    let mut found = false;
    visit::children(e, &mut |e| found |= mentions(e, var));
    found
}
