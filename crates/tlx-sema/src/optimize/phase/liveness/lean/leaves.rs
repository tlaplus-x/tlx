//! Replace managed reads by explicit phase/data inputs. No projected slot reaches C.
use std::collections::BTreeSet;

use super::super::super::max_local;
use super::super::{ActionRead, Atom, ObsSink, Slot};
use super::{Control, Emitter, ObsContext, Reads};
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
            _ => format!("(sem.{kind} {id} c d choice.2 p input)"),
        })
    }

    /// Lower one state-level observation (`INVARIANT`, `init_props`, `CONSTRAINT`)
    /// through the shared context-aware traversal (`Analysis::walk_obs`) so
    /// `observed : Phase → Field → Bool` and the emitted holes use the exact
    /// same short-circuit order, phase guards, and binder scoping as liveness.
    pub(super) fn obs_leaf(&mut self, e: &Expr, kind: &str, ctx: &ObsContext, observed: &mut [Vec<bool>]) -> Option<String> {
        let mut next = max_local(e).checked_add(1)?;
        let mut holes = vec![];
        let masked = self.mask_obs(e, ctx, observed, &mut next, &mut holes)?;
        let id = self.atoms.len();
        self.atoms.push(format!("{kind} HIR: {masked:#?}\nRecord holes: {holes:#?}"));
        Some(format!("(sem.observe {id} c p input)"))
    }

    /// Lower one action check over both endpoints. Slot reads become the
    /// explicit `p`/`q` phase and `input`/`input'` observed-value inputs; the
    /// whole predicate is a single opaque `sem.actionTest` atom.
    pub(super) fn action_leaf(&mut self, e: &Expr, kind: &str, observed: &mut [Vec<bool>]) -> Option<String> {
        let mut next = max_local(e).checked_add(1)?;
        let mut holes = vec![];
        let masked = self.action_mask(e, observed, &mut next, &mut holes, false)?;
        let id = self.atoms.len();
        self.atoms.push(format!("{kind} HIR: {masked:#?}\nRecord holes: {holes:#?}"));
        Some(format!("(sem.actionTest {id} c d p q input input')"))
    }

    /// Lower an action read using the shared `Analysis::classify_action_read`
    /// classifier. `ambient` says the enclosing read already selects the target
    /// endpoint (the key of a whole-lookup prime, or a key that is itself read
    /// through the target map), so an unprimed read inside it still addresses
    /// the target endpoint.
    fn action_mask(&self, e: &Expr, observed: &mut [Vec<bool>], next: &mut u32, holes: &mut Vec<String>, ambient: bool) -> Option<Expr> {
        match self.a.classify_action_read(e) {
            ActionRead::Slot { slot, key, map_primed, key_primed } => {
                if map_primed && ambient {
                    return None;
                }
                let primed = map_primed || ambient;
                let hole_desc = match slot {
                    None => if primed { "phase'" } else { "phase" }.to_owned(),
                    Some(slot) => {
                        let f = self.fields.iter().position(|x| x == &slot)?;
                        for row in observed.iter_mut() {
                            row[f] = true;
                        }
                        format!("data field {f}")
                    }
                };
                // The key identifies which endpoint slot the read addresses and in
                // which endpoint it is evaluated; without both, two different keyed
                // reads would lower to the same atom.
                let key_scope = ambient || key_primed;
                if key_primed && ambient {
                    return None;
                }
                let key = match key {
                    Some(key) => Some(self.action_mask(key, observed, next, holes, key_scope)?),
                    None => None,
                };
                let local = LocalId(*next);
                *next = next.checked_add(1)?;
                holes.push(format!("{local:?} = {hole_desc}, source key {key:#?}; primed={primed}; key primed={key_scope}"));
                Some(Expr::new(ExprKind::Local(local), e.span))
            }
            ActionRead::ProvedMembership => Some(Expr::new(ExprKind::Bool(true), e.span)),
            ActionRead::FixedDomain => {
                let local = LocalId(*next);
                *next = next.checked_add(1)?;
                holes.push(format!("{local:?} = fixed domain"));
                Some(Expr::new(ExprKind::Local(local), e.span))
            }
            ActionRead::ControlMap => {
                let local = LocalId(*next);
                *next = next.checked_add(1)?;
                holes.push(format!("{local:?} = phase map; primed={ambient}"));
                Some(Expr::new(ExprKind::Local(local), e.span))
            }
            ActionRead::BoxAction { action, sub } => {
                let action = self.action_mask(action, observed, next, holes, ambient)?;
                Some(Expr::new(ExprKind::BoxAction { action, sub: sub.clone() }, e.span))
            }
            ActionRead::Unchanged(_) => Some(e.clone()),
            ActionRead::Unsupported => None,
            ActionRead::Recurse => {
                let mut result = e.clone();
                let mut valid = true;
                visit::children_mut(&mut result, &mut |child| {
                    if let Some(e) = self.action_mask(child, observed, next, holes, ambient) {
                        *child = e;
                    } else {
                        valid = false;
                    }
                });
                valid.then_some(result)
            }
        }
    }

    fn mask_obs(&self, e: &Expr, ctx: &ObsContext, observed: &mut [Vec<bool>], next: &mut u32, holes: &mut Vec<String>) -> Option<Expr> {
        struct MaskObsSink<'a, 'e, 'd> {
            emitter: &'a Emitter<'e, 'd>,
            observed: &'a mut [Vec<bool>],
            next: &'a mut u32,
            holes: &'a mut Vec<String>,
        }
        impl ObsSink for MaskObsSink<'_, '_, '_> {
            fn proved_membership(&mut self, e: &Expr) -> Option<Option<Expr>> {
                Some(Some(Expr::new(ExprKind::Bool(true), e.span)))
            }
            fn fixed_domain(&mut self, e: &Expr) -> Option<Option<Expr>> {
                let local = LocalId(*self.next);
                *self.next = self.next.checked_add(1)?;
                self.holes.push(format!("{local:?} = fixed domain"));
                Some(Some(Expr::new(ExprKind::Local(local), e.span)))
            }
            fn control_read(&mut self, e: &Expr, index: Option<Expr>) -> Option<Option<Expr>> {
                let local = LocalId(*self.next);
                *self.next = self.next.checked_add(1)?;
                self.holes.push(format!("{local:?} = phase, source key {index:#?}"));
                Some(Some(Expr::new(ExprKind::Local(local), e.span)))
            }
            fn slot_read(&mut self, e: &Expr, slot: &Slot, index: Option<Expr>, allowed: &BTreeSet<Atom>) -> Option<Option<Expr>> {
                let f = self.emitter.fields.iter().position(|x| x == slot)?;
                for (p_idx, p) in self.emitter.phases.iter().enumerate() {
                    if allowed.contains(p) {
                        self.observed[p_idx][f] = true;
                    }
                }
                let local = LocalId(*self.next);
                *self.next = self.next.checked_add(1)?;
                self.holes.push(format!("{local:?} = data field {f}, source key {index:#?}; phase-guard={allowed:?}"));
                Some(Some(Expr::new(ExprKind::Local(local), e.span)))
            }
            fn bare_projected_var(&mut self, _e: &Expr, _var: VarId) -> Option<Option<Expr>> {
                None
            }
            fn bare_control_var(&mut self, e: &Expr) -> Option<Option<Expr>> {
                let local = LocalId(*self.next);
                *self.next = self.next.checked_add(1)?;
                self.holes.push(format!("{local:?} = phase map"));
                Some(Some(Expr::new(ExprKind::Local(local), e.span)))
            }
        }
        let mut sink = MaskObsSink { emitter: self, observed, next, holes };
        self.a.walk_obs(e, ctx, &mut sink, true)?
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
        if self.a.is_proved_membership(e) {
            return Some(Expr::new(ExprKind::Bool(true), e.span));
        }
        if self.a.is_fixed_domain_read(e) {
            if kind == "initial" {
                return None;
            }
            let local = LocalId(*next);
            *next = next.checked_add(1)?;
            holes.push(format!("{local:?} = fixed domain"));
            return Some(Expr::new(ExprKind::Local(local), e.span));
        }
        if let Some(index) = self.a.control_read(e) {
            if kind == "initial" {
                return None;
            }
            let actor_read = self.a.keys.is_none() || index.is_some_and(|i| matches!(&*i.kind, ExprKind::Local(l) if Some(*l) == actor));
            let index = match index {
                Some(idx) => Some(self.mask(idx, kind, actor, reads, next, holes)?),
                None => None,
            };
            let local = LocalId(*next);
            *next = next.checked_add(1)?;
            holes.push(format!("{local:?} = phase, source key {index:#?}; actor-relative={actor_read}"));
            return Some(Expr::new(ExprKind::Local(local), e.span));
        }
        if let Some((slot, index)) = self.a.slot_read(e) {
            if kind == "initial" {
                return None;
            }
            let f = self.fields.iter().position(|x| x == &slot)?;
            let actor_read = self.a.keys.is_none() || index.is_some_and(|i| matches!(&*i.kind, ExprKind::Local(l) if Some(*l) == actor));
            if actor_read {
                reads.actor[f] = true;
            } else {
                reads.global[f] = true;
            }
            let index = match index {
                Some(idx) => Some(self.mask(idx, kind, actor, reads, next, holes)?),
                None => None,
            };
            let local = LocalId(*next);
            *next = next.checked_add(1)?;
            holes.push(format!("{local:?} = data field {f}, source key {index:#?}; actor-relative={actor_read}"));
            return Some(Expr::new(ExprKind::Local(local), e.span));
        }
        if matches!(&*e.kind, ExprKind::Var(v) if self.a.is_projected_var(*v))
            || matches!(&*e.kind, ExprKind::Builtin { op: B::Prime, .. } if self.a.mentions_any_managed(e))
        {
            return None;
        }
        if matches!(&*e.kind, ExprKind::Var(v) if matches!(&self.a.control, Control::Var { var } if *v == *var)) {
            if kind == "initial" {
                return None;
            }
            let local = LocalId(*next);
            *next = next.checked_add(1)?;
            holes.push(format!("{local:?} = phase map"));
            return Some(Expr::new(ExprKind::Local(local), e.span));
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
