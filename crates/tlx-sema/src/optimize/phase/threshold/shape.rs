//! Representation-agnostic recognition of threshold-counter initializations and
//! transfers shared by static validation (`mod.rs`), standalone Lean emission
//! (`lean.rs`), and symmetry-composed Lean emission (`sym/lower.rs`).

use crate::{builtins::Builtin as B, hir::*};

use super::super::{atom_nat, domain::Domains, expr_structurally_eq, variable};

/// Recognized scalar counter initialization shape.
pub(super) enum SeedShape<'e> {
    Const(i128),
    Ite { cond: &'e Expr, then: &'e Expr, els: &'e Expr },
}

/// Recognized counter-map initialization shape.
pub(super) enum MapSeedShape<'e> {
    FnConstruct { local: LocalId, set: &'e Expr, body: &'e Expr },
    Ite { cond: &'e Expr, then: &'e Expr, els: &'e Expr },
}

/// Recognized single-slot counter transfer shape (scalar or one map entry).
pub(super) enum SlotUpdate<'e> {
    Keep,
    Reset(i128),
    Add(i128),
    Ite { cond: &'e Expr, then: &'e Expr, els: &'e Expr },
}

/// Recognized counter-map transfer envelope.
pub(super) enum MapTransferShape<'e> {
    Keep,
    FnConstruct { local: LocalId, set: &'e Expr, body: &'e Expr },
    Except(Vec<(&'e Expr, &'e Expr)>),
    Ite { cond: &'e Expr, then: &'e Expr, els: &'e Expr },
}

pub(super) fn seed_shape<'e>(domains: &Domains, rhs: &'e Expr) -> Option<SeedShape<'e>> {
    if let Some(n) = atom_nat(domains, rhs) {
        return Some(SeedShape::Const(n));
    }
    if let ExprKind::If { cond, then, els } = &*rhs.kind {
        return Some(SeedShape::Ite { cond, then, els });
    }
    None
}

pub(super) fn map_seed_shape<'e>(rhs: &'e Expr) -> Option<MapSeedShape<'e>> {
    match &*rhs.kind {
        ExprKind::FnConstruct { bounds, body } => {
            let [bound] = bounds.as_slice() else { return None };
            let BoundVars::Many(ids) = &bound.vars else { return None };
            let [local] = ids.as_slice() else { return None };
            Some(MapSeedShape::FnConstruct { local: *local, set: &bound.set, body })
        }
        ExprKind::If { cond, then, els } => Some(MapSeedShape::Ite { cond, then, els }),
        _ => None,
    }
}

pub(super) fn scalar_update<'e>(domains: &Domains, var: VarId, rhs: &'e Expr) -> Option<SlotUpdate<'e>> {
    slot_update_with(domains, rhs, |e| variable(e, false) == Some(var))
}

pub(super) fn map_slot_update<'e>(domains: &Domains, var: VarId, idx: &Expr, val: &'e Expr) -> Option<SlotUpdate<'e>> {
    slot_update_with(domains, val, |e| {
        matches!(
            &*e.kind,
            ExprKind::FnApp { func, args }
                if args.len() == 1 && variable(func, false) == Some(var) && expr_structurally_eq(&args[0], idx)
        )
    })
}

fn slot_update_with<'e>(domains: &Domains, expr: &'e Expr, is_self_read: impl Fn(&Expr) -> bool) -> Option<SlotUpdate<'e>> {
    if is_self_read(expr) {
        return Some(SlotUpdate::Keep);
    }
    if let Some(r) = atom_nat(domains, expr) {
        return Some(SlotUpdate::Reset(r));
    }
    match &*expr.kind {
        ExprKind::Builtin { op: B::Plus, args } if args.len() == 2 => {
            for (lhs, delta_e) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                if is_self_read(lhs) {
                    if let Some(d) = atom_nat(domains, delta_e) {
                        return Some(SlotUpdate::Add(d));
                    }
                }
            }
            None
        }
        ExprKind::If { cond, then, els } => Some(SlotUpdate::Ite { cond, then, els }),
        _ => None,
    }
}

pub(super) fn map_transfer_shape<'e>(var: VarId, rhs: &'e Expr) -> Option<MapTransferShape<'e>> {
    if variable(rhs, false) == Some(var) {
        return Some(MapTransferShape::Keep);
    }
    match &*rhs.kind {
        ExprKind::FnConstruct { bounds, body } => {
            let [bound] = bounds.as_slice() else { return None };
            let BoundVars::Many(ids) = &bound.vars else { return None };
            let [local] = ids.as_slice() else { return None };
            Some(MapTransferShape::FnConstruct { local: *local, set: &bound.set, body })
        }
        ExprKind::Except { base, updates } if variable(base, false) == Some(var) => {
            let mut pairs = Vec::with_capacity(updates.len());
            for (path, val) in updates {
                let [ExceptKey::Index(indices)] = path.as_slice() else { return None };
                let [idx] = indices.as_slice() else { return None };
                pairs.push((idx, val));
            }
            Some(MapTransferShape::Except(pairs))
        }
        ExprKind::If { cond, then, els } => Some(MapTransferShape::Ite { cond, then, els }),
        _ => None,
    }
}
