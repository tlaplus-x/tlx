//! Shared symmetry-group validation, key reference IR, and domain independence/comparability
//! helpers used by both `keyed` and `choose_sym`.
#![allow(dead_code, unused_imports)]

use super::domain::{self, Atom, Domain};
use crate::{hir::*, visit};
use std::collections::BTreeSet;

pub(super) type GroupMask = u16;

#[derive(Clone, Debug)]
pub(super) struct GroupInfo {
    pub(super) keys: BTreeSet<Atom>,
    pub(super) size: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum KeyRef {
    Bound(usize),
    Slot(usize),
    Fixed(usize),
}

impl KeyRef {
    pub(super) fn lean(self) -> String {
        match self {
            Self::Bound(i) => format!("(KeyRef.bound {i})"),
            Self::Slot(s) => format!("(KeyRef.slot ⟨{s}, by decide⟩)"),
            Self::Fixed(id) => format!("(KeyRef.fixed {id})"),
        }
    }
}

pub(super) fn validate_groups(raw: &[Vec<String>]) -> Option<(Vec<GroupInfo>, BTreeSet<Atom>)> {
    if raw.is_empty() || raw.len() > 16 {
        return None;
    }
    let mut groups = Vec::with_capacity(raw.len());
    let mut all_keys = BTreeSet::new();
    let mut order: u128 = 1;
    for g in raw {
        if !(2..=6).contains(&g.len()) {
            return None;
        }
        let keys: BTreeSet<Atom> = g.iter().map(|k| Atom::Model(k.as_str().into())).collect();
        if keys.len() != g.len() || !domain::compatible(&keys) || !all_keys.is_disjoint(&keys) {
            return None;
        }
        let fact = (1..=g.len() as u128).product::<u128>();
        order = order.checked_mul(fact)?;
        if order > 720 {
            return None;
        }
        all_keys.extend(keys.iter().cloned());
        groups.push(GroupInfo { size: keys.len(), keys });
    }
    Some((groups, all_keys))
}

pub(super) fn group_mask_exact(groups: &[GroupInfo], set: &BTreeSet<Atom>) -> Option<(GroupMask, BTreeSet<Atom>)> {
    let mut mask: GroupMask = 0;
    let mut rest = set.clone();
    for (gi, g) in groups.iter().enumerate() {
        if g.keys.is_subset(set) {
            mask |= 1 << gi;
            for k in &g.keys {
                rest.remove(k);
            }
        } else if !g.keys.is_disjoint(set) {
            return None;
        }
    }
    Some((mask, rest))
}

pub(super) fn mask_atoms_domain(groups: &[GroupInfo], mask: GroupMask) -> Domain {
    let mut atoms = BTreeSet::new();
    for (gi, g) in groups.iter().enumerate() {
        if (mask & (1 << gi)) != 0 {
            atoms.extend(g.keys.iter().cloned());
        }
    }
    Domain::Atoms(atoms)
}

/// Domain inference is a trusted lowering layer, not an invariant assumption.
pub(super) fn independent(d: &Domain, keys: &BTreeSet<Atom>) -> bool {
    match d {
        Domain::Bottom | Domain::Integer(_) => true,
        Domain::Top | Domain::Mapping(_) => false,
        Domain::Atoms(a) => a.is_disjoint(keys),
        Domain::Set(d) | Domain::Seq(d) => independent(d, keys),
        Domain::Record(fs) => fs.values().all(|d| independent(d, keys)),
        Domain::Records(rs) => rs.iter().all(|fs| fs.values().all(|d| independent(d, keys))),
        Domain::Function(ks, d) => ks.is_disjoint(keys) && independent(d, keys),
    }
}

/// Runtime symmetry uses TLC's partial comparison (`cmp_tlc`) to select a canonical
/// representative, so values at each permuted slot must be mutually comparable.
pub(super) fn comparable(d: &Domain) -> bool {
    match d {
        Domain::Bottom | Domain::Integer(_) => true,
        Domain::Top | Domain::Mapping(_) => false,
        Domain::Atoms(a) => domain::atoms_mutually_comparable(a),
        Domain::Set(d) | Domain::Seq(d) => comparable(d),
        Domain::Record(fs) => fs.values().all(comparable),
        Domain::Records(rs) => {
            rs.iter().all(|fs| fs.values().all(comparable))
                && rs.iter().enumerate().all(|(i, a)| {
                    rs[i + 1..].iter().all(|b| {
                        a.len() != b.len()
                            || a.iter().all(|(k, va)| match b.get(k) {
                                Some(vb) => comparable(&va.join(vb)),
                                None => true,
                            })
                    })
                })
        }
        Domain::Function(ks, d) => domain::atoms_mutually_comparable(ks) && comparable(d),
    }
}

pub(super) fn subst_local(e: &Expr, target: LocalId, repl: &Expr) -> Expr {
    if matches!(&*e.kind, ExprKind::Local(id) if *id == target) {
        return repl.clone();
    }
    let mut out = e.clone();
    visit::children_mut(&mut out, &mut |child| {
        *child = subst_local(child, target, repl);
    });
    out
}
