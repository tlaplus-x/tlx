//! State-variable shape classification, k-subset family matching, and choice-aware
//! branch splitting for `choose_sym`.

pub(super) use super::super::sym_groups::{comparable, group_mask_exact, independent, mask_atoms_domain, validate_groups, GroupInfo};
use super::super::{
    domain::{self, Atom, Domain},
    max_local, variable, Branch,
};
use super::GroupMask;
use crate::{builtins::Builtin as B, hir::*, visit, Program};
use std::collections::{BTreeSet, HashMap};
use std::sync::Arc;
use tlx_front::cfg::{CfgValue, Config, ConstBinding};

#[derive(Clone, Debug)]
pub(super) enum VarShape {
    Core,
    FixedMap { mask: GroupMask, map_id: usize },
    ScalarSlot { mask: GroupMask, has_fixed: bool, slot_id: usize },
    KeySetFlag { mask: GroupMask, flag_id: usize },
    BoolMapFlag { mask: GroupMask, flag_id: usize },
    MsgSet { mask: GroupMask, msg_id: usize, fields: Vec<Arc<str>>, key_field: Arc<str>, val_field: Option<Arc<str>> },
}

#[allow(clippy::too_many_arguments)] // per-shape counters and group mask accumulate across variables in one pass
pub(super) fn classify_var(
    groups: &[GroupInfo],
    all_keys: &BTreeSet<Atom>,
    d: &Domain,
    proj_fields: Option<&BTreeSet<Arc<str>>>,
    num_maps: &mut usize,
    num_slots: &mut usize,
    num_flags: &mut usize,
    num_msgs: &mut usize,
    used_groups: &mut GroupMask,
) -> Option<VarShape> {
    if independent(d, all_keys) {
        return Some(VarShape::Core);
    }
    match d {
        Domain::Function(ks, payload) if independent(payload, all_keys) && comparable(payload) && domain::compatible(ks) => {
            let (mask, fixed) = group_mask_exact(groups, ks)?;
            if mask == 0 || !fixed.is_empty() {
                return None;
            }
            *used_groups |= mask;
            if is_pure_bool_domain(payload) {
                let flag_id = *num_flags;
                *num_flags += 1;
                Some(VarShape::BoolMapFlag { mask, flag_id })
            } else {
                let map_id = *num_maps;
                *num_maps += 1;
                Some(VarShape::FixedMap { mask, map_id })
            }
        }
        Domain::Atoms(atoms) if domain::compatible(atoms) => {
            let (mask, fixed) = group_mask_exact(groups, atoms)?;
            if mask == 0 {
                return None;
            }
            let slot_id = *num_slots;
            *num_slots += 1;
            *used_groups |= mask;
            Some(VarShape::ScalarSlot { mask, has_fixed: !fixed.is_empty(), slot_id })
        }
        Domain::Set(elem) => {
            if let Domain::Atoms(atoms) = &**elem {
                if !domain::compatible(atoms) {
                    return None;
                }
                let (mask, fixed) = group_mask_exact(groups, atoms)?;
                if mask == 0 || !fixed.is_empty() {
                    return None;
                }
                let flag_id = *num_flags;
                *num_flags += 1;
                *used_groups |= mask;
                return Some(VarShape::KeySetFlag { mask, flag_id });
            }
            if let Domain::Record(fs) = &**elem {
                if !comparable(elem) {
                    return None;
                }
                let dep: Vec<(&Arc<str>, &Domain)> = fs.iter().filter(|(_, fd)| !independent(fd, all_keys)).collect();
                let [(kf, Domain::Atoms(atoms))] = dep.as_slice() else { return None };
                if !domain::compatible(atoms) {
                    return None;
                }
                let (mask, fixed) = group_mask_exact(groups, atoms)?;
                if mask == 0 || !fixed.is_empty() {
                    return None;
                }
                let val_field = match proj_fields {
                    None => None,
                    Some(pfs) if pfs.is_empty() => None,
                    Some(pfs) if pfs.len() == 1 => {
                        let vf = pfs.iter().next()?.clone();
                        if &vf == *kf || !fs.contains_key(&vf) {
                            return None;
                        }
                        Some(vf)
                    }
                    Some(_) => return None,
                };
                let msg_id = *num_msgs;
                *num_msgs += 1;
                *used_groups |= mask;
                return Some(VarShape::MsgSet { mask, msg_id, fields: fs.keys().cloned().collect(), key_field: (*kf).clone(), val_field });
            }
            None
        }
        _ => None,
    }
}

pub(super) fn is_pure_bool_domain(d: &Domain) -> bool {
    matches!(d, Domain::Atoms(bs) if !bs.is_empty() && bs.iter().all(|a| matches!(a, Atom::Bool(_))))
}

pub(super) fn domain_is_integer(d: &Domain) -> bool {
    match d {
        Domain::Integer(_) => true,
        Domain::Atoms(as_) if !as_.is_empty() => as_.iter().all(|a| matches!(a, Atom::Num(_))),
        _ => false,
    }
}

/// Check if `set_expr` is a 0-ary `CONSTANT` bound in `cfg` to the exact set of all
/// `k`-element subsets of one symmetry group (`1 <= k <= n`, `|S| == C(n, k)`),
/// such as `Offers = {{matches, paper}, {matches, tobacco}, {paper, tobacco}}`.
pub(super) fn exact_k_subset_family(program: &Program, cfg: &Config, set_expr: &Expr, groups: &[GroupInfo]) -> Option<(GroupMask, usize)> {
    let ExprKind::Const(cid) = &*set_expr.kind else { return None };
    let cname = &program.consts[cid.idx()].name;
    let cval = cfg.constants.iter().find_map(|b| match b {
        ConstBinding::Value { name, value, module: None } if name == &**cname => Some(value),
        _ => None,
    })?;
    let CfgValue::Set(subsets) = cval else { return None };
    if subsets.is_empty() {
        return None;
    }
    let mut parsed_subsets: BTreeSet<BTreeSet<Atom>> = BTreeSet::new();
    let mut card_opt: Option<usize> = None;
    for item in subsets {
        let CfgValue::Set(elems) = item else { return None };
        let mut s = BTreeSet::new();
        for el in elems {
            let CfgValue::ModelValue(mv) = el else { return None };
            s.insert(Atom::Model(mv.as_str().into()));
        }
        if s.len() != elems.len() || s.is_empty() {
            return None;
        }
        match card_opt {
            None => card_opt = Some(s.len()),
            Some(k) if k != s.len() => return None,
            Some(_) => {}
        }
        parsed_subsets.insert(s);
    }
    let k = card_opt?;
    for (gi, g) in groups.iter().enumerate() {
        if k <= g.size && parsed_subsets.iter().all(|s| s.is_subset(&g.keys)) {
            if parsed_subsets.len() == binomial(g.size, k) {
                return Some((1u16 << gi, k));
            }
            return None;
        }
    }
    None
}

fn binomial(n: usize, k: usize) -> usize {
    if k > n {
        return 0;
    }
    let mut res = 1usize;
    for i in 0..k {
        res = res * (n - i) / (i + 1);
    }
    res
}

pub(super) fn expr_has_choose(e: &Expr) -> bool {
    if matches!(&*e.kind, ExprKind::Choose { .. }) {
        return true;
    }
    let mut found = false;
    visit::children(e, &mut |c| found |= expr_has_choose(c));
    found
}

pub(super) fn collect_primed_vars(e: &Expr, in_prime: bool, out: &mut BTreeSet<VarId>) {
    match &*e.kind {
        ExprKind::Var(v) if in_prime => {
            out.insert(*v);
        }
        ExprKind::Builtin { op: B::Prime | B::Unchanged, args } => {
            for a in args {
                collect_primed_vars(a, true, out);
            }
        }
        _ => visit::children(e, &mut |c| collect_primed_vars(c, in_prime, out)),
    }
}

pub(super) fn mentions_primed_var(e: &Expr, in_prime: bool, target: VarId) -> bool {
    match &*e.kind {
        ExprKind::Var(v) => in_prime && *v == target,
        ExprKind::Builtin { op: B::Prime | B::Unchanged, args } => args.iter().any(|a| mentions_primed_var(a, true, target)),
        _ => {
            let mut found = false;
            visit::children(e, &mut |c| found |= mentions_primed_var(c, in_prime, target));
            found
        }
    }
}

pub(super) fn collect_projected_fields(e: &Expr, fold_vars: &HashMap<LocalId, Option<Expr>>, out: &mut HashMap<VarId, BTreeSet<Arc<str>>>) {
    if let ExprKind::Field { record, field } = &*e.kind {
        if let ExprKind::Choose { vars: BoundVars::Many(ids), set: Some(cset), .. } = &*record.kind {
            if let [v] = ids.as_slice() {
                if !fold_vars.contains_key(v) {
                    let mv_opt = match &*cset.kind {
                        ExprKind::SetFilter { bound, .. } => variable(&bound.set, false),
                        _ => variable(cset, false),
                    };
                    if let Some(mv) = mv_opt {
                        out.entry(mv).or_default().insert(field.clone());
                    }
                }
            }
        }
    }
    visit::children(e, &mut |c| collect_projected_fields(c, fold_vars, out));
}

pub(super) fn split_branches(e: &Expr) -> Option<Vec<Branch>> {
    fn split(e: &Expr, remaining: &mut usize, depth: usize) -> Option<Vec<Branch>> {
        if *remaining == 0 || depth >= 128 {
            return None;
        }
        *remaining -= 1;
        match &*e.kind {
            ExprKind::Or(es) => {
                let mut out = Vec::new();
                for e in es {
                    out.extend(split(e, remaining, depth + 1)?);
                    if out.len() > 512 {
                        return None;
                    }
                }
                Some(out)
            }
            ExprKind::And(es) => {
                let mut out = vec![Branch { bounds: vec![], terms: vec![] }];
                for e in es {
                    let alts = split(e, remaining, depth + 1)?;
                    if out.len().saturating_mul(alts.len()) > 512 {
                        return None;
                    }
                    if alts.is_empty() && out.iter().any(|a| a.terms.iter().any(expr_has_choose)) {
                        return None;
                    }
                    let mut combined = Vec::new();
                    for a in &out {
                        let prior_has_choose = a.terms.iter().any(expr_has_choose);
                        for b in &alts {
                            if prior_has_choose && !b.bounds.is_empty() {
                                return None;
                            }
                            if a.terms.len() + b.terms.len() > 512 || a.bounds.len() + b.bounds.len() > 128 {
                                return None;
                            }
                            let mut branch = a.clone();
                            branch.bounds.extend(b.bounds.iter().cloned());
                            branch.terms.extend(b.terms.iter().cloned());
                            combined.push(branch);
                        }
                    }
                    out = combined;
                }
                Some(out)
            }
            ExprKind::Quant { kind: QuantKind::Exists, bounds, body } => {
                if bounds.iter().any(|b| expr_has_choose(&b.set)) {
                    return None;
                }
                let mut out = split(body, remaining, depth + 1)?;
                for b in &mut out {
                    if bounds.len() + b.bounds.len() > 128 {
                        return None;
                    }
                    let mut combined = bounds.clone();
                    combined.append(&mut b.bounds);
                    b.bounds = combined;
                }
                Some(out)
            }
            ExprKind::If { cond, then, els } => {
                let mut left = split(then, remaining, depth + 1)?;
                let mut right = split(els, remaining, depth + 1)?;
                if expr_has_choose(cond)
                    && (left.is_empty()
                        || right.is_empty()
                        || left.iter().any(|b| !b.bounds.is_empty())
                        || right.iter().any(|b| !b.bounds.is_empty()))
                {
                    return None;
                }
                let neg = Expr::new(ExprKind::Builtin { op: B::Not, args: vec![cond.clone()] }, cond.span);
                for b in &mut left {
                    b.terms.insert(0, cond.clone());
                }
                for b in &mut right {
                    b.terms.insert(0, neg.clone());
                }
                left.extend(right);
                if left.len() > 512 {
                    return None;
                }
                Some(left)
            }
            _ => Some(vec![Branch { bounds: vec![], terms: vec![e.clone()] }]),
        }
    }
    split(e, &mut 100_000, 0)
}

pub(super) fn max_local_in_branches(bs: &[Branch]) -> u32 {
    let mut m = 0;
    for b in bs {
        for bnd in &b.bounds {
            for id in bnd.vars.locals() {
                m = m.max(id.0);
            }
            m = m.max(max_local(&bnd.set));
        }
        for t in &b.terms {
            m = m.max(max_local(t));
        }
    }
    m
}
