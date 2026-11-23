//! Certified automatic symmetry for disjoint products of full permutation groups.
//! Supports fixed-domain maps, mixed-domain maps, scalar/optional key slots,
//! sets of keys, sets of single-key tagged records, fixed records of those shapes,
//! multi-writer updates, whole-map updates, and key cardinalities.
//! Key operations are explicit rule IR; leaves never receive renamed keys.

mod erasure;
mod expressions;
mod output;
mod step;

use super::{
    binding,
    domain::{self, Atom, Domain, Domains, Locals},
    sym_groups::{comparable, group_mask_exact, independent, subst_local, validate_groups, GroupInfo, GroupMask, KeyRef},
    sym_norm::SymNormalizer,
    unchanged, variable, Branch,
};
use crate::{builtins::Builtin as B, hir::*, Program};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
use tlx_front::cfg::Config;

#[derive(Clone, Debug)]
struct RecordMsgShape {
    fields: Vec<Arc<str>>,
    key_field: Arc<str>,
    mask: GroupMask,
    map_id: usize,
}

#[derive(Clone, Debug)]
enum FieldShape {
    Core,
    FixedMap { mask: GroupMask, map_id: usize },
    ScalarSlot { mask: GroupMask, has_fixed: bool, slot_id: usize },
}

#[derive(Clone, Debug)]
enum VarShape {
    Core,
    FixedMap { mask: GroupMask, map_id: usize },
    MixedMap { mask: GroupMask, fixed_keys: BTreeSet<Atom>, map_id: usize },
    ScalarSlot { mask: GroupMask, has_fixed: bool, slot_id: usize },
    KeySet { mask: GroupMask, has_fixed: bool, map_id: usize },
    RecordSet { keyed: Vec<RecordMsgShape>, has_free: bool },
    FixedRecord { fields: BTreeMap<Arc<str>, FieldShape> },
}

struct Emitter<'a> {
    domains: &'a Domains,
    groups: &'a [GroupInfo],
    all_keys: &'a BTreeSet<Atom>,
    shapes: Vec<VarShape>,
    num_maps: usize,
    num_slots: usize,
    num_consts: usize,
    omitted: Vec<VarId>,
    atoms: Vec<String>,
    fixed_atoms: Vec<String>,
    next_local: u32,
}

struct Case {
    hidden: Vec<String>,
    guard: String,
    writes: Vec<String>,
    slot_writes: Vec<String>,
    keys: Vec<(LocalId, GroupMask)>,
}

/// Generate a connected certificate for a disjoint product of full permutation groups.
/// Unsupported state shapes or key operations fail closed. No verifier is run.
pub fn symmetry_certificate(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    observations: &[Expr],
    groups: &[Vec<String>],
) -> Option<String> {
    emit(program, cfg, init, next, observations, groups, vec![])
}

/// Certify erasure followed by symmetry for the exact installed variable tuple.
pub fn symmetry_projection_certificate(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    observations: &[Expr],
    groups: &[Vec<String>],
    view: &Expr,
) -> Option<String> {
    let ExprKind::Tuple(values) = &*view.kind else { return None };
    let retained = values.iter().map(|e| variable(e, false)).collect::<Option<Vec<_>>>()?;
    if retained.windows(2).any(|pair| pair[0].0 >= pair[1].0) || retained.iter().any(|v| v.idx() >= program.vars.len()) {
        return None;
    }
    let omitted: Vec<_> = (0..program.vars.len()).map(|i| VarId(i as u32)).filter(|v| !retained.contains(v)).collect();
    if omitted.is_empty() {
        return None;
    }
    emit(program, cfg, init, next, observations, groups, omitted)
}

fn emit(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    observations: &[Expr],
    raw_groups: &[Vec<String>],
    omitted: Vec<VarId>,
) -> Option<String> {
    let (groups, all_keys) = validate_groups(raw_groups)?;
    if !super::sym_totality::check_model_totality_with_omitted(program, cfg, init, next, observations, raw_groups, &omitted) {
        return None;
    }
    let mut normalize = SymNormalizer::new(program);
    let initial = normalize.normalize(init)?;
    let init_branches = keyed_branches(&initial)?;
    let steps = keyed_branches(&normalize.normalize(next)?)?;
    let observations = observations.iter().map(|o| normalize.normalize(o)).collect::<Option<Vec<_>>>()?;
    let domains = Domains::infer(program, cfg, &init_branches, &steps)?;

    let mut shapes = Vec::with_capacity(domains.vars.len());
    let mut num_maps = 0usize;
    let mut num_slots = 0usize;
    let mut used_groups: GroupMask = 0;

    for (i, d) in domains.vars.iter().enumerate() {
        if omitted.contains(&VarId(i as u32)) {
            shapes.push(VarShape::Core);
            continue;
        }
        let shape = classify_var(&groups, &all_keys, d, &mut num_maps, &mut num_slots, &mut used_groups)?;
        shapes.push(shape);
    }
    let all_mask: GroupMask = (1u16 << groups.len()) - 1;
    if (num_maps == 0 && num_slots == 0) || used_groups != all_mask || steps.is_empty() {
        return None;
    }

    let mut e = Emitter {
        domains: &domains,
        groups: &groups,
        all_keys: &all_keys,
        shapes,
        num_maps,
        num_slots,
        num_consts: program.consts.len(),
        omitted,
        atoms: vec![],
        fixed_atoms: vec![],
        next_local: (program.locals.len() as u32).max(max_local_in_steps(&steps, &observations)) + 1,
    };
    let mut cases = Vec::new();
    for b in &steps {
        e.cases_for_branch(b, &mut cases)?;
        if cases.len() > 512 {
            return None;
        }
    }
    if cases.is_empty() {
        return None;
    }
    let observation = e.tests(&observations, &[])?;
    Some(e.output(&initial, &cases, &observation))
}

fn classify_var(
    groups: &[GroupInfo],
    all_keys: &BTreeSet<Atom>,
    d: &Domain,
    num_maps: &mut usize,
    num_slots: &mut usize,
    used_groups: &mut GroupMask,
) -> Option<VarShape> {
    if independent(d, all_keys) {
        return Some(VarShape::Core);
    }
    match d {
        Domain::Function(ks, payload) if independent(payload, all_keys) && comparable(payload) && domain::compatible(ks) => {
            let (mask, fixed_keys) = group_mask_exact(groups, ks)?;
            if mask == 0 {
                return None;
            }
            let map_id = *num_maps;
            *num_maps += 1;
            *used_groups |= mask;
            if fixed_keys.is_empty() {
                Some(VarShape::FixedMap { mask, map_id })
            } else {
                Some(VarShape::MixedMap { mask, fixed_keys, map_id })
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
                if mask == 0 {
                    return None;
                }
                let map_id = *num_maps;
                *num_maps += 1;
                *used_groups |= mask;
                return Some(VarShape::KeySet { mask, has_fixed: !fixed.is_empty(), map_id });
            }
            if let Some(records) = elem.records() {
                if !comparable(elem) {
                    return None;
                }
                let mut keyed = Vec::new();
                let mut has_free = false;
                for fs in records {
                    let dep: Vec<(&Arc<str>, &Domain)> = fs.iter().filter(|(_, fd)| !independent(fd, all_keys)).collect();
                    match dep.as_slice() {
                        [] => has_free = true,
                        [(kf, Domain::Atoms(atoms))] if domain::compatible(atoms) => {
                            let (mask, fixed) = group_mask_exact(groups, atoms)?;
                            if mask == 0 || !fixed.is_empty() {
                                return None;
                            }
                            let map_id = *num_maps;
                            *num_maps += 1;
                            *used_groups |= mask;
                            keyed.push(RecordMsgShape { fields: fs.keys().cloned().collect(), key_field: (*kf).clone(), mask, map_id });
                        }
                        _ => return None,
                    }
                }
                if keyed.is_empty() {
                    return None;
                }
                return Some(VarShape::RecordSet { keyed, has_free });
            }
            None
        }
        Domain::Record(fs) => {
            let mut fields = BTreeMap::new();
            let mut any_keyed = false;
            for (name, fdom) in fs {
                if independent(fdom, all_keys) {
                    fields.insert(name.clone(), FieldShape::Core);
                } else if let Domain::Function(ks, payload) = fdom {
                    if !independent(payload, all_keys) || !comparable(payload) || !domain::compatible(ks) {
                        return None;
                    }
                    let (mask, fixed) = group_mask_exact(groups, ks)?;
                    if mask == 0 || !fixed.is_empty() {
                        return None;
                    }
                    let map_id = *num_maps;
                    *num_maps += 1;
                    *used_groups |= mask;
                    any_keyed = true;
                    fields.insert(name.clone(), FieldShape::FixedMap { mask, map_id });
                } else if let Domain::Atoms(atoms) = fdom {
                    if !domain::compatible(atoms) {
                        return None;
                    }
                    let (mask, fixed) = group_mask_exact(groups, atoms)?;
                    if mask == 0 {
                        return None;
                    }
                    let slot_id = *num_slots;
                    *num_slots += 1;
                    *used_groups |= mask;
                    any_keyed = true;
                    fields.insert(name.clone(), FieldShape::ScalarSlot { mask, has_fixed: !fixed.is_empty(), slot_id });
                } else {
                    return None;
                }
            }
            any_keyed.then_some(VarShape::FixedRecord { fields })
        }
        _ => None,
    }
}

fn keyed_branches(e: &Expr) -> Option<Vec<Branch>> {
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
                    let alternatives = split(e, remaining, depth + 1)?;
                    if out.len().saturating_mul(alternatives.len()) > 512 {
                        return None;
                    }
                    let mut combined = Vec::new();
                    for a in &out {
                        for b in &alternatives {
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

fn max_local_in_steps(steps: &[Branch], obs: &[Expr]) -> u32 {
    let mut m = 0;
    for b in steps {
        for bnd in &b.bounds {
            for id in bnd.vars.locals() {
                m = m.max(id.0);
            }
            m = m.max(super::max_local(&bnd.set));
        }
        for t in &b.terms {
            m = m.max(super::max_local(t));
        }
    }
    for o in obs {
        m = m.max(super::max_local(o));
    }
    m
}

impl Emitter<'_> {
    fn is_non_core(&self, v: VarId) -> bool {
        !matches!(self.shapes[v.idx()], VarShape::Core)
    }

    fn alloc_local(&mut self) -> LocalId {
        let id = LocalId(self.next_local);
        self.next_local += 1;
        id
    }

    pub(super) fn mask_lean(&self, mask: GroupMask) -> String {
        if self.groups.len() == 1 {
            return if mask == 1 { "(fun _ => true)".into() } else { "(fun _ => false)".into() };
        }
        let mut parts = Vec::new();
        for gi in 0..self.groups.len() {
            let b = (mask & (1 << gi)) != 0;
            parts.push(format!("| {gi} => {b}"));
        }
        format!("(fun g => match g.val with {} | _ => false)", parts.join(" "))
    }
}
