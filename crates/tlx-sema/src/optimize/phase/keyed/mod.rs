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
    domain::{self, Atom, Domain, Domains, Locals},
    sym_groups::{comparable, group_mask_exact, independent, subst_local, validate_groups, ActionKeyRef, GroupInfo, GroupMask, KeyRef},
    sym_norm::SymNormalizer,
    unchanged, variable, Branch,
};
use crate::{hir::*, Program};
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

/// Generate a connected keyed symmetry certificate covering invariants, init properties,
/// constraints, action constraints, and action properties. Declines `SymGroupKind::Str`.
pub fn symmetry_certificate_with_typed_groups(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: super::CheckSpec<'_>,
    groups: &[super::SymGroup],
) -> Option<String> {
    if super::has_str_group(groups) {
        return None;
    }
    let raw: Vec<Vec<String>> = groups.iter().map(|g| g.keys.clone()).collect();
    emit(program, cfg, init, next, spec, &raw, vec![])
}

/// Certify erasure followed by symmetry covering invariants, init properties,
/// constraints, action constraints, and action properties. Declines `SymGroupKind::Str`.
pub fn symmetry_projection_certificate_with_typed_groups(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: super::CheckSpec<'_>,
    groups: &[super::SymGroup],
    view: &Expr,
) -> Option<String> {
    if super::has_str_group(groups) {
        return None;
    }
    let (_, omitted) = super::parse_retained_view(program, view)?;
    let raw: Vec<Vec<String>> = groups.iter().map(|g| g.keys.clone()).collect();
    emit(program, cfg, init, next, spec, &raw, omitted)
}

fn emit(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: super::CheckSpec<'_>,
    raw_groups: &[Vec<String>],
    omitted: Vec<VarId>,
) -> Option<String> {
    let (groups, all_keys) = validate_groups(raw_groups)?;
    if !super::sym_totality::check_model_totality_with_spec(program, cfg, init, next, spec, raw_groups, &omitted) {
        return None;
    }
    let mut normalize = SymNormalizer::with_config(program, cfg);
    let initial = normalize.normalize(init)?;
    let init_branches = super::branches_with_if(&initial)?;
    let steps = super::branches_with_if(&normalize.normalize(next)?)?;
    let norm = spec.try_map(|o| normalize.normalize(o))?;
    let norm_spec = norm.as_spec();
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

    let max_obs_local = norm_spec.all_exprs().map(super::max_local).max().unwrap_or(0);
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
        next_local: (program.locals.len() as u32).max(max_local_in_steps(&steps, norm_spec.invariants)).max(max_obs_local) + 1,
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
    let observation = e.tests(norm_spec.invariants, &[])?;
    let init_observation = e.tests(norm_spec.init_props, &[])?;
    let constraint_test = e.tests(norm_spec.constraints, &[])?;
    let action_constraint_test = e.action_tests(norm_spec.action_constraints, &[])?;
    let action_observation = e.action_tests(norm_spec.action_props, &[])?;
    let obs_bundle = super::ObsBundle {
        observation: &observation,
        init_observation: &init_observation,
        constraint_test: &constraint_test,
        action_constraint_test: &action_constraint_test,
        action_observation: &action_observation,
        constrained: spec.is_constrained(),
    };
    normalize.attach_const_subst(e.output(&initial, &cases, &obs_bundle))
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
