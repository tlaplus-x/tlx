//! Generic recursive finite equivariant value & expression symmetry certificate.
//!
//! Covers arbitrary finite combinations of symmetric keys, key-free atoms,
//! sequences/tuples, finite sets, finite functions, and records over disjoint
//! products of full permutation groups (order <= 5040). Used as a certified
//! fallback when the narrower `keyed` certificate does not apply.

pub(in crate::optimize::phase) mod lower;
pub(in crate::optimize::phase) mod output;

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use tlx_front::cfg::{CfgValue, Config, EffectiveConst};

use super::domain::Atom;
use super::sym_norm::SymNormalizer;
use super::CheckSpec;
use crate::{hir::*, Program};

pub(in crate::optimize::phase) type GroupMask = u16;

#[derive(Clone, Debug)]
pub(in crate::optimize::phase) struct GroupInfo {
    pub(in crate::optimize::phase) keys: Vec<Arc<str>>,
    pub(in crate::optimize::phase) key_set: BTreeSet<Arc<str>>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(in crate::optimize::phase) enum AtomKey {
    Int(i128),
    Str(Arc<str>),
    Bool(bool),
    Model(Arc<str>),
    Decimal(Arc<str>),
}

impl AtomKey {
    pub(in crate::optimize::phase) fn from_key_free_atom(a: &Atom, all_keys: &BTreeSet<Arc<str>>) -> Option<Self> {
        match a {
            Atom::Num(n) => Some(Self::Int(*n)),
            Atom::Bool(b) => Some(Self::Bool(*b)),
            Atom::Str(s) => Some(Self::Str(s.clone())),
            Atom::Model(m) => (!all_keys.contains(m)).then(|| Self::Model(m.clone())),
        }
    }

    pub(in crate::optimize::phase) fn describe(&self) -> String {
        match self {
            Self::Int(n) => format!("int:{n}"),
            Self::Str(s) => format!("str:{s:?}"),
            Self::Bool(b) => format!("bool:{b}"),
            Self::Model(m) => format!("model:{m}"),
            Self::Decimal(d) => format!("decimal:{d}"),
        }
    }
}

/// Fold lowered `EquivRule.Form` conjuncts into one formula, defaulting to
/// `(Form.truth true)` when empty.
pub(in crate::optimize::phase) fn fold_form_conj(forms: impl IntoIterator<Item = String>) -> String {
    let mut it = forms.into_iter();
    let Some(first) = it.next() else {
        return "(Form.truth true)".to_string();
    };
    it.fold(first, |acc, f| format!("(Form.conj {acc} {f})"))
}

/// Generate a connected `EquivRule` certificate for a disjoint product of full
/// permutation groups. Unsupported constructs fail closed (`None`).
pub fn symmetry_certificate(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    observations: &[Expr],
    groups: &[Vec<String>],
) -> Option<String> {
    symmetry_certificate_with_spec(program, cfg, init, next, CheckSpec::invariants_only(observations), groups)
}

/// Generate a connected `EquivRule` certificate covering invariants, init properties,
/// constraints, action constraints, and action properties.
pub fn symmetry_certificate_with_spec(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: CheckSpec<'_>,
    groups: &[Vec<String>],
) -> Option<String> {
    let (groups, all_keys) = validate_groups(groups)?;
    let const_bindings = collect_const_bindings(program, cfg)?;
    let mut norm = SymNormalizer::for_equiv_with_config(program, cfg);
    let init_norm = norm.normalize(init)?;
    let next_norm = norm.normalize(next)?;
    let owned_spec = spec.try_map(|e| norm.normalize(e))?;
    let norm_spec = owned_spec.as_spec();

    let const_info = super::sym_totality::collect_const_info(program, cfg);
    let totality =
        super::sym_totality::TotalityChecker::with_const_info(program, &groups, &all_keys, const_info, &init_norm, &next_norm, None);
    if !totality.check_all_with_spec(&init_norm, &next_norm, norm_spec, &[]) {
        return None;
    }
    let mut ctx = lower::LowerCtx::new(program, &groups, &all_keys, &const_bindings, &totality);
    let init_form = ctx.lower_form(&init_norm, false)?;
    let next_form = ctx.lower_form(&next_norm, true)?;
    let lower_conj = |ctx: &mut lower::LowerCtx<'_>, es: &[Expr], action: bool| -> Option<String> {
        let mut acc = String::from("(Form.truth true)");
        for e in es {
            let f = if action { ctx.lower_action_pred(e)? } else { ctx.lower_form(e, false)? };
            acc = if acc == "(Form.truth true)" { f } else { format!("(Form.conj {acc} {f})") };
        }
        Some(acc)
    };
    let obs_form = lower_conj(&mut ctx, norm_spec.invariants, false)?;
    let init_obs_form = lower_conj(&mut ctx, norm_spec.init_props, false)?;
    let constraint_form = lower_conj(&mut ctx, norm_spec.constraints, false)?;
    let action_constraint_form = lower_conj(&mut ctx, norm_spec.action_constraints, true)?;
    let action_obs_form = lower_conj(&mut ctx, norm_spec.action_props, true)?;

    // Refuse if any group in the product is never referenced by the spec.
    let full_mask: GroupMask = ((1u32 << groups.len()) - 1) as GroupMask;
    if ctx.used_groups != full_mask {
        return None;
    }

    let forms = output::Forms {
        init: &init_form,
        next: &next_form,
        obs: &obs_form,
        init_obs: &init_obs_form,
        constraint: &constraint_form,
        action_constraint: &action_constraint_form,
        action_obs: &action_obs_form,
        constrained: spec.is_constrained(),
    };
    norm.attach_const_subst(output::render(program, &groups, &ctx, init, &forms))
}

/// Generate a connected `ErasedEquivRule` certificate composing unobserved-variable
/// erasure with recursive equivariant symmetry over the exact retained-variable tuple.
pub fn symmetry_projection_certificate_with_spec(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: CheckSpec<'_>,
    groups: &[Vec<String>],
    view: &Expr,
) -> Option<String> {
    let (retained, omitted) = super::parse_retained_view(program, view)?;
    let (groups, all_keys) = validate_groups(groups)?;
    let const_bindings = collect_const_bindings(program, cfg)?;
    let mut norm = SymNormalizer::for_equiv_with_config(program, cfg);
    let init_norm = norm.normalize(init)?;
    let next_norm = norm.normalize(next)?;
    let owned_spec = spec.try_map(|e| norm.normalize(e))?;
    let norm_spec = owned_spec.as_spec();

    let const_info = super::sym_totality::collect_const_info(program, cfg);
    let totality =
        super::sym_totality::TotalityChecker::with_const_info(program, &groups, &all_keys, const_info, &init_norm, &next_norm, None);
    if !totality.check_all_with_spec(&init_norm, &next_norm, norm_spec, &omitted) {
        return None;
    }

    let init_raw = super::branches_with_if(&init_norm)?;
    let step_raw = super::branches_with_if(&next_norm)?;
    if init_raw.is_empty() || step_raw.is_empty() {
        return None;
    }

    let mut ctx = lower::LowerCtx::with_retained(program, &groups, &all_keys, &const_bindings, &totality, &retained);
    let mut hidden_atoms: Vec<String> = Vec::new();

    let mut init_branches = Vec::with_capacity(init_raw.len());
    for b in &init_raw {
        let hidden = extract_hidden_transfers(b, &omitted, false, &mut hidden_atoms)?;
        let (bounds, body) = ctx.lower_erased_branch(b, &omitted, false)?;
        init_branches.push(output::ErasedBranch { bounds, body, hidden });
    }
    let mut step_branches = Vec::with_capacity(step_raw.len());
    for b in &step_raw {
        let hidden = extract_hidden_transfers(b, &omitted, true, &mut hidden_atoms)?;
        let (bounds, body) = ctx.lower_erased_branch(b, &omitted, true)?;
        step_branches.push(output::ErasedBranch { bounds, body, hidden });
    }

    let lower_conj = |ctx: &mut lower::LowerCtx<'_>, es: &[Expr], action: bool| -> Option<String> {
        let mut acc = String::from("(Form.truth true)");
        for e in es {
            let f = if action { ctx.lower_action_pred(e)? } else { ctx.lower_form(e, false)? };
            acc = if acc == "(Form.truth true)" { f } else { format!("(Form.conj {acc} {f})") };
        }
        Some(acc)
    };
    let obs_form = lower_conj(&mut ctx, norm_spec.invariants, false)?;
    let init_obs_form = lower_conj(&mut ctx, norm_spec.init_props, false)?;
    let constraint_form = lower_conj(&mut ctx, norm_spec.constraints, false)?;
    let action_constraint_form = lower_conj(&mut ctx, norm_spec.action_constraints, true)?;
    let action_obs_form = lower_conj(&mut ctx, norm_spec.action_props, true)?;

    // Refuse if any group in the product is never referenced by the retained spec.
    let full_mask: GroupMask = ((1u32 << groups.len()) - 1) as GroupMask;
    if ctx.used_groups != full_mask {
        return None;
    }

    let erased = output::ErasedSpec {
        retained_count: retained.len(),
        omitted: &omitted,
        init_branches: &init_branches,
        step_branches: &step_branches,
        hidden_atoms: &hidden_atoms,
        obs: &obs_form,
        init_obs: &init_obs_form,
        constraint: &constraint_form,
        action_constraint: &action_constraint_form,
        action_obs: &action_obs_form,
        constrained: spec.is_constrained(),
    };
    norm.attach_const_subst(output::render_erased(&groups, &ctx, init, &erased))
}

fn extract_hidden_transfers(
    branch: &super::Branch,
    omitted: &[VarId],
    primed: bool,
    hidden_atoms: &mut Vec<String>,
) -> Option<Vec<String>> {
    use super::erasure::{branch_hidden_binding, HiddenBinding};
    use crate::optimize::lean::literal;
    let mut out = Vec::with_capacity(omitted.len());
    for &v in omitted {
        let bind = branch_hidden_binding(branch, v, primed)?;
        let term = match bind {
            HiddenBinding::Unchanged => {
                let i = omitted.iter().position(|x| *x == v)?;
                format!("h ⟨{i}, by decide⟩")
            }
            HiddenBinding::Assign { rhs, .. } => match &*rhs.kind {
                ExprKind::Num(n) if i32::try_from(*n).is_ok() => format!("sem.number ({n})"),
                ExprKind::Str(s) => format!("sem.string {}", literal(s)),
                ExprKind::Bool(b) => format!("sem.boolean {b}"),
                ExprKind::Var(u) if primed => {
                    if let Some(i) = omitted.iter().position(|x| x == u) {
                        format!("h ⟨{i}, by decide⟩")
                    } else {
                        let id = hidden_atoms.len();
                        hidden_atoms.push(format!("Hidden update expr HIR: {rhs:#?}"));
                        format!("sem.hiddenUpdate {id} s t ws h")
                    }
                }
                _ if !primed => {
                    let id = hidden_atoms.len();
                    hidden_atoms.push(format!("Hidden init expr HIR: {rhs:#?}"));
                    format!("sem.hiddenSeed {id} s ws")
                }
                _ => {
                    let id = hidden_atoms.len();
                    hidden_atoms.push(format!("Hidden update expr HIR: {rhs:#?}"));
                    format!("sem.hiddenUpdate {id} s t ws h")
                }
            },
        };
        out.push(term);
    }
    Some(out)
}

pub(in crate::optimize::phase) fn validate_groups(raw: &[Vec<String>]) -> Option<(Vec<GroupInfo>, BTreeSet<Arc<str>>)> {
    if raw.is_empty() || raw.len() > super::AUTOSYM_MAX_GROUPS {
        return None;
    }
    let mut groups = Vec::with_capacity(raw.len());
    let mut all_keys = BTreeSet::new();
    let mut order: u128 = 1;
    for g in raw {
        if !(2..=super::AUTOSYM_MAX_KEYS).contains(&g.len()) {
            return None;
        }
        let keys: Vec<Arc<str>> = g.iter().map(|s| Arc::from(s.as_str())).collect();
        let key_set: BTreeSet<Arc<str>> = keys.iter().cloned().collect();
        if key_set.len() != g.len() || !all_keys.is_disjoint(&key_set) {
            return None;
        }
        let fact: u128 = (1..=g.len() as u128).product();
        order = order.checked_mul(fact)?;
        if order > super::AUTOSYM_MAX_ORDER {
            return None;
        }
        all_keys.extend(key_set.iter().cloned());
        groups.push(GroupInfo { keys, key_set });
    }
    Some((groups, all_keys))
}

/// Partition an exact finite atom set into complete symmetric-group indices and
/// key-free fixed atoms. Fails closed (`None`) if any symmetric group overlaps
/// partially or if an uncovered moved key remains.
pub(in crate::optimize::phase) fn classify_key_set(
    keys: &BTreeSet<Atom>,
    groups: &[GroupInfo],
    all_keys: &BTreeSet<Arc<str>>,
) -> Option<(Vec<usize>, Vec<Atom>)> {
    let mut sym_groups = Vec::new();
    let mut covered_keys: BTreeSet<Arc<str>> = BTreeSet::new();
    for (gi, g) in groups.iter().enumerate() {
        let present = g.keys.iter().filter(|k| keys.contains(&Atom::Model((*k).clone()))).count();
        if present == g.keys.len() {
            sym_groups.push(gi);
            covered_keys.extend(g.keys.iter().cloned());
        } else if present != 0 {
            return None;
        }
    }
    let mut fixed_keys = Vec::new();
    for k in keys {
        if let Atom::Model(m) = k {
            if covered_keys.contains(m) {
                continue;
            }
            if all_keys.contains(m) {
                return None;
            }
        }
        fixed_keys.push(k.clone());
    }
    Some((sym_groups, fixed_keys))
}

pub(in crate::optimize::phase) fn collect_const_bindings<'a>(
    program: &Program,
    cfg: &'a Config,
) -> Option<BTreeMap<ConstId, &'a CfgValue>> {
    if super::sym_totality::cfg_overrides_or_tables(program, cfg) {
        return None;
    }
    let mut out = BTreeMap::new();
    for (i, c) in program.consts.iter().enumerate() {
        if c.arity != 0 {
            continue;
        }
        if let Some(EffectiveConst::Value(val)) = cfg.effective_constant(&c.name) {
            out.insert(ConstId(i as u32), val);
        }
    }
    Some(out)
}
