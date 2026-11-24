//! Generic recursive finite equivariant value & expression symmetry certificate.
//!
//! Covers arbitrary finite combinations of symmetric keys, key-free atoms,
//! sequences/tuples, finite sets, finite functions, and records over disjoint
//! products of full permutation groups (order <= 720). Used as a certified
//! fallback when the narrower `keyed` certificate does not apply.

mod lower;
mod output;

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use tlx_front::cfg::{CfgValue, Config, EffectiveConst};

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
pub(super) enum AtomKey {
    Int(i128),
    Str(Arc<str>),
    Bool(bool),
    Model(Arc<str>),
    Decimal(Arc<str>),
}

impl AtomKey {
    pub(super) fn describe(&self) -> String {
        match self {
            Self::Int(n) => format!("int:{n}"),
            Self::Str(s) => format!("str:{s:?}"),
            Self::Bool(b) => format!("bool:{b}"),
            Self::Model(m) => format!("model:{m}"),
            Self::Decimal(d) => format!("decimal:{d}"),
        }
    }
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

pub(in crate::optimize::phase) fn validate_groups(raw: &[Vec<String>]) -> Option<(Vec<GroupInfo>, BTreeSet<Arc<str>>)> {
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
        let keys: Vec<Arc<str>> = g.iter().map(|s| Arc::from(s.as_str())).collect();
        let key_set: BTreeSet<Arc<str>> = keys.iter().cloned().collect();
        if key_set.len() != g.len() || !all_keys.is_disjoint(&key_set) {
            return None;
        }
        let fact: u128 = (1..=g.len() as u128).product();
        order = order.checked_mul(fact)?;
        if order > 720 {
            return None;
        }
        all_keys.extend(key_set.iter().cloned());
        groups.push(GroupInfo { keys, key_set });
    }
    Some((groups, all_keys))
}

fn collect_const_bindings<'a>(program: &Program, cfg: &'a Config) -> Option<BTreeMap<ConstId, &'a CfgValue>> {
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
