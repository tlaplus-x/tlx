//! Generic recursive finite equivariant value & expression symmetry certificate.
//!
//! Covers arbitrary finite combinations of symmetric keys, key-free atoms,
//! sequences/tuples, finite sets, finite functions, and records over disjoint
//! products of full permutation groups (order <= 720). Used as a certified
//! fallback when the narrower `keyed` certificate does not apply.

mod lower;
mod output;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use tlx_front::cfg::{CfgValue, Config, ConstBinding};

use super::sym_norm::SymNormalizer;
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
    let (groups, all_keys) = validate_groups(groups)?;
    let mut norm = SymNormalizer::for_equiv(program);
    let init_norm = norm.normalize(init)?;
    let next_norm = norm.normalize(next)?;
    let obs_norm: Vec<Expr> = observations.iter().map(|e| norm.normalize(e)).collect::<Option<_>>()?;

    let const_bindings = collect_const_bindings(program, cfg)?;
    let totality = super::sym_totality::TotalityChecker::new(program, &groups, &all_keys, &const_bindings, &init_norm, &next_norm);
    if !totality.check_all(&init_norm, &next_norm, &obs_norm) {
        return None;
    }
    let mut ctx = lower::LowerCtx::new(program, &groups, &all_keys, &const_bindings, &totality);
    let init_form = ctx.lower_form(&init_norm, false)?;
    let next_form = ctx.lower_form(&next_norm, true)?;
    let mut obs_form = String::from("(Form.truth true)");
    for obs in &obs_norm {
        let f = ctx.lower_form(obs, false)?;
        obs_form = if obs_form == "(Form.truth true)" { f } else { format!("(Form.conj {obs_form} {f})") };
    }

    // Refuse if any group in the product is never referenced by the spec.
    let full_mask: GroupMask = ((1u32 << groups.len()) - 1) as GroupMask;
    if ctx.used_groups != full_mask {
        return None;
    }

    Some(output::render(program, &groups, &ctx, init, &init_form, &next_form, &obs_form))
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
    let mut by_name: HashMap<&str, &'a CfgValue> = HashMap::new();
    for b in &cfg.constants {
        match b {
            ConstBinding::Value { name, value, module: None } => {
                by_name.insert(name.as_str(), value);
            }
            _ => return None,
        }
    }
    let mut out = BTreeMap::new();
    for (i, c) in program.consts.iter().enumerate() {
        if c.arity != 0 {
            continue;
        }
        if let Some(&val) = by_name.get(c.name.as_ref()) {
            out.insert(ConstId(i as u32), val);
        }
    }
    Some(out)
}
