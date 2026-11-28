//! Check specifications, automatic-symmetry bounds, and retained-view parsing
//! shared by every structural projection.

use crate::hir::{Expr, ExprKind, VarId};
use crate::Program;

use super::branch::variable;
use super::ordered::OrderedPlan;

/// The largest automatic-symmetry product order (`7!`) the keyed, equivariant
/// and choice certificate emitters accept, and the largest factor (number of
/// model values) they accept. `tlx-cli` applies no larger group, and the
/// runtime canonicalizes these disjoint products without enumerating `|G|`
/// permutations, so the bound is the certificate/search cost, not the
/// per-state canonicalization cost.
pub const AUTOSYM_MAX_ORDER: u128 = 5040;
pub const AUTOSYM_MAX_KEYS: usize = 7;

/// The largest number of factors in an automatic-symmetry product: one bit per
/// factor in the emitters' `GroupMask`.
pub const AUTOSYM_MAX_GROUPS: usize = 16;

/// Atom kind of one full permutation group factor.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SymGroupKind {
    /// Permutes `ModelValue` atoms.
    Model,
    /// Permutes opaque `String` scalarset atoms (never record field names).
    Str,
}

/// One typed full permutation group factor (`Model` or opaque `Str`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SymGroup {
    pub kind: SymGroupKind,
    pub keys: Vec<String>,
}

impl SymGroup {
    pub fn model(keys: Vec<String>) -> Self {
        Self { kind: SymGroupKind::Model, keys }
    }

    pub fn str(keys: Vec<String>) -> Self {
        Self { kind: SymGroupKind::Str, keys }
    }
}

pub(in crate::optimize::phase) fn model_groups(raw: &[Vec<String>]) -> Vec<SymGroup> {
    raw.iter().map(|keys| SymGroup::model(keys.clone())).collect()
}

pub(in crate::optimize::phase) fn has_str_group(groups: &[SymGroup]) -> bool {
    groups.iter().any(|g| g.kind == SymGroupKind::Str)
}

/// All safety-level observations and admission constraints checked by `tlx-runtime`.
#[derive(Clone, Copy, Debug, Default)]
pub struct CheckSpec<'a> {
    /// State invariants (`INVARIANT` and `[]P` properties), checked on every Init and Next state.
    pub invariants: &'a [Expr],
    /// State-level `PROPERTY` conjuncts (`init_props`), checked on every Init state.
    pub init_props: &'a [Expr],
    /// State `CONSTRAINT` predicates governing admission into `AdmittedReachable`.
    pub constraints: &'a [Expr],
    /// Action `ACTION_CONSTRAINT` predicates governing transition admission into `AdmittedReachable`.
    pub action_constraints: &'a [Expr],
    /// Action `PROPERTY` conjuncts (`[][A]_sub`), checked on every Next transition from `AdmittedReachable`.
    pub action_props: &'a [Expr],
}

impl<'a> CheckSpec<'a> {
    pub fn invariants_only(invariants: &'a [Expr]) -> Self {
        Self { invariants, ..Self::default() }
    }

    pub fn is_constrained(&self) -> bool {
        !self.init_props.is_empty() || !self.constraints.is_empty() || !self.action_constraints.is_empty() || !self.action_props.is_empty()
    }

    pub fn has_action_checks(&self) -> bool {
        !self.action_constraints.is_empty() || !self.action_props.is_empty()
    }

    pub fn all_state_preds(&self) -> impl Iterator<Item = &'a Expr> {
        self.invariants.iter().chain(self.init_props.iter()).chain(self.constraints.iter())
    }

    pub fn all_exprs(&self) -> impl Iterator<Item = &'a Expr> {
        self.invariants
            .iter()
            .chain(self.init_props.iter())
            .chain(self.constraints.iter())
            .chain(self.action_constraints.iter())
            .chain(self.action_props.iter())
    }

    pub(in crate::optimize::phase) fn state_only(self) -> Option<Self> {
        (!self.has_action_checks()).then_some(self)
    }

    pub(in crate::optimize::phase) fn try_map(self, mut f: impl FnMut(&Expr) -> Option<Expr>) -> Option<OwnedCheckSpec> {
        Some(OwnedCheckSpec {
            invariants: self.invariants.iter().map(&mut f).collect::<Option<_>>()?,
            init_props: self.init_props.iter().map(&mut f).collect::<Option<_>>()?,
            constraints: self.constraints.iter().map(&mut f).collect::<Option<_>>()?,
            action_constraints: self.action_constraints.iter().map(&mut f).collect::<Option<_>>()?,
            action_props: self.action_props.iter().map(&mut f).collect::<Option<_>>()?,
        })
    }
}

/// Lowered observation and constraint strings passed by name into symmetry emitters.
pub(in crate::optimize::phase) struct ObsBundle<'a> {
    pub observation: &'a str,
    pub init_observation: &'a str,
    pub constraint_test: &'a str,
    pub action_constraint_test: &'a str,
    pub action_observation: &'a str,
    pub constrained: bool,
}

/// Owned counterpart of [`CheckSpec`] for normalized predicate vectors.
#[derive(Clone, Debug, Default)]
pub(in crate::optimize::phase) struct OwnedCheckSpec {
    pub invariants: Vec<Expr>,
    pub init_props: Vec<Expr>,
    pub constraints: Vec<Expr>,
    pub action_constraints: Vec<Expr>,
    pub action_props: Vec<Expr>,
}

impl OwnedCheckSpec {
    pub(in crate::optimize::phase) fn as_spec(&self) -> CheckSpec<'_> {
        CheckSpec {
            invariants: &self.invariants,
            init_props: &self.init_props,
            constraints: &self.constraints,
            action_constraints: &self.action_constraints,
            action_props: &self.action_props,
        }
    }
}

/// Validate that `view` is a tuple of distinct retained state variables and
/// return `(retained, omitted)` with `!omitted.is_empty()`. The tuple may use
/// any variable order: the projection emits the retained slots in that same
/// order, so it stays connected to the installed `VIEW`.
pub(in crate::optimize::phase) fn parse_retained_view(program: &Program, view: &Expr) -> Option<(Vec<VarId>, Vec<VarId>)> {
    let ExprKind::Tuple(values) = &*view.kind else { return None };
    let retained = values.iter().map(|e| variable(e, false)).collect::<Option<Vec<_>>>()?;
    let unique = retained.iter().enumerate().all(|(i, v)| v.idx() < program.vars.len() && !retained[..i].contains(v));
    if !unique {
        return None;
    }
    let omitted: Vec<_> = (0..program.vars.len()).map(|i| VarId(i as u32)).filter(|v| !retained.contains(v)).collect();
    (!omitted.is_empty()).then_some((retained, omitted))
}

/// A checked state-key projection and labels for the information it forgets.
pub struct FieldProjection {
    pub view: Expr,
    pub fields: Vec<String>,
    /// Generated certificate for the supported rule IR, never implicitly verified.
    pub certificate: Option<String>,
    /// When present, replaces the identity VIEW with a structural runtime key.
    pub ordered: Option<OrderedPlan>,
    /// True when a threshold-counter projection relies on mathematical
    /// natural-number semantics (at least one projected counter is not
    /// statically proved `<= i32::MAX`).
    pub mathematical_counter_arithmetic: bool,
}
