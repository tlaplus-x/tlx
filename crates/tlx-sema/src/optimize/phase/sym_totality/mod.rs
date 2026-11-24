//! Shared, conservative totality & finite-shape gate for all automatic symmetry
//! certificate engines (`keyed`, `erased`, `equiv_sym`, and `choose_sym`).
//!
//! In `tlx`/TLC semantics, short-circuiting over a symmetric key set (`\E`, `\A`,
//! `f = g`, `f # g`, `CHOOSE`) makes any runtime evaluation error order-dependent.
//! This module therefore fails closed unless expressions in observations and
//! value-position Boolean contexts are proved total, 32-bit overflow-free,
//! type-comparable, and finitely enumerable from `Init` and `Next` alone
//! (never assuming checked invariants).

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use tlx_front::cfg::{CfgValue, Config, ConstBinding};

use super::equiv_sym::{GroupInfo, GroupMask};
use super::sym_norm::SymNormalizer;
use crate::{builtins::Builtin as B, hir::*, Program};

mod check;
mod infer;
mod shape;

use shape::*;

const MAX_STEPS: usize = 80_000;
const MAX_I32_U32: u32 = i32::MAX as u32;
const MAX_UNION_MEMBERS: usize = 8;
const MAX_STR_SET: usize = 32;
const MAX_UNMOVED_SET: usize = 16;
const MAX_SHAPE_DEPTH: usize = 8;
const MAX_SHAPE_NODES: usize = 128;

/// Model-value typing matching `tlx_value::intern::mv_type_of` and `order::mv_eq`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum MvType {
    /// Untyped model value (no `c_` prefix): comparable with all values.
    Untyped,
    /// Typed model value (single-char prefix `c` before `_`, e.g. `P_1`):
    /// comparable only with untyped model values and same-prefix model values.
    Typed(char),
    /// Mixed or unknown typing: conservatively incomparable with non-model
    /// values and with typed model values.
    Unknown,
}

impl MvType {
    pub(crate) fn of_name(s: &str) -> Self {
        let mut chars = s.chars();
        match (chars.next(), chars.next(), chars.next()) {
            (Some(c0), Some('_'), Some(_)) => Self::Typed(c0),
            _ => Self::Untyped,
        }
    }

    fn join(self, other: Self) -> Self {
        if self == other {
            self
        } else {
            Self::Unknown
        }
    }
}

/// Abstract value shape inferred strictly from `Init` and `Next`.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Shape {
    Bottom,
    Top,
    Bool,
    /// Signed 32-bit integer (`Some((lo, hi))` = guaranteed `lo <= v <= hi` in `i32`).
    Int(Option<(i32, i32)>),
    /// String (`Some(set)` = exact finite upper bound on possible strings).
    Str(Option<BTreeSet<Arc<str>>>),
    /// Model values: moved symmetry `groups`, typing, and optional exact set of unmoved names.
    Model {
        groups: GroupMask,
        mv_type: MvType,
        unmoved: Option<BTreeSet<Arc<str>>>,
    },
    /// Set (`finite == true` iff guaranteed finitely enumerable; `max_card` = optional
    /// verified `<= i32::MAX` upper bound on cardinality).
    Set {
        elem: Box<Shape>,
        finite: bool,
        max_card: Option<u32>,
    },
    /// Sequence of homogeneous elements with optional length bounds.
    Seq {
        elem: Box<Shape>,
        min_len: u32,
        max_len: Option<u32>,
    },
    /// Fixed-length tuple.
    Tuple(Vec<Shape>),
    /// Fixed-field record.
    Record(BTreeMap<Arc<str>, Shape>),
    /// Finite function with domain shape, exactness flag, range shape, and optional domain-size bound.
    Func {
        dom: Box<Shape>,
        exact_dom: bool,
        range: Box<Shape>,
        max_dom: Option<u32>,
    },
    /// Small finite union of distinct shapes.
    Union(Vec<Shape>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(super) enum PlaceKey {
    Local(LocalId),
    Var(VarId, bool),
}

/// Externally proved sound `i32` interval hint (from `Init` and `Next` alone, never invariants)
/// used to tighten inferred `Shape::Int(None)` positions without widening any other shape.
#[derive(Clone, Debug)]
pub(crate) enum IntBoundHint {
    Int(i32, i32),
    Map(Box<IntBoundHint>),
    Set(Box<IntBoundHint>),
    Record(BTreeMap<Arc<str>, IntBoundHint>),
}

#[derive(Clone, Default)]
pub(crate) struct CheckEnv {
    locals: HashMap<LocalId, Shape>,
    local_dom: HashMap<LocalId, (Expr, bool)>,
    var_overrides: HashMap<(VarId, bool), Shape>,
    fn_app_overrides: HashMap<(VarId, bool, PlaceKey), Shape>,
    at_shape: Option<Shape>,
    /// Definitely-bound variables along the current action/init path:
    /// `Some((false, set))` during `Init`, `Some((true, set))` during `Next`, `None` otherwise.
    bound_vars: Option<(bool, BTreeSet<VarId>)>,
}

impl CheckEnv {
    pub(super) fn with_var_tracking(primed: bool) -> Self {
        Self { bound_vars: Some((primed, BTreeSet::new())), ..Self::default() }
    }

    pub(super) fn mark_var_bound(&mut self, v: VarId) {
        if let Some((_, bv)) = &mut self.bound_vars {
            bv.insert(v);
        }
    }

    pub(super) fn intersect_var_bound(&mut self, other: &Option<(bool, BTreeSet<VarId>)>) {
        if let (Some((p1, a)), Some((p2, b))) = (&mut self.bound_vars, other) {
            if p1 == p2 {
                a.retain(|v| b.contains(v));
            }
        }
    }

    pub(super) fn has_bound_all_vars(&self, num_vars: usize) -> bool {
        match &self.bound_vars {
            Some((_, bv)) => (0..num_vars).all(|i| bv.contains(&VarId(i as u32))),
            None => false,
        }
    }
    pub(crate) fn bind_local(&mut self, id: LocalId, shape: Shape, dom_origin: Option<(Expr, bool)>) {
        self.locals.insert(id, shape);
        if let Some(d) = dom_origin {
            self.local_dom.insert(id, d);
        } else {
            self.local_dom.remove(&id);
        }
    }

    pub(crate) fn with_local(&self, id: LocalId, shape: Shape) -> Self {
        let mut out = self.clone();
        out.bind_local(id, shape, None);
        out
    }

    pub(crate) fn unbind_local(&mut self, id: LocalId) {
        self.locals.remove(&id);
        self.local_dom.remove(&id);
        self.fn_app_overrides.retain(|&(_, _, k), _| k != PlaceKey::Local(id));
    }

    fn bind_var_override(&mut self, v: VarId, primed: bool, shape: Shape) {
        self.var_overrides.insert((v, primed), shape);
    }
}

/// Constant binding values (supports both literal `CfgValue` and `C <- Def` substitutions).
#[derive(Clone)]
pub(crate) enum ConstInfo<'a> {
    Value(&'a CfgValue),
    Subst(DefId),
}

pub(crate) fn collect_const_info<'a>(program: &Program, cfg: &'a Config) -> BTreeMap<ConstId, ConstInfo<'a>> {
    use tlx_front::cfg::EffectiveConst;
    let mut out = BTreeMap::new();
    for (i, c) in program.consts.iter().enumerate() {
        if c.arity != 0 {
            continue;
        }
        let id = ConstId(i as u32);
        match cfg.effective_constant(&c.name) {
            Some(EffectiveConst::Value(value)) => {
                out.insert(id, ConstInfo::Value(value));
            }
            Some(EffectiveConst::Subst(target)) => {
                if let Some(RootSymbol::Def(def_id)) = program.lookup_resolved_root(target) {
                    if program.defs[def_id.idx()].params.is_empty() && !program.def_is_let(def_id) {
                        out.insert(id, ConstInfo::Subst(def_id));
                    }
                }
            }
            None => {}
        }
    }
    // Drop cyclic or overly deep `ConstInfo::Subst` chains so downstream
    // checkers (`infer_expr`, `check_expr`, `const_exact_i32`, `is_exact_static_set`)
    // never diverge on cyclic constant substitutions.
    let cyclic: Vec<ConstId> = out
        .keys()
        .copied()
        .filter(|&id| matches!(out.get(&id), Some(ConstInfo::Subst(_))) && !subst_is_acyclic(program, &out, id, &mut Vec::new(), 0))
        .collect();
    for id in cyclic {
        out.remove(&id);
    }
    out
}

fn expr_const_refs(program: &Program, e: &Expr, seen_defs: &mut Vec<DefId>, out: &mut Vec<ConstId>) {
    match &*e.kind {
        ExprKind::Const(c) => out.push(*c),
        ExprKind::Apply { op: OpRef::Def(d), .. } | ExprKind::OpArg(OpRef::Def(d)) => {
            if !seen_defs.contains(d) {
                seen_defs.push(*d);
                if let DefKind::Op(body) = &program.defs[d.idx()].kind {
                    expr_const_refs(program, body, seen_defs, out);
                }
            }
        }
        _ => {}
    }
    crate::visit::children(e, &mut |child| expr_const_refs(program, child, seen_defs, out));
}

fn subst_is_acyclic(
    program: &Program,
    info: &BTreeMap<ConstId, ConstInfo<'_>>,
    c: ConstId,
    stack: &mut Vec<ConstId>,
    depth: usize,
) -> bool {
    if depth >= 32 || stack.contains(&c) {
        return false;
    }
    let Some(ConstInfo::Subst(def_id)) = info.get(&c) else {
        return true;
    };
    let DefKind::Op(body) = &program.defs[def_id.idx()].kind else {
        return false;
    };
    stack.push(c);
    let mut refs = Vec::new();
    expr_const_refs(program, body, &mut Vec::new(), &mut refs);
    let ok = refs.into_iter().all(|next| subst_is_acyclic(program, info, next, stack, depth + 1));
    stack.pop();
    ok
}

pub(crate) struct TotalityChecker<'a> {
    program: &'a Program,
    groups: &'a [GroupInfo],
    all_keys: &'a BTreeSet<Arc<str>>,
    consts: BTreeMap<ConstId, ConstInfo<'a>>,
    var_shapes: Vec<Shape>,
    allow_choose_folds: Option<&'a HashMap<LocalId, Option<Expr>>>,
}

/// True if `cfg` contains any definition override (`Def = v`, `Def <- Other`, or module-scoped
/// override) or operator constant table (`F(a) = v`), which symmetry normalizers do not model.
///
/// Mirrors `bind_cfg` (`tlx-eval/src/interp/cfg.rs`): detects overrides of operators imported
/// via anonymous `INSTANCE` (visible in root scope) as well as named `INSTANCE` definitions.
pub(crate) fn cfg_overrides_or_tables(program: &Program, cfg: &Config) -> bool {
    let any_non_let_def =
        |target: &str| program.defs.iter().enumerate().any(|(i, d)| &*d.name == target && !program.def_is_let(DefId(i as u32)));
    cfg.constants.iter().any(|b| match b {
        ConstBinding::Value { name, module, .. } | ConstBinding::Subst { name, module, .. } => {
            module.is_some()
                || match program.lookup_resolved_root(name) {
                    Some(RootSymbol::Const(_)) => false,
                    Some(RootSymbol::Def(_)) => true,
                    _ => any_non_let_def(name),
                }
        }
        ConstBinding::OpValue { .. } => true,
    })
}

/// Top-level shared totality gate called before `keyed`, `erased`, and `equiv_sym`.
pub(crate) fn check_model_totality_with_omitted(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    observations: &[Expr],
    raw_groups: &[Vec<String>],
    omitted: &[VarId],
) -> bool {
    if cfg_overrides_or_tables(program, cfg) {
        return false;
    }
    let Some((groups, all_keys)) = super::equiv_sym::validate_groups(raw_groups) else {
        return false;
    };
    let mut norm = SymNormalizer::for_equiv(program);
    let Some(init_norm) = norm.normalize(init) else { return false };
    let Some(next_norm) = norm.normalize(next) else { return false };
    let Some(obs_norm) = observations.iter().map(|e| norm.normalize(e)).collect::<Option<Vec<_>>>() else {
        return false;
    };
    let consts = collect_const_info(program, cfg);
    let checker = TotalityChecker::with_const_info(program, &groups, &all_keys, consts, &init_norm, &next_norm, None);
    checker.check_all_with_omitted(&init_norm, &next_norm, &obs_norm, omitted)
}

/// Build and run the shared `TotalityChecker` for `choose_sym` on its already-normalized
/// trees, returning the checker so `choose_sym` can reuse it on hoisted/rewritten `CHOOSE`
/// predicates without maintaining a second totality engine.
#[allow(clippy::too_many_arguments)]
pub(crate) fn build_choose_totality_checker<'a>(
    program: &'a Program,
    cfg: &'a Config,
    groups: &'a [GroupInfo],
    all_keys: &'a BTreeSet<Arc<str>>,
    init_norm: &Expr,
    next_norm: &Expr,
    obs_norm: &[Expr],
    fold_vars: &'a HashMap<LocalId, Option<Expr>>,
    bound_hints: &[Option<IntBoundHint>],
) -> Option<TotalityChecker<'a>> {
    if cfg_overrides_or_tables(program, cfg) {
        return None;
    }
    let consts = collect_const_info(program, cfg);
    let mut checker = TotalityChecker::with_const_info(program, groups, all_keys, consts, init_norm, next_norm, Some(fold_vars));
    for (shape, hint) in checker.var_shapes.iter_mut().zip(bound_hints) {
        if let Some(h) = hint {
            *shape = tighten_shape_with_hint(shape, h);
        }
    }
    checker.check_all(init_norm, next_norm, obs_norm).then_some(checker)
}

impl<'a> TotalityChecker<'a> {
    pub(crate) fn new(
        program: &'a Program,
        groups: &'a [GroupInfo],
        all_keys: &'a BTreeSet<Arc<str>>,
        consts: &BTreeMap<ConstId, &'a CfgValue>,
        init_norm: &Expr,
        next_norm: &Expr,
    ) -> Self {
        let info = consts.iter().map(|(&id, &v)| (id, ConstInfo::Value(v))).collect();
        Self::with_const_info(program, groups, all_keys, info, init_norm, next_norm, None)
    }

    pub(crate) fn with_const_info(
        program: &'a Program,
        groups: &'a [GroupInfo],
        all_keys: &'a BTreeSet<Arc<str>>,
        consts: BTreeMap<ConstId, ConstInfo<'a>>,
        init_norm: &Expr,
        next_norm: &Expr,
        allow_choose_folds: Option<&'a HashMap<LocalId, Option<Expr>>>,
    ) -> Self {
        let mut checker =
            Self { program, groups, all_keys, consts, var_shapes: vec![Shape::Bottom; program.vars.len()], allow_choose_folds };
        checker.var_shapes = checker.infer_var_shapes(init_norm, next_norm);
        checker
    }

    /// Check complete observations, value-position expressions in `Init`/`Next`, and
    /// runtime orbit-canonicalizer comparability of all retained state variables.
    pub(crate) fn check_all(&self, init_norm: &Expr, next_norm: &Expr, obs_norm: &[Expr]) -> bool {
        self.check_all_with_omitted(init_norm, next_norm, obs_norm, &[])
    }

    pub(crate) fn check_all_with_omitted(&self, init_norm: &Expr, next_norm: &Expr, obs_norm: &[Expr], omitted: &[VarId]) -> bool {
        // Runtime orbit canonicalization compares `state` with `π(state)` across all
        // retained state variables; every retained variable must therefore be self-comparable
        // and have safe <= i32::MAX set cardinality bounds.
        for (i, shape) in self.var_shapes.iter().enumerate() {
            if !omitted.contains(&VarId(i as u32)) && (!shape_self_comparable(shape) || !shape_has_safe_set_cards(shape, self.groups)) {
                return false;
            }
        }
        let obs_env = CheckEnv::default();
        for obs in obs_norm {
            if !self.check_form_total(obs, false, false, &obs_env) {
                return false;
            }
        }
        let mut steps = MAX_STEPS;
        let num_vars = self.program.vars.len();
        let mut init_env = CheckEnv::with_var_tracking(false);
        let mut init_bound = BTreeSet::new();
        if !self.check_action_formula(init_norm, false, &mut init_env, &mut init_bound, &mut steps)
            || !init_env.has_bound_all_vars(num_vars)
        {
            return false;
        }
        let mut next_env = CheckEnv::with_var_tracking(true);
        let mut next_bound = BTreeSet::new();
        self.check_action_formula(next_norm, true, &mut next_env, &mut next_bound, &mut steps) && next_env.has_bound_all_vars(num_vars)
    }

    pub(crate) fn check_form_total(&self, e: &Expr, allow_prime: bool, in_prime: bool, env: &CheckEnv) -> bool {
        let mut steps = MAX_STEPS;
        self.check_form(e, allow_prime, in_prime, env, &mut steps)
    }

    /// Action-level `\E` enumerator check: ONLY called in genuine action-enumeration
    /// position (`Next` disjunction/conjunction/action-`\E`), NEVER in Boolean value position.
    pub(crate) fn check_action_quant_safe(&self, e: &Expr, in_prime: bool, env: &CheckEnv) -> bool {
        if in_prime {
            return false;
        }
        let mut steps = MAX_STEPS;
        let mut bound = BTreeSet::new();
        let mut local_env = env.clone();
        self.check_action_formula(e, true, &mut local_env, &mut bound, &mut steps)
    }

    pub(crate) fn is_definitely_seq(&self, e: &Expr, in_prime: bool, env: &CheckEnv) -> bool {
        let mut steps = MAX_STEPS;
        let s = self.infer_expr(e, in_prime, &self.var_shapes, env, &mut steps);
        is_seq_shape(&s)
    }

    pub(crate) fn apply_positive_fact(&self, cond: &Expr, in_prime: bool, env: &mut CheckEnv) {
        self.apply_fact(cond, true, in_prime, env);
    }

    pub(crate) fn apply_negative_fact(&self, cond: &Expr, in_prime: bool, env: &mut CheckEnv) {
        self.apply_fact(cond, false, in_prime, env);
    }

    pub(crate) fn bound_elem_info(&self, set: &Expr, in_prime: bool, env: &CheckEnv) -> (Shape, Option<(Expr, bool)>) {
        let origin = match &*set.kind {
            ExprKind::Builtin { op: B::Domain, args } if args.len() == 1 => Some((args[0].clone(), in_prime)),
            _ => None,
        };
        let mut steps = MAX_STEPS;
        let elem = self.set_elem_shape(set, in_prime, env, &mut steps);
        (elem, origin)
    }

    pub(crate) fn prove_tuple_set_arity(&self, set: &Expr, arity: usize, in_prime: bool, env: &CheckEnv) -> Option<Vec<Shape>> {
        let mut steps = MAX_STEPS;
        let elem = self.set_elem_shape(set, in_prime, env, &mut steps);
        extract_exact_tuple_arity(&elem, arity)
    }

    pub(crate) fn check_expr_total_shape(&self, e: &Expr, env: &CheckEnv) -> Option<Shape> {
        let mut steps = MAX_STEPS;
        self.check_expr(e, false, false, env, &mut steps)
    }

    pub(crate) fn set_elem_of(&self, s: &Shape) -> Option<Shape> {
        set_elem_of_shape(s)
    }

    pub(crate) fn var_elem_shape(&self, v: VarId) -> Option<Shape> {
        set_elem_of_shape(self.var_shapes.get(v.idx())?)
    }

    pub(crate) fn group_key_shape(&self, mask: GroupMask) -> Shape {
        let mut mv_type: Option<MvType> = None;
        for (gi, g) in self.groups.iter().enumerate() {
            if (mask & (1u16 << gi)) != 0 {
                for k in &g.keys {
                    let kt = MvType::of_name(k);
                    mv_type = Some(mv_type.map_or(kt, |acc| acc.join(kt)));
                }
            }
        }
        Shape::Model { groups: mask, mv_type: mv_type.unwrap_or(MvType::Unknown), unmoved: Some(BTreeSet::new()) }
    }

    pub(crate) fn bind_step_bounds(&self, bounds: &[Bound], hints: &HashMap<LocalId, IntBoundHint>) -> Option<CheckEnv> {
        let mut env = CheckEnv::default();
        for b in bounds {
            let (elem, origin) = self.bound_elem_info(&b.set, false, &env);
            match &b.vars {
                BoundVars::Many(ids) => {
                    for &id in ids {
                        let s = hints.get(&id).map_or_else(|| elem.clone(), |h| tighten_shape_with_hint(&elem, h));
                        env.bind_local(id, s, origin.clone());
                    }
                }
                BoundVars::Tuple(ids) => {
                    let parts = extract_exact_tuple_arity(&elem, ids.len())?;
                    for (&id, p) in ids.iter().zip(parts) {
                        env.bind_local(id, p, None);
                    }
                }
            }
        }
        Some(env)
    }
}
