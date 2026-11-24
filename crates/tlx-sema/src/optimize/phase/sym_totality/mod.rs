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

/// Constant binding values (supports literal `CfgValue`, pure builtin targets
/// such as `C <- Nat`, and non-builtin `C <- Def` substitutions).
#[derive(Clone)]
pub(crate) enum ConstInfo<'a> {
    Value(&'a CfgValue),
    Builtin(B),
    Subst(DefId),
}

fn collect_raw_const_info<'a>(program: &Program, cfg: &'a Config) -> BTreeMap<ConstId, ConstInfo<'a>> {
    use super::ConstSubstTarget;
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
            Some(EffectiveConst::Subst(target)) => match super::resolve_const_subst_name(program, target) {
                Some(ConstSubstTarget::PureBuiltin(op, _)) => {
                    out.insert(id, ConstInfo::Builtin(op));
                }
                Some(ConstSubstTarget::Def(def_id)) => {
                    out.insert(id, ConstInfo::Subst(def_id));
                }
                Some(ConstSubstTarget::Const(_)) | None => {}
            },
            None => {}
        }
    }
    out
}

pub(crate) fn collect_const_info<'a>(program: &Program, cfg: &'a Config) -> BTreeMap<ConstId, ConstInfo<'a>> {
    let mut out = collect_raw_const_info(program, cfg);
    // Drop cyclic or overly deep `ConstInfo::Subst` chains so downstream
    // checkers (`infer_expr`, `check_expr`, `const_exact_i32`, `is_exact_static_set`)
    // never diverge on cyclic constant substitutions.
    let mut checker = SubstAcyclicity::new(program, &out);
    let cyclic: Vec<ConstId> =
        out.keys().copied().filter(|&id| matches!(out.get(&id), Some(ConstInfo::Subst(_))) && !checker.is_acyclic(id)).collect();
    for id in cyclic {
        out.remove(&id);
    }
    out
}

const MAX_SUBST_DEPTH: usize = 32;
const MAX_SUBST_WORK: usize = 100_000;

struct ConstFrame {
    c: ConstId,
    deps: Arc<[ConstId]>,
    next_idx: usize,
    max_child: usize,
}

struct SubstAcyclicity<'a> {
    program: &'a Program,
    info: &'a BTreeMap<ConstId, ConstInfo<'a>>,
    /// Cached deduplicated constant references reachable from each `DefId`, shared across DFS frames.
    def_const_deps: HashMap<DefId, Option<Arc<[ConstId]>>>,
    /// Memoized maximum substitution-chain height (`0` for non-subst leaf,
    /// `Some(h)` with `h < MAX_SUBST_DEPTH` for valid acyclic subst, `None` for
    /// cyclic, non-op, or too-deep subst). Never caches budget exhaustion.
    heights: HashMap<ConstId, Option<usize>>,
    /// Initial work budget (used for deterministic work accounting in tests).
    #[cfg(test)]
    initial_budget: usize,
    /// Bounded remaining work budget across AST visits, cached set merges, and DFS edges.
    budget: usize,
}

impl<'a> SubstAcyclicity<'a> {
    fn new(program: &'a Program, info: &'a BTreeMap<ConstId, ConstInfo<'a>>) -> Self {
        Self::with_budget(program, info, MAX_SUBST_WORK)
    }

    fn with_budget(program: &'a Program, info: &'a BTreeMap<ConstId, ConstInfo<'a>>, budget: usize) -> Self {
        Self {
            program,
            info,
            def_const_deps: HashMap::new(),
            heights: HashMap::new(),
            #[cfg(test)]
            initial_budget: budget,
            budget,
        }
    }

    #[cfg(test)]
    fn work_used(&self) -> usize {
        self.initial_budget - self.budget
    }

    fn debit(&mut self, cost: usize) -> bool {
        let Some(rem) = self.budget.checked_sub(cost) else {
            self.budget = 0;
            return false;
        };
        self.budget = rem;
        true
    }

    fn collect_expr_const_refs(&mut self, root: &Expr, seen_defs: &mut BTreeSet<DefId>, out: &mut BTreeSet<ConstId>) -> bool {
        let mut stack: Vec<Expr> = vec![root.clone()];
        while let Some(e) = stack.pop() {
            if !self.debit(1) {
                return false;
            }
            match &*e.kind {
                ExprKind::Const(c) => {
                    out.insert(*c);
                }
                ExprKind::Apply { op: OpRef::Def(d), .. } | ExprKind::OpArg(OpRef::Def(d)) => {
                    if let Some(cached) = self.def_const_deps.get(d).cloned() {
                        let Some(deps) = cached else {
                            return false;
                        };
                        if !self.debit(deps.len()) {
                            return false;
                        }
                        out.extend(deps.iter().copied());
                    } else if seen_defs.insert(*d) {
                        if let DefKind::Op(body) = &self.program.defs[d.idx()].kind {
                            stack.push(body.clone());
                        }
                    }
                }
                _ => {}
            }
            crate::visit::children(&e, &mut |child| stack.push(child.clone()));
        }
        true
    }

    fn deps_of_def(&mut self, def_id: DefId) -> Option<Arc<[ConstId]>> {
        if let Some(cached) = self.def_const_deps.get(&def_id).cloned() {
            if !self.debit(1) {
                return None;
            }
            return cached;
        }
        let DefKind::Op(body) = &self.program.defs[def_id.idx()].kind else {
            self.def_const_deps.insert(def_id, None);
            return None;
        };
        let mut seen_defs = BTreeSet::from([def_id]);
        let mut refs = BTreeSet::new();
        if !self.collect_expr_const_refs(body, &mut seen_defs, &mut refs) {
            return None;
        }
        let deps: Arc<[ConstId]> = refs.into_iter().collect();
        self.def_const_deps.insert(def_id, Some(deps.clone()));
        Some(deps)
    }

    fn push_frame(&mut self, c: ConstId, visiting: &mut BTreeSet<ConstId>, frames: &mut Vec<ConstFrame>) -> Result<Option<usize>, bool> {
        if !self.debit(1) {
            return Err(false);
        }
        if let Some(&cached) = self.heights.get(&c) {
            return cached.map(Some).ok_or(true);
        }
        if visiting.contains(&c) {
            return Err(true);
        }
        let Some(ConstInfo::Subst(def_id)) = self.info.get(&c) else {
            self.heights.insert(c, Some(0));
            return Ok(Some(0));
        };
        let def_id = *def_id;
        let Some(deps) = self.deps_of_def(def_id) else {
            if self.budget == 0 {
                return Err(false);
            }
            self.heights.insert(c, None);
            return Err(true);
        };
        visiting.insert(c);
        frames.push(ConstFrame { c, deps, next_idx: 0, max_child: 0 });
        Ok(None)
    }

    fn const_height(&mut self, root: ConstId) -> Option<usize> {
        let mut visiting = BTreeSet::new();
        let mut frames = Vec::new();
        match self.push_frame(root, &mut visiting, &mut frames) {
            Ok(Some(h)) => return Some(h),
            Ok(None) => {}
            Err(_) => return None,
        }
        while let Some(top) = frames.last_mut() {
            if top.next_idx < top.deps.len() {
                let dep = top.deps[top.next_idx];
                top.next_idx += 1;
                match self.push_frame(dep, &mut visiting, &mut frames) {
                    Ok(Some(h)) => {
                        let parent = frames.last_mut().unwrap();
                        parent.max_child = parent.max_child.max(h);
                    }
                    Ok(None) => {}
                    Err(permanent) => {
                        // Every ancestor in `frames` reaches this permanently invalid
                        // dependency (cycle, non-op, or height >= MAX_SUBST_DEPTH),
                        // so caching `None` is path-independent. On budget exhaustion
                        // (`!permanent`), leave `heights` untouched.
                        for f in frames.drain(..) {
                            visiting.remove(&f.c);
                            if permanent {
                                self.heights.insert(f.c, None);
                            }
                        }
                        return None;
                    }
                }
            } else {
                let frame = frames.pop().unwrap();
                visiting.remove(&frame.c);
                let height = frame.max_child + 1;
                if height >= MAX_SUBST_DEPTH {
                    self.heights.insert(frame.c, None);
                    for f in frames.drain(..) {
                        visiting.remove(&f.c);
                        self.heights.insert(f.c, None);
                    }
                    return None;
                }
                self.heights.insert(frame.c, Some(height));
                if let Some(parent) = frames.last_mut() {
                    parent.max_child = parent.max_child.max(height);
                } else {
                    return Some(height);
                }
            }
        }
        None
    }

    fn is_acyclic(&mut self, c: ConstId) -> bool {
        self.const_height(c).is_some()
    }
}

pub(crate) struct TotalityChecker<'a> {
    program: &'a Program,
    groups: &'a [GroupInfo],
    all_keys: &'a BTreeSet<Arc<str>>,
    consts: BTreeMap<ConstId, ConstInfo<'a>>,
    var_shapes: Vec<Shape>,
    allow_choose_folds: Option<&'a HashMap<LocalId, Option<Expr>>>,
    /// Scoped to state-projection emitters: permits reading `Len(seq)` and
    /// iterating `1..Len(seq)` on unbounded sequences while keeping all arithmetic
    /// strictly 32-bit overflow-checked.
    allow_unbounded_seq_len: bool,
    /// Scoped strictly to certified relative-age clock projections: permits
    /// `(stamp + d) cmp clock` comparisons on the proven mathematical clock variable.
    age_clock: Option<VarId>,
}

/// True if `cfg` contains any definition override (`Def = v`, `Def <- Other`, or module-scoped
/// override), operator constant table (`F(a) = v`), nonzero-arity constant substitution,
/// or invalid `CONSTANT C <- target` substitution, which proof normalizers refuse.
///
/// Mirrors `bind_cfg` (`tlx-eval/src/interp/cfg.rs`): detects overrides of operators imported
/// via anonymous `INSTANCE` (visible in root scope) as well as named `INSTANCE` definitions.
pub(crate) fn cfg_overrides_or_tables(program: &Program, cfg: &Config) -> bool {
    !cfg_constants_supported(program, cfg)
}

/// Iteratively verify that `root_def` is transitively pure through all called
/// definitions, `LET` bindings, operator arguments, and referenced substituted
/// constants, with cycle handling and a bounded work budget.
fn def_is_pure(program: &Program, cfg: &Config, root_def: DefId, budget: &mut usize) -> bool {
    use crate::builtins::Effect;
    let mut visited_defs = BTreeSet::new();
    let mut visited_consts = BTreeSet::new();
    let mut stack: Vec<Expr> = Vec::new();

    let push_def = |did: DefId, visited_defs: &mut BTreeSet<DefId>, stack: &mut Vec<Expr>| -> bool {
        let d = &program.defs[did.idx()];
        if let Some(op) = d.builtin {
            return op.metadata().effect == Effect::Pure;
        }
        if !visited_defs.insert(did) {
            return true;
        }
        match &d.kind {
            DefKind::Op(body) => {
                stack.push(body.clone());
                true
            }
            DefKind::Fn { bounds, body } => {
                for b in bounds {
                    stack.push(b.set.clone());
                }
                stack.push(body.clone());
                true
            }
            DefKind::Pending => false,
        }
    };

    if !push_def(root_def, &mut visited_defs, &mut stack) {
        return false;
    }

    while let Some(e) = stack.pop() {
        if *budget == 0 {
            return false;
        }
        *budget -= 1;
        match &*e.kind {
            ExprKind::Builtin { op, .. } => {
                if op.metadata().effect != Effect::Pure {
                    return false;
                }
            }
            ExprKind::Apply { op, .. } | ExprKind::OpArg(op) => match op {
                OpRef::Builtin(b) => {
                    if b.metadata().effect != Effect::Pure {
                        return false;
                    }
                }
                OpRef::Def(d) => {
                    if !push_def(*d, &mut visited_defs, &mut stack) {
                        return false;
                    }
                }
                OpRef::Const(c) => {
                    let name = &program.consts[c.idx()].name;
                    let Some(target) = cfg.last_constant_subst(name) else {
                        return false;
                    };
                    if visited_consts.insert(*c) {
                        match program.lookup_resolved_root(target) {
                            Some(RootSymbol::Def(d)) => {
                                if !push_def(d, &mut visited_defs, &mut stack) {
                                    return false;
                                }
                            }
                            _ => return false,
                        }
                    }
                }
                OpRef::Param(_) => {}
            },
            ExprKind::Let { defs, .. } => {
                for &d in defs {
                    if !push_def(d, &mut visited_defs, &mut stack) {
                        return false;
                    }
                }
            }
            ExprKind::Const(c) => {
                if program.consts[c.idx()].arity == 0
                    && visited_consts.insert(*c)
                    && cfg.last_constant_subst(&program.consts[c.idx()].name).is_some()
                {
                    match super::resolve_const_subst_target(program, cfg, *c) {
                        Some(super::ConstSubstTarget::PureBuiltin(_, _)) => {}
                        Some(super::ConstSubstTarget::Def(d)) => {
                            if !push_def(d, &mut visited_defs, &mut stack) {
                                return false;
                            }
                        }
                        Some(super::ConstSubstTarget::Const(other)) => {
                            stack.push(Expr::new(ExprKind::Const(other), e.span));
                        }
                        None => return false,
                    }
                }
            }
            _ => {}
        }
        crate::visit::children(&e, &mut |child| stack.push(child.clone()));
    }
    true
}

/// True iff every constant binding in `cfg` is either an unqualified value binding on a
/// non-override constant or an unqualified zero-arity `CONSTANT C <- target` substitution
/// targeting a pure, non-`LET` zero-arity root definition or zero-arity constant.
pub fn cfg_constants_supported(program: &Program, cfg: &Config) -> bool {
    let any_non_let_def =
        |target: &str| program.defs.iter().enumerate().any(|(i, d)| &*d.name == target && !program.def_is_let(DefId(i as u32)));
    let mut purity_budget = MAX_SUBST_WORK;
    cfg.constants.iter().all(|b| match b {
        ConstBinding::Value { name, module, .. } => {
            module.is_none()
                && match program.lookup_resolved_root(name) {
                    Some(RootSymbol::Const(cid)) => program.consts[cid.idx()].arity == 0,
                    Some(RootSymbol::Def(_)) => false,
                    _ => !any_non_let_def(name),
                }
        }
        ConstBinding::Subst { name, op, module } => {
            if module.is_some() {
                return false;
            }
            let valid_lhs = match program.lookup_resolved_root(name) {
                Some(RootSymbol::Const(cid)) => program.consts[cid.idx()].arity == 0,
                _ => false,
            };
            if !valid_lhs {
                return false;
            }
            match super::resolve_const_subst_name(program, op) {
                Some(super::ConstSubstTarget::PureBuiltin(_, _) | super::ConstSubstTarget::Const(_)) => true,
                Some(super::ConstSubstTarget::Def(did)) => def_is_pure(program, cfg, did, &mut purity_budget),
                None => false,
            }
        }
        ConstBinding::OpValue { .. } => false,
    })
}

/// Verify totality of all newly added constrained observations (`init_props`,
/// `constraints`, `action_constraints`, and `action_props`, including primed
/// reads in action predicates) for non-symmetry emitters such as erasure.
pub(crate) fn check_constrained_observations_total(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: super::CheckSpec<'_>,
) -> bool {
    check_observations_total_inner(program, cfg, init, next, spec, false, None)
}

/// Verify totality of constrained observations for state-projection emitters
/// (`phase`, `sequence`, `history`, `ordered`). Permits reading `Len(seq)` and
/// `1..Len(seq)` on unbounded sequences while requiring strict 32-bit safe
/// bounds for all arithmetic (`+`, `-`, `*`, `\div`, `%`, `^`, `Gcd`, unary `-`)
/// and strictly checking indexing, fields, `Head`/`Tail`, `Choose`, and sets.
pub(crate) fn check_projection_observations_total(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: super::CheckSpec<'_>,
) -> bool {
    check_observations_total_inner(program, cfg, init, next, spec, true, None)
}

/// Verify totality of constrained observations for a certified relative-age
/// projection with proven mathematical clock `clock`: permits relative-age
/// deadline comparisons `(stamp + d) cmp clock` while requiring strict 32-bit
/// safe bounds for all other arithmetic.
pub(crate) fn check_age_observations_total(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: super::CheckSpec<'_>,
    clock: VarId,
) -> bool {
    check_observations_total_inner(program, cfg, init, next, spec, true, Some(clock))
}

fn normalize_for_totality<'a>(
    program: &Program,
    cfg: &'a Config,
    init: &Expr,
    next: &Expr,
    spec: super::CheckSpec<'_>,
) -> Option<(Expr, Expr, super::OwnedCheckSpec, BTreeMap<ConstId, ConstInfo<'a>>)> {
    if cfg_overrides_or_tables(program, cfg) {
        return None;
    }
    let mut norm = SymNormalizer::for_equiv_with_config(program, cfg);
    let init_norm = norm.normalize(init)?;
    let next_norm = norm.normalize(next)?;
    let spec_norm = spec.try_map(|e| norm.normalize(e))?;
    let consts = collect_const_info(program, cfg);
    Some((init_norm, next_norm, spec_norm, consts))
}

fn check_observations_total_inner(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: super::CheckSpec<'_>,
    allow_unbounded_seq_len: bool,
    age_clock: Option<VarId>,
) -> bool {
    if !spec.is_constrained() {
        return true;
    }
    let obs_only = super::CheckSpec { invariants: &[], ..spec };
    let Some((init_norm, next_norm, spec_norm, consts)) = normalize_for_totality(program, cfg, init, next, obs_only) else {
        return false;
    };
    let empty_keys = BTreeSet::new();
    let mut checker = TotalityChecker::with_const_info(program, &[], &empty_keys, consts, &init_norm, &next_norm, None);
    checker.allow_unbounded_seq_len = allow_unbounded_seq_len;
    checker.age_clock = age_clock;
    let obs_env = CheckEnv::default();
    for obs in spec_norm.init_props.iter().chain(spec_norm.constraints.iter()) {
        if !checker.check_form_total(obs, false, false, &obs_env) {
            return false;
        }
    }
    for act in spec_norm.action_constraints.iter().chain(spec_norm.action_props.iter()) {
        if !checker.check_form_total(act, true, false, &obs_env) {
            return false;
        }
    }
    true
}

/// Top-level shared totality gate called before `keyed`, `erased`, and `equiv_sym`.
pub(crate) fn check_model_totality_with_spec(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: super::CheckSpec<'_>,
    raw_groups: &[Vec<String>],
    omitted: &[VarId],
) -> bool {
    let Some((groups, all_keys)) = super::equiv_sym::validate_groups(raw_groups) else {
        return false;
    };
    let Some((init_norm, next_norm, spec_norm, consts)) = normalize_for_totality(program, cfg, init, next, spec) else {
        return false;
    };
    let checker = TotalityChecker::with_const_info(program, &groups, &all_keys, consts, &init_norm, &next_norm, None);
    checker.check_all_with_spec(&init_norm, &next_norm, spec_norm.as_spec(), omitted)
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
    spec_norm: super::CheckSpec<'_>,
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
    checker.check_all_with_spec(init_norm, next_norm, spec_norm, &[]).then_some(checker)
}

impl<'a> TotalityChecker<'a> {
    pub(crate) fn with_const_info(
        program: &'a Program,
        groups: &'a [GroupInfo],
        all_keys: &'a BTreeSet<Arc<str>>,
        consts: BTreeMap<ConstId, ConstInfo<'a>>,
        init_norm: &Expr,
        next_norm: &Expr,
        allow_choose_folds: Option<&'a HashMap<LocalId, Option<Expr>>>,
    ) -> Self {
        let mut checker = Self {
            program,
            groups,
            all_keys,
            consts,
            var_shapes: vec![Shape::Bottom; program.vars.len()],
            allow_choose_folds,
            allow_unbounded_seq_len: false,
            age_clock: None,
        };
        checker.var_shapes = checker.infer_var_shapes(init_norm, next_norm);
        checker
    }

    /// Check complete observations, constraints, action predicates, value-position expressions
    /// in `Init`/`Next`, and runtime orbit-canonicalizer comparability of all retained state variables.
    pub(crate) fn check_all_with_spec(&self, init_norm: &Expr, next_norm: &Expr, spec: super::CheckSpec<'_>, omitted: &[VarId]) -> bool {
        // Runtime orbit canonicalization compares `state` with `π(state)` across all
        // retained state variables; every retained variable must therefore be self-comparable
        // and have safe <= i32::MAX set cardinality bounds.
        for (i, shape) in self.var_shapes.iter().enumerate() {
            if !omitted.contains(&VarId(i as u32)) && (!shape_self_comparable(shape) || !shape_has_safe_set_cards(shape, self.groups)) {
                return false;
            }
        }
        let obs_env = CheckEnv::default();
        for obs in spec.all_state_preds() {
            if !self.check_form_total(obs, false, false, &obs_env) {
                return false;
            }
        }
        for act in spec.action_constraints.iter().chain(spec.action_props.iter()) {
            if !self.check_form_total(act, true, false, &obs_env) {
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
            ExprKind::Builtin { op: B::DotDot, args } if args.len() == 2 && matches!(&*args[0].kind, ExprKind::Num(1)) => {
                if let ExprKind::Builtin { op: B::Len, args: la } = &*args[1].kind {
                    if la.len() == 1 && self.is_definitely_seq(&la[0], in_prime, env) {
                        Some((la[0].clone(), in_prime))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
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

#[cfg(test)]
mod tests {
    use super::*;
    use tlx_front::cfg::parse_cfg;

    fn raw_subst_map<'a>(program: &Program, cfg: &'a Config) -> BTreeMap<ConstId, ConstInfo<'a>> {
        collect_raw_const_info(program, cfg)
    }

    #[test]
    fn collect_const_info_caches_deep_dag_and_drops_cycles_and_excess_depth() {
        // 30-level acyclic doubling DAG: D_i == C_{i+1} + C_{i+1} (2^29 uncached paths).
        let levels = 30usize;
        let mut tla = String::from("---- MODULE SubstDag ----\nEXTENDS Naturals\nCONSTANT ");
        tla.push_str(&(0..levels).map(|i| format!("C{i}")).collect::<Vec<_>>().join(", "));
        tla.push_str("\nVARIABLE x\n");
        for i in 0..(levels - 1) {
            tla.push_str(&format!("D{i} == C{} + C{}\n", i + 1, i + 1));
        }
        tla.push_str(&format!("D{} == 1\nInit == x = 0\nNext == x' = x\n====\n", levels - 1));
        let mut cfg_src = String::from("INIT Init\nNEXT Next\nCONSTANTS\n");
        for i in 0..levels {
            cfg_src.push_str(&format!("  C{i} <- D{i}\n"));
        }
        let dir = tlx_testkit::TempDir::with_spec("subst-dag", &tla, &cfg_src);
        let program = Program::load(&dir.join("SubstDag.tla"), &[]).unwrap();
        let cfg = parse_cfg(&cfg_src).unwrap();
        let raw = raw_subst_map(&program, &cfg);
        let mut checker = SubstAcyclicity::new(&program, &raw);
        for id in raw.keys().copied() {
            assert!(checker.is_acyclic(id));
        }
        assert!(checker.work_used() < 300, "memoized 30-level DAG should take O(levels) work, got {}", checker.work_used());
        assert_eq!(collect_const_info(&program, &cfg).len(), levels, "all 30 acyclic levels must be retained");

        // Cyclic substitution `A <- DA`, `DA == B`, `B <- DB`, `DB == A` must be dropped.
        let cyc_tla = "---- MODULE SubstCycle ----\nCONSTANT A, B, Good\nVARIABLE x\nDA == B\nDB == A\nDGood == 1\nInit == x = 0\nNext == x' = x\n====\n";
        let cyc_cfg = "INIT Init\nNEXT Next\nCONSTANTS\n  A <- DA\n  B <- DB\n  Good <- DGood\n";
        let dir = tlx_testkit::TempDir::with_spec("subst-cycle", cyc_tla, cyc_cfg);
        let program = Program::load(&dir.join("SubstCycle.tla"), &[]).unwrap();
        let cfg = parse_cfg(cyc_cfg).unwrap();
        let info = collect_const_info(&program, &cfg);
        assert_eq!(info.len(), 1, "only acyclic Good should remain, got {}", info.len());

        // 35-level chain exceeds MAX_SUBST_DEPTH (32): deepest 31 survive, top 4 are dropped.
        let deep = 35usize;
        let mut deep_tla = String::from("---- MODULE SubstDeep ----\nCONSTANT ");
        deep_tla.push_str(&(0..deep).map(|i| format!("C{i}")).collect::<Vec<_>>().join(", "));
        deep_tla.push_str("\nVARIABLE x\n");
        for i in 0..(deep - 1) {
            deep_tla.push_str(&format!("D{i} == C{}\n", i + 1));
        }
        deep_tla.push_str(&format!("D{} == 1\nInit == x = 0\nNext == x' = x\n====\n", deep - 1));
        let mut deep_cfg = String::from("INIT Init\nNEXT Next\nCONSTANTS\n");
        for i in 0..deep {
            deep_cfg.push_str(&format!("  C{i} <- D{i}\n"));
        }
        let dir = tlx_testkit::TempDir::with_spec("subst-deep", &deep_tla, &deep_cfg);
        let program = Program::load(&dir.join("SubstDeep.tla"), &[]).unwrap();
        let cfg = parse_cfg(&deep_cfg).unwrap();
        assert_eq!(collect_const_info(&program, &cfg).len(), MAX_SUBST_DEPTH - 1);

        // Long 2,000-level acyclic chain: iterative explicit stack uses O(N) work without
        // stack overflow and preserves the valid MAX_SUBST_DEPTH - 1 shorter suffix.
        let long = 2_000usize;
        let mut long_tla = String::from("---- MODULE SubstLong ----\nCONSTANT ");
        long_tla.push_str(&(0..long).map(|i| format!("C{i}")).collect::<Vec<_>>().join(", "));
        long_tla.push_str("\nVARIABLE x\n");
        for i in 0..(long - 1) {
            long_tla.push_str(&format!("D{i} == C{}\n", i + 1));
        }
        long_tla.push_str(&format!("D{} == 1\nInit == x = 0\nNext == x' = x\n====\n", long - 1));
        let mut long_cfg = String::from("INIT Init\nNEXT Next\nCONSTANTS\n");
        for i in 0..long {
            long_cfg.push_str(&format!("  C{i} <- D{i}\n"));
        }
        let dir = tlx_testkit::TempDir::with_spec("subst-long", &long_tla, &long_cfg);
        let program = Program::load(&dir.join("SubstLong.tla"), &[]).unwrap();
        let cfg = parse_cfg(&long_cfg).unwrap();
        let raw = raw_subst_map(&program, &cfg);
        let mut checker = SubstAcyclicity::new(&program, &raw);
        let kept = raw.keys().copied().filter(|&id| checker.is_acyclic(id)).count();
        assert_eq!(kept, MAX_SUBST_DEPTH - 1);
        assert!(checker.work_used() < 12_000, "2000-level chain should use linear work, got {}", checker.work_used());
        assert_eq!(collect_const_info(&program, &cfg).len(), MAX_SUBST_DEPTH - 1);
    }

    #[test]
    fn subst_acyclicity_charges_cached_dep_merges_and_cached_height_edges() {
        // 8 leaf constants L0..L7 and 16 constants A0..A15 whose definitions D0..D15
        // all call `Shared` (`<<L0, ..., L7>>`). After D0 scans `Shared` and caches
        // its 8-element dep set + L0..L7 heights, D1..D15 hit cached `def_const_deps`
        // (charging 8 per merge) and cached `heights` (charging 1 per edge).
        let mut tla = String::from("---- MODULE SubstCacheBudget ----\nCONSTANT ");
        let leaves: Vec<String> = (0..8).map(|i| format!("L{i}")).collect();
        let callers: Vec<String> = (0..16).map(|i| format!("A{i}")).collect();
        tla.push_str(&leaves.iter().chain(&callers).cloned().collect::<Vec<_>>().join(", "));
        tla.push_str("\nVARIABLE x\nShared == <<");
        tla.push_str(&leaves.join(", "));
        tla.push_str(">>\n");
        for i in 0..16 {
            tla.push_str(&format!("D{i} == Shared\n"));
        }
        tla.push_str("Init == x = 0\nNext == x' = x\n====\n");
        let mut cfg_src = String::from("INIT Init\nNEXT Next\nCONSTANTS\n");
        for l in &leaves {
            cfg_src.push_str(&format!("  {l} = 1\n"));
        }
        for i in 0..16 {
            cfg_src.push_str(&format!("  A{i} <- D{i}\n"));
        }
        let dir = tlx_testkit::TempDir::with_spec("subst-cache-budget", &tla, &cfg_src);
        let program = Program::load(&dir.join("SubstCacheBudget.tla"), &[]).unwrap();
        let cfg = parse_cfg(&cfg_src).unwrap();
        let raw = raw_subst_map(&program, &cfg);

        // Budget 45 suffices to validate `A0` (scanning `Shared`, caching its 8 deps, and
        // caching `L0..L7` heights), then exhausts on subsequent cached merges / cached height edges.
        let mut tight = SubstAcyclicity::with_budget(&program, &raw, 45);
        let a0 = ConstId(8);
        assert!(tight.is_acyclic(a0), "A0 should succeed and populate caches");
        let mut accepted = 1usize;
        for idx in 9..24 {
            if tight.is_acyclic(ConstId(idx)) {
                accepted += 1;
            }
        }
        assert!(accepted < 4, "cached dep merges and cached height edges must consume budget (accepted {accepted}/16)");
        assert_eq!(tight.budget, 0);

        // Sharing `D0` directly across `A0..A15` hits both `deps_of_def` cache and `heights` cache:
        // each `A_i` still charges 1 root + 1 cached `deps_of_def` + 8 cached `heights` edges = 10 work.
        let mut shared_cfg = String::from("INIT Init\nNEXT Next\nCONSTANTS\n");
        for l in &leaves {
            shared_cfg.push_str(&format!("  {l} = 1\n"));
        }
        for i in 0..16 {
            shared_cfg.push_str(&format!("  A{i} <- D0\n"));
        }
        let shared_cfg = parse_cfg(&shared_cfg).unwrap();
        let shared_raw = raw_subst_map(&program, &shared_cfg);
        let mut edge_tight = SubstAcyclicity::with_budget(&program, &shared_raw, 60);
        assert!(edge_tight.is_acyclic(a0));
        let shared_accepted = (9..24).filter(|&idx| edge_tight.is_acyclic(ConstId(idx))).count();
        assert!(shared_accepted < 5, "cached height edges on shared D0 must consume budget (accepted {shared_accepted}/15)");
    }
}
