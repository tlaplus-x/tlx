//! Unified HIR normalizer for symmetry lowering and totality analysis.
//!
//! Consolidates the three symmetry normalizer modes under a single engine:
//! - [`SymNormalizer::new`] / [`SymNormalizer::with_config`] (`NormMode::Standard`):
//!   substitutes `@` eagerly in `EXCEPT`, packs multi-arg function/index tuples,
//!   desugars `CASE ... OTHER` to right-nested `IF`, and splits provably-arity-safe
//!   tuple binders (used by `keyed`, `domain`, and public domain queries).
//! - [`SymNormalizer::for_equiv_with_config`] (`NormMode::Equiv`):
//!   preserves `EXCEPT` and `@` intact with lexical scope IDs for sequential
//!   `letBind` lowering, normalizes `SelectSeq` predicate arguments to unary
//!   `LAMBDA`s, and preserves `CASE` and tuple binders (used by `equiv_sym` and
//!   `sym_totality`).
//! - [`SymNormalizer::for_choose_with_config`] (`NormMode::Choose`):
//!   substitutes `@` eagerly in `EXCEPT` and lowers commutative-associative
//!   recursive `CHOOSE` integer set-sum folds to explicit `fold_vars` markers
//!   (used by `choose_sym`).
//!
//! All modes enforce `Enumerator::target` / `Enumerator::unchanged` assignment
//! preservation via [`block_non_target`] and [`block_unchanged_tuple`].

mod folds;
mod helpers;
mod rec;

use std::collections::{BTreeMap, HashMap, HashSet};

use tlx_front::cfg::Config;

use crate::{
    builtins::{Builtin as B, Effect},
    hir::*,
    visit, Program,
};

pub(in crate::optimize::phase) use folds::{classify_ac_op, is_chooses_first_lambda, AcOpKind};
pub(in crate::optimize::phase) use helpers::{
    block_non_target, block_unchanged_tuple, desugar_except_at, exact_tuple_arity, lookup_resolved_root,
};
pub use helpers::{infer_var_domains, proves_var_membership};
pub(in crate::optimize::phase) use rec::RecOpKind;

use helpers::{expr_contains_at, expr_syntactically_eq, is_infallible_path, paths_disjoint};

#[derive(Clone, Copy, PartialEq, Eq)]
enum NormMode {
    Standard,
    Equiv,
    Choose,
}

#[derive(Clone)]
pub(super) enum OpBinding {
    Ref(OpRef),
    Lambda { params: Vec<LocalId>, body: Expr, env: EnvMap, op_env: HashMap<LocalId, OpBinding>, lex_at: Option<usize> },
}

pub(super) type EnvMap = HashMap<LocalId, (Expr, Option<usize>)>;

/// Bounded, semantics-preserving HIR normalizer shared across `keyed`,
/// `equiv_sym`, `choose_sym`, `domain`, and `sym_totality`.
pub struct SymNormalizer<'a> {
    pub(super) program: &'a Program,
    cfg: Option<&'a Config>,
    mode: NormMode,
    pub(super) stack: Vec<DefId>,
    const_stack: Vec<ConstId>,
    expanded_substs: BTreeMap<ConstId, String>,
    /// `.cfg` definition overrides the runtime applies; `None` when the
    /// configuration has an override this analysis cannot certify, in which
    /// case lowering an operator definition fails closed.
    redirect: Option<super::CfgRedirects>,
    /// Definition and parameterized-constant overrides actually lowered, with
    /// the argument tuple each use site applied.
    expanded_overrides: Vec<super::AppliedOverride>,
    override_keys: HashSet<(String, Vec<String>)>,
    model_hirs: Vec<String>,
    saw_override: bool,
    remaining: usize,
    pub(crate) local: u32,
    at_stack: Vec<(Expr, bool)>,
    next_except_id: usize,
    pub(super) let_at: HashMap<DefId, Option<usize>>,
    pub(super) let_vals: HashMap<DefId, Expr>,
    in_enabled: bool,
    /// Synthetic bound `LocalId`s of lowered recursive `CHOOSE` sum folds
    /// (`NormMode::Choose`), mapped to optional domain supersets from `[S \in SUBSET D]`.
    pub(crate) fold_vars: HashMap<LocalId, Option<Expr>>,
    /// Recognized bounded finite `RECURSIVE` operators normalized in `NormMode::Equiv`.
    pub(in crate::optimize::phase) rec_ops: HashMap<DefId, RecOpKind>,
}

impl<'a> SymNormalizer<'a> {
    pub fn new(program: &'a Program) -> Self {
        Self::with_mode(program, None, NormMode::Standard)
    }

    /// Create a normalizer that also resolves `CONSTANT C <- Def` substitutions
    /// from `cfg` when `Def` is a root definition with no module qualifier.
    pub fn with_config(program: &'a Program, cfg: &'a Config) -> Self {
        Self::with_mode(program, Some(cfg), NormMode::Standard)
    }

    /// Create a normalizer in `equiv_sym` / `sym_totality` mode with `CONSTANT C <- Def` expansion.
    pub(in crate::optimize::phase) fn for_equiv_with_config(program: &'a Program, cfg: &'a Config) -> Self {
        Self::with_mode(program, Some(cfg), NormMode::Equiv)
    }

    /// Create a normalizer in `choose_sym` mode (substituting `@` in `EXCEPT`
    /// and recognizing recursive `CHOOSE` integer set-sum folds).
    pub(in crate::optimize::phase) fn for_choose_with_config(program: &'a Program, cfg: &'a Config) -> Self {
        Self::with_mode(program, Some(cfg), NormMode::Choose)
    }

    fn with_mode(program: &'a Program, cfg: Option<&'a Config>, mode: NormMode) -> Self {
        let remaining = if mode == NormMode::Equiv { 150_000 } else { 100_000 };
        Self {
            program,
            cfg,
            mode,
            stack: Vec::new(),
            const_stack: Vec::new(),
            expanded_substs: BTreeMap::new(),
            redirect: cfg.and_then(|cfg| super::cfg_def_redirects(program, cfg)),
            expanded_overrides: Vec::new(),
            override_keys: HashSet::new(),
            model_hirs: Vec::new(),
            saw_override: false,
            remaining,
            local: program.locals.len() as u32,
            at_stack: Vec::new(),
            next_except_id: 0,
            let_at: HashMap::new(),
            let_vals: HashMap::new(),
            in_enabled: false,
            fold_vars: HashMap::new(),
            rec_ops: HashMap::new(),
        }
    }

    /// Normalize a root expression. Returns `None` on unsupported constructs or
    /// budget/depth exhaustion.
    pub fn normalize(&mut self, e: &Expr) -> Option<Expr> {
        let result = self.expand(e, &HashMap::new(), &HashMap::new(), None, None, 0)?;
        if self.saw_override {
            self.model_hirs.push(super::syntactic_expr_repr(self.program, &result)?);
        }
        Some(result)
    }

    pub(in crate::optimize::phase) fn attach_const_subst(&self, cert: super::OpenCert) -> Option<String> {
        let cfg = self.cfg?;
        super::attach_const_subst_obligation(
            self.program,
            cfg,
            &self.expanded_substs,
            &super::OverrideObligations { applied: &self.expanded_overrides, model_hirs: &self.model_hirs },
            |cid| self.expand_declared_const_subst(cid),
            |name, args| self.expand_declared_override(name, args),
            cert,
        )
    }

    /// Re-derive an applied `.cfg` override from the configuration alone, for
    /// the certificate's binding obligation.
    fn expand_declared_override(&self, name: &str, args: &[Expr]) -> Option<String> {
        let cfg = self.cfg?;
        let target = cfg.last_constant_subst(name)?;
        let super::ConstSubstTarget::Def(target) = super::resolve_override_name(self.program, target)? else { return None };
        let mut fresh = Self::with_mode(self.program, self.cfg, self.mode);
        let span = self.program.defs[target.idx()].span;
        let expanded = fresh.apply_def(target, args, &HashMap::new(), &HashMap::new(), None, None, span, 1)?;
        super::canonical_expr_repr(self.program, &expanded)
    }

    fn builtin_override(&self, op: B) -> Option<(DefId, DefId)> {
        self.redirect.as_ref()?.builtins.get(&op).copied()
    }

    /// Record one applied override use site, deduplicated by the replaced name
    /// and canonical argument tuple.
    fn record_override(&mut self, name: String, target: String, args: &[Expr], result: &Expr) -> Option<()> {
        let key = (name.clone(), args.iter().map(|a| super::canonical_expr_repr(self.program, a)).collect::<Option<Vec<_>>>()?);
        if self.override_keys.insert(key) {
            let applied = super::canonical_expr_repr(self.program, result)?;
            let applied_syntax = super::syntactic_expr_repr(self.program, result)?;
            self.expanded_overrides.push(super::AppliedOverride { name, target, args: args.to_vec(), applied, applied_syntax });
        }
        self.saw_override = true;
        Some(())
    }

    pub(in crate::optimize::phase) fn expand_declared_const_subst(&self, c: ConstId) -> Option<String> {
        let cfg = self.cfg?;
        let (seen, terminal) = super::resolve_const_subst_chain(self.program, cfg, c)?;
        let resolved = match terminal {
            super::ConstSubstTarget::PureBuiltin(op, span) => {
                let mut fresh = Self::with_mode(self.program, self.cfg, self.mode);
                fresh.expand_apply(OpRef::Builtin(op), &[], &HashMap::new(), &HashMap::new(), None, None, span, 1)?
            }
            super::ConstSubstTarget::Const(other) => Expr::new(ExprKind::Const(other), Span::default()),
            super::ConstSubstTarget::Def(id) => {
                let d = &self.program.defs[id.idx()];
                let mut fresh = Self::with_mode(self.program, self.cfg, self.mode);
                fresh.const_stack.extend_from_slice(&seen);
                fresh.apply_def(id, &[], &HashMap::new(), &HashMap::new(), None, None, d.span, 1).map(block_non_target)?
            }
        };
        super::canonical_expr_repr(self.program, &resolved)
    }

    fn record_const_subst(&mut self, c: ConstId, res: &Expr) -> bool {
        let Some(repr) = super::canonical_expr_repr(self.program, res) else {
            return false;
        };
        match self.expanded_substs.get(&c) {
            Some(prev) => prev == &repr,
            None => {
                self.expanded_substs.insert(c, repr);
                true
            }
        }
    }

    pub(super) fn alloc_local(&mut self) -> LocalId {
        let id = LocalId(self.local);
        self.local += 1;
        id
    }

    fn bind(&mut self, vars: &BoundVars, env: &mut EnvMap, cur_except: Option<usize>, span: Span) -> BoundVars {
        let ids = vars
            .locals()
            .iter()
            .map(|old| {
                let id = self.alloc_local();
                env.insert(*old, (Expr::new(ExprKind::Local(id), span), cur_except));
                id
            })
            .collect();
        match vars {
            BoundVars::Many(_) => BoundVars::Many(ids),
            BoundVars::Tuple(_) => BoundVars::Tuple(ids),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn expand_bounds(
        &mut self,
        bounds: &[Bound],
        env: &mut EnvMap,
        op_env: &HashMap<LocalId, OpBinding>,
        allow_split_times: bool,
        cur_except: Option<usize>,
        lex_at: Option<usize>,
        depth: usize,
    ) -> Option<Vec<Bound>> {
        let mut out = Vec::with_capacity(bounds.len());
        for b in bounds {
            let set = self.expand(&b.set, env, op_env, cur_except, lex_at, depth)?;
            if self.mode != NormMode::Standard {
                let vars = self.bind(&b.vars, env, cur_except, b.set.span);
                out.push(Bound { vars, set });
                continue;
            }
            match &b.vars {
                BoundVars::Many(_) => {
                    let vars = self.bind(&b.vars, env, cur_except, b.set.span);
                    out.push(Bound { vars, set });
                }
                BoundVars::Tuple(ids) => {
                    if allow_split_times {
                        if let ExprKind::Builtin { op: B::Times, args } = &*set.kind {
                            if args.len() == ids.len() && ids.len() >= 2 {
                                for (old, part) in ids.iter().zip(args.iter()) {
                                    let fresh = self.alloc_local();
                                    env.insert(*old, (Expr::new(ExprKind::Local(fresh), part.span), cur_except));
                                    out.push(Bound { vars: BoundVars::Many(vec![fresh]), set: part.clone() });
                                }
                                continue;
                            }
                        }
                    }
                    if exact_tuple_arity(&set) == Some(ids.len()) {
                        let tuple_id = self.alloc_local();
                        let tuple_expr = Expr::new(ExprKind::Local(tuple_id), b.set.span);
                        for (idx, old) in ids.iter().enumerate() {
                            let proj = Expr::new(
                                ExprKind::FnApp {
                                    func: tuple_expr.clone(),
                                    args: vec![Expr::new(ExprKind::Num((idx + 1) as i128), b.set.span)],
                                },
                                b.set.span,
                            );
                            env.insert(*old, (proj, cur_except));
                        }
                        out.push(Bound { vars: BoundVars::Many(vec![tuple_id]), set });
                    } else {
                        let vars = self.bind(&b.vars, env, cur_except, b.set.span);
                        out.push(Bound { vars, set });
                    }
                }
            }
        }
        Some(out)
    }

    pub(super) fn eval_op_arg(
        &self,
        arg: &Expr,
        env: &EnvMap,
        op_env: &HashMap<LocalId, OpBinding>,
        lex_at: Option<usize>,
    ) -> Option<OpBinding> {
        match &*arg.kind {
            ExprKind::Lambda { params, body } => {
                Some(OpBinding::Lambda { params: params.clone(), body: body.clone(), env: env.clone(), op_env: op_env.clone(), lex_at })
            }
            ExprKind::OpArg(OpRef::Param(p)) => op_env.get(p).cloned(),
            ExprKind::OpArg(OpRef::Const(_)) if self.cfg.is_none() => None,
            ExprKind::OpArg(op_ref) => Some(OpBinding::Ref(*op_ref)),
            _ => None,
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn bind_call_args(
        &mut self,
        params: &[LocalId],
        raw_args: &[Expr],
        caller_env: &EnvMap,
        caller_op_env: &HashMap<LocalId, OpBinding>,
        callee_env: &mut EnvMap,
        callee_op_env: &mut HashMap<LocalId, OpBinding>,
        cur_except: Option<usize>,
        lex_at: Option<usize>,
        depth: usize,
    ) -> Option<()> {
        if params.len() != raw_args.len() {
            return None;
        }
        for (&param, raw) in params.iter().zip(raw_args.iter()) {
            if self.program.locals[param.idx()].arity > 0 {
                let bound = self.eval_op_arg(raw, caller_env, caller_op_env, lex_at)?;
                callee_op_env.insert(param, bound);
            } else {
                let val = self.expand(raw, caller_env, caller_op_env, cur_except, lex_at, depth + 1)?;
                callee_env.insert(param, (val, cur_except));
            }
        }
        Some(())
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn expand(
        &mut self,
        e: &Expr,
        env: &EnvMap,
        op_env: &HashMap<LocalId, OpBinding>,
        cur_except: Option<usize>,
        lex_at: Option<usize>,
        depth: usize,
    ) -> Option<Expr> {
        if depth >= 128 || self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        let kind = match &*e.kind {
            ExprKind::Local(l) => {
                if let Some((subst, bound_except)) = env.get(l) {
                    if self.mode == NormMode::Equiv && cur_except != *bound_except && expr_contains_at(subst) {
                        return None;
                    }
                    return Some(subst.clone());
                }
                return Some(e.clone());
            }
            ExprKind::Const(c) => {
                if let Some(cfg) = self.cfg {
                    if self.program.consts[c.idx()].arity == 0 && cfg.last_constant_subst(&self.program.consts[c.idx()].name).is_some() {
                        if self.const_stack.contains(c) {
                            return None;
                        }
                        let res = match super::resolve_const_subst_target(self.program, cfg, *c)? {
                            super::ConstSubstTarget::PureBuiltin(op, span) => {
                                // A substituted builtin may itself be replaced by a
                                // definition override (`C <- Nat`, `Nat <- ...`).
                                self.expand_apply(OpRef::Builtin(op), &[], env, op_env, cur_except, lex_at, span, depth + 1)?
                            }
                            super::ConstSubstTarget::Def(def_id) => {
                                self.const_stack.push(*c);
                                let res =
                                    self.apply_def(def_id, &[], env, op_env, cur_except, lex_at, e.span, depth + 1).map(block_non_target);
                                self.const_stack.pop();
                                res?
                            }
                            super::ConstSubstTarget::Const(other) => {
                                self.const_stack.push(*c);
                                let res =
                                    self.expand(&Expr::new(ExprKind::Const(other), e.span), env, op_env, cur_except, lex_at, depth + 1);
                                self.const_stack.pop();
                                res?
                            }
                        };
                        return self.record_const_subst(*c, &res).then_some(res);
                    }
                }
                ExprKind::Const(*c)
            }
            ExprKind::InstVar { subst, .. } => {
                if self.mode != NormMode::Standard || self.in_enabled {
                    return None;
                }
                return self.expand(subst, env, op_env, cur_except, lex_at, depth + 1).map(block_non_target);
            }
            ExprKind::At => {
                if self.mode == NormMode::Equiv {
                    if cur_except.is_none() || cur_except != lex_at {
                        return None;
                    }
                    ExprKind::At
                } else {
                    let idx = lex_at?;
                    let (expr, used) = self.at_stack.get_mut(idx)?;
                    *used = true;
                    return Some(expr.clone());
                }
            }
            ExprKind::Let { defs, body } => {
                let prev: Vec<_> = defs.iter().map(|&d| (d, self.let_at.insert(d, lex_at))).collect();
                let res = self.expand(body, env, op_env, cur_except, lex_at, depth + 1);
                for (d, old) in prev {
                    match old {
                        Some(v) => {
                            self.let_at.insert(d, v);
                        }
                        None => {
                            self.let_at.remove(&d);
                        }
                    }
                }
                return res.map(block_unchanged_tuple);
            }
            ExprKind::Apply { op, args } => {
                return self.expand_apply(*op, args, env, op_env, cur_except, lex_at, e.span, depth + 1);
            }
            ExprKind::Builtin { op, args } if self.builtin_override(*op).is_some() => {
                let expanded: Vec<_> =
                    args.iter().map(|a| self.expand(a, env, op_env, cur_except, lex_at, depth + 1)).collect::<Option<_>>()?;
                let (lhs, target) = self.builtin_override(*op)?;
                let result = self.apply_def(target, &expanded, env, op_env, cur_except, lex_at, e.span, depth + 1)?;
                let name = self.program.defs[lhs.idx()].name.to_string();
                let target_name = self.program.defs[target.idx()].name.to_string();
                self.record_override(name, target_name, &expanded, &result)?;
                return Some(result);
            }
            ExprKind::Builtin { op, args } if self.mode == NormMode::Equiv => {
                return self.apply_builtin(*op, args, env, op_env, cur_except, lex_at, e.span, depth);
            }
            ExprKind::Builtin { op: B::Enabled, args } => {
                let prev = self.in_enabled;
                self.in_enabled = true;
                let expanded = args.iter().map(|a| self.expand(a, env, op_env, cur_except, lex_at, depth + 1)).collect::<Option<Vec<_>>>();
                self.in_enabled = prev;
                ExprKind::Builtin { op: B::Enabled, args: expanded? }
            }
            ExprKind::OpArg(_) | ExprKind::Lambda { .. } | ExprKind::QuantUnbounded { .. } | ExprKind::TemporalQuant { .. } => {
                return None;
            }
            ExprKind::Quant { kind, bounds, body } => {
                let mut scope = env.clone();
                let bounds = self.expand_bounds(bounds, &mut scope, op_env, true, cur_except, lex_at, depth + 1)?;
                ExprKind::Quant { kind: *kind, bounds, body: self.expand(body, &scope, op_env, cur_except, lex_at, depth + 1)? }
            }
            ExprKind::FnConstruct { bounds, body } => {
                let mut scope = env.clone();
                let allow_split_times = bounds.len() == 1;
                let bounds = self.expand_bounds(bounds, &mut scope, op_env, allow_split_times, cur_except, lex_at, depth + 1)?;
                ExprKind::FnConstruct { bounds, body: self.expand(body, &scope, op_env, cur_except, lex_at, depth + 1)? }
            }
            ExprKind::SetMap { expr, bounds } => {
                let mut scope = env.clone();
                let bounds = self.expand_bounds(bounds, &mut scope, op_env, true, cur_except, lex_at, depth + 1)?;
                ExprKind::SetMap { expr: self.expand(expr, &scope, op_env, cur_except, lex_at, depth + 1)?, bounds }
            }
            ExprKind::SetFilter { bound, pred } => {
                let mut scope = env.clone();
                let mut bounds =
                    self.expand_bounds(std::slice::from_ref(bound), &mut scope, op_env, false, cur_except, lex_at, depth + 1)?;
                ExprKind::SetFilter { bound: bounds.remove(0), pred: self.expand(pred, &scope, op_env, cur_except, lex_at, depth + 1)? }
            }
            ExprKind::Choose { vars, set, body } => {
                let set = match set {
                    Some(s) => Some(self.expand(s, env, op_env, cur_except, lex_at, depth + 1)?),
                    None => None,
                };
                let mut scope = env.clone();
                let vars = match (self.mode, vars, set.as_ref()) {
                    (NormMode::Standard, BoundVars::Tuple(ids), Some(s)) if exact_tuple_arity(s) == Some(ids.len()) => {
                        let tuple_id = self.alloc_local();
                        let tuple_expr = Expr::new(ExprKind::Local(tuple_id), e.span);
                        for (idx, old) in ids.iter().enumerate() {
                            let proj = Expr::new(
                                ExprKind::FnApp {
                                    func: tuple_expr.clone(),
                                    args: vec![Expr::new(ExprKind::Num((idx + 1) as i128), e.span)],
                                },
                                e.span,
                            );
                            scope.insert(*old, (proj, cur_except));
                        }
                        BoundVars::Many(vec![tuple_id])
                    }
                    _ => self.bind(vars, &mut scope, cur_except, e.span),
                };
                ExprKind::Choose { vars, set, body: self.expand(body, &scope, op_env, cur_except, lex_at, depth + 1)? }
            }
            ExprKind::Case { arms, other } if self.mode == NormMode::Standard => {
                let expanded_arms: Vec<(Expr, Expr)> = arms
                    .iter()
                    .map(|(g, v)| {
                        Some((
                            self.expand(g, env, op_env, cur_except, lex_at, depth + 1)?,
                            self.expand(v, env, op_env, cur_except, lex_at, depth + 1)?,
                        ))
                    })
                    .collect::<Option<_>>()?;
                let expanded_other = match other {
                    Some(o) => Some(self.expand(o, env, op_env, cur_except, lex_at, depth + 1)?),
                    None => None,
                };
                if let Some(mut acc) = expanded_other {
                    for (cond, then) in expanded_arms.into_iter().rev() {
                        let span = cond.span;
                        acc = Expr::new(ExprKind::If { cond, then, els: acc }, span);
                    }
                    return Some(acc);
                }
                ExprKind::Case { arms: expanded_arms, other: None }
            }
            ExprKind::FnApp { func, args } => {
                if matches!(self.mode, NormMode::Choose | NormMode::Equiv) {
                    if let [target_raw] = args.as_slice() {
                        if let ExprKind::Apply { op: OpRef::Def(sum_id), args: fargs } = &*func.kind {
                            if fargs.is_empty() {
                                // A `.cfg` override replaces this definition; the
                                // fold recognizer only knows the shadowed body, so
                                // let the call flow through `apply_def`, which
                                // applies and records the configured replacement.
                                let overridden = self.redirect.as_ref().is_some_and(|r| r.defs.contains_key(sum_id));
                                if !overridden {
                                    if let Some(folded) =
                                        self.try_expand_fn_fold(*sum_id, target_raw, env, op_env, cur_except, lex_at, e.span, depth)
                                    {
                                        return folded;
                                    }
                                }
                            }
                        }
                    }
                }
                let func = self.expand(func, env, op_env, cur_except, lex_at, depth + 1)?;
                let mut args: Vec<_> =
                    args.iter().map(|a| self.expand(a, env, op_env, cur_except, lex_at, depth + 1)).collect::<Option<_>>()?;
                if self.mode == NormMode::Standard && args.len() > 1 {
                    args = vec![Expr::new(ExprKind::Tuple(args), e.span)];
                }
                ExprKind::FnApp { func, args }
            }
            ExprKind::Except { base, updates } => {
                return self.expand_except(base, updates, env, op_env, cur_except, lex_at, e.span, depth);
            }
            _ => {
                let mut out = Expr::new((*e.kind).clone(), e.span);
                let mut valid = true;
                visit::children_mut(&mut out, &mut |c| match self.expand(c, env, op_env, cur_except, lex_at, depth + 1) {
                    Some(x) => *c = x,
                    None => valid = false,
                });
                if !valid {
                    return None;
                }
                (*out.kind).clone()
            }
        };
        if matches!(&kind, ExprKind::Builtin { op, .. } if op.metadata().effect != Effect::Pure) {
            return None;
        }
        Some(Expr::new(kind, e.span))
    }

    #[allow(clippy::too_many_arguments)]
    fn expand_except(
        &mut self,
        base: &Expr,
        updates: &[(Vec<ExceptKey>, Expr)],
        env: &EnvMap,
        op_env: &HashMap<LocalId, OpBinding>,
        cur_except: Option<usize>,
        lex_at: Option<usize>,
        span: Span,
        depth: usize,
    ) -> Option<Expr> {
        let base = self.expand(base, env, op_env, cur_except, lex_at, depth + 1)?;
        if self.mode == NormMode::Equiv {
            let mut out_updates = Vec::with_capacity(updates.len());
            for (path, rhs) in updates {
                let mut out_path = Vec::with_capacity(path.len());
                for key in path {
                    match key {
                        ExceptKey::Field(f) => out_path.push(ExceptKey::Field(f.clone())),
                        ExceptKey::Index(args) => {
                            let args = args
                                .iter()
                                .map(|a| self.expand(a, env, op_env, cur_except, lex_at, depth + 1))
                                .collect::<Option<Vec<_>>>()?;
                            out_path.push(ExceptKey::Index(args));
                        }
                    }
                }
                let eid = Some(self.next_except_id);
                self.next_except_id += 1;
                let rhs = self.expand(rhs, env, op_env, eid, eid, depth + 1)?;
                out_updates.push((out_path, rhs));
            }
            return Some(Expr::new(ExprKind::Except { base, updates: out_updates }, span));
        }

        let mut expanded: Vec<(Vec<ExceptKey>, Expr)> = Vec::new();
        for (path, rhs) in updates {
            let mut old = base.clone();
            let mut keys = Vec::with_capacity(path.len());
            for key in path {
                let key = match key {
                    ExceptKey::Field(field) => ExceptKey::Field(field.clone()),
                    ExceptKey::Index(args) => {
                        let mut ex: Vec<_> =
                            args.iter().map(|a| self.expand(a, env, op_env, cur_except, lex_at, depth + 1)).collect::<Option<_>>()?;
                        if self.mode == NormMode::Standard && ex.len() > 1 {
                            ex = vec![Expr::new(ExprKind::Tuple(ex), span)];
                        }
                        ExceptKey::Index(ex)
                    }
                };
                old = Expr::new(
                    match &key {
                        ExceptKey::Field(field) => ExprKind::Field { record: old, field: field.clone() },
                        ExceptKey::Index(args) => ExprKind::FnApp { func: old, args: args.clone() },
                    },
                    span,
                );
                keys.push(key);
            }
            let at_idx = self.at_stack.len();
            self.at_stack.push((old.clone(), false));
            let rhs_res = self.expand(rhs, env, op_env, cur_except, Some(at_idx), depth + 1);
            let (_, at_used) = self.at_stack.pop().unwrap();
            let rhs = rhs_res?;
            if at_used && expanded.iter().any(|(prior, _)| !paths_disjoint(prior, &keys)) {
                return None;
            }
            if self.mode == NormMode::Standard {
                if let ExprKind::Except { base: inner_base, updates: inner_updates } = &*rhs.kind {
                    if !inner_updates.is_empty()
                        && expr_syntactically_eq(inner_base, &old)
                        && expanded.iter().all(|(prior, _)| paths_disjoint(prior, &keys))
                        && inner_updates.iter().all(|(ip, _)| is_infallible_path(ip))
                    {
                        for (ip, iv) in inner_updates {
                            let mut full_path = keys.clone();
                            full_path.extend(ip.iter().cloned());
                            expanded.push((full_path, iv.clone()));
                        }
                        continue;
                    }
                }
            }
            expanded.push((keys, rhs));
        }
        Some(Expr::new(ExprKind::Except { base, updates: expanded }, span))
    }

    #[allow(clippy::too_many_arguments)]
    fn expand_apply(
        &mut self,
        op: OpRef,
        args: &[Expr],
        env: &EnvMap,
        op_env: &HashMap<LocalId, OpBinding>,
        cur_except: Option<usize>,
        lex_at: Option<usize>,
        span: Span,
        depth: usize,
    ) -> Option<Expr> {
        match op {
            OpRef::Builtin(b) => {
                if let Some((lhs, target)) = self.builtin_override(b) {
                    let expanded_args =
                        args.iter().map(|a| self.expand(a, env, op_env, cur_except, lex_at, depth + 1)).collect::<Option<Vec<_>>>()?;
                    let result = self.apply_def(target, args, env, op_env, cur_except, lex_at, span, depth)?;
                    let name = self.program.defs[lhs.idx()].name.to_string();
                    let target_name = self.program.defs[target.idx()].name.to_string();
                    self.record_override(name, target_name, &expanded_args, &result)?;
                    return Some(result);
                }
                self.apply_builtin(b, args, env, op_env, cur_except, lex_at, span, depth)
            }
            OpRef::Def(id) => self.apply_def(id, args, env, op_env, cur_except, lex_at, span, depth),
            OpRef::Const(c) => {
                let arity = self.program.consts[c.idx()].arity;
                let name = self.program.consts[c.idx()].name.to_string();
                let target_name = self.cfg?.last_constant_subst(&name)?.to_string();
                let super::ConstSubstTarget::Def(def_id) = super::resolve_override_name(self.program, &target_name)? else {
                    return None;
                };
                if self.program.defs[def_id.idx()].params.len() != arity {
                    return None;
                }
                let expanded_args =
                    args.iter().map(|a| self.expand(a, env, op_env, cur_except, lex_at, depth + 1)).collect::<Option<Vec<_>>>()?;
                let result = self.apply_def(def_id, args, env, op_env, cur_except, lex_at, span, depth).map(block_non_target)?;
                let target_name = self.program.defs[def_id.idx()].name.to_string();
                self.record_override(name, target_name, &expanded_args, &result)?;
                Some(result)
            }
            OpRef::Param(p) => match op_env.get(&p)?.clone() {
                OpBinding::Ref(inner) => self.expand_apply(inner, args, env, op_env, cur_except, lex_at, span, depth).map(block_non_target),
                OpBinding::Lambda { params, body, env: mut cap_env, op_env: mut cap_op_env, lex_at: lam_at } => {
                    self.bind_call_args(&params, args, env, op_env, &mut cap_env, &mut cap_op_env, cur_except, lex_at, depth)?;
                    self.expand(&body, &cap_env, &cap_op_env, cur_except, lam_at, depth + 1).map(block_non_target)
                }
            },
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn apply_builtin(
        &mut self,
        op: B,
        args: &[Expr],
        env: &EnvMap,
        op_env: &HashMap<LocalId, OpBinding>,
        cur_except: Option<usize>,
        lex_at: Option<usize>,
        span: Span,
        depth: usize,
    ) -> Option<Expr> {
        if op.metadata().effect != Effect::Pure {
            return None;
        }
        if self.mode == NormMode::Equiv {
            match (op, args) {
                (B::SelectSeq, [seq, pred]) => {
                    let seq = self.expand(seq, env, op_env, cur_except, lex_at, depth + 1)?;
                    let pred_lam = self.expand_op_arg_arity(pred, 1, true, env, op_env, cur_except, lex_at, span, depth + 1)?;
                    return Some(Expr::new(ExprKind::Builtin { op, args: vec![seq, pred_lam] }, span));
                }
                (B::BagOfAll, [f_arg, bag]) => {
                    let f_lam = self.expand_op_arg_arity(f_arg, 1, true, env, op_env, cur_except, lex_at, span, depth + 1)?;
                    let bag = self.expand(bag, env, op_env, cur_except, lex_at, depth + 1)?;
                    return Some(Expr::new(ExprKind::Builtin { op, args: vec![f_lam, bag] }, span));
                }
                (B::FoldSet | B::FoldFunction | B::FoldSeq | B::FoldLeft | B::FoldLeftDomain | B::FoldBag, [op_arg, base, coll]) => {
                    let op_lam = self.expand_op_arg_arity(op_arg, 2, true, env, op_env, cur_except, lex_at, span, depth + 1)?;
                    let base = self.expand(base, env, op_env, cur_except, lex_at, depth + 1)?;
                    let coll = self.expand(coll, env, op_env, cur_except, lex_at, depth + 1)?;
                    return Some(Expr::new(ExprKind::Builtin { op, args: vec![op_lam, base, coll] }, span));
                }
                (B::FoldRight | B::FoldRightDomain, [op_arg, seq, base]) => {
                    let op_lam = self.expand_op_arg_arity(op_arg, 2, true, env, op_env, cur_except, lex_at, span, depth + 1)?;
                    let seq = self.expand(seq, env, op_env, cur_except, lex_at, depth + 1)?;
                    let base = self.expand(base, env, op_env, cur_except, lex_at, depth + 1)?;
                    return Some(Expr::new(ExprKind::Builtin { op, args: vec![op_lam, seq, base] }, span));
                }
                (B::FoldFunctionOnSet, [op_arg, base, fun, indices]) => {
                    let op_lam = self.expand_op_arg_arity(op_arg, 2, true, env, op_env, cur_except, lex_at, span, depth + 1)?;
                    let base = self.expand(base, env, op_env, cur_except, lex_at, depth + 1)?;
                    let fun = self.expand(fun, env, op_env, cur_except, lex_at, depth + 1)?;
                    let indices = self.expand(indices, env, op_env, cur_except, lex_at, depth + 1)?;
                    return Some(Expr::new(ExprKind::Builtin { op, args: vec![op_lam, base, fun, indices] }, span));
                }
                (B::MapThenFoldSet, [op_arg, base, f_arg, choose_arg, set]) => {
                    let op_lam = self.expand_op_arg_arity(op_arg, 2, false, env, op_env, cur_except, lex_at, span, depth + 1)?;
                    let base = self.expand(base, env, op_env, cur_except, lex_at, depth + 1)?;
                    let f_lam = self.expand_op_arg_arity(f_arg, 1, false, env, op_env, cur_except, lex_at, span, depth + 1)?;
                    let choose_lam = self.expand_op_arg_arity(choose_arg, 1, false, env, op_env, cur_except, lex_at, span, depth + 1)?;
                    let set = self.expand(set, env, op_env, cur_except, lex_at, depth + 1)?;
                    return Some(Expr::new(ExprKind::Builtin { op, args: vec![op_lam, base, f_lam, choose_lam, set] }, span));
                }
                _ => {}
            }
        }
        let prev = self.in_enabled;
        if op == B::Enabled {
            self.in_enabled = true;
        }
        let expanded: Option<Vec<_>> = args.iter().map(|a| self.expand(a, env, op_env, cur_except, lex_at, depth + 1)).collect();
        self.in_enabled = prev;
        Some(Expr::new(ExprKind::Builtin { op, args: expanded? }, span))
    }

    #[allow(clippy::too_many_arguments)]
    fn expand_op_arg_arity(
        &mut self,
        e: &Expr,
        arity: usize,
        reject_native_lit: bool,
        env: &EnvMap,
        op_env: &HashMap<LocalId, OpBinding>,
        cur_except: Option<usize>,
        lex_at: Option<usize>,
        span: Span,
        depth: usize,
    ) -> Option<Expr> {
        let ov = self.eval_op_arg(e, env, op_env, lex_at)?;
        let is_lit = |b: &Expr| matches!(&*b.kind, ExprKind::Num(_) | ExprKind::Str(_));
        match ov {
            OpBinding::Lambda { params, body, env: mut cap_env, op_env: cap_op_env, lex_at: lam_at } if params.len() == arity => {
                if reject_native_lit && is_lit(&body) {
                    return None;
                }
                let mut fresh = Vec::with_capacity(arity);
                for &p in &params {
                    if self.program.locals[p.idx()].arity != 0 {
                        return None;
                    }
                    let id = self.alloc_local();
                    cap_env.insert(p, (Expr::new(ExprKind::Local(id), span), cur_except));
                    fresh.push(id);
                }
                let body = self.expand(&body, &cap_env, &cap_op_env, cur_except, lam_at, depth + 1)?;
                Some(Expr::new(ExprKind::Lambda { params: fresh, body }, span))
            }
            OpBinding::Ref(op) => {
                if reject_native_lit {
                    if let OpRef::Def(d) = op {
                        let def = &self.program.defs[d.idx()];
                        if def.builtin.is_none() {
                            if let DefKind::Op(raw_body) = &def.kind {
                                if is_lit(raw_body) {
                                    return None;
                                }
                            }
                        }
                    }
                }
                let fresh: Vec<LocalId> = (0..arity).map(|_| self.alloc_local()).collect();
                let args: Vec<Expr> = fresh.iter().map(|&id| Expr::new(ExprKind::Local(id), span)).collect();
                let body = self.expand_apply(op, &args, env, op_env, cur_except, lex_at, span, depth + 1)?;
                Some(Expr::new(ExprKind::Lambda { params: fresh, body }, span))
            }
            _ => None,
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn apply_def(
        &mut self,
        id: DefId,
        args: &[Expr],
        env: &EnvMap,
        op_env: &HashMap<LocalId, OpBinding>,
        cur_except: Option<usize>,
        lex_at: Option<usize>,
        span: Span,
        depth: usize,
    ) -> Option<Expr> {
        if self.cfg.is_some() {
            let redirect = self.redirect.as_ref()?;
            if let Some(&target) = redirect.defs.get(&id) {
                // Expand the actual arguments in the caller's context once for
                // the certificate's override obligation; the call itself binds
                // the raw arguments below.
                let expanded_args =
                    args.iter().map(|a| self.expand(a, env, op_env, cur_except, lex_at, depth + 1)).collect::<Option<Vec<_>>>()?;
                let result = self.apply_def(target, args, env, op_env, cur_except, lex_at, span, depth)?;
                let name = self.program.defs[id.idx()].name.to_string();
                let target_name = self.program.defs[target.idx()].name.to_string();
                self.record_override(name, target_name, &expanded_args, &result)?;
                return Some(result);
            }
        }
        if matches!(self.mode, NormMode::Choose | NormMode::Equiv) && args.is_empty() {
            if let Some(val) = self.let_vals.get(&id) {
                return Some(val.clone());
            }
        }
        let d = &self.program.defs[id.idx()];
        if let Some(op) = d.builtin {
            // A builtin operator replaced through this definition: the
            // replacement body runs at every use of the operator.
            if let Some((_, replacement)) = self.builtin_override(op) {
                return self.apply_def(replacement, args, env, op_env, cur_except, lex_at, span, depth);
            }
            return self.apply_builtin(op, args, env, op_env, cur_except, lex_at, span, depth);
        }
        if self.stack.contains(&id) || d.params.len() != args.len() {
            return None;
        }
        if self.program.is_strict_call_def(id) && !super::normalize::strict_call_preserves_args(self.program, d) {
            return None;
        }
        if matches!(self.mode, NormMode::Choose | NormMode::Equiv) && !args.is_empty() {
            let sum_only = self.mode == NormMode::Choose;
            if let DefKind::Op(body) = &d.kind {
                for (k, &s_local) in d.params.iter().enumerate() {
                    if let Some(matched) = folds::match_rec_fold_body(self.program, id, s_local, Some((&d.params, k)), body, sum_only) {
                        return self.expand_op_fold(id, k, s_local, &matched, args, env, op_env, cur_except, lex_at, span, depth);
                    }
                }
                if self.mode == NormMode::Equiv {
                    for k in 0..d.params.len() {
                        if let Some(matched) = rec::match_fix_set_body(self.program, id, &d.params, k, body) {
                            return self.expand_fix_set(id, k, &matched, args, env, op_env, cur_except, lex_at, span, depth);
                        }
                    }
                    for k in 0..d.params.len() {
                        if let Some(matched) = rec::match_iter_rec_body(id, &d.params, k, body) {
                            return self.expand_iter_rec(id, k, &matched, args, env, op_env, cur_except, lex_at, span, depth);
                        }
                    }
                }
            }
        }
        let mut scope = env.clone();
        let mut op_scope = op_env.clone();
        self.bind_call_args(&d.params, args, env, op_env, &mut scope, &mut op_scope, cur_except, lex_at, depth)?;
        let is_plain_nullary = args.is_empty() && matches!(d.kind, DefKind::Op(_));
        let body = match &d.kind {
            DefKind::Op(body) => body.clone(),
            DefKind::Fn { bounds, body } => Expr::new(ExprKind::FnConstruct { bounds: bounds.clone(), body: body.clone() }, d.span),
            DefKind::Pending => return None,
        };
        let def_at = self.let_at.get(&id).copied().unwrap_or(None);
        self.stack.push(id);
        let result = self.expand(&body, &scope, &op_scope, cur_except, def_at, depth + 1);
        self.stack.pop();
        if is_plain_nullary {
            result
        } else {
            result.map(block_non_target)
        }
    }
}
