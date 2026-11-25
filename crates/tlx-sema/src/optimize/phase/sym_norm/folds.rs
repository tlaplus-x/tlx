//! Recognition and normalization of commutative-associative folds:
//! - recursive `CHOOSE` folds (`+` in `NormMode::Choose`; `+`, `*`, `\cup`, `\cap` in `NormMode::Equiv`),
//! - `ACOp` classification and `chooses_first` selector recognition shared by `sym_totality` and `equiv_sym`.

use std::collections::HashMap;

use crate::{builtins::Builtin as B, hir::*, Program};

use super::helpers::mentions_local;
use super::{EnvMap, NormMode, OpBinding, SymNormalizer};

/// Verified commutative-associative binary operator over finite sets.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::optimize::phase) enum AcOpKind {
    IntAdd,
    IntMul,
    SetCup,
    SetCap,
    BoolAnd,
    BoolOr,
}

impl AcOpKind {
    pub(in crate::optimize::phase) fn lean_ctor(self) -> &'static str {
        match self {
            Self::IntAdd => "ACOp.intAdd",
            Self::IntMul => "ACOp.intMul",
            Self::SetCup => "ACOp.setCup",
            Self::SetCap => "ACOp.setCap",
            Self::BoolAnd => "ACOp.boolAnd",
            Self::BoolOr => "ACOp.boolOr",
        }
    }
}

/// Classify a normalized binary `LAMBDA p, q : body` as one of the 6 certified
/// commutative-associative operators (`+`, `*`, `\cup`, `\cap`, `/\`, `\/`).
pub(in crate::optimize::phase) fn classify_ac_op(e: &Expr) -> Option<AcOpKind> {
    let ExprKind::Lambda { params, body } = &*e.kind else { return None };
    let [p, q] = params.as_slice() else { return None };
    let mut inner = body;
    while let ExprKind::Builtin { op: B::TLCEval, args } = &*inner.kind {
        let [a] = args.as_slice() else { break };
        inner = a;
    }
    let is_pq = |a: &Expr, b: &Expr| {
        matches!(
            (&*a.kind, &*b.kind),
            (ExprKind::Local(x), ExprKind::Local(y)) if (x == p && y == q) || (x == q && y == p)
        )
    };
    match &*inner.kind {
        ExprKind::Builtin { op: B::Plus, args } if args.len() == 2 && is_pq(&args[0], &args[1]) => Some(AcOpKind::IntAdd),
        ExprKind::Builtin { op: B::Mul, args } if args.len() == 2 && is_pq(&args[0], &args[1]) => Some(AcOpKind::IntMul),
        ExprKind::Builtin { op: B::Cup, args } if args.len() == 2 && is_pq(&args[0], &args[1]) => Some(AcOpKind::SetCup),
        ExprKind::Builtin { op: B::Cap, args } if args.len() == 2 && is_pq(&args[0], &args[1]) => Some(AcOpKind::SetCap),
        ExprKind::And(es) if es.len() == 2 && is_pq(&es[0], &es[1]) => Some(AcOpKind::BoolAnd),
        ExprKind::Or(es) if es.len() == 2 && is_pq(&es[0], &es[1]) => Some(AcOpKind::BoolOr),
        _ => None,
    }
}

/// Whether a normalized unary `LAMBDA` is `LAMBDA s : CHOOSE x \in s : TRUE`,
/// matching `Interp::chooses_first`.
pub(in crate::optimize::phase) fn is_chooses_first_lambda(e: &Expr) -> bool {
    let ExprKind::Lambda { params, body } = &*e.kind else { return false };
    let [s] = params.as_slice() else { return false };
    matches!(
        &*body.kind,
        ExprKind::Choose { vars: BoundVars::Many(vs), set: Some(cset), body: cpred }
            if vs.len() == 1
                && matches!(&*cset.kind, ExprKind::Local(l) if l == s)
                && matches!(&*cpred.kind, ExprKind::Bool(true))
    )
}

pub(super) struct RecFoldMatch {
    pub(super) op: B,
    pub(super) base_raw: Expr,
    pub(super) choose_def: DefId,
    pub(super) term_raw: Expr,
}

impl SymNormalizer<'_> {
    #[allow(clippy::too_many_arguments)]
    fn build_equiv_map_then_fold(
        &mut self,
        op: B,
        base: Expr,
        elem_var: LocalId,
        term: Expr,
        target_set: Expr,
        dom_superset: Option<Expr>,
        span: Span,
    ) -> Expr {
        let p = self.alloc_local();
        let q = self.alloc_local();
        let op_lam = Expr::new(
            ExprKind::Lambda {
                params: vec![p, q],
                body: Expr::new(
                    ExprKind::Builtin { op, args: vec![Expr::new(ExprKind::Local(p), span), Expr::new(ExprKind::Local(q), span)] },
                    span,
                ),
            },
            span,
        );
        let f_lam = Expr::new(ExprKind::Lambda { params: vec![elem_var], body: term }, span);
        let s_param = self.alloc_local();
        let y_var = self.alloc_local();
        let choose_lam = Expr::new(
            ExprKind::Lambda {
                params: vec![s_param],
                body: Expr::new(
                    ExprKind::Choose {
                        vars: BoundVars::Many(vec![y_var]),
                        set: Some(Expr::new(ExprKind::Local(s_param), span)),
                        body: Expr::new(ExprKind::Bool(true), span),
                    },
                    span,
                ),
            },
            span,
        );
        let mut args = vec![op_lam, base, f_lam, choose_lam, target_set];
        if let Some(sup) = dom_superset {
            args.push(sup);
        }
        Expr::new(ExprKind::Builtin { op: B::MapThenFoldSet, args }, span)
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn expand_op_fold(
        &mut self,
        sum_id: DefId,
        set_pos: usize,
        s_local: LocalId,
        matched: &RecFoldMatch,
        raw_args: &[Expr],
        env: &EnvMap,
        op_env: &HashMap<LocalId, OpBinding>,
        cur_except: Option<usize>,
        lex_at: Option<usize>,
        span: Span,
        depth: usize,
    ) -> Option<Expr> {
        let d = &self.program.defs[sum_id.idx()];
        let target_set = self.expand(&raw_args[set_pos], env, op_env, cur_except, lex_at, depth + 1)?;
        let mut scope = env.clone();
        let mut op_scope = op_env.clone();
        scope.remove(&s_local);
        op_scope.remove(&s_local);
        for (j, (&param, raw)) in d.params.iter().zip(raw_args.iter()).enumerate() {
            if j == set_pos {
                continue;
            }
            self.bind_call_args(
                std::slice::from_ref(&param),
                std::slice::from_ref(raw),
                env,
                op_env,
                &mut scope,
                &mut op_scope,
                cur_except,
                lex_at,
                depth,
            )?;
        }
        let def_at = self.let_at.get(&sum_id).copied().unwrap_or(None);
        let base = if self.mode == NormMode::Equiv {
            self.stack.push(sum_id);
            let b = self.expand(&matched.base_raw, &scope, &op_scope, cur_except, def_at, depth + 1);
            self.stack.pop();
            let b = b?;
            if mentions_local(&b, s_local) {
                return None;
            }
            Some(b)
        } else {
            None
        };
        let elem_var = self.alloc_local();
        let prev = self.let_vals.insert(matched.choose_def, Expr::new(ExprKind::Local(elem_var), span));
        self.stack.push(sum_id);
        let term = self.expand(&matched.term_raw, &scope, &op_scope, cur_except, def_at, depth + 1);
        self.stack.pop();
        match prev {
            Some(old) => {
                self.let_vals.insert(matched.choose_def, old);
            }
            None => {
                self.let_vals.remove(&matched.choose_def);
            }
        }
        let term = term?;
        if mentions_local(&term, s_local) {
            return None;
        }
        if self.mode == NormMode::Equiv {
            Some(self.build_equiv_map_then_fold(matched.op, base.unwrap(), elem_var, term, target_set, None, span))
        } else {
            self.fold_vars.insert(elem_var, None);
            Some(Expr::new(ExprKind::Choose { vars: BoundVars::Many(vec![elem_var]), set: Some(target_set), body: term }, span))
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn try_expand_fn_fold(
        &mut self,
        sum_id: DefId,
        target_raw: &Expr,
        env: &EnvMap,
        op_env: &HashMap<LocalId, OpBinding>,
        cur_except: Option<usize>,
        lex_at: Option<usize>,
        span: Span,
        depth: usize,
    ) -> Option<Option<Expr>> {
        if self.stack.contains(&sum_id) {
            return Some(None);
        }
        let d = &self.program.defs[sum_id.idx()];
        if !d.params.is_empty() {
            return None;
        }
        let DefKind::Fn { bounds, body } = &d.kind else { return None };
        let [Bound { vars: BoundVars::Many(svs), set: dom_set }] = bounds.as_slice() else { return None };
        let [s_local] = svs.as_slice() else { return None };
        let sum_only = self.mode == NormMode::Choose;
        let matched = match_rec_fold_body(self.program, sum_id, *s_local, None, body, sum_only)?;
        let ExprKind::Builtin { op: B::Subset, args: sub_args } = &*dom_set.kind else {
            return Some(None);
        };
        let [superset_raw] = sub_args.as_slice() else { return Some(None) };
        let def_at = self.let_at.get(&sum_id).copied().unwrap_or(None);
        let Some(target_set) = self.expand(target_raw, env, op_env, cur_except, lex_at, depth + 1) else {
            return Some(None);
        };
        let Some(superset) = self.expand(superset_raw, env, op_env, cur_except, def_at, depth + 1) else {
            return Some(None);
        };
        let mut scope = env.clone();
        scope.remove(s_local);
        let base = if self.mode == NormMode::Equiv {
            self.stack.push(sum_id);
            let b = self.expand(&matched.base_raw, &scope, op_env, cur_except, def_at, depth + 1);
            self.stack.pop();
            let Some(b) = b else { return Some(None) };
            if mentions_local(&b, *s_local) {
                return Some(None);
            }
            Some(b)
        } else {
            None
        };
        let elem_var = self.alloc_local();
        let prev = self.let_vals.insert(matched.choose_def, Expr::new(ExprKind::Local(elem_var), span));
        self.stack.push(sum_id);
        let term = self.expand(&matched.term_raw, &scope, op_env, cur_except, def_at, depth + 1);
        self.stack.pop();
        match prev {
            Some(old) => {
                self.let_vals.insert(matched.choose_def, old);
            }
            None => {
                self.let_vals.remove(&matched.choose_def);
            }
        }
        let Some(term) = term else { return Some(None) };
        if mentions_local(&term, *s_local) {
            return Some(None);
        }
        if self.mode == NormMode::Equiv {
            Some(Some(self.build_equiv_map_then_fold(matched.op, base.unwrap(), elem_var, term, target_set, Some(superset), span)))
        } else {
            self.fold_vars.insert(elem_var, Some(superset));
            Some(Some(Expr::new(ExprKind::Choose { vars: BoundVars::Many(vec![elem_var]), set: Some(target_set), body: term }, span)))
        }
    }
}

pub(super) fn match_rec_fold_body(
    program: &Program,
    sum_id: DefId,
    s_local: LocalId,
    op_params: Option<(&[LocalId], usize)>,
    body: &Expr,
    sum_only: bool,
) -> Option<RecFoldMatch> {
    let ExprKind::If { cond, then, els } = &*body.kind else { return None };
    let (base_raw, step_branch) = if is_empty_set_eq(cond, s_local) {
        (then, els)
    } else if is_nonempty_set_check(cond, s_local) {
        (els, then)
    } else {
        return None;
    };
    if sum_only && !matches!(&*base_raw.kind, ExprKind::Num(0)) {
        return None;
    }
    let ExprKind::Let { defs, body: op_body } = &*step_branch.kind else { return None };
    let [choose_def] = defs.as_slice() else { return None };
    let cdef = &program.defs[choose_def.idx()];
    if !cdef.params.is_empty() {
        return None;
    }
    let DefKind::Op(cexpr) = &cdef.kind else { return None };
    let ExprKind::Choose { vars: BoundVars::Many(vs), set: Some(cset), body: cpred } = &*cexpr.kind else {
        return None;
    };
    if vs.len() != 1 || !matches!(&*cset.kind, ExprKind::Local(l) if *l == s_local) || !matches!(&*cpred.kind, ExprKind::Bool(true)) {
        return None;
    }
    let ExprKind::Builtin { op, args } = &*op_body.kind else { return None };
    let op_ok = if sum_only { *op == B::Plus } else { matches!(op, B::Plus | B::Mul | B::Cup | B::Cap) };
    if !op_ok {
        return None;
    }
    let [a, b] = args.as_slice() else { return None };
    for (call, term) in [(a, b), (b, a)] {
        if is_rec_call(sum_id, s_local, *choose_def, op_params, call) {
            return Some(RecFoldMatch { op: *op, base_raw: base_raw.clone(), choose_def: *choose_def, term_raw: term.clone() });
        }
    }
    None
}

fn is_empty_set_eq(e: &Expr, s_local: LocalId) -> bool {
    let ExprKind::Builtin { op: B::Eq, args } = &*e.kind else { return false };
    let [a, b] = args.as_slice() else { return false };
    let is_s = |x: &Expr| matches!(&*x.kind, ExprKind::Local(l) if *l == s_local);
    let is_emp = |x: &Expr| matches!(&*x.kind, ExprKind::SetEnum(es) if es.is_empty());
    (is_s(a) && is_emp(b)) || (is_emp(a) && is_s(b))
}

fn is_nonempty_set_check(e: &Expr, s_local: LocalId) -> bool {
    match &*e.kind {
        ExprKind::Builtin { op: B::Neq, args } => {
            let [a, b] = args.as_slice() else { return false };
            let is_s = |x: &Expr| matches!(&*x.kind, ExprKind::Local(l) if *l == s_local);
            let is_emp = |x: &Expr| matches!(&*x.kind, ExprKind::SetEnum(es) if es.is_empty());
            (is_s(a) && is_emp(b)) || (is_emp(a) && is_s(b))
        }
        ExprKind::Builtin { op: B::Not, args } if args.len() == 1 => is_empty_set_eq(&args[0], s_local),
        _ => false,
    }
}

fn is_rec_call(sum_id: DefId, s_local: LocalId, choose_def: DefId, op_params: Option<(&[LocalId], usize)>, e: &Expr) -> bool {
    let is_s_minus_x = |arg: &Expr| -> bool {
        let ExprKind::Builtin { op: B::SetMinus, args } = &*arg.kind else { return false };
        let [lhs, rhs] = args.as_slice() else { return false };
        matches!(&*lhs.kind, ExprKind::Local(l) if *l == s_local)
            && matches!(&*rhs.kind, ExprKind::SetEnum(es) if matches!(es.as_slice(), [item] if matches!(&*item.kind, ExprKind::Apply { op: OpRef::Def(d), args } if *d == choose_def && args.is_empty())))
    };
    match (op_params, &*e.kind) {
        (None, ExprKind::FnApp { func, args }) => {
            matches!(&*func.kind, ExprKind::Apply { op: OpRef::Def(d), args: fa } if *d == sum_id && fa.is_empty())
                && matches!(args.as_slice(), [arg] if is_s_minus_x(arg))
        }
        (Some((params, k)), ExprKind::Apply { op: OpRef::Def(d), args }) => {
            *d == sum_id
                && args.len() == params.len()
                && args.iter().enumerate().all(|(j, a)| {
                    if j == k {
                        is_s_minus_x(a)
                    } else {
                        matches!(&*a.kind, ExprKind::Local(l) if *l == params[j])
                    }
                })
        }
        _ => false,
    }
}
