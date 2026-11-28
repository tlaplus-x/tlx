//! Recognition and normalization of bounded finite `RECURSIVE` operators in `NormMode::Equiv`:
//! - inflationary finite-set fixpoints (`LET nxt == S \cup step(S) IN IF nxt = S THEN S ELSE F(nxt)`),
//! - bounded tail-recursive operators (`IF cond(x) THEN F(step(x)) ELSE base(x)`).

use std::collections::HashMap;

use crate::{builtins::Builtin as B, hir::*, Program};

use super::{EnvMap, OpBinding, SymNormalizer};

/// Kind of bounded recursive operator normalized in `NormMode::Equiv`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::optimize::phase) enum RecOpKind {
    /// `Apply { op: Def(id), args: [init, Lambda([s], step)] }`
    FixSet,
    /// `Apply { op: Def(id), args: [init, Lambda([x], If { cond, then: step, els: base })] }`
    IterRec,
}

pub(super) struct FixSetMatch {
    pub(super) step_raw: Expr,
}

pub(super) struct IterRecMatch {
    pub(super) cond_raw: Expr,
    pub(super) step_raw: Expr,
    pub(super) base_raw: Expr,
    pub(super) negate_cond: bool,
}

fn is_nxt_ref(e: &Expr, nxt_def: DefId) -> bool {
    matches!(&*e.kind, ExprKind::Apply { op: OpRef::Def(d), args } if *d == nxt_def && args.is_empty())
}

fn is_local_ref(e: &Expr, local: LocalId) -> bool {
    matches!(&*e.kind, ExprKind::Local(l) if *l == local)
}

fn is_eq_nxt_s(e: &Expr, nxt_def: DefId, s_local: LocalId) -> bool {
    let ExprKind::Builtin { op: B::Eq, args } = &*e.kind else { return false };
    let [a, b] = args.as_slice() else { return false };
    (is_nxt_ref(a, nxt_def) && is_local_ref(b, s_local)) || (is_local_ref(a, s_local) && is_nxt_ref(b, nxt_def))
}

fn is_neq_nxt_s(e: &Expr, nxt_def: DefId, s_local: LocalId) -> bool {
    match &*e.kind {
        ExprKind::Builtin { op: B::Neq, args } => {
            let [a, b] = args.as_slice() else { return false };
            (is_nxt_ref(a, nxt_def) && is_local_ref(b, s_local)) || (is_local_ref(a, s_local) && is_nxt_ref(b, nxt_def))
        }
        ExprKind::Builtin { op: B::Not, args } if args.len() == 1 => is_eq_nxt_s(&args[0], nxt_def, s_local),
        _ => false,
    }
}

fn extract_tail_rec_arg<'a>(e: &'a Expr, def_id: DefId, params: &[LocalId], k: usize) -> Option<&'a Expr> {
    let ExprKind::Apply { op: OpRef::Def(d), args } = &*e.kind else { return None };
    if *d != def_id || args.len() != params.len() {
        return None;
    }
    for (j, arg) in args.iter().enumerate() {
        if j != k && !is_local_ref(arg, params[j]) {
            return None;
        }
    }
    Some(&args[k])
}

pub(super) fn match_fix_set_body(program: &Program, def_id: DefId, params: &[LocalId], k: usize, body: &Expr) -> Option<FixSetMatch> {
    let s_local = params[k];
    let ExprKind::Let { defs, body: if_expr } = &*body.kind else { return None };
    let [nxt_def] = defs.as_slice() else { return None };
    let nd = &program.defs[nxt_def.idx()];
    if !nd.params.is_empty() {
        return None;
    }
    let DefKind::Op(nxt_rhs) = &nd.kind else { return None };
    let ExprKind::Builtin { op: B::Cup, args } = &*nxt_rhs.kind else { return None };
    let [a, b] = args.as_slice() else { return None };
    let step_raw = if is_local_ref(a, s_local) {
        b.clone()
    } else if is_local_ref(b, s_local) {
        a.clone()
    } else {
        return None;
    };
    let ExprKind::If { cond, then, els } = &*if_expr.kind else { return None };
    let is_ret = |e: &Expr| is_local_ref(e, s_local) || is_nxt_ref(e, *nxt_def);
    let is_rec_nxt = |e: &Expr| extract_tail_rec_arg(e, def_id, params, k).is_some_and(|arg| is_nxt_ref(arg, *nxt_def));
    let ok = (is_eq_nxt_s(cond, *nxt_def, s_local) && is_ret(then) && is_rec_nxt(els))
        || (is_neq_nxt_s(cond, *nxt_def, s_local) && is_rec_nxt(then) && is_ret(els));
    ok.then_some(FixSetMatch { step_raw })
}

pub(super) fn match_iter_rec_body(def_id: DefId, params: &[LocalId], k: usize, body: &Expr) -> Option<IterRecMatch> {
    let ExprKind::If { cond, then, els } = &*body.kind else { return None };
    if let Some(step_raw) = extract_tail_rec_arg(then, def_id, params, k) {
        return Some(IterRecMatch { cond_raw: cond.clone(), step_raw: step_raw.clone(), base_raw: els.clone(), negate_cond: false });
    }
    if let Some(step_raw) = extract_tail_rec_arg(els, def_id, params, k) {
        return Some(IterRecMatch { cond_raw: cond.clone(), step_raw: step_raw.clone(), base_raw: then.clone(), negate_cond: true });
    }
    None
}

impl SymNormalizer<'_> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn expand_fix_set(
        &mut self,
        def_id: DefId,
        k: usize,
        matched: &FixSetMatch,
        raw_args: &[Expr],
        env: &EnvMap,
        op_env: &HashMap<LocalId, OpBinding>,
        cur_except: Option<usize>,
        lex_at: Option<usize>,
        span: Span,
        depth: usize,
    ) -> Option<Expr> {
        if self.rec_ops.get(&def_id).is_some_and(|&prev| prev != RecOpKind::FixSet) {
            return None;
        }
        let d = &self.program.defs[def_id.idx()];
        let s_local = d.params[k];
        let init = self.expand(&raw_args[k], env, op_env, cur_except, lex_at, depth + 1)?;
        let mut scope = env.clone();
        let mut op_scope = op_env.clone();
        scope.remove(&s_local);
        op_scope.remove(&s_local);
        for (j, (&param, raw)) in d.params.iter().zip(raw_args.iter()).enumerate() {
            if j == k {
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
        let s_var = self.alloc_local();
        scope.insert(s_local, (Expr::new(ExprKind::Local(s_var), span), cur_except));
        let def_at = self.let_at.get(&def_id).copied().unwrap_or(None);
        self.stack.push(def_id);
        let step = self.expand(&matched.step_raw, &scope, &op_scope, cur_except, def_at, depth + 1);
        self.stack.pop();
        let step = step?;
        self.rec_ops.insert(def_id, RecOpKind::FixSet);
        let step_lam = Expr::new(ExprKind::Lambda { params: vec![s_var], body: step }, span);
        Some(Expr::new(ExprKind::Apply { op: OpRef::Def(def_id), args: vec![init, step_lam] }, span))
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn expand_iter_rec(
        &mut self,
        def_id: DefId,
        k: usize,
        matched: &IterRecMatch,
        raw_args: &[Expr],
        env: &EnvMap,
        op_env: &HashMap<LocalId, OpBinding>,
        cur_except: Option<usize>,
        lex_at: Option<usize>,
        span: Span,
        depth: usize,
    ) -> Option<Expr> {
        if self.rec_ops.get(&def_id).is_some_and(|&prev| prev != RecOpKind::IterRec) {
            return None;
        }
        let d = &self.program.defs[def_id.idx()];
        let x_local = d.params[k];
        let init = self.expand(&raw_args[k], env, op_env, cur_except, lex_at, depth + 1)?;
        let mut scope = env.clone();
        let mut op_scope = op_env.clone();
        scope.remove(&x_local);
        op_scope.remove(&x_local);
        for (j, (&param, raw)) in d.params.iter().zip(raw_args.iter()).enumerate() {
            if j == k {
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
        let x_var = self.alloc_local();
        scope.insert(x_local, (Expr::new(ExprKind::Local(x_var), span), cur_except));
        let def_at = self.let_at.get(&def_id).copied().unwrap_or(None);
        self.stack.push(def_id);
        let cond = self.expand(&matched.cond_raw, &scope, &op_scope, cur_except, def_at, depth + 1);
        let step = self.expand(&matched.step_raw, &scope, &op_scope, cur_except, def_at, depth + 1);
        let base = self.expand(&matched.base_raw, &scope, &op_scope, cur_except, def_at, depth + 1);
        self.stack.pop();
        let (mut cond, step, base) = (cond?, step?, base?);
        if matched.negate_cond {
            cond = Expr::new(ExprKind::Builtin { op: B::Not, args: vec![cond] }, span);
        }
        self.rec_ops.insert(def_id, RecOpKind::IterRec);
        let body = Expr::new(ExprKind::If { cond, then: step, els: base }, span);
        let step_lam = Expr::new(ExprKind::Lambda { params: vec![x_var], body }, span);
        Some(Expr::new(ExprKind::Apply { op: OpRef::Def(def_id), args: vec![init, step_lam] }, span))
    }
}
