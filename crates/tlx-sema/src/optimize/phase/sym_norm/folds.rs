//! Recognition and normalization of commutative-associative recursive `CHOOSE`
//! integer set-sum folds (`NormMode::Choose`).
#![allow(dead_code, unused_imports)]

use std::collections::HashMap;

use crate::{builtins::Builtin as B, hir::*, Program};

use super::helpers::mentions_local;
use super::{EnvMap, OpBinding, SymNormalizer};

impl SymNormalizer<'_> {
    #[allow(clippy::too_many_arguments)]
    pub(super) fn expand_op_fold(
        &mut self,
        sum_id: DefId,
        set_pos: usize,
        s_local: LocalId,
        choose_def: DefId,
        raw_term: &Expr,
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
        let elem_var = self.alloc_local();
        let prev = self.let_vals.insert(choose_def, Expr::new(ExprKind::Local(elem_var), span));
        let def_at = self.let_at.get(&sum_id).copied().unwrap_or(None);
        self.stack.push(sum_id);
        let term = self.expand(raw_term, &scope, &op_scope, cur_except, def_at, depth + 1);
        self.stack.pop();
        match prev {
            Some(old) => {
                self.let_vals.insert(choose_def, old);
            }
            None => {
                self.let_vals.remove(&choose_def);
            }
        }
        let term = term?;
        if mentions_local(&term, s_local) {
            return None;
        }
        self.fold_vars.insert(elem_var, None);
        Some(Expr::new(ExprKind::Choose { vars: BoundVars::Many(vec![elem_var]), set: Some(target_set), body: term }, span))
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
        let (choose_def, raw_term) = match_sum_fold_body(self.program, sum_id, *s_local, None, body)?;
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
        let elem_var = self.alloc_local();
        let prev = self.let_vals.insert(choose_def, Expr::new(ExprKind::Local(elem_var), span));
        self.stack.push(sum_id);
        let term = self.expand(&raw_term, &scope, op_env, cur_except, def_at, depth + 1);
        self.stack.pop();
        match prev {
            Some(old) => {
                self.let_vals.insert(choose_def, old);
            }
            None => {
                self.let_vals.remove(&choose_def);
            }
        }
        let Some(term) = term else { return Some(None) };
        if mentions_local(&term, *s_local) {
            return Some(None);
        }
        self.fold_vars.insert(elem_var, Some(superset));
        Some(Some(Expr::new(ExprKind::Choose { vars: BoundVars::Many(vec![elem_var]), set: Some(target_set), body: term }, span)))
    }
}

pub(super) fn match_sum_fold_body(
    program: &Program,
    sum_id: DefId,
    s_local: LocalId,
    op_params: Option<(&[LocalId], usize)>,
    body: &Expr,
) -> Option<(DefId, Expr)> {
    let ExprKind::If { cond, then, els } = &*body.kind else { return None };
    let step_branch = if is_empty_set_eq(cond, s_local) && matches!(&*then.kind, ExprKind::Num(0)) {
        els
    } else if is_nonempty_set_check(cond, s_local) && matches!(&*els.kind, ExprKind::Num(0)) {
        then
    } else {
        return None;
    };
    let ExprKind::Let { defs, body: plus_body } = &*step_branch.kind else { return None };
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
    let ExprKind::Builtin { op: B::Plus, args } = &*plus_body.kind else { return None };
    let [a, b] = args.as_slice() else { return None };
    for (call, term) in [(a, b), (b, a)] {
        if is_rec_call(sum_id, s_local, *choose_def, op_params, call) {
            return Some((*choose_def, term.clone()));
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
