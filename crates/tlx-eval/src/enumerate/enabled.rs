//! `UNCHANGED` and the action operators built on it, `[A]_e` and `<<A>>_e`
//! (moved out of `enumerate.rs`). `UNCHANGED e` assigns the variables of
//! `e` that are still unassigned and tests the others; evaluating `ENABLED`
//! reuses this path with `enabled` set, where `UNCHANGED <<e1, ..., en>>` is
//! taken in TLC's order.

use tlx_value::order;

use super::*;

impl<'a> Enumerator<'a> {
    /// `[A]_e`: enumerate `A`, then have `e` unchanged.
    pub(super) fn box_action(&mut self, action: &Expr, sub: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        if !self.go(action, env, k)? {
            return Ok(false);
        }
        self.unchanged(sub, env, k)
    }

    /// `<<A>>_e`: enumerate `A` with the elements of `e` required to
    /// change.
    pub(super) fn angle_action(&mut self, action: &Expr, sub: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        let k2 = Cont::push(Seg::MustChange(sub, env), k);
        self.go(action, env, &k2)
    }

    /// `UNCHANGED e` as an action: assigns unassigned variables.
    pub(super) fn unchanged(&mut self, e: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        if let Some(v) = self.var_of(e, env) {
            // (A variable of an instantiated module in ENABLED: its
            // substitution's value.)
            let cur = match self.s0.unwrap().get(v.idx()) {
                Some(x) => x.clone(),
                None => self.eval(e, env)?,
            };
            return match &self.s1[v.idx()] {
                None => self.assign(v, cur, k),
                Some(x) => {
                    if order::eq_tlc(x, &cur)? {
                        self.cont(k)
                    } else {
                        // TLC warns "variable x was changed while it is specified as UNCHANGED".
                        Ok(true)
                    }
                }
            };
        }
        let ip: &'a Arc<Interp> = self.ip;
        match &*e.kind {
            // TLC's ENABLED takes `UNCHANGED <<e1, ..., en>>` in the order
            // e1, en, ..., e2 (Tool.enabledUnchangedImpl conses e2..en onto
            // the pending items in that order); this matters when an
            // expression primes variables not assigned yet.
            ExprKind::Tuple(es) if self.enabled && es.len() > 2 => {
                let k1 = Cont::push(Seg::UnchangedRev(&es[1..], env), k);
                let k2 = Cont::push(Seg::Unchanged(&es[..1], env), &k1);
                self.cont(&k2)
            }
            ExprKind::Tuple(es) => {
                let k2 = Cont::push(Seg::Unchanged(es, env), k);
                self.cont(&k2)
            }
            ExprKind::Apply { op: OpRef::Def(d), args } if args.is_empty() => match ip.plain_op_body(*d) {
                Some((d, body)) => self.unchanged(body, &ip.def_env(d, env), k),
                None => self.unchanged_eval(e, env, k),
            },
            ExprKind::Local(l) => match env.lookup(*l).and_then(|b| b.by_name(&ip.prog)) {
                Some((inner, inner_env)) => self.unchanged(inner, inner_env, k),
                None => self.unchanged_eval(e, env, k),
            },
            ExprKind::Let { defs, body } => {
                let (env2, _frame) = ip.let_env(defs, env);
                self.unchanged(body, &env2, k)
            }
            _ => self.unchanged_eval(e, env, k),
        }
    }

    /// `UNCHANGED e` evaluated as a test.
    fn unchanged_eval(&mut self, e: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        if self.is_unchanged(e, env)? {
            self.cont(k)
        } else {
            Ok(true)
        }
    }
}
