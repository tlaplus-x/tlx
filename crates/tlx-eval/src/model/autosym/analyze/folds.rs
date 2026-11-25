//! Fold analysis: applying an operator of shape `ops` to argument
//! shapes, and the breaker a fold over a set (or a function's domain)
//! adds unless its operator is known to be commutative and associative.

use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::*;

use super::super::shape::{self, Mask, OpVal, Sh, ALL};
use super::{Analyzer, Arg, DEPTH};

impl<'a> Analyzer<'a> {
    /// Apply every operator of shape `ops` to arguments of shapes `args`.
    pub(super) fn apply_ops(&mut self, ops: &Sh, args: Vec<Sh>, span: Span) -> Sh {
        let os = ops.ops();
        if os.is_empty() {
            return Sh::any(ALL);
        }
        let mut r = Sh::default();
        for o in os {
            r = r.join(&self.apply_op(&o, args.iter().cloned().map(Arg::of).collect(), span));
        }
        r
    }

    /// A breaker for a fold over elements of `mask` with operator `op`,
    /// unless `op` is commutative and associative.
    pub(super) fn fold_order(&mut self, op: &Sh, mask: Mask, what: &str, span: Span) {
        let ops = op.ops();
        if mask != 0 && (ops.is_empty() || !ops.iter().all(|o| self.commutative(o))) {
            self.breaker(mask, format!("{what} with an operator not known to be commutative and associative"), span);
        }
    }

    /// The result of folding `op` over elements of shape `x` from `base`.
    pub(super) fn fold(&mut self, op: &Sh, base: Sh, x: Sh, span: Span) -> Sh {
        let mut acc = base;
        for _ in 0..4 {
            let a = self.apply_ops(op, vec![x.clone(), acc.clone()], span);
            let b = self.apply_ops(op, vec![acc.clone(), x.clone()], span);
            let next = acc.join(&a).join(&b).limit(DEPTH);
            if next.le(&acc) {
                return acc;
            }
            acc = next;
        }
        Sh::any(acc.mask())
    }

    /// Whether every operator in `op` is known to be commutative and associative.
    pub(super) fn all_commutative(&self, op: &Sh) -> bool {
        let ops = op.ops();
        !ops.is_empty() && ops.iter().all(|o| self.commutative(o))
    }

    /// Whether every operator in `op` is the order-independent arbitrary
    /// selector `LAMBDA s : CHOOSE x \in s : TRUE` (matching `Interp::chooses_first`).
    pub(super) fn all_chooses_first(&self, op: &Sh) -> bool {
        let ops = op.ops();
        !ops.is_empty() && ops.iter().all(|o| self.chooses_first_op(o))
    }

    fn chooses_first_op(&self, o: &OpVal) -> bool {
        let body_ok = |params: &[LocalId], body: &Expr| -> bool {
            let [s] = params else { return false };
            matches!(
                &*body.kind,
                ExprKind::Choose { vars: BoundVars::Many(vs), set: Some(cset), body: cpred }
                    if vs.len() == 1
                        && matches!(&*cset.kind, ExprKind::Local(l) if l == s)
                        && matches!(&*cpred.kind, ExprKind::Bool(true))
            )
        };
        match o {
            OpVal::Lambda(e) => shape::lambda_parts(e).is_some_and(|(ps, body)| body_ok(ps, body)),
            OpVal::Def(d) => {
                let def = &self.ip.prog.defs[d.idx()];
                matches!(&def.kind, DefKind::Op(body) if def.builtin.is_none() && body_ok(&def.params, body))
            }
            OpVal::Builtin(_) => false,
        }
    }

    /// Whether `o` is known to be commutative and associative: `+`, `*`,
    /// `\cup`, `\cap`, `/\`, `\/`, or a two-parameter operator or LAMBDA
    /// applying one of them to its parameters.
    fn commutative(&self, o: &OpVal) -> bool {
        let ca = |b: B| matches!(b, B::Plus | B::Mul | B::Cup | B::Cap | B::BagCup);
        let body_ok = |params: &[LocalId], body: &Expr| -> bool {
            let [p, q] = params else { return false };
            let is_pq = |args: &[Expr]| match args {
                [x, y] => {
                    matches!((&*x.kind, &*y.kind), (ExprKind::Local(a), ExprKind::Local(b)) if (a == p && b == q) || (a == q && b == p))
                }
                _ => false,
            };
            match &*body.kind {
                ExprKind::Builtin { op, args } => ca(*op) && is_pq(args),
                ExprKind::And(es) | ExprKind::Or(es) => is_pq(es),
                _ => false,
            }
        };
        match o {
            OpVal::Builtin(b) => ca(*b),
            OpVal::Lambda(e) => shape::lambda_parts(e).is_some_and(|(ps, body)| body_ok(ps, body)),
            OpVal::Def(d) => {
                let def = &self.ip.prog.defs[d.idx()];
                match &def.kind {
                    DefKind::Op(body) if def.builtin.is_none() => body_ok(&def.params, body),
                    _ => def.builtin.is_some_and(ca),
                }
            }
        }
    }
}
