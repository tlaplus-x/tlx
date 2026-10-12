//! Forget sequence contents when every use depends only on length. Shares the
//! structural domain proof and bounded normalization with field projection.

use tlx_front::cfg::Config;

use crate::{builtins::Builtin as B, hir::*, visit, Program};

use super::{
    binding, branches,
    domain::{Domain, Domains},
    normalize::Normalizer,
    unchanged, variable, Branch, FieldProjection,
};

/// Prove a length-only key for top-level sequences. All observations must be
/// supplied, with the same execution boundary as `phase_projection`.
pub fn sequence_length_projection(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    observations: &[Expr],
) -> Option<FieldProjection> {
    let mut expand = Normalizer::new(program);
    let initial = branches(&expand.root(init)?)?;
    let steps = branches(&expand.root(next)?)?;
    let observations: Vec<_> = observations.iter().map(|e| expand.root(e)).collect::<Option<_>>()?;
    let domains = Domains::infer(program, cfg, &initial, &steps)?;
    let mut projected = Vec::new();
    for (i, domain) in domains.vars.iter().enumerate() {
        if !matches!(domain, Domain::Seq(_)) {
            continue;
        }
        let v = VarId(i as u32);
        let proof = Proof { v, domains: &domains };
        if initial.iter().all(|b| proof.branch(b, false))
            && steps.iter().all(|b| proof.branch(b, true))
            && observations.iter().all(|e| proof.read(e))
        {
            projected.push(v);
        }
    }
    if projected.is_empty() {
        return None;
    }
    let values = program
        .vars
        .iter()
        .enumerate()
        .map(|(i, v)| {
            let id = VarId(i as u32);
            let e = Expr::new(ExprKind::Var(id), v.span);
            if projected.contains(&id) {
                Expr::new(ExprKind::Builtin { op: B::Len, args: vec![e] }, v.span)
            } else {
                e
            }
        })
        .collect();
    Some(FieldProjection {
        view: Expr::new(ExprKind::Tuple(values), init.span),
        certificate: None,
        fields: projected.iter().map(|v| format!("{}.contents", program.vars[v.idx()].name)).collect(),
    })
}

struct Proof<'a> {
    v: VarId,
    domains: &'a Domains,
}

impl Proof<'_> {
    fn branch(&self, b: &Branch, primed: bool) -> bool {
        // Exactly one binding: a second equality could compare contents with
        // the first assignment, or UNCHANGED could turn it into a guard.
        let Some(rhs) = binding(b, self.v, primed) else { return false };
        if !self.transfer(&rhs) || !b.bounds.iter().all(|b| self.read(&b.set)) {
            return false;
        }
        b.terms.iter().all(|e| match &*e.kind {
            ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 && variable(&args[0], primed) == Some(self.v) => true,
            ExprKind::Builtin { op: B::Unchanged, args } if primed && args.len() == 1 && unchanged(&args[0], self.v) == 1 => {
                Self::unchanged(&args[0])
            }
            _ => self.read(e),
        })
    }

    fn unchanged(e: &Expr) -> bool {
        match &*e.kind {
            ExprKind::Var(_) => true,
            ExprKind::Tuple(es) => es.iter().all(Self::unchanged),
            _ => false,
        }
    }

    // Transfers preserve length equivalence. Appended expressions are still
    // scanned: their errors, guards and dependencies remain observable even
    // though their resulting elements are forgotten in the key.
    fn transfer(&self, e: &Expr) -> bool {
        match &*e.kind {
            ExprKind::Var(v) => *v == self.v,
            ExprKind::Tuple(es) => es.iter().all(|e| self.read(e)),
            ExprKind::Builtin { op: B::Append, args } if args.len() == 2 => self.transfer(&args[0]) && self.read(&args[1]),
            ExprKind::If { cond, then, els } => self.read(cond) && self.transfer(then) && self.transfer(els),
            _ => false,
        }
    }

    fn read(&self, e: &Expr) -> bool {
        match &*e.kind {
            ExprKind::Var(v) if *v == self.v => return false,
            ExprKind::Builtin { op: B::Len, args } if args.len() == 1 && self.reference(&args[0]) => return true,
            ExprKind::Builtin { op: B::In, args }
                if args.len() == 2 && self.reference(&args[0]) && self.domains.belongs(&self.domains.vars[self.v.idx()], &args[1]) =>
            {
                return true
            }
            _ => {}
        }
        let mut valid = true;
        visit::children(e, &mut |e| valid &= self.read(e));
        valid
    }

    fn reference(&self, e: &Expr) -> bool {
        variable(e, false) == Some(self.v) || variable(e, true) == Some(self.v)
    }
}
