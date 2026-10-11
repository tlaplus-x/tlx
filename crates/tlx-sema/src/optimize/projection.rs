//! Backward state liveness (a conservative cone of influence) on resolved HIR.
//!
//! Literal assignments and copies are total transfers. Their inputs are live
//! only when the assigned variable is live. Guards, observations and unknown
//! expressions seed a worklist; transitive dependencies close the live set.
//! See docs/optimization.md for the resulting quotient's proof.

use std::collections::HashSet;

use crate::builtins::Builtin as B;
use crate::hir::*;
use crate::{visit, Program};

/// Variables irrelevant to the supplied behavior and observations. The caller
/// must supply every checked observation, exclude temporal checking, and ensure
/// configuration bindings do not override the definitions analyzed here.
/// Unknown constructs retain their referenced variables; effects or exhausted
/// analysis budgets disable the reduction. Does not change executable HIR.
pub fn unobserved_variables(program: &Program, init: &Expr, next: &Expr, observations: &[Expr]) -> Vec<VarId> {
    let mut scan = Scan {
        program,
        read: vec![false; program.vars.len()],
        dependencies: vec![Vec::new(); program.vars.len()],
        seen: HashSet::new(),
        expanding: HashSet::new(),
        remaining: 100_000,
        complete: true,
    };
    let initial = scan.action(init, false, 0);
    let steps = scan.action(next, true, 0);
    for e in observations {
        scan.value(e, 0);
    }
    if !scan.complete {
        return Vec::new();
    }
    let mut work = Vec::new();
    for (i, (init, step)) in initial.iter().zip(steps).enumerate() {
        scan.read[i] |= *init != 1 || step > 1;
        if scan.read[i] {
            work.push(i);
        }
    }
    // Least fixed point of L = roots union dependencies(L). Cycles with no
    // path to an observation remain dead; one live member retains the cycle.
    while let Some(v) = work.pop() {
        for &input in &scan.dependencies[v] {
            if !scan.read[input] {
                scan.read[input] = true;
                work.push(input);
            }
        }
    }
    scan.read.iter().enumerate().filter(|(_, live)| !**live).map(|(i, _)| VarId(i as u32)).collect()
}

struct Scan<'a> {
    program: &'a Program,
    read: Vec<bool>,
    dependencies: Vec<Vec<usize>>,
    seen: HashSet<DefId>,
    expanding: HashSet<DefId>,
    remaining: usize,
    complete: bool,
}

impl Scan<'_> {
    fn enter(&mut self, depth: usize) -> bool {
        if self.remaining == 0 || depth >= 128 {
            self.complete = false;
            return false;
        }
        self.remaining -= 1;
        true
    }

    // Maximum bindings on any syntactic alternative, saturated at two. Two
    // bindings can test the old value (UNCHANGED x /\ x' = literal), so cannot
    // justify forgetting x even when there is no explicit unprimed read.
    fn action(&mut self, e: &Expr, primed: bool, depth: usize) -> Vec<u8> {
        let mut writes = vec![0; self.read.len()];
        if !self.enter(depth) {
            return writes;
        }
        match &*e.kind {
            ExprKind::And(es) | ExprKind::Or(es) => {
                let conjunction = matches!(&*e.kind, ExprKind::And(_));
                for e in es {
                    merge(&mut writes, &self.action(e, primed, depth + 1), conjunction);
                }
            }
            ExprKind::If { cond, then, els } => {
                self.value(cond, depth + 1);
                writes = self.action(then, primed, depth + 1);
                merge(&mut writes, &self.action(els, primed, depth + 1), false);
            }
            ExprKind::Case { arms, other } => {
                for (guard, body) in arms {
                    self.value(guard, depth + 1);
                    merge(&mut writes, &self.action(body, primed, depth + 1), false);
                }
                if let Some(body) = other {
                    merge(&mut writes, &self.action(body, primed, depth + 1), false);
                }
            }
            ExprKind::Quant { kind: QuantKind::Exists, bounds, body } => {
                for b in bounds {
                    self.value(&b.set, depth + 1);
                }
                writes = self.action(body, primed, depth + 1);
            }
            ExprKind::Let { body, .. } => writes = self.action(body, primed, depth + 1),
            ExprKind::Apply { op: OpRef::Def(id), args } if self.program.defs[id.idx()].builtin.is_none() => {
                // Parameters are call-by-name. Treat all actuals as reads,
                // including operator actuals, rather than assuming values.
                for arg in args {
                    self.value(arg, depth + 1);
                }
                if !self.expanding.insert(*id) {
                    self.complete = false;
                } else {
                    match &self.program.defs[id.idx()].kind {
                        DefKind::Op(body) => writes = self.action(body, primed, depth + 1),
                        _ => self.value(e, depth + 1),
                    }
                    self.expanding.remove(id);
                }
            }
            ExprKind::Builtin { op: B::Eq, args }
                if args.len() == 2 && (literal(&args[1]) || primed && matches!(&*args[1].kind, ExprKind::Var(_))) =>
            {
                if let Some(v) = target(&args[0], primed) {
                    writes[v.idx()] = 1;
                    if let ExprKind::Var(input) = &*args[1].kind {
                        self.dependencies[v.idx()].push(input.idx());
                    }
                } else {
                    self.value(e, depth + 1);
                }
            }
            ExprKind::Builtin { op: B::Unchanged, args } if primed && args.len() == 1 => {
                writes = self.unchanged(&args[0], depth + 1);
            }
            _ => self.value(e, depth + 1),
        }
        writes
    }

    fn unchanged(&mut self, e: &Expr, depth: usize) -> Vec<u8> {
        let mut writes = vec![0; self.read.len()];
        if !self.enter(depth) {
            return writes;
        }
        match &*e.kind {
            ExprKind::Var(v) => writes[v.idx()] = 1,
            ExprKind::Tuple(es) => {
                for e in es {
                    merge(&mut writes, &self.unchanged(e, depth + 1), true);
                }
            }
            ExprKind::Apply { op: OpRef::Def(id), args } if args.is_empty() && self.program.defs[id.idx()].builtin.is_none() => {
                if !self.expanding.insert(*id) {
                    self.complete = false;
                } else {
                    match &self.program.defs[id.idx()].kind {
                        DefKind::Op(body) => writes = self.unchanged(body, depth + 1),
                        _ => self.value(e, depth + 1),
                    }
                    self.expanding.remove(id);
                }
            }
            _ => self.value(e, depth + 1),
        }
        writes
    }

    fn value(&mut self, e: &Expr, depth: usize) {
        if !self.enter(depth) {
            return;
        }
        match &*e.kind {
            ExprKind::Var(v) => self.read[v.idx()] = true,
            ExprKind::Builtin { op, .. } => self.complete &= !op.is_volatile(),
            ExprKind::Apply { op, .. } | ExprKind::OpArg(op) => self.operator(*op, depth + 1),
            _ => {}
        }
        visit::children(e, &mut |child| self.value(child, depth + 1));
    }

    fn operator(&mut self, op: OpRef, depth: usize) {
        match op {
            OpRef::Builtin(b) => self.complete &= !b.is_volatile(),
            OpRef::Const(_) => self.complete = false,
            // Every supplied operator actual is scanned at its call site.
            OpRef::Param(_) => {}
            OpRef::Def(id) if self.seen.insert(id) => {
                let d = &self.program.defs[id.idx()];
                if let Some(b) = d.builtin {
                    self.complete &= !b.is_volatile();
                    return;
                }
                match &d.kind {
                    DefKind::Op(body) => self.value(body, depth),
                    DefKind::Fn { bounds, body } => {
                        for b in bounds {
                            self.value(&b.set, depth);
                        }
                        self.value(body, depth);
                    }
                    DefKind::Pending => self.complete = false,
                }
            }
            OpRef::Def(_) => {}
        }
    }
}

fn merge(into: &mut [u8], from: &[u8], conjunction: bool) {
    for (a, b) in into.iter_mut().zip(from) {
        *a = if conjunction { (*a + b).min(2) } else { (*a).max(*b) };
    }
}

fn target(e: &Expr, primed: bool) -> Option<VarId> {
    let e = if primed {
        let ExprKind::Builtin { op: B::Prime, args } = &*e.kind else { return None };
        if args.len() != 1 {
            return None;
        }
        &args[0]
    } else {
        e
    };
    match &*e.kind {
        ExprKind::Var(v) => Some(*v),
        _ => None,
    }
}

fn literal(e: &Expr) -> bool {
    match &*e.kind {
        ExprKind::Bool(_) | ExprKind::Str(_) => true,
        ExprKind::Num(n) => i32::try_from(*n).is_ok(),
        _ => false,
    }
}
