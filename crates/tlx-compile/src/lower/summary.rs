//! Immutable summaries of one compiled-function graph. State-buffer requirements
//! are separate from memo reads: ENABLED owns its next-state buffer, and an
//! interpreter fallback can have known memo reads without requiring IR buffers.

use crate::enc::mixed::Reads;
use crate::ir::{Expr, ExprKind, FnDef};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Effects {
    pub volatile: bool,
    pub beyond_output: bool,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct StateContract {
    pub current: bool,
    pub next: Vec<bool>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Summary {
    pub reads: Option<Reads>,
    pub effects: Effects,
    pub context: StateContract,
    pub enabled: bool,
    pub operator_args: bool,
    pub recursive: bool,
    /// Some dependency could not be resolved; absence flags are not proofs.
    pub unknown: bool,
}

impl Summary {
    pub fn empty(nvars: usize) -> Self {
        Self {
            reads: Some(Reads::default()),
            effects: Effects::default(),
            context: StateContract { current: false, next: vec![false; nvars] },
            enabled: false,
            operator_args: false,
            recursive: false,
            unknown: false,
        }
    }

    pub fn unknown(nvars: usize) -> Self {
        let mut s = Self::empty(nvars);
        s.reads = None;
        s.unknown = true;
        s.effects = Effects { volatile: true, beyond_output: true };
        s
    }

    fn join(&mut self, other: &Self, external: bool) {
        match (&mut self.reads, &other.reads) {
            (Some(a), Some(b)) => {
                for (a, b) in [(&mut a.cur, &b.cur), (&mut a.next, &b.next)] {
                    a.extend(b);
                    a.sort_unstable();
                    a.dedup();
                }
            }
            (_, None) => self.reads = None,
            _ => {}
        }
        self.effects.volatile |= other.effects.volatile;
        self.effects.beyond_output |= other.effects.beyond_output;
        self.context.current |= other.context.current;
        if external {
            for (a, b) in self.context.next.iter_mut().zip(&other.context.next) {
                *a |= b;
            }
        }
        self.enabled |= other.enabled;
        self.operator_args |= other.operator_args;
        self.unknown |= other.unknown;
        self.recursive |= other.recursive;
    }
}

/// One edge also records whether the callee uses the caller's next-state buffer.
#[derive(Clone, Copy)]
struct Edge {
    callee: usize,
    external: bool,
}

/// Collect local facts once. HIR/environment semantics belong to the caller's
/// `leaf` provider; following compiled calls and ENABLED scopes belongs here.
fn scan(e: &Expr, external: bool, out: &mut Summary, edges: &mut Vec<Edge>, leaf: &impl Fn(&Expr) -> Summary) {
    out.join(&leaf(e), external);
    match &*e.kind {
        ExprKind::Var(v) => {
            out.context.current = true;
            if let Some(r) = &mut out.reads {
                r.cur.push(*v);
            }
        }
        ExprKind::NextVar(v) => {
            if external {
                if let Some(bit) = out.context.next.get_mut(*v as usize) {
                    *bit = true;
                }
            }
            if let Some(r) = &mut out.reads {
                r.next.push(*v);
            }
        }
        ExprKind::Call { func, .. } => edges.push(Edge { callee: *func as usize, external }),
        ExprKind::Enabled(s) => {
            out.enabled = true;
            out.reads = None;
            out.unknown = true;
            s.for_each_expr_deep(&mut |e| scan(e, false, out, edges, leaf));
            return;
        }
        ExprKind::Interp { .. }
        | ExprKind::Const(_)
        | ExprKind::ConstWords(_)
        | ExprKind::Temp(_)
        | ExprKind::Not(_)
        | ExprKind::And(_)
        | ExprKind::Or(_)
        | ExprKind::If(..)
        | ExprKind::IntBin(..)
        | ExprKind::IntCmp(..)
        | ExprKind::Neg(_)
        | ExprKind::Eq(..)
        | ExprKind::Convert(_)
        | ExprKind::Exists { .. }
        | ExprKind::Forall { .. }
        | ExprKind::Choose { .. }
        | ExprKind::Let { .. }
        | ExprKind::Apply { .. }
        | ExprKind::ValField { .. }
        | ExprKind::Slice { .. }
        | ExprKind::Index { .. }
        | ExprKind::ExceptAt { .. }
        | ExprKind::ExceptIndex { .. }
        | ExprKind::BitMember { .. }
        | ExprKind::BitSetOp { .. }
        | ExprKind::BitCard(..)
        | ExprKind::Rank { .. }
        | ExprKind::Concat(_)
        | ExprKind::Pack { .. }
        | ExprKind::BitSet(_)
        | ExprKind::SeqLen(_)
        | ExprKind::SeqIndex { .. }
        | ExprKind::SeqTail { .. }
        | ExprKind::SeqAppend { .. }
        | ExprKind::SeqSub { .. }
        | ExprKind::SortedOp { .. }
        | ExprKind::SeqFilter { .. }
        | ExprKind::SeqConcat { .. }
        | ExprKind::UnionField { .. }
        | ExprKind::UnionFieldInt { .. }
        | ExprKind::ConstElems { .. }
        | ExprKind::IntRange { .. }
        | ExprKind::Subsets { .. }
        | ExprKind::Fail(_)
        | ExprKind::Filter { .. }
        | ExprKind::MapSet { .. }
        | ExprKind::Collect { .. }
        | ExprKind::Fold { .. }
        | ExprKind::UnionFold { .. }
        | ExprKind::RankFlat { .. }
        | ExprKind::Recode { .. }
        | ExprKind::RankUnion { .. }
        | ExprKind::Lookup { .. }
        | ExprKind::SortedMember { .. }
        | ExprKind::SortedInsert { .. }
        | ExprKind::MapGet { .. }
        | ExprKind::MapPut { .. }
        | ExprKind::MapBuild { .. }
        | ExprKind::MapMerge { .. }
        | ExprKind::Tuple(_)
        | ExprKind::ValOp { .. }
        | ExprKind::RefOp { .. }
        | ExprKind::RefElems(_)
        | ExprKind::OrderedSet { .. } => {}
    }
    e.for_each_child(&mut |e| scan(e, external, out, edges, leaf));
}

/// Private storage makes summaries immutable after the fixed point completes.
pub(crate) struct Functions {
    summaries: Vec<Summary>,
    nvars: usize,
}

impl Functions {
    pub fn new(funcs: &[FnDef], nvars: usize, leaf: impl Fn(&Expr) -> Summary, pending: impl Fn(usize) -> Option<Summary>) -> Self {
        let mut summaries = Vec::new();
        let mut edges = Vec::new();
        for (i, f) in funcs.iter().enumerate() {
            let mut local = pending(i).unwrap_or_else(|| Summary::empty(nvars));
            let mut calls = Vec::new();
            if pending(i).is_none() {
                scan(&f.body, true, &mut local, &mut calls, &leaf);
            }
            summaries.push(local);
            edges.push(calls);
        }
        for (i, summary) in summaries.iter_mut().enumerate() {
            let mut seen = vec![false; funcs.len()];
            let mut todo: Vec<_> = edges[i].iter().map(|e| e.callee).collect();
            while let Some(j) = todo.pop() {
                if j == i {
                    summary.recursive = true;
                    break;
                }
                if j < seen.len() && !std::mem::replace(&mut seen[j], true) {
                    todo.extend(edges[j].iter().map(|e| e.callee));
                }
            }
        }
        loop {
            let mut changed = false;
            for (i, calls) in edges.iter().enumerate() {
                let before = summaries[i].clone();
                // Normalize direct reads even in a function with no calls.
                summaries[i].join(&Summary::empty(nvars), true);
                for edge in calls {
                    let callee = summaries.get(edge.callee).cloned().unwrap_or_else(|| Summary::unknown(nvars));
                    summaries[i].join(&callee, edge.external);
                }
                changed |= before != summaries[i];
            }
            if !changed {
                break;
            }
        }
        Self { summaries, nvars }
    }

    pub fn expression(&self, e: &Expr, leaf: impl Fn(&Expr) -> Summary) -> Summary {
        let mut out = Summary::empty(self.nvars);
        let mut edges = Vec::new();
        scan(e, true, &mut out, &mut edges, &leaf);
        for edge in edges {
            let unknown = Summary::unknown(self.nvars);
            out.join(self.summaries.get(edge.callee).unwrap_or(&unknown), edge.external);
        }
        out.join(&Summary::empty(self.nvars), true);
        out
    }

    pub fn contracts(&self) -> Vec<StateContract> {
        self.summaries.iter().map(|s| s.context.clone()).collect()
    }
}

impl super::Lowerer<'_> {
    pub(super) fn summary_leaf(&self, e: &Expr) -> Summary {
        // A local provider has no IR buffer requirements; scan derives them.
        let mut s = Summary::empty(0);
        let fallback = self.fallback_facts(e);
        s.reads = fallback.reads;
        s.unknown = s.reads.is_none();
        s.enabled = fallback.enabled;
        s.operator_args = fallback.operator_args;
        s.recursive = fallback.recursive;
        s.effects = Effects { volatile: self.local_volatile(e, false), beyond_output: self.local_volatile(e, true) };
        if let ExprKind::Interp { deferred, .. } = &*e.kind {
            s.operator_args |= deferred.iter().any(|d| matches!(d, crate::ir::Deferred::OpRef(..) | crate::ir::Deferred::Lambda(..)));
        }
        s
    }

    pub(crate) fn expression_summary(&self, e: &Expr) -> Summary {
        if self.typing.summary.borrow().is_none() {
            let functions = Functions::new(
                &self.typing.funcs,
                self.nvars(),
                |e| self.summary_leaf(e),
                |i| {
                    self.pending_fn(i as u32).map(|d| {
                        let mut s = Summary::unknown(self.nvars());
                        let volatile = self.def_volatile(d);
                        s.effects = Effects { volatile, beyond_output: volatile };
                        s
                    })
                },
            );
            *self.typing.summary.borrow_mut() = Some(std::rc::Rc::new(functions));
        }
        let functions = self.typing.summary.borrow().as_ref().unwrap().clone();
        functions.expression(e, |e| self.summary_leaf(e))
    }
}

/// Lowering's mutable typing, with automatic invalidation on *any* mutable
/// access. Even direct edits to the public function vector cannot leave stale
/// summaries behind. A frozen native-planning borrow reuses one immutable graph.
pub struct AnalyzedTyping {
    typing: crate::types::Typing,
    summary: std::cell::RefCell<Option<std::rc::Rc<Functions>>>,
}

impl AnalyzedTyping {
    pub(super) fn new(typing: crate::types::Typing) -> Self {
        Self { typing, summary: Default::default() }
    }
    pub(crate) fn cached_contracts(&self) -> Option<Vec<StateContract>> {
        self.summary.borrow().as_ref().map(|s| s.contracts())
    }
    pub(super) fn into_inner(self) -> crate::types::Typing {
        self.typing
    }
    pub(super) fn invalidate(&mut self) {
        self.summary.get_mut().take();
        self.typing.funcs_changed();
    }
}

impl std::ops::Deref for AnalyzedTyping {
    type Target = crate::types::Typing;
    fn deref(&self) -> &Self::Target {
        &self.typing
    }
}
impl std::ops::DerefMut for AnalyzedTyping {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.invalidate();
        &mut self.typing
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Stmt, Ty};

    fn expr(kind: ExprKind) -> Expr {
        Expr::new(Ty::Int, kind)
    }
    fn call(func: u32) -> Expr {
        expr(ExprKind::Call { func, args: vec![] })
    }
    fn function(body: Expr) -> FnDef {
        FnDef { name: "f".into(), params: vec![], temps: vec![], ret: Ty::Int, body, budgeted: false }
    }
    fn leaf(e: &Expr) -> Summary {
        let mut s = Summary::empty(2);
        if let ExprKind::ValOp { op, .. } = &*e.kind {
            s.effects.volatile = op.is_volatile();
            s.effects.beyond_output = op.is_volatile() && !op.is_output();
        }
        s
    }

    #[test]
    fn recursive_fixed_point_propagates_reads_and_effects() {
        let funcs = vec![
            function(call(1)),
            function(expr(ExprKind::Tuple(vec![
                call(0),
                expr(ExprKind::Var(1)),
                expr(ExprKind::NextVar(0)),
                expr(ExprKind::ValOp { op: tlx_sema::builtins::Builtin::PrintT, args: vec![] }),
            ]))),
        ];
        let graph = Functions::new(&funcs, 2, leaf, |_| None);
        for s in &graph.summaries {
            assert_eq!(s.reads, Some(Reads { cur: vec![1], next: vec![0] }));
            assert_eq!(s.effects, Effects { volatile: true, beyond_output: false });
            assert_eq!(s.context, StateContract { current: true, next: vec![true, false] });
            assert!(s.recursive);
        }
    }

    #[test]
    fn enabled_scopes_next_buffers_but_keeps_current_requirements() {
        let funcs = vec![
            function(expr(ExprKind::Enabled(Box::new(Stmt::Guard { cond: call(1), then: Box::new(Stmt::Emit) })))),
            function(expr(ExprKind::Tuple(vec![expr(ExprKind::Var(1)), expr(ExprKind::NextVar(0))]))),
        ];
        let graph = Functions::new(&funcs, 2, leaf, |_| None);
        assert_eq!(graph.summaries[0].reads, None);
        assert!(graph.summaries[0].enabled);
        assert_eq!(graph.summaries[0].context, StateContract { current: true, next: vec![false, false] });
        assert_eq!(graph.summaries[1].context.next, vec![true, false]);
    }

    #[test]
    fn missing_and_in_progress_functions_remain_conservative() {
        let funcs = vec![function(call(9)), function(expr(ExprKind::Var(0)))];
        let graph = Functions::new(&funcs, 2, leaf, |i| (i == 1).then(|| Summary::unknown(2)));
        for i in [0, 1, 9] {
            let s = graph.expression(&call(i), leaf);
            assert_eq!(s.reads, None);
            assert!(s.unknown);
            assert!(s.effects.volatile && s.effects.beyond_output);
        }
    }

    #[test]
    fn mutable_typing_access_invalidates_the_snapshot() {
        let typing = crate::types::Typing::new(std::sync::Arc::new(tlx_layout::Layout::new(vec![])));
        let mut t = AnalyzedTyping::new(typing);
        *t.summary.borrow_mut() = Some(std::rc::Rc::new(Functions::new(&[], 0, |_| Summary::empty(0), |_| None)));
        let _ = &t.funcs;
        assert!(t.summary.borrow().is_some());
        assert!(crate::verify::typing(&t).is_ok());
        assert!(t.verified_cache().get().is_some());
        t.funcs.push(function(call(0)));
        assert!(t.summary.borrow().is_none());
        assert!(t.verified_cache().get().is_none());
        assert!(crate::verify::typing(&t).is_ok());
        // A same-length replacement must invalidate the verifier too.
        t.funcs[0].body = call(9);
        assert!(crate::verify::typing(&t).is_err());
    }
}
