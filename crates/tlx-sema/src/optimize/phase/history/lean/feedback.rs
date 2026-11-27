//! Substitute proved summary predicates into otherwise history-free consumers.
//! Each hole is a Boolean, never a raw history or an assumed preservation fact.
use super::super::super::max_local;
use super::Emitter;
use crate::{builtins::Builtin as B, hir::*, visit};

impl Emitter<'_> {
    pub(in super::super::super) fn value(&mut self, e: &Expr, primed: bool) -> Option<String> {
        if self.independent(e) {
            let next = if primed { "d" } else { "c" };
            return Some(format!("(sem.value {} c {next} choice.2)", self.atom(e)?));
        }
        if !primed {
            return None;
        }
        self.feedback(e, "Value")
    }

    pub(super) fn feedback(&mut self, e: &Expr, kind: &str) -> Option<String> {
        let local = max_local(e);
        let mut next_local = local.checked_add(1)?;
        let mut holes = vec![];
        let mut remaining = 10_000;
        let masked = self.mask_feedback(e, &mut next_local, &mut holes, &mut remaining)?;
        if holes.is_empty() || !self.independent(&masked) {
            return None;
        }
        let id = self.atoms.len();
        self.atoms.push(format!("Summary consumer HIR: {masked:#?}\nBoolean holes (in argument order): {holes:#?}"));
        let args = holes.iter().map(|(_, p)| format!("decide ({p})")).collect::<Vec<_>>().join(", ");
        Some(if kind == "Observe" {
            format!("(sem.feedbackObserve {id} c [{args}])")
        } else {
            format!("(sem.feedback{kind} {id} c d choice.2 [{args}])")
        })
    }

    fn mask_feedback(&mut self, e: &Expr, next: &mut u32, holes: &mut Vec<(LocalId, String)>, remaining: &mut usize) -> Option<Expr> {
        *remaining = remaining.checked_sub(1)?;
        if self.independent(e) {
            return Some(e.clone());
        }
        if let Some(predicate) = self.summary_read(e) {
            if holes.len() >= 256 {
                return None;
            }
            let local = LocalId(*next);
            *next = next.checked_add(1)?;
            holes.push((local, predicate));
            return Some(Expr::new(ExprKind::Local(local), e.span));
        }
        // Summary predicates inspect the current history. Dependent binders
        // and next-state reads require separate lowering, not opaque leaves.
        match &*e.kind {
            ExprKind::Quant { .. }
            | ExprKind::QuantUnbounded { .. }
            | ExprKind::FnConstruct { .. }
            | ExprKind::SetFilter { .. }
            | ExprKind::SetMap { .. }
            | ExprKind::Choose { .. }
            | ExprKind::Lambda { .. }
            | ExprKind::TemporalQuant { .. }
            | ExprKind::Builtin { op: B::Prime, .. } => None,
            _ => {
                let mut result = e.clone();
                let mut valid = true;
                visit::children_mut(&mut result, &mut |child| {
                    if let Some(masked) = self.mask_feedback(child, next, holes, remaining) {
                        *child = masked;
                    } else {
                        valid = false;
                    }
                });
                (valid && self.independent(&result)).then_some(result)
            }
        }
    }
}
