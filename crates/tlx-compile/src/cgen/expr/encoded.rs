//! Dispatch of the encoded-value expression families of C generation: the map family to
//! `maps.rs`, the value family of slices, indexing, EXCEPT updates, loop builders and
//! sequence operations to `sequences.rs`, and the set family to `sets.rs`.

use super::super::{CGen, R};
use crate::ir::*;

impl CGen<'_> {
    pub(super) fn expr_encoded(&mut self, e: &Expr) -> R<String> {
        match &*e.kind {
            // The value family: slices, indexing, EXCEPT updates, the loop builders
            // and the sequence operations (dispatched to `sequences.rs`).
            ExprKind::Slice { .. }
            | ExprKind::Index { .. }
            | ExprKind::ExceptAt { .. }
            | ExprKind::ExceptIndex { .. }
            | ExprKind::Filter { .. }
            | ExprKind::MapSet { .. }
            | ExprKind::Fold { .. }
            | ExprKind::UnionFold { .. }
            | ExprKind::Collect { .. }
            | ExprKind::SeqLen(_)
            | ExprKind::SeqIndex { .. }
            | ExprKind::SeqTail { .. }
            | ExprKind::SeqSub { .. }
            | ExprKind::SeqFilter { .. }
            | ExprKind::SeqConcat { .. }
            | ExprKind::SeqAppend { .. } => self.seq_expr(e),
            // The map family (dispatched to `maps.rs`).
            ExprKind::MapGet { .. } | ExprKind::MapPut { .. } | ExprKind::MapBuild { .. } | ExprKind::MapMerge(..) => self.map_expr(e),
            // The set family: bit sets, sorted sets, the ranks, the recodes, union
            // field access and the boxed builders (dispatched to `sets.rs`).
            ExprKind::BitMember { .. }
            | ExprKind::BitSetOp(..)
            | ExprKind::BitCard(..)
            | ExprKind::Rank(..)
            | ExprKind::Concat(..)
            | ExprKind::Pack { .. }
            | ExprKind::BitSet(..)
            | ExprKind::UnionField { .. }
            | ExprKind::UnionFieldInt { .. }
            | ExprKind::SortedMember { .. }
            | ExprKind::Recode { .. }
            | ExprKind::RankUnion { .. }
            | ExprKind::Lookup { .. }
            | ExprKind::RankFlat { .. }
            | ExprKind::SortedInsert { .. }
            | ExprKind::SortedOp { .. } => self.set_expr(e),
            _ => unreachable!("not an encoded-value expression"),
        }
    }
}
