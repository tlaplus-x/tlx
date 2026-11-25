//! The frame-scoped lowering state.
//!
//! A frame is entered at every entry point (`lower_action`, `lower_init`,
//! `lower_pred*`, `lower_value_action`), which starts from an empty `Frame`,
//! and around the body of every compiled function (`calls::lower_fn_body`),
//! which swaps the caller's frame out and back in. Grouping the fields means
//! a new frame-scoped field is picked up by every entry point and by the
//! nested frame at once, instead of by a hand-maintained reset list that can
//! fall behind (CODE-12).
//!
//! Everything that outlives a frame - the typing and function registry, the
//! shape interning order, the constant/string caches, the `Repeat`
//! numbering and the statement budget - stays on the `Lowerer` (see the
//! field comments there).
//!
//! Entering a frame swaps the caller's frame out and exiting swaps it back
//! in (`Lowerer::in_frame` for the entry points, which restores on the error
//! exit too; `calls::lower_fn_body` for a compiled function body). A frame
//! accidentally left in place would not be seen by the next entry point -
//! that one swaps it out as well - but restoring keeps one frame's temps and
//! context from being carried along at all.

use std::collections::HashMap;
use std::sync::Arc;

use tlx_sema::hir;

use crate::ir::*;

use super::materialize::Materialized;

/// The state of the frame being lowered: the temps allocated in it with
/// their static metadata and the context of the expression being lowered
/// (`@`, the inlining stack, the assumed result types of the recursive
/// functions being unrolled, and whether the argument of a prime is being
/// lowered).
///
/// `pub` only because it is the `Deref` target of the public `Lowerer`
/// (a less visible type in a public interface is rejected); the module is
/// private, so the frame is not reachable outside the crate.
#[derive(Default)]
pub struct Frame {
    /// Types of the temps allocated in the frame; `lower_fn_body` hands the
    /// temps of a compiled function to its caller.
    pub(super) temps: Vec<Ty>,
    /// Static bounds of integer temps (see `share`).
    pub(super) temp_ranges: HashMap<Temp, (i64, i64)>,
    /// Static bounds of the cardinality of encoded-set temps tighter than
    /// their shape's (see `share` and `iter_bound`).
    pub(super) temp_cards: HashMap<Temp, usize>,
    /// The possible one-word encodings of binder temps that iterate over a
    /// constant list (see `iter_temp`).
    pub(super) temp_words: HashMap<Temp, Arc<[u64]>>,
    /// While lowering a predicate: its materialized definitions.
    pub(super) mat: Option<Materialized>,
    /// The value of `@` while lowering an EXCEPT update.
    pub(super) at: Option<Expr>,
    /// Definitions being inlined (to stop at recursion).
    pub(super) inline_stack: Vec<hir::DefId>,
    /// Assumed result types of the recursive function definitions being
    /// unrolled (the type of an application deeper than the unrolling).
    pub(super) fn_result: Vec<(hir::DefId, Ty)>,
    /// Lowering the argument of a prime: variables read the next state.
    pub(super) primed: bool,
    /// Lowering the function operand of a `FnApp` (TLC's `KeepLazy`):
    /// function constructors must not be built eagerly.
    pub(super) keep_lazy: bool,
}

impl Frame {
    /// Take this frame, leaving an empty one in its place: the body of a
    /// compiled function starts from an empty frame and the caller's frame
    /// is restored when it is done (`calls::lower_fn_body`).
    pub(super) fn swap(&mut self) -> Frame {
        std::mem::take(self)
    }

    /// Where the frame stands now, for a lowering step that has to decide by
    /// lowering and may then decline (`Lowerer::typed_sort_seq`).
    pub(super) fn snapshot(&self) -> FrameMark {
        FrameMark { temps: self.temps.len(), mat: self.mat.clone() }
    }

    /// Undo everything allocated or materialized since `mark`: a declined
    /// step must leave the frame exactly as it was, or the temps nobody
    /// reads stay in it and a materialized definition its result never uses
    /// is still computed once per evaluation.
    pub(super) fn restore(&mut self, mark: FrameMark) {
        self.temps.truncate(mark.temps);
        self.temp_ranges.retain(|t, _| (*t as usize) < mark.temps);
        self.temp_cards.retain(|t, _| (*t as usize) < mark.temps);
        self.temp_words.retain(|t, _| (*t as usize) < mark.temps);
        self.mat = mark.mat;
    }
}

/// See `Frame::snapshot`.
pub(super) struct FrameMark {
    temps: usize,
    mat: Option<Materialized>,
}
