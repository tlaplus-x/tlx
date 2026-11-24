//! Boxed regions of the IR (docs/mixed-mode.md §4).
//!
//! A *region* is a maximal subtree of boxed nodes (the `Coverage`
//! definition: `Ty::Val` values and the operations on them, plus the
//! conversions into and out of `Val`): in mixed mode the host evaluates it
//! as a whole while the typed rest runs natively. This module shapes the
//! regions during lowering so that they are cheap to hand to the host:
//!
//! - **R3** (`regions_post`): a boxed subtree whose nodes are all boxed and
//!   that contains an interpreter fallback is replaced by one `Interp` of
//!   its HIR expression, so that the interpreter keeps its laziness (a
//!   function definition applied to an argument, `SUBSET`/`CHOOSE`
//!   structures) instead of the IR building intermediate values.
//! - **R9, widening** (`regions_post`): a binding construct (`\E`, `\A`,
//!   `CHOOSE`, filters, set maps, function construction, folds) whose body
//!   contains an interpreter fallback that depends on the bound element is
//!   replaced by one `Interp` of the whole construct: the interpreter
//!   evaluates it at once instead of being called once per element. A
//!   fallback that is itself an iteration (`iteration`) is not one of
//!   those: it is the loop an inner widening already handed to the host,
//!   and folding the enclosing construct into it would discard the
//!   enclosing loop's native iteration (hoisting treats a nested loop the
//!   same way, `extract_invariant`).
//! - **R9, hoisting** (`hoist_stmt` / `hoist_pred`): a pure region in the
//!   body of a binding construct that does not depend on the element is
//!   computed once before the construct (when its source is not empty).
//! - **R4**: purity of a region (no side-effecting / nondeterministic
//!   builtin, `ir_volatile`).
//!
//! The transforms never create an interpreter fallback in a function that
//! has none (whether a function contains one decides how the compiled tier
//! runs it), and are disabled by `Lowerer::regions` (tests).
//!
//! `Lowerer::action_regions` / `pred_regions` list the regions of lowered
//! functions (root, inputs, context, statically assigned next-state
//! variables, purity, read set) for `enc::mixed::RegionTable`; code
//! generation decides the final region roots (`enc::mixed`).

use std::collections::HashSet;
use std::sync::atomic::Ordering;

use tlx_base::diag::{self, Topic};
use tlx_sema::hir::{self, ExprKind as H};

use super::*;
use crate::enc::mixed::{Reads, Region, RegionCtx, RegionInfo};

// ---------------------------------------------------------------------------
// classification

/// A leaf: no computation (an input of a region rather than part of it).
fn is_leaf(e: &Expr) -> bool {
    matches!(
        &*e.kind,
        ExprKind::Const(_) | ExprKind::ConstWords(_) | ExprKind::Var(_) | ExprKind::NextVar(_) | ExprKind::Temp(_) | ExprKind::Fail(_)
    )
}

/// A node computing on boxed values (the `Coverage` definition, plus the
/// conversions into and out of `Val` and equality of boxed values).
pub fn is_boxed(e: &Expr) -> bool {
    use ExprKind as K;
    match &*e.kind {
        K::Interp { .. } | K::ValOp { .. } | K::Apply(..) | K::ValField(..) | K::Tuple(_) => true,
        K::Convert(x) => x.ty == Ty::Val || e.ty == Ty::Val,
        K::Eq(a, _) => a.ty == Ty::Val,
        K::ConstElems { .. } | K::IntRange(..) | K::Subsets(_) | K::OrderedSet { .. } | K::RefElems(_) => false,
        _ => e.ty == Ty::Val && !is_leaf(e),
    }
}

/// The parts of a binding construct of an expression: the bound temp, the
/// iteration source and the expressions evaluated per element (in order).
fn loop_parts(e: &Expr) -> Option<(Temp, &Expr, Vec<&Expr>)> {
    use ExprKind as K;
    Some(match &*e.kind {
        K::Exists { bind, set, body }
        | K::Forall { bind, set, body }
        | K::Choose { bind, set, body }
        | K::Fold { bind, set, body, .. }
        | K::UnionFold { bind, set, body } => (*bind, set, vec![body]),
        K::Filter { bind, set, pred } => (*bind, set, vec![pred]),
        K::SeqFilter { bind, seq, pred, .. } => (*bind, seq, vec![pred]),
        K::Collect { bind, set, elem } => (*bind, set, vec![elem]),
        K::MapSet { bind, set, elem, cond } => (*bind, set, cond.iter().chain([elem]).collect()),
        K::MapBuild { bind, set, rank, value, .. } => (*bind, set, vec![rank, value]),
        _ => return None,
    })
}

/// `loop_parts` with mutable access; the bodies are the ones evaluated on
/// every element (for a `MapSet` with a condition, only the condition).
fn loop_parts_mut(e: &mut Expr) -> Option<(Temp, &mut Expr, Vec<&mut Expr>)> {
    use ExprKind as K;
    Some(match &mut *e.kind {
        K::Exists { bind, set, body }
        | K::Forall { bind, set, body }
        | K::Choose { bind, set, body }
        | K::Fold { bind, set, body, .. }
        | K::UnionFold { bind, set, body } => (*bind, set, vec![body]),
        K::Filter { bind, set, pred } => (*bind, set, vec![pred]),
        K::SeqFilter { bind, seq, pred, .. } => (*bind, seq, vec![pred]),
        K::Collect { bind, set, elem } => (*bind, set, vec![elem]),
        K::MapSet { bind, set, elem, cond } => match cond {
            Some(c) => (*bind, set, vec![c]),
            None => (*bind, set, vec![elem]),
        },
        K::MapBuild { bind, set, rank, value, .. } => (*bind, set, vec![rank, value]),
        _ => return None,
    })
}

/// Temps bound in `e` (by binders, `Let`s and the statements of `ENABLED`).
fn bound_temps(e: &Expr, out: &mut HashSet<Temp>) {
    use ExprKind as K;
    match &*e.kind {
        K::Let { temp, .. } => {
            out.insert(*temp);
        }
        K::Enabled(s) => stmt_bound_temps(s, out),
        _ => {
            if let Some((b, _, _)) = loop_parts(e) {
                out.insert(b);
            }
        }
    }
    if !matches!(&*e.kind, K::Enabled(_)) {
        e.for_each_child(&mut |c| bound_temps(c, out));
    }
}

pub(crate) fn stmt_bound_temps(s: &Stmt, out: &mut HashSet<Temp>) {
    match s {
        Stmt::Let { temp, .. } => {
            out.insert(*temp);
        }
        Stmt::ForEach { bind, .. } | Stmt::Repeat { bind, .. } => {
            out.insert(*bind);
        }
        _ => {}
    }
    if let Some(e) = s.expr() {
        bound_temps(e, out);
    }
    s.for_each_sub_stmt(&mut |b| stmt_bound_temps(b, out));
}

/// Temps `e` reads that are not bound inside it, in order of first
/// occurrence (evaluation order): the inputs of `e` as a region.
pub fn free_temps(e: &Expr) -> Vec<Temp> {
    let mut used = Vec::new();
    used_temps(e, &mut used);
    let mut bound = HashSet::new();
    bound_temps(e, &mut bound);
    used.retain(|t| !bound.contains(t));
    used
}

fn used_temps(e: &Expr, out: &mut Vec<Temp>) {
    if let ExprKind::Temp(t) = &*e.kind {
        if !out.contains(t) {
            out.push(*t);
        }
    }
    e.for_each_child(&mut |c| used_temps(c, out));
}

/// Number of boxed nodes in `e` (see `is_boxed`).
pub(super) fn count_boxed(e: &Expr) -> usize {
    let mut n = is_boxed(e) as usize;
    e.for_each_child(&mut |c| n += count_boxed(c));
    n
}

/// Number of interpreter fallbacks in `e`.
fn count_interp(e: &Expr) -> usize {
    let mut n = matches!(&*e.kind, ExprKind::Interp { .. }) as usize;
    e.for_each_child(&mut |c| n += count_interp(c));
    n
}

/// A typed expression worth computing once outside a binding construct
/// (`hoist_typed`): it loops or calls a compiled function, and it has no
/// boxed node (regions are R9's) or `ENABLED`.
fn typed_invariant(e: &Expr) -> bool {
    fn clean(e: &Expr, costly: &mut bool) -> bool {
        use ExprKind as K;
        if e.ty == Ty::Val || is_boxed(e) || matches!(&*e.kind, K::Enabled(_)) {
            return false;
        }
        *costly |= loop_parts(e).is_some() || matches!(&*e.kind, K::Call { .. });
        let mut ok = true;
        e.for_each_child(&mut |c| ok = ok && clean(c, costly));
        ok
    }
    let mut costly = false;
    !is_leaf(e) && clean(e, &mut costly) && costly
}

/// Whether `f` holds for one of the maximal boxed subtrees of `e` (not
/// looking inside them). With `shield`, nested iterations ([`iteration`])
/// are not entered: a region in the body of a construct inside `e` is
/// evaluated once per element of *that* construct, not of the construct `e`
/// is the body of.
fn any_region(e: &Expr, f: &mut dyn FnMut(&Expr) -> bool, shield: bool) -> bool {
    if shield && iteration(e) {
        return false;
    }
    if is_boxed(e) {
        return f(e);
    }
    let mut found = false;
    e.for_each_child(&mut |c| found = found || any_region(c, f, shield));
    found
}

/// Whether `e` is a whole iteration: a binding construct, or an
/// interpreter fallback of one ([`hir_iteration`]) — what an inner R9
/// widening leaves behind, with or without the conversion into the
/// construct's representation.
///
/// Widening must not cascade through a tower of native loops: the host
/// call an inner widening made evaluates that inner loop, and folding the
/// enclosing construct into it as well would discard the enclosing loop's
/// native iteration for nothing (IsConflictSerializable's
/// `UNION {findCycleNodes(node, {}) : node \in startPoints}`: seven nested
/// unions over the unrolled recursion, all replaced by one fallback, which
/// then runs the whole recursive graph search in the interpreter).
fn iteration(e: &Expr) -> bool {
    if loop_parts(e).is_some() {
        return true;
    }
    let inner = match &*e.kind {
        ExprKind::Convert(y) => y,
        _ => e,
    };
    matches!(&*inner.kind, ExprKind::Interp { expr, .. } if hir_iteration(expr))
}

/// A whole iteration in the HIR: the shapes R9 widening folds into one
/// interpreter fallback — the quantifiers, `CHOOSE`, filters, set maps,
/// function constructors and the folds the lowering turns into an IR loop
/// (`lower::fold`). `UNION S` is the iteration of a set map with the union
/// around it (the lowering peels it, `big_union_mapped`).
fn hir_iteration(e: &hir::Expr) -> bool {
    use hir::ExprKind as H;
    use tlx_sema::builtins::Builtin as B;
    match &*e.kind {
        H::Quant { .. }
        | H::QuantUnbounded { .. }
        | H::TemporalQuant { .. }
        | H::Choose { .. }
        | H::SetFilter { .. }
        | H::SetMap { .. }
        | H::FnConstruct { .. }
        | H::Builtin { op: B::MapThenFoldSet | B::FoldSet | B::FoldFunctionOnSet | B::FoldFunction | B::FoldSeq, .. } => true,
        H::Builtin { op: B::Union, args } => matches!(&args[..], [a] if hir_iteration(a)),
        _ => false,
    }
}

/// The node one R9 widening replaces: `x` under the `Let`s and conversions
/// `widen_candidate` peels.
fn widened_root(x: &Expr) -> &Expr {
    let mut root = x;
    loop {
        match &*root.kind {
            ExprKind::Let { body, .. } => root = body,
            ExprKind::Convert(y) | ExprKind::Not(y) => root = y,
            _ => break,
        }
    }
    root
}

/// Widenings performed in this process, for the `TLX_COVERAGE` diagnostic
/// (`widen #N`): the number and the kind of the lowered sub-expressions
/// region formation replaced (`widened_root`'s label). A layout restart
/// lowers the program again, so the count then starts from the running
/// total, not from zero.
static WIDENED: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// R3: `x` is a boxed operation whose subtree is made of boxed operations,
/// boolean connectives and leaves only, with at least one interpreter
/// fallback (and something else: a lone fallback is already one).
fn foldable(x: &Expr) -> bool {
    let root = match &*x.kind {
        ExprKind::Convert(y) if y.ty == Ty::Val => y,
        _ => x,
    };
    if !is_boxed(root) || matches!(&*root.kind, ExprKind::Interp { .. }) || loop_parts(root).is_some() {
        return false;
    }
    let mut interps = 0;
    all_boxed(root, &mut interps) && interps > 0
}

fn all_boxed(e: &Expr, interps: &mut usize) -> bool {
    use ExprKind as K;
    match &*e.kind {
        K::Interp { .. } => {
            *interps += 1;
            true
        }
        _ if is_leaf(e) => true,
        K::Convert(_)
        | K::Not(_)
        | K::And(_)
        | K::Or(_)
        | K::If(..)
        | K::Eq(..)
        | K::Let { .. }
        | K::ValOp { .. }
        | K::Apply(..)
        | K::ValField(..)
        | K::Tuple(_) => {
            let mut ok = true;
            e.for_each_child(&mut |c| ok = ok && all_boxed(c, interps));
            ok
        }
        _ => false,
    }
}

/// R9: some binding construct in `x` (outside interpreter fallbacks) has in
/// its body a region with an interpreter fallback that depends on the
/// bound element (or on temps bound inside the body). With `shield`, a
/// region inside a nested iteration ([`iteration`]) does not count: a
/// fallback that the whole element body already is — or that an inner
/// widening made the whole inner loop — is the element's work only through
/// that loop, which is evaluated natively.
fn has_dependent_loop_region(x: &Expr, shield: bool) -> bool {
    if matches!(&*x.kind, ExprKind::Interp { .. }) {
        return false;
    }
    if let Some((bind, _, bodies)) = loop_parts(x) {
        let mut bound = HashSet::from([bind]);
        for b in &bodies {
            bound_temps(b, &mut bound);
        }
        let mut dependent = |r: &Expr| count_interp(r) > 0 && free_temps(r).iter().any(|t| bound.contains(t));
        // A body that is one whole iteration has no element work of its own:
        // the host call it makes *is* the element's work, so this construct
        // folds it too (the shield only covers an iteration nested in a body
        // that does something else around it).
        if shield && bodies.iter().any(|b| iteration(b)) {
            return true;
        }
        if bodies.iter().any(|b| any_region(b, &mut dependent, shield)) {
            return true;
        }
    }
    let mut found = false;
    x.for_each_child(&mut |c| {
        // A nested iteration is a construct of its own: its element work is
        // not this construct's, so with `shield` it is not entered (a boxed
        // node in `x` that is not an iteration is still searched).
        found = found || !(shield && iteration(c)) && has_dependent_loop_region(c, shield);
    });
    found
}

/// R9 widening applies to `x`: `(candidate, widen)`. `candidate` is
/// whether the construct qualifies — a binding construct (under `Let`s,
/// conversions and negations) with a dependent fallback region in its body,
/// or a boxed node with such a construct inside (larger typed expressions
/// that contain one, e.g. a conjunction of a typed conjunct and such a
/// quantifier, do not qualify: their typed parts stay typed). `widen` is
/// the subset whose dependent region is not a nested iteration
/// ([`iteration`]): those keep their native iteration.
///
/// The split of the pair matters: `candidate` also decides whether the
/// construct goes through the memoizable-source exception
/// ([`Lowerer::split_memoizable`]), which applies whatever the widening
/// decision is (Quicksort's `\E newseq \in Partitions(I, p, seq)` binds its
/// source region once instead of once per element either way).
fn widen_candidate(x: &Expr) -> (bool, bool) {
    let mut root = x;
    loop {
        match &*root.kind {
            ExprKind::Let { body, .. } => root = body,
            ExprKind::Convert(y) | ExprKind::Not(y) => root = y,
            _ => break,
        }
    }
    if !(loop_parts(root).is_some() || is_boxed(root)) {
        return (false, false);
    }
    let candidate = has_dependent_loop_region(root, false);
    let widen = has_dependent_loop_region(root, true);
    (candidate, widen)
}

/// Whether `x` has both an interpreter fallback and a binding construct
/// (outside fallbacks): a cheap pre-check of `has_dependent_loop_region`.
fn has_interp_and_loop(x: &Expr) -> (bool, bool) {
    if matches!(&*x.kind, ExprKind::Interp { .. }) {
        return (true, false);
    }
    let mut acc = (false, loop_parts(x).is_some());
    x.for_each_child(&mut |c| {
        if !(acc.0 && acc.1) {
            let (i, l) = has_interp_and_loop(c);
            acc = (acc.0 || i, acc.1 || l);
        }
    });
    acc
}

/// Whether the HIR expression mentions `@` (bound only while lowering an
/// EXCEPT, not in the interpreter's environment).
fn mentions_at(e: &hir::Expr) -> bool {
    let mut found = matches!(&*e.kind, H::At);
    if !found {
        tlx_sema::visit::children(e, &mut |c| found = found || mentions_at(c));
    }
    found
}

/// `w` (a boxed value) in representation `ty`.
fn in_repr(w: Expr, ty: Ty) -> Expr {
    if ty == Ty::Val {
        w
    } else {
        Expr::new(ty, ExprKind::Convert(w))
    }
}

impl Lowerer<'_> {
    /// R3 and R9 widening on the lowered form `x` of `e` (see the module
    /// documentation): `x`, or one interpreter fallback for `e` in `x`'s
    /// representation.
    pub(super) fn regions_post(&mut self, e: &hir::Expr, env: &LEnv, mut x: Expr) -> Expr {
        if !self.regions || matches!(&*e.kind, H::Local(_)) {
            return x;
        }
        let (interp, lp) = has_interp_and_loop(&x);
        if !interp {
            return x;
        }
        let (candidate, widen) = if lp { widen_candidate(&x) } else { (false, false) };
        // `widen` decides the R9 fold: a withheld construct (its dependent
        // region is a nested iteration, `iteration`) keeps its native
        // iteration. R3 folding (`foldable`) still applies to it, as it did
        // when the widening was merely a candidate.
        if !widen && !foldable(&x) {
            return x;
        }
        if candidate && self.split_memoizable(&mut x) {
            return x;
        }
        if self.at.is_some() && mentions_at(e) {
            return x;
        }
        let w = self.interp(e, env);
        // The interpreter must see every value the IR computed outside `x`
        // (captured locals, LET values), else it would recompute them;
        // materialized definitions it computes once per state, too.
        let captured = free_temps(&w);
        if !free_temps(&x).iter().all(|t| captured.contains(t) || self.is_materialized_temp(*t)) {
            return x;
        }
        if widen {
            let n = WIDENED.fetch_add(1, Ordering::Relaxed) + 1;
            diag::emit(
                Topic::Coverage,
                format_args!(
                    "widen #{} {}:{}: one fallback replaces {}, the lowered form of the construct",
                    n,
                    e.span.line,
                    e.span.col,
                    crate::ir_fmt::label(widened_root(&x))
                ),
            );
        }
        in_repr(w, x.ty)
    }

    /// R9 exception: a construct that reads the next state (a
    /// transition predicate, e.g. the WF condition of an action) is
    /// evaluated once per transition, so widened, its region would never
    /// be memoized. When it contains fallbacks that are pure and read the
    /// current state only, as sources of binding constructs (Quicksort's
    /// `\E newseq \in Partitions(I, p, seq)`), these are bound before
    /// their constructs instead, as regions of their own memoized on their
    /// inputs, and `x` is not widened (returns true).
    fn split_memoizable(&mut self, x: &mut Expr) -> bool {
        if self.region_reads(x).is_none_or(|r| r.next.is_empty()) {
            return false;
        }
        let mut found = false;
        self.split_sources(x, &mut found);
        found
    }

    /// Bind the memoizable fallback sources of the binding constructs in
    /// `e` (outside fallbacks) before them; `found` also for such
    /// fallbacks already bound by a `Let`.
    fn split_sources(&mut self, e: &mut Expr, found: &mut bool) {
        if matches!(&*e.kind, ExprKind::Interp { .. }) {
            return;
        }
        e.for_each_child_mut(&mut |c| self.split_sources(c, found));
        if let ExprKind::Let { value, .. } = &*e.kind {
            *found |= self.memoizable_interp(value);
            return;
        }
        let split = match loop_parts(e) {
            Some((_, src, _)) => self.memoizable_interp(src),
            None => false,
        };
        if split {
            *found = true;
            let (_, src, _) = loop_parts_mut(e).expect("binding construct");
            let t = self.temp(src.ty);
            let r = std::mem::replace(src, temp_ref(src.ty, t));
            let body = std::mem::replace(e, bool_lit(false));
            *e = let_in([(t, r)], body);
        }
    }

    /// An interpreter fallback whose result may be memoized on its inputs:
    /// pure, with a known read set of the current state only.
    fn memoizable_interp(&self, e: &Expr) -> bool {
        matches!(&*e.kind, ExprKind::Interp { .. }) && !self.ir_volatile(e) && self.region_reads(e).is_some_and(|r| r.next.is_empty())
    }

    // ------------------------------------------------------------------
    // R9: hoisting loop-invariant regions

    /// Hoist loop-invariant regions (and typed loop-invariant expressions:
    /// `hoist_typed`) out of the binding constructs of the expressions of
    /// `s`.
    pub(super) fn hoist_stmt(&mut self, s: &mut Stmt) {
        s.for_each_expr_deep_mut(&mut |e| self.hoist_pred(e));
    }

    /// `hoist_stmt` for an expression (a predicate).
    pub(super) fn hoist_pred(&mut self, e: &mut Expr) {
        if self.regions {
            self.hoist_expr(e);
        }
        self.hoist_typed(e);
        self.share_ranks(e);
    }

    /// Typed loop-invariant expressions that loop themselves or call a
    /// compiled function (`Max(S)` in the body of a `CHOOSE`) are
    /// computed once before the binding construct, as R9 hoists regions:
    /// only from strict positions of the body (every conjunct of a
    /// `CHOOSE` body: an element is chosen only if they all hold), and only
    /// when the source has an element.
    pub(super) fn hoist_typed(&mut self, e: &mut Expr) {
        e.for_each_child_mut(&mut |c| self.hoist_typed(c));
        let Some((bind, src, bodies)) = loop_parts(e) else { return };
        if matches!(&*src.kind, ExprKind::ConstElems { count: 0, .. }) {
            return;
        }
        let mut bound = HashSet::from([bind]);
        for b in bodies {
            bound_temps(b, &mut bound);
        }
        let all_conjuncts = matches!(&*e.kind, ExprKind::Choose { .. });
        let mut hoisted: Vec<(Temp, Expr)> = Vec::new();
        {
            let (_, _, bodies) = loop_parts_mut(e).expect("binding construct");
            for b in bodies {
                self.extract_typed(b, &bound, &mut hoisted, all_conjuncts);
            }
        }
        if !hoisted.is_empty() {
            self.wrap_hoisted(e, hoisted);
        }
    }

    /// Move the typed loop-invariant expressions worth computing once in
    /// strict position of `e` (the body of a binding construct binding
    /// `bound`; with `all_conjuncts`, a `CHOOSE` body) to `out`, leaving
    /// temps.
    fn extract_typed(&mut self, e: &mut Expr, bound: &HashSet<Temp>, out: &mut Vec<(Temp, Expr)>, all_conjuncts: bool) {
        use ExprKind as K;
        if typed_invariant(e) && !free_temps(e).iter().any(|t| bound.contains(t)) {
            let t = self.temp(e.ty);
            let r = std::mem::replace(e, temp_ref(e.ty, t));
            out.push((t, r));
            return;
        }
        if loop_parts(e).is_some() {
            if let Some((_, src, _)) = loop_parts_mut(e) {
                self.extract_typed(src, bound, out, false);
            }
            return;
        }
        match &mut *e.kind {
            K::And(xs) if all_conjuncts => xs.iter_mut().for_each(|x| self.extract_typed(x, bound, out, true)),
            K::And(xs) | K::Or(xs) => {
                if let Some(x) = xs.first_mut() {
                    self.extract_typed(x, bound, out, false);
                }
            }
            K::If(c, _, _) => self.extract_typed(c, bound, out, false),
            K::MapPut { base, rank, .. } => {
                self.extract_typed(base, bound, out, false);
                self.extract_typed(rank, bound, out, false);
            }
            K::Enabled(_) | K::Interp { .. } => {}
            _ => e.for_each_child_mut(&mut |c| self.extract_typed(c, bound, out, false)),
        }
    }

    fn hoist_expr(&mut self, e: &mut Expr) {
        if matches!(&*e.kind, ExprKind::Interp { .. }) {
            e.for_each_child_mut(&mut |c| self.hoist_expr(c));
            return;
        }
        // Inner constructs first: what they hoist may then leave the outer one.
        e.for_each_child_mut(&mut |c| self.hoist_expr(c));
        let Some((bind, src, _)) = loop_parts(e) else { return };
        if matches!(&*src.kind, ExprKind::ConstElems { count: 0, .. }) {
            return;
        }
        let mut bound = HashSet::from([bind]);
        if let Some((_, _, bodies)) = loop_parts(e) {
            for b in bodies {
                bound_temps(b, &mut bound);
            }
        }
        let mut hoisted: Vec<(Temp, Expr)> = Vec::new();
        {
            let (_, _, bodies) = loop_parts_mut(e).expect("binding construct");
            for b in bodies {
                self.extract_invariant(b, &bound, &mut hoisted);
            }
        }
        if hoisted.is_empty() {
            return;
        }
        self.wrap_hoisted(e, hoisted);
    }

    /// Bind the expressions `hoisted` (taken out of the binding construct
    /// `e`) before `e`.
    fn wrap_hoisted(&mut self, e: &mut Expr, hoisted: Vec<(Temp, Expr)>) {
        let elem_ty = loop_parts(e).map(|(bind, _, _)| self.temps[bind as usize]).expect("binding construct");
        // Evaluate the source once; compute the hoisted expressions only if
        // it has an element (they would not be evaluated otherwise: an
        // error in them must not turn into a failure of the whole
        // construct).
        let is_seq = matches!(&*e.kind, ExprKind::SeqFilter { .. });
        let (_, src, _) = loop_parts_mut(e).expect("binding construct");
        let mut outer: Vec<(Temp, Expr)> = Vec::new();
        let guard = match &mut *src.kind {
            ExprKind::ConstElems { .. } => None,
            // A stored set: its handle once (the source is not a value).
            ExprKind::RefElems(x) => {
                if !is_trivial(x) {
                    let t = self.temp(x.ty);
                    outer.push((t, std::mem::replace(x, temp_ref(x.ty, t))));
                }
                let b = self.temp(elem_ty);
                Some(Expr::new(Ty::Bool, ExprKind::Exists { bind: b, set: src.clone(), body: bool_lit(true) }))
            }
            ExprKind::IntRange(lo, hi) => {
                for b in [lo, hi] {
                    if !is_trivial(b) {
                        let t = self.temp(Ty::Int);
                        outer.push((t, std::mem::replace(b, temp_ref(Ty::Int, t))));
                    }
                }
                let ExprKind::IntRange(lo, hi) = &*src.kind else { unreachable!() };
                Some(Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Le, lo.clone(), hi.clone())))
            }
            _ => {
                // Iteration sources are not values and cannot be bound to
                // a temp. Share their value operand, retaining the source
                // wrapper for both the nonempty guard and the loop.
                let value = match &mut *src.kind {
                    ExprKind::Subsets(base) | ExprKind::OrderedSet { set: base, .. } => base,
                    _ => src,
                };
                if !is_trivial(value) {
                    let t = self.temp(value.ty);
                    let r = temp_ref(value.ty, t);
                    outer.push((t, std::mem::replace(value, r)));
                }
                let (_, src, _) = loop_parts(e).expect("binding construct");
                let s = src.clone();
                Some(if is_seq {
                    Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Gt, Expr::new(Ty::Int, ExprKind::SeqLen(s)), int_lit(0)))
                } else {
                    let b = self.temp(elem_ty);
                    Expr::new(Ty::Bool, ExprKind::Exists { bind: b, set: s, body: bool_lit(true) })
                })
            }
        };
        let guard = match guard {
            Some(g) if hoisted.len() > 1 => {
                let t = self.temp(Ty::Bool);
                outer.push((t, g));
                Some(temp_ref(Ty::Bool, t))
            }
            g => g,
        };
        let typing = &self.typing;
        let lets = hoisted.into_iter().map(|(t, r)| {
            let v = match &guard {
                None => r,
                Some(g) => {
                    let ty = r.ty;
                    // (Never used: the construct has no element.)
                    let dummy = match ty {
                        Ty::Bool => bool_lit(false),
                        Ty::Int => int_lit(0),
                        Ty::Enc(sid) => Expr::new(ty, ExprKind::ConstWords(vec![0; typing.words(sid) as usize].into())),
                        Ty::Val => val_lit(Value::FALSE),
                    };
                    Expr::new(ty, ExprKind::If(g.clone(), r, dummy))
                }
            };
            (t, v)
        });
        let body = std::mem::replace(e, bool_lit(false));
        let inner = let_in(lets.collect::<Vec<_>>().into_iter().rev(), body);
        *e = let_in(outer.into_iter().rev(), inner);
    }

    /// Move the loop-invariant pure regions in strict position of `e` (the
    /// body of a binding construct binding `bound`) to `out`, leaving temps.
    fn extract_invariant(&mut self, e: &mut Expr, bound: &HashSet<Temp>, out: &mut Vec<(Temp, Expr)>) {
        use ExprKind as K;
        if is_boxed(e) {
            // A conversion into an encoding stays in the loop (only boxed
            // values and scalars are hoisted).
            let target = match &mut *e.kind {
                K::Convert(x) if matches!(e.ty, Ty::Enc(_)) && x.ty == Ty::Val => x,
                _ => e,
            };
            if matches!(target.ty, Ty::Enc(_))
                || is_leaf(target)
                || matches!(&*target.kind, K::Convert(c) if matches!(&*c.kind, K::Const(_) | K::ConstWords(_)))
            {
                return;
            }
            if target.contains_enabled() || free_temps(target).iter().any(|t| bound.contains(t)) || self.ir_volatile(target) {
                return;
            }
            let t = self.temp(target.ty);
            let r = std::mem::replace(target, temp_ref(target.ty, t));
            out.push((t, r));
            return;
        }
        if loop_parts(e).is_some() {
            if let Some((_, src, _)) = loop_parts_mut(e) {
                self.extract_invariant(src, bound, out);
            }
            return;
        }
        match &mut *e.kind {
            K::And(xs) | K::Or(xs) => {
                if let Some(x) = xs.first_mut() {
                    self.extract_invariant(x, bound, out);
                }
            }
            K::If(c, _, _) => self.extract_invariant(c, bound, out),
            K::MapPut { base, rank, .. } => {
                self.extract_invariant(base, bound, out);
                self.extract_invariant(rank, bound, out);
            }
            K::Enabled(_) => {}
            _ => e.for_each_child_mut(&mut |c| self.extract_invariant(c, bound, out)),
        }
    }

    // ------------------------------------------------------------------
    // region table

    /// Append the regions (maximal boxed subtrees) of a lowered action
    /// (`init`: of Init) to `out`, for `RegionTable::new`.
    pub fn action_regions(&self, f: &ActionFn, init: bool, out: &mut Vec<Region>) {
        let ctx = if init { RegionCtx::Init } else { RegionCtx::Action };
        let mut cx = TableCx { lw: self, func: f.name.clone(), temps: f.temps.clone().into(), ctx, enabled: false, out };
        cx.stmt(&f.body, &mut vec![false; self.nvars()]);
    }

    /// Append the regions of a lowered predicate (`transition`: over a
    /// step) to `out`.
    pub fn pred_regions(&self, p: &PredFn, transition: bool, out: &mut Vec<Region>) {
        let ctx = if transition { RegionCtx::TransPred } else { RegionCtx::StatePred };
        let mut cx = TableCx { lw: self, func: p.name.clone(), temps: p.temps.clone().into(), ctx, enabled: false, out };
        cx.expr(&p.body, &vec![transition; self.nvars()]);
    }

    /// The state variables a region reads (None if unknown).
    pub fn region_reads(&self, e: &Expr) -> Option<Reads> {
        self.expression_summary(e).reads
    }
}

/// Collects the regions of one function (walking statements to track the
/// statically assigned variables).
struct TableCx<'t, 'l, 'a> {
    lw: &'l Lowerer<'a>,
    func: Arc<str>,
    temps: Arc<[Ty]>,
    ctx: RegionCtx,
    enabled: bool,
    out: &'t mut Vec<Region>,
}

impl TableCx<'_, '_, '_> {
    fn stmt(&mut self, s: &Stmt, assigned: &mut Vec<bool>) {
        if let Some(e) = s.expr() {
            self.expr(e, assigned);
        }
        match s {
            Stmt::Assign { var, body, .. } => {
                let was = std::mem::replace(&mut assigned[*var as usize], true);
                self.stmt(body, assigned);
                assigned[*var as usize] = was;
            }
            Stmt::Compose { first, second, paths, .. } => {
                let saved = std::mem::replace(&mut self.enabled, true);
                self.stmt(first, &mut vec![false; assigned.len()]);
                self.stmt(second, &mut vec![false; assigned.len()]);
                self.enabled = saved;
                for path in paths {
                    let mut merged = assigned.clone();
                    for (a, b) in merged.iter_mut().zip(&path.assigned) {
                        *a |= *b;
                    }
                    self.stmt(&path.rest, &mut merged);
                }
            }
            _ => s.for_each_sub_stmt(&mut |b| self.stmt(b, assigned)),
        }
    }

    fn expr(&mut self, e: &Expr, assigned: &[bool]) {
        if let ExprKind::Enabled(s) = &*e.kind {
            let saved = std::mem::replace(&mut self.enabled, true);
            self.stmt(s, &mut vec![false; assigned.len()]);
            self.enabled = saved;
            return;
        }
        if is_boxed(e) && !is_leaf(e) {
            let summary = self.lw.expression_summary(e);
            let info = RegionInfo { func: self.func.clone(), enabled: self.enabled, pure: !summary.effects.volatile, reads: summary.reads };
            let r = Region {
                expr: e.clone(),
                temps: self.temps.clone(),
                inputs: free_temps(e),
                ctx: self.ctx,
                assigned: assigned.into(),
                info,
            };
            self.out.push(r);
            return;
        }
        e.for_each_child(&mut |c| self.expr(c, assigned));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn temp(ty: Ty, t: Temp) -> Expr {
        temp_ref(ty, t)
    }

    fn valop(op: tlx_sema::builtins::Builtin, args: Vec<Expr>) -> Expr {
        Expr::new(Ty::Val, ExprKind::ValOp { op, args })
    }

    #[test]
    fn boxed_classification() {
        use tlx_sema::builtins::Builtin as B;
        let v = valop(B::Cup, vec![temp(Ty::Val, 0), val_lit(Value::Int(1))]);
        assert!(is_boxed(&v));
        assert!(!is_boxed(&temp(Ty::Val, 0)));
        assert!(!is_boxed(&int_lit(3)));
        let conv = Expr::new(Ty::Bool, ExprKind::Convert(v.clone()));
        assert!(is_boxed(&conv));
        assert!(!is_boxed(&Expr::new(Ty::Int, ExprKind::IntBin(IntOp::Add, temp(Ty::Int, 1), int_lit(1)))));
        assert!(is_boxed(&eq(temp(Ty::Val, 0), v)));
    }

    #[test]
    fn region_inputs_in_order_without_bound_temps() {
        use tlx_sema::builtins::Builtin as B;
        // { t2 \cup t0 : t1 \in t0 } with t3 bound by a Let inside.
        let body = Expr::new(
            Ty::Val,
            ExprKind::Let {
                temp: 3,
                value: temp(Ty::Val, 2),
                body: valop(B::Cup, vec![temp(Ty::Val, 3), temp(Ty::Val, 0), temp(Ty::Val, 1)]),
            },
        );
        let e =
            Expr::new(Ty::Bool, ExprKind::Exists { bind: 1, set: temp(Ty::Val, 0), body: Expr::new(Ty::Bool, ExprKind::Convert(body)) });
        assert_eq!(free_temps(&e), vec![0, 2]);
    }

    #[test]
    fn fold_criterion() {
        use tlx_sema::builtins::Builtin as B;
        let interp = |n: u32| {
            Expr::new(
                Ty::Val,
                ExprKind::Interp {
                    expr: hir::Expr::new(H::Local(hir::LocalId(n)), Default::default()),
                    binds: Vec::new(),
                    deferred: Vec::new(),
                    env: Env::default(),
                },
            )
        };
        // Apply(Interp(f), Convert(3)): all boxed, with a fallback.
        let app = Expr::new(Ty::Val, ExprKind::Apply(interp(0), Expr::new(Ty::Val, ExprKind::Convert(int_lit(3)))));
        assert!(foldable(&app));
        assert!(foldable(&Expr::new(Ty::Bool, ExprKind::Convert(app.clone()))));
        // A lone fallback, or boxed operations without one: unchanged.
        assert!(!foldable(&interp(0)));
        assert!(!foldable(&valop(B::Cup, vec![temp(Ty::Val, 0), temp(Ty::Val, 1)])));
        // A typed computation inside: not folded.
        let typed = Expr::new(Ty::Val, ExprKind::Convert(Expr::new(Ty::Int, ExprKind::IntBin(IntOp::Add, temp(Ty::Int, 1), int_lit(1)))));
        assert!(!foldable(&Expr::new(Ty::Val, ExprKind::Apply(interp(0), typed))));
    }

    #[test]
    fn dependent_loop_regions() {
        let interp = |binds: Vec<(hir::LocalId, Expr)>| {
            Expr::new(
                Ty::Val,
                ExprKind::Interp {
                    expr: hir::Expr::new(H::Local(hir::LocalId(0)), Default::default()),
                    binds,
                    deferred: Vec::new(),
                    env: Env::default(),
                },
            )
        };
        let dep = Expr::new(
            Ty::Bool,
            ExprKind::Convert(interp(vec![(hir::LocalId(1), Expr::new(Ty::Val, ExprKind::Convert(temp(Ty::Int, 5))))])),
        );
        let indep = Expr::new(Ty::Bool, ExprKind::Convert(interp(vec![(hir::LocalId(1), temp(Ty::Val, 6))])));
        let range = Expr::new(Ty::Val, ExprKind::IntRange(int_lit(1), int_lit(3)));
        let l1 = Expr::new(Ty::Bool, ExprKind::Forall { bind: 5, set: range.clone(), body: dep });
        let l2 = Expr::new(Ty::Bool, ExprKind::Forall { bind: 5, set: range, body: indep });
        assert!(has_dependent_loop_region(&l1, false));
        assert!(!has_dependent_loop_region(&l2, false));
        assert!(has_dependent_loop_region(&not(l1), false));
    }

    /// The constructs `iteration` recognizes as a whole iteration: every
    /// shape R9 widening folds, as a fallback and as an IR loop node. A
    /// fallback of one is what an inner widening leaves, and the enclosing
    /// loop must not fold it again (integration: `tests/region_formation.rs`).
    #[test]
    fn iterations_are_recognized() {
        use tlx_sema::builtins::Builtin as B;
        let span = Default::default();
        let set_map = || hir::Expr::new(H::SetMap { expr: hir::Expr::new(H::At, span), bounds: Vec::new() }, span);
        let interp =
            |e: hir::Expr| Expr::new(Ty::Val, ExprKind::Interp { expr: e, binds: Vec::new(), deferred: Vec::new(), env: Env::default() });
        assert!(hir_iteration(&set_map()));
        assert!(hir_iteration(&hir::Expr::new(H::Builtin { op: B::Union, args: vec![set_map()] }, span)));
        // The folds the lowering turns into an IR loop (`lower::fold`).
        for op in [B::MapThenFoldSet, B::FoldSet, B::FoldFunctionOnSet, B::FoldFunction, B::FoldSeq] {
            assert!(hir_iteration(&hir::Expr::new(H::Builtin { op, args: Vec::new() }, span)), "{op:?}");
        }
        // Not an iteration: the recursion-limit fallback itself.
        assert!(!hir_iteration(&hir::Expr::new(H::At, span)));
        // A fallback of an iteration is one, under its conversion too.
        assert!(iteration(&interp(set_map())));
        assert!(iteration(&Expr::new(Ty::Bool, ExprKind::Convert(interp(set_map())))));
        let range = Expr::new(Ty::Val, ExprKind::IntRange(int_lit(1), int_lit(3)));
        assert!(iteration(&Expr::new(Ty::Bool, ExprKind::Forall { bind: 5, set: range, body: bool_lit(true) })));
        assert!(!iteration(&Expr::new(Ty::Bool, ExprKind::Convert(interp(hir::Expr::new(H::At, span))))));
    }
}
