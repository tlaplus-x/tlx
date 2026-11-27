//! Enumeration of sets in TLC's enumeration order (tlc-semantics.md §1.5).

use std::borrow::Cow;
use std::sync::Arc;

use super::{cardinality, is_empty_set, is_enumerable, member, next_combination};
use crate::error::{err, ValueError, ValueErrorKind};
use crate::intern::Sym;
use crate::lazy::LazySet;
use crate::repr::{interval_len, set_elems};
use crate::value::{normalize_vec, FcnDom, Value};
use crate::Result;

/// Visit the elements of a set in TLC's enumeration order (see `enumerate`)
/// without materializing the whole set. `f` returns `Ok(false)` to stop
/// early; the result is `Ok(false)` iff `f` stopped the enumeration.
/// Unlike `enumerate`, no size limits are applied (e.g. `\E x \in SUBSET (1..40)`
/// works if the witness is found early, like in TLC).
pub fn for_each_element(s: &Value, f: &mut dyn FnMut(Value) -> Result<bool>) -> Result<bool> {
    match s {
        Value::Set(elems) => {
            for e in elems.iter() {
                if !f(e.clone())? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Value::Interval(lo, hi) => {
            let n = interval_len(*lo, *hi)?;
            for i in 0..n as i64 {
                if !f(Value::Int(lo + i))? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        Value::LazySet(l) => for_each_lazy(s, l, f),
        _ => err(format!("Attempted to enumerate a non-set value:\n{s}")),
    }
}

/// One component of a product, record set or set of functions: its elements
/// in the enumeration order the odometer must follow. An interval is read by
/// index instead of being copied (TLC's enumerators convert a constituent
/// only when the whole set is materialized, and an interval is exactly sized
/// there), so a bounded traversal over `1..4000000 \X {1}` stops at the
/// limit without allocating the interval.
#[derive(Clone)]
enum Comp<'a> {
    Slice(&'a [Value]),
    Range(i64, usize),
    Owned(Arc<[Value]>),
}

impl Comp<'_> {
    fn len(&self) -> usize {
        match self {
            Comp::Slice(es) => es.len(),
            Comp::Range(_, n) => *n,
            Comp::Owned(es) => es.len(),
        }
    }

    fn get(&self, i: usize) -> Value {
        match self {
            Comp::Slice(es) => es[i].clone(),
            Comp::Range(lo, _) => Value::Int(lo + i as i64),
            Comp::Owned(es) => es[i].clone(),
        }
    }
}

/// The component view of a set (`Comp`): an enumerated set or an interval is
/// read in place, any other lazy set is materialized in its enumeration order
/// (the order TLC's enumerators use) — without the materialization bound,
/// which applies to the set being enumerated, not to its pieces.
fn comp_of(v: &Value) -> Result<Comp<'_>> {
    Ok(match v {
        Value::Set(es) => Comp::Slice(es),
        Value::Interval(lo, hi) => Comp::Range(*lo, interval_len(*lo, *hi)? as usize),
        _ => Comp::Owned(Arc::from(enumerate_unbounded(v)?)),
    })
}

/// Odometer over component enumerations, last component fastest.
fn odometer(comps: &[Comp<'_>], f: &mut dyn FnMut(&[Value]) -> Result<bool>) -> Result<bool> {
    if comps.iter().any(|c| c.len() == 0) {
        return Ok(true);
    }
    let mut idx = vec![0usize; comps.len()];
    let mut cur: Vec<Value> = comps.iter().map(|c| c.get(0)).collect();
    loop {
        if !f(&cur)? {
            return Ok(false);
        }
        let mut i = comps.len();
        loop {
            if i == 0 {
                return Ok(true);
            }
            i -= 1;
            idx[i] += 1;
            if idx[i] < comps[i].len() {
                cur[i] = comps[i].get(idx[i]);
                break;
            }
            idx[i] = 0;
            cur[i] = comps[i].get(0);
        }
    }
}

/// The shape of the functions of `[D -> R]` with a given (normalized)
/// domain (TLC `SetOfFcnsValue`: FcnRcdValues over the interval `D`, or over
/// the enumerated domain otherwise, see `Value::fcn_over`).
enum FcnShape {
    Tuple,
    /// Records (`[a: S, b: T]`, TLC `SetOfRcdsValue`).
    Record(Vec<Sym>),
    Fcn(Vec<Value>, FcnDom),
}

fn shape_of(dom_set: &Value, dom: Vec<Value>) -> FcnShape {
    if !matches!(dom_set, Value::Interval(..)) {
        FcnShape::Fcn(dom, FcnDom::Enumerated)
    } else if dom.iter().enumerate().all(|(i, k)| matches!(k, Value::Int(n) if *n == i as i64 + 1)) {
        FcnShape::Tuple
    } else {
        FcnShape::Fcn(dom, FcnDom::Interval)
    }
}

fn build_fcn(shape: &FcnShape, vals: &[Value]) -> Value {
    match shape {
        FcnShape::Tuple => Value::Tuple(Arc::from(vals)),
        FcnShape::Record(names) => Value::Record(names.iter().copied().zip(vals.iter().cloned()).collect()),
        FcnShape::Fcn(keys, d) => Value::Fcn(keys.iter().cloned().zip(vals.iter().cloned()).collect(), *d),
    }
}

/// Whether a component can be read by index in place (`Comp`): an enumerated
/// set or an interval. Any other set is streamed by `for_each_product`.
fn indexable(v: &Value) -> bool {
    matches!(v, Value::Set(_) | Value::Interval(..))
}

/// What is known about a set's emptiness without enumerating it:
/// `Some(true)` empty, `Some(false)` certainly non-empty, `None` undecided.
/// The infinite built-in sets (`Seq(S)`, `Nat`, `Int`, `STRING`, `Any`) are
/// certainly non-empty; a finite size decides; an unknown shape stays
/// undecided (`SUBSET {}` is one element, not empty).
fn empty_fact(v: &Value) -> Option<bool> {
    match v {
        Value::LazySet(l) if matches!(&**l, LazySet::Seq(_) | LazySet::Nat | LazySet::Int | LazySet::StringSet | LazySet::Any) => {
            Some(false)
        }
        _ => match size_fact(v) {
            SizeFact::Known(0) => Some(true),
            SizeFact::Known(_) | SizeFact::Overflow => Some(false),
            SizeFact::Unknown => None,
        },
    }
}

/// Whether a component is empty, at traversal time: a size fact decides
/// without evaluating, and an undecided lazy set asks TLC's `isEmpty`, which
/// looks for the first element (a filter's predicate runs only up to it).
/// Non-sets are left to the enumerability check that follows.
fn is_empty_component(v: &Value) -> Result<bool> {
    match v {
        Value::Set(es) => Ok(es.is_empty()),
        Value::Interval(lo, hi) => Ok(hi < lo),
        Value::LazySet(_) => match empty_fact(v) {
            Some(b) => Ok(b),
            None => crate::ops::is_empty_checked(v),
        },
        _ => Ok(false),
    }
}

/// Traverse a product, record set or set of functions over components that
/// may be lazy, last component fastest: each component is enumerated with
/// `for_each_element`, which stops when the consumer does, so an outer
/// collector's limit stops a lazy component before it is evaluated in full
/// (`NestedStop` must report the bound, not a later predicate's error).
fn for_each_product(
    comps: &[Value],
    cur: &mut Vec<Value>,
    build: &dyn Fn(&[Value]) -> Result<Value>,
    f: &mut dyn FnMut(Value) -> Result<bool>,
) -> Result<bool> {
    fn go(
        comps: &[Value],
        level: usize,
        cur: &mut Vec<Value>,
        build: &dyn Fn(&[Value]) -> Result<Value>,
        f: &mut dyn FnMut(Value) -> Result<bool>,
    ) -> Result<bool> {
        if level == comps.len() {
            return f(build(cur)?);
        }
        let mut done = true;
        // (`for_each_enumerated` streams each component in TLC's order,
        // matching `SetOfTuplesValue`/`SetOfRcdsValue` enumerators, so the
        // consumer's early stop stops before visiting the rest of a component.)
        for_each_enumerated(&comps[level], &mut |x| {
            cur.push(x);
            let r = go(comps, level + 1, cur, build, f);
            cur.pop();
            match r {
                Ok(true) => Ok(true),
                Ok(false) => {
                    done = false;
                    Ok(false)
                }
                Err(e) => Err(e),
            }
        })?;
        Ok(done)
    }
    go(comps, 0, cur, build, f)
}

fn for_each_lazy(s: &Value, l: &LazySet, f: &mut dyn FnMut(Value) -> Result<bool>) -> Result<bool> {
    match l {
        LazySet::Enum(es) => {
            // SetEnumValue.Enumerator normalizes, unlike cap/diff.
            for e in normalize_vec(es.clone())? {
                if !f(e)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        LazySet::KSubset(k, base) => super::ksubset::ksubset_for_each(*k, base, f),
        LazySet::Subset(base) => {
            let elems = subset_base_elems(base)?;
            for_each_subset_of(&elems, f)
        }
        LazySet::FcnSet(dom, range) => {
            // `[D -> R]` is empty iff D is non-empty and R is empty; the
            // domain decides first (`[{} -> R]` is the singleton of the empty
            // function, not empty), and an empty range ends the traversal
            // before the domain is enumerated.
            if !is_empty_component(dom)? && is_empty_component(range)? {
                return Ok(true);
            }
            let d = match (is_enumerable(dom), set_elems(dom)) {
                (true, Ok(Some(e))) => e.into_vec(),
                (true, Err(e)) => return Err(e),
                _ => {
                    return err(format!(
                        "Attempted to enumerate a set of the form [D -> R],but the domain D:\n{dom}\ncannot be enumerated."
                    ))
                }
            };
            if d.is_empty() {
                // TLC: an FcnRcdValue over the (enumerated) domain.
                return f(Value::fcn_over(dom, Vec::new())?);
            }
            if !is_enumerable(range) {
                return err(format!("Attempted to enumerate a set of the form [D -> R],but the range R:\n{range}\ncannot be enumerated."));
            }
            let n = d.len();
            let shape = shape_of(dom, d);
            if indexable(range) {
                let r = comp_of(range)?;
                let comps = vec![r; n];
                return odometer(&comps, &mut |vals| f(build_fcn(&shape, vals)));
            }
            let comps = vec![range.clone(); n];
            let build = |vals: &[Value]| Ok(build_fcn(&shape, vals));
            let mut cur = Vec::with_capacity(comps.len());
            for_each_product(&comps, &mut cur, &build, f)
        }
        LazySet::Product(sets) => {
            // TLC's enumerator converts each constituent in order and stops at
            // the first empty one; the emptiness test looks for the first
            // element (a filter's predicate runs only up to it), before the
            // enumerability checks and before any sibling traversal.
            for c in sets {
                if is_empty_component(c)? {
                    return Ok(true);
                }
            }
            for (i, c) in sets.iter().enumerate() {
                if !is_enumerable(c) {
                    return err(format!("Attempted to enumerate a set of the form s1 \\X s2 ... \\X sn,\nbut can't enumerate s{i}:\n{c}"));
                }
            }
            let build = |vals: &[Value]| Ok(Value::Tuple(Arc::from(vals)));
            if sets.iter().all(indexable) {
                let comps: Vec<Comp> = sets.iter().map(comp_of).collect::<Result<_>>()?;
                return odometer(&comps, &mut |vals| f(Value::Tuple(Arc::from(vals))));
            }
            let mut cur = Vec::with_capacity(sets.len());
            for_each_product(sets, &mut cur, &build, f)
        }
        LazySet::RecordSet(fields) => {
            // (As products: an empty field empties the record set before the
            // other fields are traversed.)
            for (_, c) in fields.iter() {
                if is_empty_component(c)? {
                    return Ok(true);
                }
            }
            for (name, c) in fields.iter() {
                if !is_enumerable(c) {
                    return err(format!(
                        "Attempted to enumerate a set of the form [l1 : v1, ..., ln : vn],\nbut can't enumerate the value of the `{}' field:\n{c}",
                        name.as_str()
                    ));
                }
            }
            let shape = if fields.is_empty() { FcnShape::Tuple } else { FcnShape::Record(fields.iter().map(|(n, _)| *n).collect()) };
            if fields.iter().all(|(_, c)| indexable(c)) {
                let comps: Vec<Comp> = fields.iter().map(|(_, c)| comp_of(c)).collect::<Result<_>>()?;
                return odometer(&comps, &mut |vals| f(build_fcn(&shape, vals)));
            }
            let sets: Vec<Value> = fields.iter().map(|(_, c)| c.clone()).collect();
            let build = |vals: &[Value]| Ok(build_fcn(&shape, vals));
            let mut cur = Vec::with_capacity(sets.len());
            for_each_product(&sets, &mut cur, &build, f)
        }
        LazySet::Seq(_) | LazySet::Nat | LazySet::Int | LazySet::StringSet | LazySet::Any => {
            err(format!("TLC encountered the non-enumerable quantifier bound\n{s}."))
        }
        LazySet::Union(sets) => {
            if !is_enumerable(sets) {
                return err(format!("Attempted to enumerate the nonenumerable set:\n{s}"));
            }
            for_each_element(sets, &mut |e| {
                if !is_enumerable(&e) {
                    return err("Attempted to enumerate UNION(s), but some element of s is nonenumerable.");
                }
                for_each_element(&e, f)
            })
        }
        LazySet::Cup(a, b) => {
            if !is_enumerable(a) || !is_enumerable(b) {
                return err(format!("Attempted to enumerate S \\cup T when S:\n{a}\nand T:\n{b}\nare not both enumerable"));
            }
            Ok(for_each_element(a, f)? && for_each_element(b, f)?)
        }
        LazySet::Cap(a, b) => {
            let (src, other) = if is_enumerable(a) {
                (a, b)
            } else if is_enumerable(b) {
                (b, a)
            } else {
                return err(format!("Attempted to enumerate S \\cap T when neither S:\n{a}\nnor T:\n{b}\nis enumerable"));
            };
            for_each_element(src, &mut |e| if member(&e, other)? { f(e) } else { Ok(true) })
        }
        LazySet::Diff(a, b) => {
            if !is_enumerable(a) {
                return err(format!("Attempted to enumerate S \\ T when S:\n{a}\nis not enumerable."));
            }
            for_each_element(a, &mut |e| if member(&e, b)? { Ok(true) } else { f(e) })
        }
        LazySet::Custom(c) => match c.enumerate()? {
            Some(elems) => {
                for e in elems {
                    if !f(e)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            None => Err(c.not_enumerable(s)),
        },
    }
}

/// Enumerate a set in TLC's *enumeration* order (what `\E`, `x' \in S`,
/// set-formers see). For `Set`/`Interval` this is the normalized order; lazy
/// sets follow §1.5 (e.g. `\X` last component fastest; `Cup`/`Union` may
/// repeat elements). Errors if the set is infinite / not enumerable.
///
/// This materializes a lazy set, as TLC's `toSetEnum` does for the normalized
/// order, so it is limited by [`crate::limits::growth_limit`] — except where
/// TLC does not build the set that way: `SUBSET S` and `kSubset(k, S)`
/// enumerate lazily in the normalized order, an enumerated set is already
/// built, and an interval is copied into an exactly sized array (TLC's
/// `IntervalValue.toSetEnum`), which its `ValueVec` never has to grow.
///
/// The collection streams a set filter (`for_each_enumerated`), so the
/// predicate runs only on the elements reached and a predicate error after
/// the limit is never evaluated, as in TLC's materializing `SetPredValue`.
pub fn enumerate(s: &Value) -> Result<Vec<Value>> {
    enumerate_impl(s, true)
}

/// `enumerate` of a piece of a streamed traversal (a product's component, a
/// set of functions' range): TLC's enumerators stream those, and the bound
/// applies to the set being enumerated, not to its pieces. The size overflow
/// of the piece still reports its own error.
fn enumerate_unbounded(s: &Value) -> Result<Vec<Value>> {
    enumerate_impl(s, false)
}

fn subset_base_elems(base: &Value) -> Result<crate::repr::Elems<'_>> {
    match (is_enumerable(base), set_elems(base)) {
        (true, Ok(Some(e))) => Ok(e),
        (true, Err(e)) => Err(e),
        _ => err(format!("Attempted to compute the value of an expression of form\nSUBSET S, but S is a non-enumerable value:\n{base}")),
    }
}

fn for_each_subset_of(elems: &crate::repr::Elems<'_>, f: &mut dyn FnMut(Value) -> Result<bool>) -> Result<bool> {
    let n = elems.len();
    for k in 0..=n {
        let mut idx: Vec<usize> = (0..k).collect();
        loop {
            let subset: Arc<[Value]> = idx.iter().map(|&i| elems.get(i).into_owned()).collect();
            if !f(Value::Set(subset))? {
                return Ok(false);
            }
            if !next_combination(&mut idx, n) {
                break;
            }
        }
    }
    Ok(true)
}

/// Whether `v`'s cardinality is computed from its parts without materializing
/// `v` itself (`ops::sets::size` never enumerates `v`, only its operands).
/// Checking `size` before collecting `SUBSET v` avoids building an exponential
/// or large compositional base (such as `SUBSET {x \in 1..20 : P}` or
/// `[1..5 -> {x \in 1..2 : P}]`) only to discover that the outer powerset
/// overflows TLC's 32-bit size (`SubsetValue.toSetEnum` asks `size()` first).
fn has_compositional_size(v: &Value) -> bool {
    matches!(
        v,
        Value::LazySet(l)
            if matches!(**l, LazySet::Subset(_) | LazySet::KSubset(..) | LazySet::FcnSet(..) | LazySet::Product(_) | LazySet::RecordSet(_))
    )
}

/// Collect `SUBSET base` into a `Vec`: unlike the streaming visitor, a full
/// collection must refuse a base with 31 or more distinct elements before
/// allocating any output subsets (TLC's `SubsetValue.toSetEnum` checks
/// `size()` first), even when `size_fact(base)` was `Unknown` (e.g. a
/// deferred `LazySet::Enum` or a compositional set over a lazy filter).
fn enumerate_subset(s: &Value, base: &Value) -> Result<Vec<Value>> {
    if size_fact(s) == SizeFact::Overflow || has_compositional_size(base) {
        if let Some(e) = materialization_error(s) {
            return Err(e);
        }
    }
    let elems = subset_base_elems(base)?;
    if elems.len() >= 31 {
        let s = s.clone();
        return Err(ValueError::lazy(ValueErrorKind::Overflow, move || format!("Overflow when computing the number of elements in:\n{s}")));
    }
    let mut out = Vec::new();
    for_each_subset_of(&elems, &mut |subset| {
        out.push(subset);
        Ok(true)
    })?;
    Ok(out)
}

fn enumerate_impl(s: &Value, bounded: bool) -> Result<Vec<Value>> {
    match s {
        Value::Set(elems) => return Ok(elems.to_vec()),
        Value::Interval(lo, hi) => {
            let n = interval_len(*lo, *hi)?;
            return Ok((0..n as i64).map(|i| Value::Int(lo + i)).collect());
        }
        Value::LazySet(l) => {
            if let LazySet::Subset(base) = &**l {
                return enumerate_subset(s, base);
            }
        }
        _ => {}
    }
    let bounded = bounded && !streams_normalized(s) && !matches!(s, Value::LazySet(l) if matches!(**l, LazySet::Enum(_)));
    if !bounded {
        // (The preallocated/streamed traversals report the size overflow; a
        // bounded materialization decides the bound first, below.)
        check_enumerable_size(s)?;
    }
    if bounded {
        // A size the components decide (`[D -> R]`, `D \X R`, a record set) is
        // known before anything is built: TLC appends through the whole set,
        // so an oversized one is the error without materializing its pieces
        // (a product over `1..4000000` must not copy the interval). An
        // unknown size is left to the bounded visitor, which stops at the
        // limit without evaluating a filter predicate while sizing.
        match size_fact(s) {
            SizeFact::Overflow => return Err(crate::limits::too_many_elements()),
            SizeFact::Known(n) if n > crate::limits::growth_limit() => return Err(crate::limits::too_many_elements()),
            SizeFact::Known(_) | SizeFact::Unknown => {}
        }
    }
    let limit = if bounded { Some(crate::limits::growth_limit()) } else { None };
    let mut out = Vec::new();
    let mut over = false;
    for_each_enumerated(s, &mut |e| {
        if limit.is_some_and(|limit| out.len() as i64 >= limit) {
            over = true;
            return Ok(false);
        }
        out.push(e);
        Ok(true)
    })?;
    if over {
        return Err(crate::limits::too_many_elements());
    }
    Ok(out)
}

/// Visit the elements `enumerate` returns, in the same order and with the
/// same errors, without materializing them all first. Unlike
/// `for_each_element`, an evaluator-provided set (`LazySet::Custom`, e.g. a
/// set filter `{x \in S : P}` over a non-enumerated S) is streamed too: `P`
/// is evaluated element by element, interleaved with `f`, like TLC's
/// `SetPredValue.elements()` (where an error in `P` surfaces only when its
/// element is reached). Used where `x \in S` enumerates the values of a
/// variable (Init), `isEmpty()`, and `\subseteq`.
pub fn for_each_enumerated(s: &Value, f: &mut dyn FnMut(Value) -> Result<bool>) -> Result<bool> {
    if let Value::LazySet(l) = s {
        match &**l {
            LazySet::Custom(c) => {
                return match c.for_each(f)? {
                    Some(done) => Ok(done),
                    None => Err(c.not_enumerable(s)),
                };
            }
            LazySet::Union(sets) => {
                if !is_enumerable(sets) {
                    return err(format!("Attempted to enumerate the nonenumerable set:\n{s}"));
                }
                return for_each_enumerated(sets, &mut |e| {
                    if !is_enumerable(&e) {
                        return err("Attempted to enumerate UNION(s), but some element of s is nonenumerable.");
                    }
                    for_each_enumerated(&e, f)
                });
            }
            LazySet::Cup(a, b) => {
                if !is_enumerable(a) || !is_enumerable(b) {
                    return err(format!("Attempted to enumerate S \\cup T when S:\n{a}\nand T:\n{b}\nare not both enumerable"));
                }
                return Ok(for_each_enumerated(a, f)? && for_each_enumerated(b, f)?);
            }
            LazySet::Cap(a, b) => {
                let (src, other) = if is_enumerable(a) {
                    (a, b)
                } else if is_enumerable(b) {
                    (b, a)
                } else {
                    return err(format!("Attempted to enumerate S \\cap T when neither S:\n{a}\nnor T:\n{b}\nis enumerable"));
                };
                return for_each_enumerated(src, &mut |e| if member(&e, other)? { f(e) } else { Ok(true) });
            }
            LazySet::Diff(a, b) => {
                if !is_enumerable(a) {
                    return err(format!("Attempted to enumerate S \\ T when S:\n{a}\nis not enumerable."));
                }
                return for_each_enumerated(a, &mut |e| if member(&e, b)? { Ok(true) } else { f(e) });
            }
            _ => {}
        }
    }
    // No size check: this is TLC's `Enumerable.elements()` (the default
    // order), which never asks a set for its `size()`, so a set whose size
    // overflows the int range (a `SUBSET` of 31 or more elements, a function,
    // record or tuple set whose product of component sizes does) is still
    // enumerated element by element; a caller that stops early (an `x' \in S`
    // whose continuation stopped) never needs the whole set. (A *bound* asks
    // TLC for the normalized order, which materializes all but `SUBSET S`;
    // see `docs/compat.md` section 5 and `tlx_eval::eval::BoundElems`.)
    for_each_element(s, f)
}

/// What `for_each_enumerated_seqs` visits.
pub trait SeqsVisitor {
    /// One element; `Ok(false)` stops the enumeration.
    fn elem(&mut self, v: Value) -> Result<bool>;
    /// The elements of the set of sequences `[1..n -> R]` (`range`: the
    /// elements of R in enumeration order), all or some of them, in their
    /// enumeration order (lexicographic, the last component fastest), as
    /// `elem` would see them: `Ok(None)` if not handled (then each element
    /// is visited), else whether the enumeration was completed.
    fn seqs(&mut self, n: usize, range: &[Value]) -> Result<Option<bool>>;
}

/// `for_each_enumerated`, except that each set of sequences `[1..n -> R]`
/// enumerated (the set itself or an element of a `UNION`, such as
/// `UNION {[1..n -> S] : n \in 1..k}`) is offered to `v.seqs` as a whole
/// (e.g. to filter it without visiting every element). Same order, same
/// errors.
pub fn for_each_enumerated_seqs(s: &Value, v: &mut dyn SeqsVisitor) -> Result<bool> {
    let Value::LazySet(l) = s else { return for_each_element(s, &mut |x| v.elem(x)) };
    match &**l {
        LazySet::FcnSet(dom, range) => {
            // (No size check: as in `for_each_enumerated`, TLC enumerates a
            // set of sequences element by element whatever its size.)
            seqs_with(s, dom, range, v)
        }
        LazySet::Union(sets) => {
            if !is_enumerable(sets) {
                return err(format!("Attempted to enumerate the nonenumerable set:\n{s}"));
            }
            for_each_element(sets, &mut |e| {
                if !is_enumerable(&e) {
                    return err("Attempted to enumerate UNION(s), but some element of s is nonenumerable.");
                }
                match &e {
                    Value::LazySet(l) => match &**l {
                        LazySet::FcnSet(dom, range) => seqs_with(&e, dom, range, v),
                        _ => for_each_element(&e, &mut |x| v.elem(x)),
                    },
                    _ => for_each_element(&e, &mut |x| v.elem(x)),
                }
            })
        }
        _ => for_each_enumerated(s, &mut |x| v.elem(x)),
    }
}

/// Normalized read-only view over the base elements of `SUBSET base`, in TLC's
/// order (avoiding materializing an integer interval just to inspect it).
pub struct SubsetBase<'a>(crate::repr::Elems<'a>);

impl<'a> SubsetBase<'a> {
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.len() == 0
    }

    pub fn get(&self, i: usize) -> Cow<'_, Value> {
        self.0.get(i)
    }

    /// `(lo, hi)` when the base is a non-empty integer interval `lo..hi`.
    pub fn as_interval(&self) -> Option<(i64, i64)> {
        match self.0 {
            crate::repr::Elems::Range(lo, len) if len > 0 => Some((lo, lo + len as i64 - 1)),
            _ => None,
        }
    }
}

/// What `for_each_enumerated_subsets` visits.
pub trait SubsetVisitor {
    /// One element; `Ok(false)` stops the enumeration.
    fn elem(&mut self, v: Value) -> Result<bool>;
    /// The subsets of `base` (normalized elements in TLC's order), visited in
    /// `SUBSET` enumeration order (increasing cardinality, then lexicographic
    /// by index): `Ok(None)` if not handled (then each subset is visited via
    /// `elem`), else whether the enumeration completed.
    fn subsets(&mut self, base: &SubsetBase<'_>) -> Result<Option<bool>>;
}

/// `for_each_enumerated`, except that each powerset `SUBSET B` enumerated (the
/// set itself or an element of a `UNION`) is offered to `v.subsets` as a whole
/// (e.g. to filter it without visiting every subset). Same order, same errors.
pub fn for_each_enumerated_subsets(s: &Value, v: &mut dyn SubsetVisitor) -> Result<bool> {
    let Value::LazySet(l) = s else { return for_each_element(s, &mut |x| v.elem(x)) };
    match &**l {
        LazySet::Subset(base) => subsets_with(base, v),
        LazySet::Union(sets) => {
            if !is_enumerable(sets) {
                return err(format!("Attempted to enumerate the nonenumerable set:\n{s}"));
            }
            for_each_enumerated(sets, &mut |e| {
                if !is_enumerable(&e) {
                    return err("Attempted to enumerate UNION(s), but some element of s is nonenumerable.");
                }
                match &e {
                    Value::LazySet(l) => match &**l {
                        LazySet::Subset(base) => subsets_with(base, v),
                        _ => for_each_enumerated(&e, &mut |x| v.elem(x)),
                    },
                    _ => for_each_enumerated(&e, &mut |x| v.elem(x)),
                }
            })
        }
        _ => for_each_enumerated(s, &mut |x| v.elem(x)),
    }
}

fn subsets_with(base: &Value, v: &mut dyn SubsetVisitor) -> Result<bool> {
    let elems = SubsetBase(subset_base_elems(base)?);
    if let Some(done) = v.subsets(&elems)? {
        return Ok(done);
    }
    for_each_subset_of(&elems.0, &mut |x| v.elem(x))
}

/// Visit all subsets `E` of `base` (already in TLC's normalized order) such
/// that every index in `required` is present, all remaining elements come from
/// `optional`, and `min_card <= |E| <= max_card`, in TLC's exact `SUBSET`
/// enumeration order (increasing cardinality, then lexicographic by index).
///
/// `required` and `optional` must be strictly increasing, disjoint index
/// slices into `0..base.len()`. Because inserting a fixed disjoint set
/// `required` preserves both equal-cardinality symmetric differences and
/// element order, enumerating `optional` combinations in lexicographic order
/// reproduces the exact subsequence of `SUBSET base` order.
pub fn for_each_constrained_subset(
    base: &SubsetBase<'_>,
    required: &[usize],
    optional: &[usize],
    min_card: usize,
    max_card: usize,
    f: &mut dyn FnMut(Value) -> Result<bool>,
) -> Result<bool> {
    debug_assert!(required.windows(2).all(|w| w[0] < w[1]));
    debug_assert!(optional.windows(2).all(|w| w[0] < w[1]));
    debug_assert!(required.last().is_none_or(|&i| i < base.len()));
    debug_assert!(optional.last().is_none_or(|&i| i < base.len()));
    if min_card > max_card || max_card < required.len() || min_card > required.len() + optional.len() {
        return Ok(true);
    }
    let k_lo = min_card.saturating_sub(required.len());
    let k_hi = (max_card - required.len()).min(optional.len());
    let n_opt = optional.len();
    for k_opt in k_lo..=k_hi {
        let mut idx: Vec<usize> = (0..k_opt).collect();
        let total_len = required.len() + k_opt;
        loop {
            let subset: Arc<[Value]> = if required.is_empty() {
                idx.iter().map(|&j| base.get(optional[j]).into_owned()).collect()
            } else if k_opt == 0 {
                required.iter().map(|&i| base.get(i).into_owned()).collect()
            } else {
                let mut merged = Vec::with_capacity(total_len);
                let (mut ri, mut oi) = (0usize, 0usize);
                while ri < required.len() && oi < k_opt {
                    let r = required[ri];
                    let o = optional[idx[oi]];
                    debug_assert!(r != o, "required and optional must be disjoint");
                    if r < o {
                        merged.push(base.get(r).into_owned());
                        ri += 1;
                    } else {
                        merged.push(base.get(o).into_owned());
                        oi += 1;
                    }
                }
                for &r in &required[ri..] {
                    merged.push(base.get(r).into_owned());
                }
                for &j in &idx[oi..] {
                    merged.push(base.get(optional[j]).into_owned());
                }
                Arc::from(merged)
            };
            if !f(Value::Set(subset))? {
                return Ok(false);
            }
            if !next_combination(&mut idx, n_opt) {
                break;
            }
        }
    }
    Ok(true)
}

/// The elements of `s` = `[dom -> range]` (as `for_each_element`), offered
/// to `v.seqs` if they are sequences.
fn seqs_with(s: &Value, dom: &Value, range: &Value, v: &mut dyn SeqsVisitor) -> Result<bool> {
    if let Value::Interval(1, n) = dom {
        if *n >= 1 && is_enumerable(range) && !is_empty_set(range) {
            if let Ok(r) = enumerate_unbounded(range) {
                if let Some(done) = v.seqs(*n as usize, &r)? {
                    return Ok(done);
                }
            }
        }
    }
    for_each_element(s, &mut |x| v.elem(x))
}

/// `enumerate` refuses to materialize a set whose TLC int `size()` overflows
/// (TLC's `Value.size` reports the overflow, and `SubsetValue.toSetEnum` asks
/// for `size()` too). Enumeration itself does not: `Enumerable.elements()`
/// never calls `size()`, so `for_each_enumerated` streams such a set.
fn check_enumerable_size(s: &Value) -> Result<()> {
    // (`size_fact` decides from the shape alone: computing the exact error
    // enumerates a lazy component, and a filter component would evaluate its
    // predicate while only checking the size.)
    if size_fact(s) != SizeFact::Overflow {
        return Ok(());
    }
    match materialization_error(s) {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

/// The `size()` overflow error of `s`, when `s` is one of the lazy sets that
/// `enumerate` cannot materialize: a `SUBSET` of 31 or more elements, or a
/// function, record or tuple set whose product of component sizes exceeds
/// TLC's int range. The evaluator asks this to decide between materializing a
/// bound variable's domain and streaming it (`for_each_enumerated`).
pub fn materialization_error(s: &Value) -> Option<ValueError> {
    if !matches!(s, Value::LazySet(l) if matches!(**l, LazySet::Subset(_) | LazySet::FcnSet(..) | LazySet::Product(_) | LazySet::RecordSet(_)))
    {
        return None;
    }
    match cardinality(s) {
        Err(e) if e.kind == ValueErrorKind::Overflow => Some(e),
        _ => None,
    }
}

/// Enumerate in normalized (sorted, deduplicated) order — used by CHOOSE.
pub fn enumerate_normalized(s: &Value) -> Result<Vec<Value>> {
    match s {
        Value::Set(_) | Value::Interval(..) | Value::LazySet(_) => normalize_enumerated(s, enumerate(s)?),
        _ => err(format!("Attempted to enumerate a non-set value:\n{s}")),
    }
}

/// `enumerate_normalized(s)` from `elems`, which is `enumerate(s)` (for a
/// caller that already enumerated `s`: a set filter `{x \in S : P}`
/// evaluates `P` again on every enumeration).
pub fn normalize_enumerated(s: &Value, elems: Vec<Value>) -> Result<Vec<Value>> {
    match s {
        Value::Set(_) | Value::Interval(..) => Ok(elems),
        // SUBSET enumerates in normalized order already (cardinality, then
        // lexicographic), like TLC's `SubsetValue.elementsNormalized`.
        // (So do k-subsets, `SubsetValue.kElements`.)
        Value::LazySet(l) if matches!(**l, LazySet::Subset(_) | LazySet::KSubset(..)) => Ok(elems),
        Value::LazySet(_) => normalize_vec(elems),
        _ => err(format!("Attempted to enumerate a non-set value:\n{s}")),
    }
}

/// Whether TLC enumerates `s` in the normalized order without materializing
/// it: `SUBSET S` and `kSubset(k, S)`, whose `elements(Ordering.NORMALIZED)`
/// stream (`SubsetValue` overrides it, and `KSubsetValue` inherits that).
/// They are the sets a quantifier's bound does not build, so `-maxSetSize`
/// does not limit them.
pub fn streams_normalized(s: &Value) -> bool {
    matches!(s, Value::LazySet(l) if matches!(**l, LazySet::Subset(_) | LazySet::KSubset(..)))
}

/// How a quantifier's bound domain must be enumerated. TLC asks for
/// `elements(Ordering.NORMALIZED)` (`TI/Tool.java` `contexts`), which
/// `EnumerableValue` implements by `toSetEnum`: `SubsetValue` and
/// `KSubsetValue` override it to stream, `SetEnumValue` is already enumerated
/// and `IntervalValue` fills an exactly sized array, while every other lazy
/// set is built element by element in a growing `ValueVec`, so `-maxSetSize`
/// applies — and a size over TLC's int is that error rather than a reason to
/// stream, because the growth reaches the bound first.
///
/// Both the interpreter (`Interp::bound_elems`) and the compiled tier's
/// boxed-domain iteration ask this, so the two tiers cannot disagree on where
/// a domain errors.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BoundKind {
    /// An enumerated set or an interval: its elements are already there.
    Share,
    /// `SUBSET S` / `kSubset(k, S)`: TLC streams them in the normalized
    /// order.
    Stream,
    /// A lazy set TLC materializes: `enumerate`, which applies the bound.
    Materialize,
    /// A function, tuple or record set whose size overflows TLC's int.
    Overflow,
}

/// [`BoundKind`] of the value of a quantifier's domain (`v`).
pub fn bound_kind(v: &Value) -> BoundKind {
    match v {
        Value::Set(_) | Value::Interval(..) => BoundKind::Share,
        Value::LazySet(_) if streams_normalized(v) => BoundKind::Stream,
        Value::LazySet(_) if size_fact(v) == SizeFact::Overflow => BoundKind::Overflow,
        _ => BoundKind::Materialize,
    }
}

/// What is known about a set's number of elements without enumerating it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SizeFact {
    /// The number of elements.
    Known(i64),
    /// More than TLC's int (its `size()` overflows).
    Overflow,
    /// Not decided by the set's shape: a union, intersection, difference or
    /// set filter — or a product with such a component. Counting it would take
    /// the enumeration this exists to avoid (and would evaluate a filter's
    /// predicate while sizing), so callers fall back to the bounded visitor.
    Unknown,
}

/// [`SizeFact`] of `s`, computed from the components' facts only: a product,
/// record set or set of functions is decided by its parts, and an unknown
/// part leaves the whole unknown (unless a part is known empty, which decides
/// the empty product).
pub fn size_fact(s: &Value) -> SizeFact {
    use SizeFact::{Known, Overflow, Unknown};
    match s {
        Value::Set(es) => Known(es.len() as i64),
        Value::Interval(lo, hi) => match interval_len(*lo, *hi) {
            Ok(n) => Known(n as i64),
            Err(_) => Overflow,
        },
        Value::LazySet(l) => match &**l {
            // Do not sort or normalize a deferred enumeration during sizing:
            // sorting can enumerate contained lazy sets (e.g. a set filter).
            LazySet::Enum(es) => match es.len() {
                0 => Known(0),
                1 => Known(1),
                _ => Unknown,
            },
            LazySet::KSubset(k, base) => ksubset_fact(*k, base),
            LazySet::Subset(base) => match size_fact(base) {
                Known(n) if n >= 31 => Overflow,
                Known(n) => Known(1i64 << n),
                Overflow => Overflow,
                Unknown => Unknown,
            },
            LazySet::FcnSet(d, r) => {
                let df = size_fact(d);
                let rf = size_fact(r);
                match df {
                    // An empty domain makes `[{} -> R]` the singleton of the
                    // empty function, whatever the range's size is (TLC does
                    // not ask for it).
                    Known(0) => Known(1),
                    Known(dn) => match rf {
                        Known(0) => Known(0),
                        Known(1) => Known(1),
                        Known(rn) => {
                            let mut sz: i64 = 1;
                            for _ in 0..dn {
                                sz = sz.saturating_mul(rn);
                                if sz > i32::MAX as i64 {
                                    return Overflow;
                                }
                            }
                            Known(sz)
                        }
                        // (A domain of size >= 1 and a range over the int.)
                        Overflow => Overflow,
                        Unknown => Unknown,
                    },
                    Overflow => match rf {
                        Known(0) => Known(0),
                        Known(1) => Known(1),
                        Known(_) | Overflow => Overflow,
                        Unknown => Unknown,
                    },
                    // (Whether the domain is empty is undecided: with an empty
                    // range the set holds 1 or 0 elements, and with a larger
                    // range 1 or many.)
                    Unknown => match rf {
                        Known(1) => Known(1),
                        Known(_) | Overflow | Unknown => Unknown,
                    },
                }
            }
            LazySet::Product(sets) => product_fact(sets.iter().map(size_fact)),
            LazySet::RecordSet(fields) => product_fact(fields.iter().map(|(_, c)| size_fact(c))),
            LazySet::Union(_)
            | LazySet::Cup(..)
            | LazySet::Cap(..)
            | LazySet::Diff(..)
            | LazySet::Custom(_)
            | LazySet::Seq(_)
            | LazySet::Nat
            | LazySet::Int
            | LazySet::StringSet
            | LazySet::Any => Unknown,
        },
        _ => Unknown,
    }
}

/// [`size_fact`] of a product of facts (TLC's product of the component sizes
/// with its int overflow): a known empty factor makes the product empty
/// whatever the other factors are, an unknown factor leaves it unknown, and
/// the rest multiply.
fn product_fact(facts: impl Iterator<Item = SizeFact>) -> SizeFact {
    use SizeFact::{Known, Overflow, Unknown};
    let facts: Vec<SizeFact> = facts.collect();
    if facts.contains(&Known(0)) {
        return Known(0);
    }
    if facts.contains(&Unknown) {
        return Unknown;
    }
    if facts.contains(&Overflow) {
        return Overflow;
    }
    let mut sz: i64 = 1;
    for f in facts {
        let Known(n) = f else { unreachable!("filtered above") };
        sz = sz.saturating_mul(n);
        if sz > i32::MAX as i64 {
            return Overflow;
        }
    }
    Known(sz)
}

/// [`size_fact`] of `kSubset(k, base)` from the base's fact alone: `k < 0`
/// and `k == 0` decide without the base, and the binomial needs its size,
/// which must not be enumerated (`KSubsetValue.count` reads `size(base)` in
/// TLC, but asking for it here would materialize a lazy base).
fn ksubset_fact(k: i64, base: &Value) -> SizeFact {
    use SizeFact::{Known, Overflow, Unknown};
    if k < 0 {
        return Known(0);
    }
    if k == 0 {
        return Known(1);
    }
    match size_fact(base) {
        Known(n) => {
            if k > n {
                return Known(0);
            }
            match super::ksubset::choose(n, k) {
                Some(c) if c <= i32::MAX as u128 => Known(c as i64),
                _ => Overflow,
            }
        }
        Overflow => Overflow,
        Unknown => Unknown,
    }
}

/// The number of elements of `s` when it is known without enumerating it.
pub fn size_if_known(s: &Value) -> Option<i64> {
    match size_fact(s) {
        SizeFact::Known(n) => Some(n),
        SizeFact::Overflow | SizeFact::Unknown => None,
    }
}

/// Whether materializing `s` the way `enumerate` does would fail the set
/// bound (`limits::growth_limit`, TLC's `-maxSetSize`): `s` is a lazy set
/// that TLC materializes (not `SUBSET S`, `kSubset(k, S)` or an enumerated
/// set) and its size is over the limit or overflows TLC's int.
///
/// A caller that would answer a materialization from the set itself — the
/// compiler, whose layouts enumerate constant sets once at compile time —
/// asks this to leave the expression to the interpreter instead, which
/// materializes (and so reports TLC's "too many elements") where TLC does.
/// The size of a union, intersection or difference is not computed here: it
/// would take the enumeration this exists to avoid, and building one of them
/// eagerly (`ops::sets::union`) applies the bound already.
pub fn over_set_bound(s: &Value) -> bool {
    match bound_kind(s) {
        BoundKind::Overflow => true,
        BoundKind::Materialize => matches!(size_fact(s), SizeFact::Known(n) if n > crate::limits::growth_limit()),
        BoundKind::Share | BoundKind::Stream => false,
    }
}

#[cfg(test)]
mod tests {
    use super::for_each_element;
    use crate::lazy::LazySet;
    use crate::value::Value;
    use std::sync::Arc;

    /// Independent oracle for `SUBSET (0..n)` in TLC's order: build every
    /// subset by extension, then order by size and lexicographically.
    fn reference_powerset(n: usize) -> Vec<Vec<usize>> {
        let mut all = vec![Vec::new()];
        for i in 0..n {
            for s in all.clone() {
                let mut t = s;
                t.push(i);
                all.push(t);
            }
        }
        all.sort_by(|a, b| a.len().cmp(&b.len()).then_with(|| a.cmp(b)));
        all
    }

    #[test]
    fn subset_enumerates_in_tlc_order() {
        for n in 0..=6 {
            let base = Value::Set((1..=n as i64).map(Value::Int).collect::<Vec<_>>().into());
            let subset = Value::LazySet(Arc::new(LazySet::Subset(base)));
            let mut got: Vec<Vec<i64>> = Vec::new();
            let done = for_each_element(&subset, &mut |s| {
                let Value::Set(es) = s else { unreachable!("an element of SUBSET S is a set") };
                got.push(es.iter().map(|e| e.as_int().unwrap()).collect());
                Ok(true)
            })
            .unwrap();
            assert!(done, "n={n}");
            let expected: Vec<Vec<i64>> =
                reference_powerset(n).into_iter().map(|s| s.into_iter().map(|i| i as i64 + 1).collect()).collect();
            assert_eq!(got, expected, "n={n}");
        }
    }

    #[test]
    fn subset_stops_early_and_reports_the_first_error() {
        let subset = Value::LazySet(Arc::new(LazySet::Subset(Value::Set(vec![Value::Int(1), Value::Int(2)].into()))));
        let mut seen = 0;
        let done = for_each_element(&subset, &mut |_| {
            seen += 1;
            Ok(false)
        })
        .unwrap();
        assert!(!done);
        assert_eq!(seen, 1, "the visitor stopped on the first subset");

        let mut visits = 0;
        let e = for_each_element(&subset, &mut |_| {
            visits += 1;
            Err(crate::ValueError::new("first error"))
        })
        .unwrap_err();
        assert_eq!(e.to_string(), "first error");
        assert_eq!(visits, 1, "the first error ends the enumeration");
    }

    /// `SUBSET S` over a base that `is_enumerable` accepts but that cannot be
    /// normalized must report that enumeration error, not the non-enumerable
    /// one (the fallible-enumeration fix for heterogeneous lazy sets).
    #[test]
    fn subset_of_an_unorderable_base_reports_the_enumeration_error() {
        let mixed = Value::LazySet(Arc::new(LazySet::Enum(vec![Value::Bool(true), Value::Int(1)])));
        let subset = Value::LazySet(Arc::new(LazySet::Subset(mixed.clone())));
        let direct = crate::ops::enumerate(&mixed).unwrap_err().to_string();
        let e = for_each_element(&subset, &mut |_| Ok(true)).unwrap_err();
        assert_eq!(e.to_string(), direct);
    }

    #[test]
    fn custom_set_streams_and_stops_early() {
        #[derive(Debug)]
        struct FailAfterFirst;
        impl crate::lazy::CustomSet for FailAfterFirst {
            fn contains(&self, v: &Value) -> crate::Result<bool> {
                Ok(*v == Value::Int(1))
            }
            fn enumerate(&self) -> crate::Result<Option<Vec<Value>>> {
                Err(crate::ValueError::new("enumerate should not be called"))
            }
            fn for_each(&self, f: &mut dyn FnMut(Value) -> crate::Result<bool>) -> crate::Result<Option<bool>> {
                if !f(Value::Int(1))? {
                    return Ok(Some(false));
                }
                Err(crate::ValueError::new("second element fails"))
            }
        }
        let s = Value::LazySet(Arc::new(LazySet::Custom(Box::new(FailAfterFirst))));
        let mut got = Vec::new();
        let done = crate::ops::for_each_enumerated(&s, &mut |v| {
            got.push(v);
            Ok(false)
        })
        .unwrap();
        assert!(!done);
        assert_eq!(got, vec![Value::Int(1)]);
        assert!(!crate::ops::is_empty_checked(&s).unwrap());
    }

    #[test]
    fn constrained_subset_matches_filtered_tlc_order() {
        let base_val = Value::Set((0..6).map(Value::Int).collect::<Vec<_>>().into());
        let base = super::SubsetBase(super::subset_base_elems(&base_val).unwrap());
        let cases: &[(&[usize], &[usize], usize, usize)] = &[
            (&[], &[0, 1, 2, 3, 4, 5], 0, 6),
            (&[], &[1, 3, 5], 0, 6),
            (&[1, 4], &[0, 2, 3, 5], 0, 6),
            (&[1, 3], &[0, 2, 4, 5], 2, 4),
            (&[2], &[], 1, 1),
            (&[2], &[0, 1], 0, 0),
            (&[2], &[0, 1], 4, 6),
            (&[], &[0, 2, 4], 2, 2),
        ];
        let all = reference_powerset(6);
        for &(req, opt, min_c, max_c) in cases {
            let mut got: Vec<Vec<usize>> = Vec::new();
            let done = super::for_each_constrained_subset(&base, req, opt, min_c, max_c, &mut |s| {
                let Value::Set(es) = s else { unreachable!() };
                got.push(es.iter().map(|e| e.as_int().unwrap() as usize).collect());
                Ok(true)
            })
            .unwrap();
            assert!(done);
            let expected: Vec<Vec<usize>> = all
                .iter()
                .filter(|s| {
                    s.len() >= min_c
                        && s.len() <= max_c
                        && req.iter().all(|r| s.contains(r))
                        && s.iter().all(|x| req.contains(x) || opt.contains(x))
                })
                .cloned()
                .collect();
            assert_eq!(got, expected, "req={req:?} opt={opt:?} card={min_c}..={max_c}");
        }
    }
}
