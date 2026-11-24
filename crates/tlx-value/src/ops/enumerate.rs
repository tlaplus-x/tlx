//! Enumeration of sets in TLC's enumeration order (tlc-semantics.md §1.5).

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

/// Odometer over component enumerations, last component fastest.
fn odometer(comps: &[Vec<Value>], f: &mut dyn FnMut(&[Value]) -> Result<bool>) -> Result<bool> {
    if comps.iter().any(|c| c.is_empty()) {
        return Ok(true);
    }
    let mut idx = vec![0usize; comps.len()];
    let mut cur: Vec<Value> = comps.iter().map(|c| c[0].clone()).collect();
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
                cur[i] = comps[i][idx[i]].clone();
                break;
            }
            idx[i] = 0;
            cur[i] = comps[i][0].clone();
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
            let elems = match (is_enumerable(base), set_elems(base)) {
                (true, Ok(Some(e))) => e,
                (true, Err(e)) => return Err(e),
                _ => {
                    return err(format!(
                        "Attempted to compute the value of an expression of form\nSUBSET S, but S is a non-enumerable value:\n{base}"
                    ))
                }
            };
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
        LazySet::FcnSet(dom, range) => {
            if is_empty_set(s) {
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
            let r = enumerate(range)?;
            let comps = vec![r; d.len()];
            let shape = shape_of(dom, d);
            odometer(&comps, &mut |vals| f(build_fcn(&shape, vals)))
        }
        LazySet::Product(sets) => {
            if sets.iter().any(is_empty_set) {
                return Ok(true);
            }
            let mut comps = Vec::with_capacity(sets.len());
            for (i, c) in sets.iter().enumerate() {
                if !is_enumerable(c) {
                    return err(format!("Attempted to enumerate a set of the form s1 \\X s2 ... \\X sn,\nbut can't enumerate s{i}:\n{c}"));
                }
                comps.push(enumerate(c)?);
            }
            odometer(&comps, &mut |vals| f(Value::Tuple(Arc::from(vals))))
        }
        LazySet::RecordSet(fields) => {
            if fields.iter().any(|(_, c)| is_empty_set(c)) {
                return Ok(true);
            }
            let mut comps = Vec::with_capacity(fields.len());
            for (name, c) in fields.iter() {
                if !is_enumerable(c) {
                    return err(format!(
                        "Attempted to enumerate a set of the form [l1 : v1, ..., ln : vn],\nbut can't enumerate the value of the `{}' field:\n{c}",
                        name.as_str()
                    ));
                }
                comps.push(enumerate(c)?);
            }
            let shape = if fields.is_empty() { FcnShape::Tuple } else { FcnShape::Record(fields.iter().map(|(n, _)| *n).collect()) };
            odometer(&comps, &mut |vals| f(build_fcn(&shape, vals)))
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
        LazySet::Custom(c) => match c.for_each(f)? {
            Some(done) => Ok(done),
            None => Err(c.not_enumerable(s)),
        },
    }
}

/// Enumerate a set in TLC's *enumeration* order (what `\E`, `x' \in S`,
/// set-formers see). For `Set`/`Interval` this is the normalized order; lazy
/// sets follow §1.5 (e.g. `\X` last component fastest; `Cup`/`Union` may
/// repeat elements). Errors if the set is infinite / not enumerable.
pub fn enumerate(s: &Value) -> Result<Vec<Value>> {
    match s {
        Value::Set(elems) => return Ok(elems.to_vec()),
        Value::Interval(lo, hi) => {
            let n = interval_len(*lo, *hi)?;
            return Ok((0..n as i64).map(|i| Value::Int(lo + i)).collect());
        }
        _ => check_enumerable_size(s)?,
    }
    let mut out = Vec::new();
    for_each_element(s, &mut |e| {
        out.push(e);
        Ok(true)
    })?;
    Ok(out)
}

/// Visit the elements `enumerate` returns, in the same order and with the
/// same errors, without materializing them all first. Unlike
/// `for_each_element`, an evaluator-provided set (`LazySet::Custom`, e.g. a
/// set filter `{x \in S : P}` over a non-enumerated S) is streamed too: `P`
/// is evaluated element by element, interleaved with `f`, like TLC's
/// `SetPredValue.elements()` (where an error in `P` surfaces only when its
/// element is reached). Used where `x \in S` enumerates the values of a
/// variable (Init).
pub fn for_each_enumerated(s: &Value, f: &mut dyn FnMut(Value) -> Result<bool>) -> Result<bool> {
    if let Value::LazySet(l) = s {
        if let LazySet::Custom(c) = &**l {
            return match c.for_each(f)? {
                Some(done) => Ok(done),
                None => Err(c.not_enumerable(s)),
            };
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

/// The elements of `s` = `[dom -> range]` (as `for_each_element`), offered
/// to `v.seqs` if they are sequences.
fn seqs_with(s: &Value, dom: &Value, range: &Value, v: &mut dyn SeqsVisitor) -> Result<bool> {
    if let Value::Interval(1, n) = dom {
        if *n >= 1 && is_enumerable(range) && !is_empty_set(range) {
            if let Ok(r) = enumerate(range) {
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
        let done = for_each_element(&s, &mut |v| {
            got.push(v);
            Ok(false)
        })
        .unwrap();
        assert!(!done);
        assert_eq!(got, vec![Value::Int(1)]);
    }
}
