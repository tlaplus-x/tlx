//! Set algebra, cardinality / finiteness and set constructors.

use std::cmp::Ordering;
use std::sync::Arc;

use super::{enumerate_normalized, for_each_element, is_empty_checked, is_empty_set, is_enumerable, is_reducible, lazy, member};
use crate::error::{err, ValueError, ValueErrorKind};
use crate::intern::Sym;
use crate::lazy::LazySet;
use crate::order::{cmp_tlc, self_comparison_is_inert};
use crate::repr::{interval_len, set_elems, Elems};
use crate::value::{normalize_vec, same_comparison_family, Value};
use crate::Result;

/// `Cardinality(s)`: TLC's FiniteSets.Cardinality refuses a set that is not
/// `Enumerable` (Nat, Int, STRING, Seq(S), Any: overridden values) with its
/// own message, and otherwise asks the set for its size (`size`).
pub fn cardinality(s: &Value) -> Result<i64> {
    match s {
        Value::LazySet(l) if matches!(**l, LazySet::Seq(_) | LazySet::Nat | LazySet::Int | LazySet::StringSet | LazySet::Any) => {
            let s = s.clone();
            Err(ValueError::lazy(ValueErrorKind::General, move || format!("Attempted to compute cardinality of the value\n{s}")))
        }
        _ => size(s),
    }
}

/// TLC's error for the size of an overridden value (`UserValue.size`: Nat,
/// Int, STRING, Seq(S), Any).
pub fn overridden_size_error(s: &Value) -> ValueError {
    let s = s.clone();
    ValueError::lazy(ValueErrorKind::General, move || format!("Attempted to compute the number of elements in the overridden value {s}."))
}

/// The number of elements of a set (TLC's `Value.size`, which a value
/// asks of its parts, e.g. when printed or converted to an enumerated set:
/// unlike `Cardinality`, an overridden value fails with
/// `overridden_size_error`).
pub fn size(s: &Value) -> Result<i64> {
    // The messages name `s` (possibly a large set): building them is deferred
    // until shown (a caller may discard the error).
    let overflow = |sep: &'static str| {
        let s = s.clone();
        Err(ValueError::lazy(ValueErrorKind::Overflow, move || format!("Overflow when computing the number of elements in{sep}{s}")))
    };
    let not_card = || {
        let s = s.clone();
        Err(ValueError::lazy(ValueErrorKind::General, move || format!("Attempted to compute cardinality of the value\n{s}")))
    };
    match s {
        Value::Set(e) => Ok(e.len() as i64),
        Value::Interval(lo, hi) => Ok(interval_len(*lo, *hi)? as i64),
        Value::LazySet(l) => match &**l {
            LazySet::Enum(es) => Ok(normalize_vec(es.clone())?.len() as i64),
            LazySet::KSubset(k, base) => super::ksubset::ksubset_size(*k, base),
            LazySet::Subset(base) => {
                let n = size(base)?;
                if n >= 31 {
                    return overflow(":\n");
                }
                Ok(1i64 << n)
            }
            // (SetOfFcnsValue.size: an empty domain, an empty range or a
            // singleton range decides without the size of the domain.)
            LazySet::FcnSet(d, r) => {
                if is_empty_checked(d)? {
                    return Ok(1);
                }
                if is_empty_checked(r)? {
                    return Ok(0);
                }
                let rn = size(r)?;
                if rn <= 1 {
                    return Ok(rn);
                }
                let dn = size(d)?;
                let mut sz: i64 = 1;
                for _ in 0..dn {
                    sz *= rn;
                    if sz > i32::MAX as i64 {
                        return overflow(":\n");
                    }
                }
                Ok(sz)
            }
            // (TLC's messages differ in the separator.)
            LazySet::Product(sets) => product_cardinality(sets.iter(), || overflow(" ")),
            LazySet::RecordSet(fields) => product_cardinality(fields.iter().map(|(_, c)| c), || overflow(":\n")),
            LazySet::Seq(_) | LazySet::Nat | LazySet::Int | LazySet::StringSet | LazySet::Any => Err(overridden_size_error(s)),
            LazySet::Union(_) | LazySet::Cup(..) | LazySet::Cap(..) | LazySet::Diff(..) | LazySet::Custom(_) => {
                Ok(enumerate_normalized(s)?.len() as i64)
            }
        },
        _ => not_card(),
    }
}

/// `cardinality(s)`, given `normalized`, which is `enumerate_normalized(s)`:
/// a set that `cardinality` counts by enumerating it is not enumerated again.
pub fn cardinality_of_normalized(s: &Value, normalized: &[Value]) -> Result<i64> {
    match s {
        Value::LazySet(l)
            if matches!(**l, LazySet::Union(_) | LazySet::Cup(..) | LazySet::Cap(..) | LazySet::Diff(..) | LazySet::Custom(_)) =>
        {
            Ok(normalized.len() as i64)
        }
        _ => cardinality(s),
    }
}

/// `IsFiniteSet(s)`
pub fn is_finite_set(s: &Value) -> Result<bool> {
    match s {
        Value::Set(_) | Value::Interval(..) | Value::Tuple(_) | Value::Record(_) | Value::Fcn(..) => Ok(true),
        Value::LazyFcn(f) => is_finite_set(&f.domain()?),
        Value::LazySet(l) => match &**l {
            LazySet::Enum(_) => Ok(true),
            LazySet::Subset(base) => is_finite_set(base),
            LazySet::KSubset(k, base) => super::ksubset::ksubset_is_finite(*k, base),
            LazySet::FcnSet(d, r) => {
                let fd = is_finite_set(d)?;
                if fd && is_empty_checked(d)? {
                    return Ok(true);
                }
                let fr = is_finite_set(r)?;
                if fr && is_empty_checked(r)? {
                    return Ok(true);
                }
                // (SetOfFcnsValue.isFinite: a singleton range admits one
                // function whatever the domain.)
                Ok(fr && (fd || size(r)? == 1))
            }
            LazySet::Product(sets) => product_is_finite(sets.iter()),
            LazySet::RecordSet(fields) => product_is_finite(fields.iter().map(|(_, c)| c)),
            LazySet::Seq(r) => Ok(is_finite_set(r)? && is_empty_checked(r)?),
            LazySet::Union(sets) => {
                if !is_enumerable(sets) {
                    return err(format!("Attempted to check if the nonenumerable set:\n{s}\nis a finite set."));
                }
                let mut fin = true;
                for_each_element(sets, &mut |e| {
                    fin = is_finite_set(&e)?;
                    Ok(fin)
                })?;
                Ok(fin)
            }
            LazySet::Cup(a, b) => Ok(is_finite_set(a)? && is_finite_set(b)?),
            LazySet::Cap(a, b) => {
                if !is_finite_set(a)? && !is_finite_set(b)? {
                    return err(format!("Attempted to check if the set {s}is finite."));
                }
                Ok(true)
            }
            LazySet::Diff(a, b) => {
                if is_finite_set(a)? {
                    return Ok(true);
                }
                if !is_finite_set(b)? {
                    return err(format!("Attempted to check if the set {s}is finite."));
                }
                Ok(false)
            }
            LazySet::Nat | LazySet::Int | LazySet::StringSet | LazySet::Any => Ok(false),
            LazySet::Custom(c) => c.is_finite(),
        },
        // (IntValue / StringValue / BoolValue / ModelValue.isFinite.)
        Value::Int(_) => err(format!("Attempted to check if the integer {s} is a finite set.")),
        Value::Str(_) => err(format!("Attempted to check if the string {s} is a finite set.")),
        Value::Bool(_) => err(format!("Attempted to check if the boolean {s} is a finite set.")),
        Value::ModelValue(_) => err(format!("Attempted to check if the model value {s} is a finite set.")),
    }
}

/// Cardinality of a product of the component sets `comps` (0 if one of them
/// is empty); `overflow` reports a size beyond TLC's int range.
fn product_cardinality<'a>(comps: impl Iterator<Item = &'a Value> + Clone, overflow: impl Fn() -> Result<i64>) -> Result<i64> {
    // (TLC asks each component in turn: one it cannot answer for fails.)
    for c in comps.clone() {
        if is_empty_checked(c)? {
            return Ok(0);
        }
    }
    let mut sz: i64 = 1;
    for c in comps {
        sz *= size(c)?;
        if sz > i32::MAX as i64 {
            return overflow();
        }
    }
    Ok(sz)
}

/// Whether a product of the component sets `comps` is finite: all components
/// are finite, or a finite one is empty.
fn product_is_finite<'a>(comps: impl Iterator<Item = &'a Value>) -> Result<bool> {
    let mut all = true;
    for c in comps {
        if is_finite_set(c)? {
            if is_empty_checked(c)? {
                return Ok(true);
            }
        } else {
            all = false;
        }
    }
    Ok(all)
}

/// Merge two normalized element lists (TLC: `S` plus the elements of `T`
/// that are not members of `S`).
fn merge_sorted(a: &Elems, b: &Elems) -> Result<Option<Vec<Value>>> {
    // Until a RHS-only element is encountered, the output is exactly the
    // consumed prefix of a. Delay allocation but retain every comparison in
    // the original merge, once, in its original direction and order.
    let mut out: Option<Vec<Value>> = None;
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        let (x, y) = (a.get(i), b.get(j));
        let order = cmp_tlc(&y, &x)?;
        match order {
            Ordering::Less => {
                if out.is_none() {
                    // The consumed prefix is exactly the output so far.
                    crate::limits::check_set_size(i)?;
                    let mut prefix = Vec::with_capacity((a.len() + b.len()).min(crate::limits::growth_limit() as usize));
                    prefix.extend((0..i).map(|k| a.get(k).into_owned()));
                    out = Some(prefix);
                }
                crate::limits::push(out.as_mut().expect("allocated above"), y.into_owned())?;
                j += 1;
            }
            Ordering::Greater | Ordering::Equal => {
                if let Some(out) = &mut out {
                    crate::limits::push(out, x.into_owned())?;
                }
                // Do not compare twice: a lazy value can evaluate effects.
                // Equal consumes both operands; Greater consumes only a.
                if order == Ordering::Equal {
                    j += 1;
                }
                i += 1;
            }
        }
    }
    if j < b.len() && out.is_none() {
        crate::limits::check_set_size(i)?;
        let mut prefix = Vec::with_capacity((a.len() + b.len() - j).min(crate::limits::growth_limit() as usize));
        prefix.extend((0..i).map(|k| a.get(k).into_owned()));
        out = Some(prefix);
    }
    if let Some(out) = &mut out {
        // Every remaining element is appended: the result's length is known.
        crate::limits::check_set_size(out.len() + (a.len() - i) + (b.len() - j))?;
        out.extend((i..a.len()).map(|k| a.get(k).into_owned()));
        out.extend((j..b.len()).map(|k| b.get(k).into_owned()));
    }
    Ok(out)
}

/// `s \cup t` (eager when both sides are enumerated sets / intervals).
///
/// Like TLC (Tool.java OPCODE_cup, `Reducible.cup`), the operands are not
/// checked to be sets: `{} \cup t` is `t` whatever `t` is, and a lazy union
/// fails only when it is used.
pub fn union(s: &Value, t: &Value) -> Result<Value> {
    if let Value::LazySet(l) = s {
        if let LazySet::Enum(es) = &**l {
            if is_reducible(t) {
                // TLC's `SetEnumValue.cup` appends the left side first: the
                // bound applies before the right operand is converted.
                crate::limits::check_set_size(es.len())?;
                let mut out = es.clone();
                for_each_element(t, &mut |e| {
                    if !member(&e, s)? {
                        crate::limits::push(&mut out, e)?;
                    }
                    Ok(true)
                })?;
                return Value::set_enum(out);
            }
        }
    }
    if is_reducible(s) {
        if is_empty_set(s) {
            return Ok(t.clone());
        }
        if is_reducible(t) {
            // TLC's `IntervalValue.cup`/`SetEnumValue.cup` append the left
            // side into a fresh vector before touching the right, so the bound
            // applies to it before any conversion or comparison.
            let a = set_elems(s)?.unwrap();
            crate::limits::check_set_size(a.len())?;
            let b = set_elems(t)?.unwrap();
            let out = match merge_sorted(&a, &b)? {
                Some(out) => out,
                None => {
                    // No right-hand element is new: the result is `s`. TLC's
                    // `SetEnumValue.cup`/`IntervalValue.cup` copy `s` into a
                    // fresh `ValueVec` even then, so the set bound applies
                    // (`(1..n) \cup {}` fails for `n` over `-maxSetSize`); only
                    // the copy is skipped here, not the check.
                    crate::limits::check_set_size(a.len())?;
                    // Only an enumerated set may stand for the result: TLC's
                    // cup builds a `SetEnumValue`, and an interval kept as an
                    // interval would be a different value to a consumer that
                    // distinguishes the representation (a function constructor
                    // makes an enumerated-domain function, so an `EXCEPT` at an
                    // absent model-value key leaves it unchanged).
                    if matches!(s, Value::Set(_)) && self_comparison_is_inert(s) {
                        return Ok(s.clone());
                    }
                    (0..a.len()).map(|k| a.get(k).into_owned()).collect()
                }
            };
            // (TLC's `IntervalValue.cup`/`SetCupValue.toSetEnum` add the
            // elements to a growing `ValueVec`, so the bound applies.)
            crate::limits::check_set_size(out.len())?;
            return Ok(Value::Set(Arc::from(out)));
        }
        return Ok(lazy(LazySet::Cup(s.clone(), t.clone())));
    }
    if is_reducible(t) {
        if is_empty_set(t) {
            return Ok(s.clone());
        }
        return Ok(lazy(LazySet::Cup(t.clone(), s.clone())));
    }
    Ok(lazy(LazySet::Cup(s.clone(), t.clone())))
}

fn filter_reducible(src: &Value, keep: &mut dyn FnMut(&Value) -> Result<bool>) -> Result<Value> {
    if let Value::LazySet(l) = src {
        if let LazySet::Enum(es) = &**l {
            let mut out = Vec::new();
            for e in es {
                if keep(e)? {
                    crate::limits::push(&mut out, e.clone())?;
                }
            }
            return Value::set_enum(out);
        }
    }
    let elems = set_elems(src)?.unwrap();
    let mut out = Vec::with_capacity(elems.len().min(crate::limits::growth_limit() as usize));
    for i in 0..elems.len() {
        let e = elems.get(i);
        if keep(&e)? {
            crate::limits::push(&mut out, e.into_owned())?;
        }
    }
    // (All kept: the same set.)
    if out.len() == elems.len() && matches!(src, Value::Set(_)) {
        return Ok(src.clone());
    }
    // (TLC's `IntervalValue.diff`/`cap` and `SetDiffValue.toSetEnum` add the
    // elements to a growing `ValueVec`, so the bound applies.)
    crate::limits::check_set_size(out.len())?;
    Ok(Value::Set(Arc::from(out)))
}

/// `s \cap t` (eager when either side is an enumerated set / interval).
///
/// Like TLC (`Reducible.cap`), the other operand is only used through
/// membership tests: `{} \cap t` is `{}` whatever `t` is.
pub fn intersect(s: &Value, t: &Value) -> Result<Value> {
    if is_reducible(s) {
        return filter_reducible(s, &mut |e| member(e, t));
    }
    if is_reducible(t) {
        return filter_reducible(t, &mut |e| member(e, s));
    }
    Ok(lazy(LazySet::Cap(s.clone(), t.clone())))
}

/// `s \ t` (eager when `s` is an enumerated set / interval).
///
/// Like TLC (`Reducible.diff`), `t` is only used through membership tests.
pub fn difference(s: &Value, t: &Value) -> Result<Value> {
    if is_reducible(s) {
        return filter_reducible(s, &mut |e| Ok(!member(e, t)?));
    }
    Ok(lazy(LazySet::Diff(s.clone(), t.clone())))
}

/// `s \subseteq t`
pub fn subseteq(s: &Value, t: &Value) -> Result<bool> {
    if !is_enumerable(s) {
        return err("Attempted to evaluate an expression of form S \\subseteq T, but S was not enumerable.");
    }
    if let (Value::Interval(a, b), Value::Interval(c, d)) = (s, t) {
        if c <= a && d >= b {
            return Ok(true);
        }
    }
    if let (Value::LazySet(x), Value::LazySet(y)) = (s, t) {
        if let (LazySet::Subset(a), LazySet::Subset(b)) = (&**x, &**y) {
            if is_enumerable(a) {
                return subseteq(a, b);
            }
        }
    }
    let mut res = true;
    super::for_each_enumerated(s, &mut |e| {
        if member(&e, t)? {
            Ok(true)
        } else {
            res = false;
            Ok(false)
        }
    })?;
    Ok(res)
}

/// `SUBSET s` (lazy)
pub fn powerset(s: &Value) -> Result<Value> {
    Ok(lazy(LazySet::Subset(s.clone())))
}

struct MergeHead {
    value: Value,
    set: usize,
    pos: usize,
}

fn heap_sift_up(heap: &mut [MergeHead], mut i: usize) -> Result<()> {
    while i > 0 {
        let p = (i - 1) / 2;
        if cmp_tlc(&heap[i].value, &heap[p].value)? == Ordering::Less {
            heap.swap(i, p);
            i = p;
        } else {
            break;
        }
    }
    Ok(())
}

fn heap_sift_down(heap: &mut [MergeHead], mut i: usize) -> Result<()> {
    let n = heap.len();
    loop {
        let l = 2 * i + 1;
        if l >= n {
            break;
        }
        let r = l + 1;
        let smallest = if r < n && cmp_tlc(&heap[r].value, &heap[l].value)? == Ordering::Less { r } else { l };
        if cmp_tlc(&heap[smallest].value, &heap[i].value)? == Ordering::Less {
            heap.swap(i, smallest);
            i = smallest;
        } else {
            break;
        }
    }
    Ok(())
}

fn heap_pop(heap: &mut Vec<MergeHead>) -> Result<Option<MergeHead>> {
    let Some(last) = heap.pop() else {
        return Ok(None);
    };
    if heap.is_empty() {
        return Ok(Some(last));
    }
    let first = std::mem::replace(&mut heap[0], last);
    heap_sift_down(heap, 0)?;
    Ok(Some(first))
}

/// The distinct union of normalized member sets: one sort when the total
/// occurrences fit the bound, otherwise a k-way min-heap merge that stops
/// immediately at distinct element `growth_limit() + 1` without flattening
/// every occurrence into memory.
fn union_normalized(lists: &[&[Value]], occurrences: usize) -> Result<Value> {
    let limit = crate::limits::growth_limit();
    if occurrences as i64 <= limit {
        let mut all = Vec::with_capacity(occurrences);
        for x in lists {
            all.extend(x.iter().cloned());
        }
        let all = normalize_vec(all)?;
        crate::limits::check_set_size(all.len())?;
        return Ok(Value::Set(Arc::from(all)));
    }
    let mut heap: Vec<MergeHead> = Vec::with_capacity(lists.len());
    for (si, x) in lists.iter().enumerate() {
        if let Some(first) = x.first() {
            heap.push(MergeHead { value: first.clone(), set: si, pos: 0 });
            let i = heap.len() - 1;
            heap_sift_up(&mut heap, i)?;
        }
    }
    let mut out: Vec<Value> = Vec::new();
    while let Some(head) = heap_pop(&mut heap)? {
        let x = lists[head.set];
        let next_pos = head.pos + 1;
        let distinct = match out.last() {
            Some(last) => !crate::order::eq_tlc(last, &head.value)?,
            None => true,
        };
        if distinct {
            crate::limits::push(&mut out, head.value)?;
        }
        if next_pos < x.len() {
            heap.push(MergeHead { value: x[next_pos].clone(), set: head.set, pos: next_pos });
            let i = heap.len() - 1;
            heap_sift_up(&mut heap, i)?;
        }
    }
    Ok(Value::Set(Arc::from(out)))
}

/// `UNION s`
pub fn big_union(s: &Value) -> Result<Value> {
    if let Some(sets) = s.enum_elements() {
        // A family of differently sized normalized sets (e.g. `{{1, 2}, {2, 3, 4}}`)
        // stays `LazySet::Enum` at the outer level; when every member is a
        // normalized `Value::Set` and all elements share a comparison family,
        // `union_normalized` computes the same distinct union in O(N log k)
        // without allocating past the bound.
        if matches!(s, Value::LazySet(_)) && sets.iter().all(|e| matches!(e, Value::Set(_))) {
            let mut total: usize = 0;
            let mut lists: Vec<&[Value]> = Vec::with_capacity(sets.len());
            let mut first: Option<&Value> = None;
            let mut comparable = true;
            for e in sets {
                let Value::Set(x) = e else { unreachable!("checked above") };
                total = total.saturating_add(x.len());
                if comparable {
                    for elem in x.iter() {
                        match first {
                            None => first = Some(elem),
                            Some(f) if !same_comparison_family(f, elem) => {
                                comparable = false;
                                break;
                            }
                            Some(_) => {}
                        }
                    }
                }
                lists.push(x);
            }
            if comparable {
                return union_normalized(&lists, total);
            }
        }
        if sets.iter().all(|e| e.enum_elements().is_some())
            && (matches!(s, Value::LazySet(_)) || sets.iter().any(|e| matches!(e, Value::LazySet(_))))
        {
            // UnionValue.union scans explicit inner sets without sorting
            // either level, testing membership in the accumulated result.
            let mut out = Vec::new();
            for set in sets {
                for e in set.enum_elements().unwrap() {
                    let mut found = false;
                    for old in &out {
                        if crate::order::eq_tlc(old, e)? {
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        crate::limits::push(&mut out, e.clone())?;
                    }
                }
            }
            return Value::set_enum(out);
        }
    }
    if let Value::Set(sets) = s {
        if sets.iter().all(|e| matches!(e, Value::Set(_))) {
            // TLC's eager `UnionValue.union` adds an element only when the
            // result does not already contain it, so the bound applies to the
            // distinct elements, not to the occurrences.
            let mut occurrences: usize = 0;
            let mut lists: Vec<&[Value]> = Vec::with_capacity(sets.len());
            for e in sets.iter() {
                let Value::Set(x) = e else { unreachable!("checked above") };
                occurrences = occurrences.saturating_add(x.len());
                lists.push(x);
            }
            return union_normalized(&lists, occurrences);
        }
    }
    Ok(lazy(LazySet::Union(s.clone())))
}

/// `[s -> t]` (lazy)
pub fn fcn_set(s: &Value, t: &Value) -> Result<Value> {
    Ok(lazy(LazySet::FcnSet(s.clone(), t.clone())))
}

/// `s1 \X ... \X sn` (lazy)
pub fn product(sets: Vec<Value>) -> Result<Value> {
    Ok(lazy(LazySet::Product(sets)))
}

/// `[f1 : s1, ...]` (lazy)
pub fn record_set(mut fields: Vec<(Sym, Value)>) -> Result<Value> {
    fields.sort_by_key(|f| f.0);
    let mut out: Vec<(Sym, Value)> = Vec::with_capacity(fields.len());
    for f in fields {
        match out.last_mut() {
            Some(last) if last.0 == f.0 => *last = f,
            _ => out.push(f),
        }
    }
    Ok(lazy(LazySet::RecordSet(out)))
}

/// `lo..hi`
pub fn interval(lo: i64, hi: i64) -> Value {
    Value::Interval(lo, hi)
}
