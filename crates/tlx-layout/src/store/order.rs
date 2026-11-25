//! TLC's `equals` and `compareTo` on stored handles, without thawing:
//! `tlx_value::order::{eq_tlc, cmp_tlc}` specialized for the
//! stored kinds (scalars, sets, intervals, tuples, records, functions),
//! dispatching on the left operand like TLC. The model-value rules and
//! other mixtures of kinds that are not mirrored here are delegated to
//! `tlx_value::order` on the thawed values, so the result and every error
//! are exactly the interpreter's.

use std::cmp::Ordering;

use tlx_value::plan::{ComparisonKind, FunctionComparison};
use tlx_value::Sym;

use super::ops::RefOpError;
use super::{int_handle, is_immediate, str_handle, tag, Body, Store, TAG_BOOL, TAG_INT, TAG_MODEL_VALUE, TAG_STR};
use crate::scalar;

type R<T> = Result<T, RefOpError>;

/// A stored function seen as TLC's `FcnRcdValue` view (`repr::FcnRef`).
#[derive(Clone, Copy)]
pub(crate) enum Fn<'a> {
    Tuple(&'a [u64]),
    Record(&'a [(Sym, u64)]),
    /// Keys (sorted in TLC order) and values.
    Fcn(&'a [u64], &'a [u64]),
}

impl Fn<'_> {
    pub(crate) fn len(&self) -> usize {
        match self {
            Fn::Tuple(t) => t.len(),
            Fn::Record(r) => r.len(),
            Fn::Fcn(k, _) => k.len(),
        }
    }
    pub(crate) fn key(&self, i: usize) -> u64 {
        match self {
            Fn::Tuple(_) => int_handle(i as i64 + 1).expect("tuple index"),
            Fn::Record(r) => str_handle(r[i].0),
            Fn::Fcn(k, _) => k[i],
        }
    }
    pub(crate) fn val(&self, i: usize) -> u64 {
        match self {
            Fn::Tuple(t) => t[i],
            Fn::Record(r) => r[i].1,
            Fn::Fcn(_, v) => v[i],
        }
    }
}

/// What a handle is, for the comparisons.
enum View<'a> {
    Imm(u64),
    BigInt(i64),
    Set(&'a [u64]),
    Interval(i64, i64),
    Fn(Fn<'a>),
}

fn view(s: &Store, h: u64) -> View<'_> {
    if is_immediate(h) {
        return View::Imm(h);
    }
    match &s.get(h).body {
        Body::Int(i) => View::BigInt(*i),
        Body::Set(es) => View::Set(es),
        Body::Interval(lo, hi) => View::Interval(*lo, *hi),
        Body::Tuple(t) => View::Fn(Fn::Tuple(t)),
        Body::Record(r) => View::Fn(Fn::Record(r)),
        // The empty function of an enumerated domain compares as `<<>>`.
        Body::Fcn(kv, _) if kv.is_empty() => View::Fn(Fn::Tuple(&[])),
        Body::Fcn(kv, _) => {
            let (k, v) = kv.split_at(kv.len() / 2);
            View::Fn(Fn::Fcn(k, v))
        }
    }
}

/// The function view of a handle (None: not a function).
pub(crate) fn fn_view(s: &Store, h: u64) -> Option<Fn<'_>> {
    match view(s, h) {
        View::Fn(f) => Some(f),
        _ => None,
    }
}

fn delegate_eq(s: &Store, a: u64, b: u64) -> R<bool> {
    tlx_value::order::eq_tlc(&s.thaw(a), &s.thaw(b)).map_err(|_| RefOpError::Eval)
}

fn delegate_cmp(s: &Store, a: u64, b: u64) -> R<Ordering> {
    tlx_value::order::cmp_tlc(&s.thaw(a), &s.thaw(b)).map_err(|_| RefOpError::Eval)
}

fn interval_len(lo: i64, hi: i64) -> usize {
    if hi < lo {
        0
    } else {
        (hi - lo + 1) as usize
    }
}

/// Compare a stored handle `h` against a 64-bit integer `v` without allocating
/// or populating `Node::elems`; `h_left` selects TLC's left/right operand order.
fn eq_with_int(s: &Store, h: u64, v: i64, h_left: bool) -> R<bool> {
    if let Some(vh) = int_handle(v) {
        return if h_left { eq_tlc(s, h, vh) } else { eq_tlc(s, vh, h) };
    }
    if tag(h) == TAG_INT {
        return Ok(false);
    }
    if let Some(Body::Int(x)) = s.node(h).map(|n| &n.body) {
        return Ok(*x == v);
    }
    let iv = tlx_value::Value::Int(v);
    let hv = s.thaw(h);
    let r = if h_left { tlx_value::order::eq_tlc(&hv, &iv) } else { tlx_value::order::eq_tlc(&iv, &hv) };
    r.map_err(|_| RefOpError::Eval)
}

fn cmp_with_int(s: &Store, h: u64, v: i64, h_left: bool) -> R<Ordering> {
    if let Some(vh) = int_handle(v) {
        return if h_left { cmp_tlc(s, h, vh) } else { cmp_tlc(s, vh, h) };
    }
    if tag(h) == TAG_INT {
        let x = (h as i64) >> scalar::TAG_BITS;
        return Ok(if h_left { x.cmp(&v) } else { v.cmp(&x) });
    }
    if let Some(Body::Int(x)) = s.node(h).map(|n| &n.body) {
        return Ok(if h_left { x.cmp(&v) } else { v.cmp(x) });
    }
    let iv = tlx_value::Value::Int(v);
    let hv = s.thaw(h);
    let r = if h_left { tlx_value::order::cmp_tlc(&hv, &iv) } else { tlx_value::order::cmp_tlc(&iv, &hv) };
    r.map_err(|_| RefOpError::Eval)
}

fn eq_set_interval(s: &Store, es: &[u64], lo: i64, hi: i64, set_left: bool) -> R<bool> {
    if es.len() != interval_len(lo, hi) {
        return Ok(false);
    }
    for (&h, v) in es.iter().zip(lo..=hi) {
        if !eq_with_int(s, h, v, set_left)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn cmp_set_interval(s: &Store, es: &[u64], lo: i64, hi: i64, set_left: bool) -> R<Ordering> {
    let n = interval_len(lo, hi);
    let c = if set_left { es.len().cmp(&n) } else { n.cmp(&es.len()) };
    if c != Ordering::Equal {
        return Ok(c);
    }
    for (&h, v) in es.iter().zip(lo..=hi) {
        let c = cmp_with_int(s, h, v, set_left)?;
        if c != Ordering::Equal {
            return Ok(c);
        }
    }
    Ok(Ordering::Equal)
}

/// TLC `a.equals(b)` on handles (`order::eq_tlc`).
pub fn eq_tlc(s: &Store, a: u64, b: u64) -> R<bool> {
    if !s.is_valid(a) || !s.is_valid(b) {
        return Err(RefOpError::Eval);
    }
    if a == b {
        return Ok(true);
    }
    match (tag(a), tag(b)) {
        (TAG_INT, TAG_INT) | (TAG_STR, TAG_STR) | (TAG_BOOL, TAG_BOOL) => return Ok(false),
        _ => {}
    }
    // Model values (typed or not) on either side, and scalar mixtures:
    // TLC's rules, by the interpreter.
    if tag(a) == TAG_MODEL_VALUE || tag(b) == TAG_MODEL_VALUE || (is_immediate(a) && is_immediate(b)) {
        return delegate_eq(s, a, b);
    }
    match (view(s, a), view(s, b)) {
        (View::BigInt(x), View::BigInt(y)) => Ok(x == y),
        (View::BigInt(_), View::Imm(y)) if tag(y) == TAG_INT => Ok(false),
        (View::Imm(x), View::BigInt(_)) if tag(x) == TAG_INT => Ok(false),
        (View::Interval(l1, h1), View::Interval(l2, h2)) => Ok(if h1 < l1 { h2 < l2 } else { l1 == l2 && h1 == h2 }),
        (View::Set(x), View::Set(y)) => {
            if x.len() != y.len() {
                return Ok(false);
            }
            eq_seq(s, x.iter().copied(), y.iter().copied())
        }
        (View::Set(x), View::Interval(lo, hi)) => eq_set_interval(s, x, lo, hi, true),
        (View::Interval(lo, hi), View::Set(y)) => eq_set_interval(s, y, lo, hi, false),
        (View::Fn(x), View::Fn(y)) => match (x, y) {
            (Fn::Tuple(t), Fn::Tuple(u)) => {
                if t.len() != u.len() {
                    return Ok(false);
                }
                eq_seq(s, t.iter().copied(), u.iter().copied())
            }
            (Fn::Tuple(_), _) => fcn_eq(s, x, y),
            (Fn::Record(r), Fn::Record(q)) => record_eq(s, r.iter().copied(), q.iter().copied(), r.len(), q.len()),
            (Fn::Record(_), Fn::Tuple([])) => Ok(false),
            (Fn::Record(r), Fn::Fcn(k, v)) if super::fcn_alias(k) == super::Alias::Record => {
                // A function over strings converts to the record (toRcd).
                let q = k.iter().zip(v).map(|(k, v)| (sym_of(*k), *v));
                record_eq(s, r.iter().copied(), q, r.len(), k.len())
            }
            (Fn::Record(_), _) => fcn_eq(s, x, y),
            (Fn::Fcn(..), _) => fcn_eq(s, x, y),
        },
        _ => delegate_eq(s, a, b),
    }
}

fn sym_of(h: u64) -> Sym {
    super::symbol(h).expect("invalid symbol handle")
}

fn eq_seq(s: &Store, a: impl Iterator<Item = u64>, b: impl Iterator<Item = u64>) -> R<bool> {
    for (x, y) in a.zip(b) {
        if !eq_tlc(s, x, y)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn record_eq(
    s: &Store,
    r: impl Iterator<Item = (Sym, u64)> + Clone,
    q: impl Iterator<Item = (Sym, u64)> + Clone,
    n: usize,
    m: usize,
) -> R<bool> {
    if n != m || r.clone().zip(q.clone()).any(|(x, y)| x.0 != y.0) {
        return Ok(false);
    }
    eq_seq(s, r.map(|x| x.1), q.map(|y| y.1))
}

/// `this.equals(fcn)` with both sides as FcnRcdValues (`order::fcn_eq`).
fn fcn_eq(s: &Store, x: Fn<'_>, y: Fn<'_>) -> R<bool> {
    let plan = FunctionComparison::new(x.len(), y.len(), matches!(x, Fn::Tuple(_)), matches!(y, Fn::Tuple(_)));
    if plan.length_order != Ordering::Equal {
        return Ok(false);
    }
    for i in plan.domains {
        if domain_cmp(s, x.key(i), y.key(i)) != Ordering::Equal {
            return Ok(false);
        }
    }
    for i in plan.values {
        if !eq_tlc(s, x.val(i), y.val(i))? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// TLC `a.compareTo(b)` on handles (`order::cmp_tlc`).
pub fn cmp_tlc(s: &Store, a: u64, b: u64) -> R<Ordering> {
    if !s.is_valid(a) || !s.is_valid(b) {
        return Err(RefOpError::Eval);
    }
    if a == b {
        return Ok(Ordering::Equal);
    }
    match (tag(a), tag(b)) {
        (TAG_INT, TAG_INT) => return Ok((a as i64 >> scalar::TAG_BITS).cmp(&(b as i64 >> scalar::TAG_BITS))),
        // (Strings by `Sym` order: their ids; Booleans by payload.)
        (TAG_STR, TAG_STR) | (TAG_BOOL, TAG_BOOL) => return Ok((a >> scalar::TAG_BITS).cmp(&(b >> scalar::TAG_BITS))),
        _ => {}
    }
    if tag(a) == TAG_MODEL_VALUE || tag(b) == TAG_MODEL_VALUE || (is_immediate(a) && is_immediate(b)) {
        return delegate_cmp(s, a, b);
    }
    match (view(s, a), view(s, b)) {
        (View::BigInt(x), View::BigInt(y)) => Ok(x.cmp(&y)),
        (View::BigInt(x), View::Imm(y)) if tag(y) == TAG_INT => Ok(x.cmp(&(y as i64 >> scalar::TAG_BITS))),
        (View::Imm(x), View::BigInt(y)) if tag(x) == TAG_INT => Ok((x as i64 >> scalar::TAG_BITS).cmp(&y)),
        (View::Interval(l1, h1), View::Interval(l2, h2)) => {
            let (n1, n2) = (interval_len(l1, h1), interval_len(l2, h2));
            if n1 != n2 || n1 == 0 {
                return Ok(n1.cmp(&n2));
            }
            Ok(l1.cmp(&l2))
        }
        (View::Set(x), View::Set(y)) => {
            let c = x.len().cmp(&y.len());
            if c != Ordering::Equal {
                return Ok(c);
            }
            cmp_seq(s, x.iter().copied(), y.iter().copied())
        }
        (View::Set(x), View::Interval(lo, hi)) => cmp_set_interval(s, x, lo, hi, true),
        (View::Interval(lo, hi), View::Set(y)) => cmp_set_interval(s, y, lo, hi, false),
        (View::Fn(x), View::Fn(y)) => match (x, y) {
            (Fn::Tuple(t), Fn::Tuple(u)) => {
                let c = t.len().cmp(&u.len());
                if c != Ordering::Equal {
                    return Ok(c);
                }
                cmp_seq(s, t.iter().copied(), u.iter().copied())
            }
            (Fn::Tuple(_), _) => fcn_cmp(s, x, y),
            (Fn::Record(r), Fn::Record(q)) => record_cmp(s, r.iter().copied(), q.iter().copied(), r.len(), q.len()),
            // `<<>>` converts to the empty record; `r` is non-empty.
            (Fn::Record(r), Fn::Tuple([])) => Ok(r.len().cmp(&0)),
            (Fn::Record(r), Fn::Fcn(k, v)) if super::fcn_alias(k) == super::Alias::Record => {
                let q = k.iter().zip(v).map(|(k, v)| (sym_of(*k), *v));
                record_cmp(s, r.iter().copied(), q, r.len(), k.len())
            }
            (Fn::Record(_), _) => fcn_cmp(s, x, y),
            (Fn::Fcn(..), _) => fcn_cmp(s, x, y),
        },
        _ => delegate_cmp(s, a, b),
    }
}

fn cmp_seq(s: &Store, a: impl Iterator<Item = u64>, b: impl Iterator<Item = u64>) -> R<Ordering> {
    for (x, y) in a.zip(b) {
        let c = cmp_tlc(s, x, y)?;
        if c != Ordering::Equal {
            return Ok(c);
        }
    }
    Ok(Ordering::Equal)
}

fn record_cmp(
    s: &Store,
    r: impl Iterator<Item = (Sym, u64)> + Clone,
    q: impl Iterator<Item = (Sym, u64)> + Clone,
    n: usize,
    m: usize,
) -> R<Ordering> {
    let c = n.cmp(&m);
    if c != Ordering::Equal {
        return Ok(c);
    }
    for (x, y) in r.clone().zip(q.clone()) {
        let c = x.0.cmp(&y.0);
        if c != Ordering::Equal {
            return Ok(c);
        }
    }
    cmp_seq(s, r.map(|x| x.1), q.map(|y| y.1))
}

/// `order::fcn_cmp`.
fn fcn_cmp(s: &Store, x: Fn<'_>, y: Fn<'_>) -> R<Ordering> {
    let plan = FunctionComparison::new(x.len(), y.len(), matches!(x, Fn::Tuple(_)), matches!(y, Fn::Tuple(_)));
    if plan.length_order != Ordering::Equal {
        return Ok(plan.length_order);
    }
    for i in plan.domains {
        let c = domain_cmp(s, x.key(i), y.key(i));
        if c != Ordering::Equal {
            return Ok(c);
        }
    }
    for i in plan.values {
        let c = cmp_tlc(s, x.val(i), y.val(i))?;
        if c != Ordering::Equal {
            return Ok(c);
        }
    }
    Ok(Ordering::Equal)
}

/// D-31: unlike mapped values, unequal domain-key kinds have a total order.
/// Keep the allocation-free comparison for ordinary domains. Frozen values
/// contain no lazy values, so structural comparison cannot fail here.
fn domain_cmp(s: &Store, a: u64, b: u64) -> Ordering {
    let (ka, kb) = (comparison_kind(s, a), comparison_kind(s, b));
    if ka != kb {
        return ka.cmp(&kb);
    }
    cmp_tlc(s, a, b).unwrap_or_else(|_| s.thaw(a).cmp(&s.thaw(b)))
}

/// Decode the representation; the kind order itself belongs to tlx-value.
fn comparison_kind(s: &Store, h: u64) -> ComparisonKind {
    match view(s, h) {
        View::Imm(h) => match tag(h) {
            TAG_MODEL_VALUE => ComparisonKind::ModelValue,
            TAG_BOOL => ComparisonKind::Bool,
            TAG_INT => ComparisonKind::Int,
            TAG_STR => ComparisonKind::Str,
            _ => unreachable!("validated immediate"),
        },
        View::BigInt(_) => ComparisonKind::Int,
        View::Set(_) | View::Interval(..) => ComparisonKind::Set,
        View::Fn(_) => ComparisonKind::Function,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tlx_value::{ops, order, Value};

    #[test]
    fn stored_function_decisions_match_boxed_consumers() {
        let store = Store::new(usize::MAX);
        let keys = [
            Value::model_value("matrix_untyped"),
            Value::model_value("x_matrix"),
            Value::TRUE,
            Value::Int(2),
            Value::str("matrix_key"),
            Value::set_from(vec![Value::Int(2)]).unwrap(),
            Value::tuple(vec![Value::Int(2)]),
            Value::record(vec![(Sym::new("matrix_key"), Value::Int(2))]),
        ];
        let mut functions: Vec<_> = keys.iter().map(|k| ops::single_fcn(k.clone(), Value::Int(0)).unwrap()).collect();
        functions.extend([
            Value::tuple(vec![Value::Int(0)]),
            ops::single_fcn(Value::Int(1), Value::Int(0)).unwrap(),
            Value::fcn_over(&Value::Interval(1, 1), vec![(Value::Int(1), Value::Int(0))]).unwrap(),
            Value::empty_fcn(),
            Value::tuple(vec![]),
        ]);
        // Equal domains expose a mapped error; unequal domains hide it.
        for key in [2, 3] {
            for value in [Value::Int(0), Value::str("mapped_error")] {
                functions.push(Value::fcn_rcd_from_pairs(vec![(Value::Int(0), value), (Value::Int(key), Value::Int(9))]).unwrap());
            }
        }
        let handles: Vec<_> = functions.iter().map(|v| store.freeze(v).unwrap()).collect();
        for (i, a) in functions.iter().enumerate() {
            for (j, b) in functions.iter().enumerate() {
                assert_eq!(cmp_tlc(&store, handles[i], handles[j]).ok(), order::cmp_tlc(a, b).ok(), "{a} vs {b}");
                assert_eq!(eq_tlc(&store, handles[i], handles[j]).ok(), order::eq_tlc(a, b).ok(), "{a} = {b}");
            }
        }
    }
}
