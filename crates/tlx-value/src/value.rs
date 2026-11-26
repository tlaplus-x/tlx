use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use crate::error::err;
use crate::intern::Sym;
use crate::lazy::{LazyFcn, LazySet};
use crate::order::{cmp_tlc, try_total_cmp};

/// A TLA+ value. Cheap to clone (compound values are reference counted).
///
/// Trait impls: `PartialEq/Eq/Hash/Ord` are *total* and structural on
/// canonical forms, suitable for sorting and hash maps of normalized values
/// (lazy values are compared by normalizing them, panicking if impossible).
/// Use `ops`/`order` for TLC semantics with errors (`eq_tlc`, `cmp_tlc`).
#[derive(Clone)]
pub enum Value {
    Bool(bool),
    /// TLC integers are 32-bit; arithmetic in `arith` checks i32 overflow.
    Int(i64),
    Str(Sym),
    ModelValue(Sym),
    /// Finite set: sorted in TLC order, no duplicates.
    Set(Arc<[Value]>),
    /// `lo..hi` (empty when hi < lo).
    Interval(i64, i64),
    /// Function with domain `1..n` (sequences, tuples, the empty function).
    Tuple(Arc<[Value]>),
    /// Function with a non-empty domain of strings; fields sorted by `Sym` order.
    Record(Arc<[(Sym, Value)]>),
    /// Any other finite function; pairs sorted by key in TLC order, keys
    /// distinct.
    ///
    /// A function TLC builds as an `FcnRcdValue` over an enumerated domain
    /// (`[x \in {1, 2} |-> e]`, `:>`, `@@`, bags, the elements of
    /// `[{"a"} -> S]`, ...) is an `Fcn` even when its domain is `1..n`
    /// (also empty) or a set of strings (see `FcnKind`): it is equal to the
    /// `Tuple` / `Record` with the same pairs (comparison, hash, fingerprint
    /// and printing use that form; consumers that view functions through
    /// `force_fcn` see it), but EXCEPT and application look keys up by
    /// equality like TLC's `FcnRcdValue`: `[f EXCEPT ![m] = e]` with a model
    /// value `m` leaves it unchanged, where a `Tuple` or `Record` rejects the
    /// key.
    ///
    /// The `FcnDom` tells how keys are looked up: by equality (an
    /// enumerated domain, above), or, for a function TLC builds as an
    /// `FcnRcdValue` over an integer interval `lo..hi` (`[k \in 0..2 |-> e]`,
    /// the elements of `[0..2 -> S]`; with `lo = 1` it is a `Tuple`), as
    /// integers: a key that is not an integer is an error, also for EXCEPT
    /// (`FcnRcdValue.select` with `intv`). It does not take part in
    /// comparison, hashing, fingerprints or printing.
    Fcn(Arc<[(Value, Value)]>, FcnDom),
    LazySet(Arc<LazySet>),
    LazyFcn(Arc<dyn LazyFcn>),
}

impl Value {
    pub const TRUE: Value = Value::Bool(true);
    pub const FALSE: Value = Value::Bool(false);

    pub fn str(s: &str) -> Value {
        Value::Str(Sym::new(s))
    }

    pub fn model_value(name: &str) -> Value {
        Value::ModelValue(Sym::new(name))
    }

    pub fn empty_set() -> Value {
        Value::Set(Arc::from(Vec::new()))
    }

    /// Build a set from arbitrary elements (sorts and deduplicates in TLC order).
    /// Errors if elements are not comparable (TLC semantics).
    pub fn set_from(elems: Vec<Value>) -> crate::Result<Value> {
        Ok(Value::Set(Arc::from(normalize_vec(elems)?)))
    }

    /// A set expression. TLC does not compare its elements at construction.
    /// Homogeneous values can keep the canonical representation; defer the
    /// others so membership and set algebra can inspect them without sorting.
    ///
    /// TLC builds such a set in a `ValueVec` that may grow only up to
    /// `setBound` (`-maxSetSize`), so a set of more elements is an error
    /// (`ValueVec.ensureCapacity`).
    pub fn set_enum(elems: Vec<Value>) -> crate::Result<Value> {
        crate::limits::check_set_size(elems.len())?;
        Self::set_enum_unbounded(elems)
    }

    /// A set literal `{e1, ..., en}`: TLC preallocates its `ValueVec` to the
    /// literal's length, so `setBound` (`-maxSetSize`) never applies to it —
    /// `ensureCapacity` is reached only when a vector grows.
    pub fn set_literal(elems: Vec<Value>) -> crate::Result<Value> {
        Self::set_enum_unbounded(elems)
    }

    fn set_enum_unbounded(elems: Vec<Value>) -> crate::Result<Value> {
        if elems.first().is_none_or(|first| elems.iter().all(|e| same_comparison_family(first, e))) {
            Self::set_from(elems)
        } else {
            Ok(Value::LazySet(Arc::new(LazySet::Enum(elems))))
        }
    }

    /// Stored elements of an explicit set, possibly unsorted and duplicated.
    /// Only operations that TLC performs without normalization use this view.
    pub fn enum_elements(&self) -> Option<&[Value]> {
        match self {
            Value::Set(es) => Some(es),
            Value::LazySet(l) => match &**l {
                LazySet::Enum(es) => Some(es),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn tuple(elems: Vec<Value>) -> Value {
        Value::Tuple(Arc::from(elems))
    }

    /// The empty function of an enumerated domain (see `Value::Fcn`).
    pub fn empty_fcn() -> Value {
        Value::Fcn(Arc::from(Vec::new()), FcnDom::Enumerated)
    }

    /// Is this the empty function of an enumerated domain?
    pub fn is_empty_fcn(&self) -> bool {
        matches!(self, Value::Fcn(p, _) if p.is_empty())
    }

    /// A function TLC builds as an `FcnRcdValue` over an enumerated domain
    /// (`:>`, `@@`, bags, permutations, ...): an `Fcn` whatever its domain
    /// (keys distinct; sorted here).
    pub fn fcn_rcd_from_pairs(pairs: Vec<(Value, Value)>) -> crate::Result<Value> {
        Ok(Value::Fcn(Arc::from(sort_pairs(pairs)?), FcnDom::Enumerated))
    }

    /// The function with domain `domain` and the given pairs, as TLC builds
    /// it from a function constructor or a set of functions
    /// (`FcnLambdaValue.toFcnRcd`, `SetOfFcnsValue`): over an interval an
    /// `FcnRcdValue` with an interval domain (a `Tuple` for `1..n`, else an
    /// `Fcn` with `FcnDom::Interval`), otherwise one over the enumerated
    /// domain (`fcn_rcd_from_pairs`).
    pub fn fcn_over(domain: &Value, pairs: Vec<(Value, Value)>) -> crate::Result<Value> {
        if matches!(domain, Value::Interval(..)) {
            Ok(fcn_over_interval(sort_pairs(pairs)?))
        } else {
            Value::fcn_rcd_from_pairs(pairs)
        }
    }

    /// Build a function from sorted, distinct pairs with an explicit domain witness.
    pub fn fcn_with_dom(pairs: Vec<(Value, Value)>, dom: FcnDom) -> Value {
        Value::Fcn(Arc::from(pairs), dom)
    }

    /// Build a function over an integer interval from sorted, distinct pairs:
    /// `Tuple` for empty / `1..n`, else `Fcn(_, FcnDom::Interval)`.
    pub fn fcn_over_interval_sorted(pairs: Vec<(Value, Value)>) -> Value {
        fcn_over_interval(pairs)
    }

    /// Build the structured/canonical function value from sorted, distinct
    /// pairs: `Tuple` for empty / `1..n`, `Record` for non-empty all-string
    /// domains, `Fcn(_, FcnDom::Interval)` for contiguous `lo..hi` (`lo # 1`),
    /// otherwise `Fcn(_, FcnDom::Enumerated)`.
    pub fn fcn_canonical_sorted(pairs: Vec<(Value, Value)>) -> Value {
        use crate::plan::Witness;
        match Witness::canonical_of_sorted_keys(pairs.iter().map(|(k, _)| k)) {
            Witness::Tuple => Value::Tuple(pairs.into_iter().map(|(_, v)| v).collect()),
            Witness::Record => Value::Record(
                pairs
                    .into_iter()
                    .map(|(k, v)| match k {
                        Value::Str(s) => (s, v),
                        _ => unreachable!(),
                    })
                    .collect(),
            ),
            Witness::Interval => Value::Fcn(Arc::from(pairs), FcnDom::Interval),
            Witness::Enumerated => Value::Fcn(Arc::from(pairs), FcnDom::Enumerated),
        }
    }

    /// This function as TLC's `FcnRcdValue` over an enumerated domain: a
    /// `Tuple` or `Record` becomes the equal `Fcn` (see `Value::Fcn`); other
    /// values are returned unchanged.
    pub fn into_fcn_rcd(self) -> Value {
        match self {
            Value::Tuple(es) => {
                Value::Fcn(es.iter().enumerate().map(|(i, e)| (Value::Int(i as i64 + 1), e.clone())).collect(), FcnDom::Enumerated)
            }
            // (Fields are sorted by `Sym` order, the TLC order of strings.)
            Value::Record(fs) => Value::Fcn(fs.iter().map(|(k, e)| (Value::Str(*k), e.clone())).collect(), FcnDom::Enumerated),
            Value::Fcn(ps, FcnDom::Interval) => Value::Fcn(ps, FcnDom::Enumerated),
            v => v,
        }
    }

    /// The `Tuple` / `Record` an `Fcn` with such a domain is equal to (TLC's
    /// `toTuple` / `toRcd`, see `FcnKind`); `None` for any other value.
    pub fn fcn_canonical(&self) -> Option<Value> {
        let Value::Fcn(pairs, _) = self else { return None };
        match FcnKind::of(pairs) {
            FcnKind::Tuple => Some(Value::Tuple(pairs.iter().map(|(_, v)| v.clone()).collect())),
            FcnKind::Record => Some(Value::Record(
                pairs
                    .iter()
                    .map(|(k, v)| match k {
                        Value::Str(s) => (*s, v.clone()),
                        _ => unreachable!("record-like keys are strings"),
                    })
                    .collect(),
            )),
            FcnKind::Fcn => None,
        }
    }

    /// Build a record; fields may be given in any order (duplicates: last wins).
    pub fn record(mut fields: Vec<(Sym, Value)>) -> Value {
        if fields.is_empty() {
            return Value::tuple(Vec::new());
        }
        if !fields.windows(2).all(|w| w[0].0 < w[1].0) {
            fields.sort_by_key(|f| f.0); // stable: duplicates keep input order
            let mut out: Vec<(Sym, Value)> = Vec::with_capacity(fields.len());
            for f in fields {
                match out.last_mut() {
                    Some(last) if last.0 == f.0 => *last = f,
                    _ => out.push(f),
                }
            }
            fields = out;
        }
        Value::Record(Arc::from(fields))
    }

    /// Build a finite function from (key, value) pairs, choosing the canonical
    /// representation (Tuple / Record / Fcn, over an enumerated domain). Keys
    /// must be distinct.
    pub fn fcn_from_pairs(pairs: Vec<(Value, Value)>) -> crate::Result<Value> {
        if pairs.is_empty() {
            return Ok(Value::tuple(Vec::new()));
        }
        // Fast path: keys 1, 2, ..., n in order.
        if pairs.iter().enumerate().all(|(i, (k, _))| matches!(k, Value::Int(n) if *n == i as i64 + 1)) {
            return Ok(Value::Tuple(pairs.into_iter().map(|(_, v)| v).collect()));
        }
        Ok(fcn_from_sorted_pairs(sort_pairs(pairs)?))
    }

    /// Is this value a set (any representation)?
    pub fn is_set(&self) -> bool {
        matches!(self, Value::Set(_) | Value::Interval(..) | Value::LazySet(_))
    }

    pub fn as_bool(&self) -> crate::Result<bool> {
        match self {
            Value::Bool(b) => Ok(*b),
            _ => err(format!("A non-boolean value was used where a boolean was expected:\n{self}")),
        }
    }

    pub fn as_int(&self) -> crate::Result<i64> {
        match self {
            Value::Int(n) => Ok(*n),
            _ => err(format!("A non-integer value was used where an integer was expected:\n{self}")),
        }
    }

    /// Fully normalize: lazy finite sets/functions become `Set`/`Tuple`/`Record`/`Fcn`,
    /// recursively. Errors for infinite values. Values stored in states are normalized.
    ///
    /// `Interval` is kept as is (it is already a canonical, compact set
    /// representation; equality/hash/fingerprint treat it as the set it denotes).
    pub fn normalize(&self) -> crate::Result<Value> {
        if self.is_normal() {
            return Ok(self.clone());
        }
        Ok(match self {
            Value::Set(elems) => Value::Set(elems.iter().map(|e| e.normalize()).collect::<crate::Result<_>>()?),
            Value::Tuple(elems) => Value::Tuple(elems.iter().map(|e| e.normalize()).collect::<crate::Result<_>>()?),
            Value::Record(fields) => Value::Record(fields.iter().map(|(k, v)| Ok((*k, v.normalize()?))).collect::<crate::Result<_>>()?),
            Value::Fcn(pairs, d) => {
                Value::Fcn(pairs.iter().map(|(k, v)| Ok((k.normalize()?, v.normalize()?))).collect::<crate::Result<_>>()?, *d)
            }
            Value::LazySet(_) => {
                let elems = crate::ops::enumerate_normalized(self)?;
                Value::Set(elems.iter().map(|e| e.normalize()).collect::<crate::Result<_>>()?)
            }
            Value::LazyFcn(f) => lazy_fcn_to_value(&**f)?.normalize()?,
            _ => self.clone(),
        })
    }

    /// True if `normalize` would return the value unchanged (no lazy parts).
    pub fn is_normal(&self) -> bool {
        match self {
            Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::ModelValue(_) | Value::Interval(..) => true,
            Value::Set(e) | Value::Tuple(e) => e.iter().all(Value::is_normal),
            Value::Record(f) => f.iter().all(|(_, v)| v.is_normal()),
            Value::Fcn(p, _) => p.iter().all(|(k, v)| k.is_normal() && v.is_normal()),
            Value::LazySet(_) | Value::LazyFcn(_) => false,
        }
    }

    /// Representation-exact equality: agrees with `PartialEq` on scalars, and
    /// additionally distinguishes construction representations (`Interval` vs
    /// `Set`, `Tuple` vs `Record` vs `Fcn(_, Enumerated)` vs `Fcn(_, Interval)`)
    /// recursively.
    pub fn exact_eq(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Str(a), Value::Str(b)) => a == b,
            (Value::ModelValue(a), Value::ModelValue(b)) => a == b,
            (Value::Interval(a, b), Value::Interval(c, d)) => (b < a && d < c) || (a == c && b == d),
            (Value::Set(a), Value::Set(b)) | (Value::Tuple(a), Value::Tuple(b)) => {
                Arc::ptr_eq(a, b) || (a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x.exact_eq(y)))
            }
            (Value::Record(a), Value::Record(b)) => {
                Arc::ptr_eq(a, b) || (a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x.0 == y.0 && x.1.exact_eq(&y.1)))
            }
            (Value::Fcn(a, da), Value::Fcn(b, db)) => {
                da == db
                    && (Arc::ptr_eq(a, b)
                        || (a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x.0.exact_eq(&y.0) && x.1.exact_eq(&y.1))))
            }
            (Value::LazySet(_), Value::LazySet(_)) | (Value::LazyFcn(_), Value::LazyFcn(_)) => self == other,
            _ => false,
        }
    }

    /// Representation-exact hash consistent with `exact_eq`.
    pub fn exact_hash<H: Hasher>(&self, state: &mut H) {
        self.exact_tag().hash(state);
        match self {
            Value::Bool(b) => b.hash(state),
            Value::Int(n) => n.hash(state),
            Value::Str(s) | Value::ModelValue(s) => s.hash(state),
            Value::Interval(lo, hi) => {
                if hi < lo {
                    (1i64, 0i64).hash(state);
                } else {
                    (lo, hi).hash(state);
                }
            }
            Value::Set(es) | Value::Tuple(es) => {
                es.len().hash(state);
                for e in es.iter() {
                    e.exact_hash(state);
                }
            }
            Value::Record(fs) => {
                fs.len().hash(state);
                for (k, v) in fs.iter() {
                    k.hash(state);
                    v.exact_hash(state);
                }
            }
            Value::Fcn(ps, _) => {
                ps.len().hash(state);
                for (k, v) in ps.iter() {
                    k.exact_hash(state);
                    v.exact_hash(state);
                }
            }
            Value::LazySet(_) | Value::LazyFcn(_) => self.hash(state),
        }
    }

    /// Deterministic total order consistent with `exact_eq` (used to sort and
    /// deduplicate exact domain-key variants in `tlx-layout`).
    pub fn exact_cmp(&self, other: &Value) -> Ordering {
        let ord = self.exact_tag().cmp(&other.exact_tag());
        if ord != Ordering::Equal {
            return ord;
        }
        match (self, other) {
            (Value::Bool(a), Value::Bool(b)) => a.cmp(b),
            (Value::Int(a), Value::Int(b)) => a.cmp(b),
            (Value::Str(a), Value::Str(b)) | (Value::ModelValue(a), Value::ModelValue(b)) => a.cmp(b),
            (Value::Interval(a, b), Value::Interval(c, d)) => {
                let lhs = if b < a { (1i64, 0i64) } else { (*a, *b) };
                let rhs = if d < c { (1i64, 0i64) } else { (*c, *d) };
                lhs.cmp(&rhs)
            }
            (Value::Set(a), Value::Set(b)) | (Value::Tuple(a), Value::Tuple(b)) => {
                if Arc::ptr_eq(a, b) {
                    return Ordering::Equal;
                }
                a.len().cmp(&b.len()).then_with(|| {
                    for (x, y) in a.iter().zip(b.iter()) {
                        let o = x.exact_cmp(y);
                        if o != Ordering::Equal {
                            return o;
                        }
                    }
                    Ordering::Equal
                })
            }
            (Value::Record(a), Value::Record(b)) => {
                if Arc::ptr_eq(a, b) {
                    return Ordering::Equal;
                }
                a.len().cmp(&b.len()).then_with(|| {
                    for (x, y) in a.iter().zip(b.iter()) {
                        let o = x.0.cmp(&y.0).then_with(|| x.1.exact_cmp(&y.1));
                        if o != Ordering::Equal {
                            return o;
                        }
                    }
                    Ordering::Equal
                })
            }
            (Value::Fcn(a, _), Value::Fcn(b, _)) => {
                if Arc::ptr_eq(a, b) {
                    return Ordering::Equal;
                }
                a.len().cmp(&b.len()).then_with(|| {
                    for (x, y) in a.iter().zip(b.iter()) {
                        let o = x.0.exact_cmp(&y.0).then_with(|| x.1.exact_cmp(&y.1));
                        if o != Ordering::Equal {
                            return o;
                        }
                    }
                    Ordering::Equal
                })
            }
            (Value::LazySet(_), Value::LazySet(_)) | (Value::LazyFcn(_), Value::LazyFcn(_)) => self.cmp(other),
            _ => unreachable!("same exact_tag implies matching variants"),
        }
    }

    #[inline]
    fn exact_tag(&self) -> u8 {
        match self {
            Value::Bool(_) => 0,
            Value::Int(_) => 1,
            Value::Str(_) => 2,
            Value::ModelValue(_) => 3,
            Value::Set(_) => 4,
            Value::Interval(..) => 5,
            Value::Tuple(_) => 6,
            Value::Record(_) => 7,
            Value::Fcn(_, FcnDom::Enumerated) => 8,
            Value::Fcn(_, FcnDom::Interval) => 9,
            Value::LazySet(_) => 10,
            Value::LazyFcn(_) => 11,
        }
    }
}

/// A conservative, transitive family in which sorting cannot fail. In
/// particular, a lazy value is not certified by its outer representation.
pub(crate) fn same_comparison_family(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Int(_), Value::Int(_))
        | (Value::Str(_), Value::Str(_))
        | (Value::Bool(_), Value::Bool(_))
        | (Value::Interval(..), Value::Interval(..)) => true,
        (Value::ModelValue(a), Value::ModelValue(b)) => a.model_value_type() == b.model_value_type(),
        (Value::Tuple(a), Value::Tuple(b)) | (Value::Set(a), Value::Set(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| same_comparison_family(a, b))
        }
        (Value::Record(a), Value::Record(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|((k, a), (l, b))| k == l && same_comparison_family(a, b))
        }
        (Value::Fcn(a, _), Value::Fcn(b, _)) => {
            a.len() == b.len()
                && a.iter().zip(b.iter()).all(|((k, a), (l, b))| same_comparison_family(k, l) && same_comparison_family(a, b))
        }
        _ => false,
    }
}

/// The heap bytes retained by `values` (statistics): the allocations of
/// their composite parts, recursively, each shared allocation counted
/// once (`seen` holds the addresses already counted, so several calls can
/// share it). Lazy values count their top-level object only.
pub fn retained_heap_bytes<'a>(values: impl IntoIterator<Item = &'a Value>, seen: &mut std::collections::HashSet<usize>) -> usize {
    const ARC_HEADER: usize = 2 * std::mem::size_of::<usize>();
    let mut stack: Vec<&Value> = values.into_iter().collect();
    let mut bytes = 0;
    while let Some(v) = stack.pop() {
        let (addr, size) = match v {
            Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::ModelValue(_) | Value::Interval(..) => continue,
            Value::Set(es) | Value::Tuple(es) => (es.as_ptr() as usize, std::mem::size_of_val(&**es)),
            Value::Record(fs) => (fs.as_ptr() as usize, std::mem::size_of_val(&**fs)),
            Value::Fcn(ps, _) => (ps.as_ptr() as usize, std::mem::size_of_val(&**ps)),
            Value::LazySet(l) => (Arc::as_ptr(l) as usize, std::mem::size_of::<LazySet>()),
            Value::LazyFcn(f) => (Arc::as_ptr(f) as *const () as usize, std::mem::size_of_val(&**f)),
        };
        if !seen.insert(addr) {
            continue;
        }
        bytes += ARC_HEADER + size;
        match v {
            Value::Set(es) | Value::Tuple(es) => stack.extend(es.iter()),
            Value::Record(fs) => stack.extend(fs.iter().map(|(_, x)| x)),
            Value::Fcn(ps, _) => ps.iter().for_each(|(k, x)| stack.extend([k, x])),
            _ => {}
        }
    }
    bytes
}

/// Build the canonical function value from pairs sorted by key in TLC order
/// with distinct keys.
pub(crate) fn fcn_from_sorted_pairs(pairs: Vec<(Value, Value)>) -> Value {
    if pairs.is_empty() {
        return Value::tuple(Vec::new());
    }
    if pairs.iter().enumerate().all(|(i, (k, _))| matches!(k, Value::Int(n) if *n == i as i64 + 1)) {
        return Value::Tuple(pairs.into_iter().map(|(_, v)| v).collect());
    }
    if pairs.iter().all(|(k, _)| matches!(k, Value::Str(_))) {
        return Value::Record(
            pairs
                .into_iter()
                .map(|(k, v)| match k {
                    Value::Str(s) => (s, v),
                    _ => unreachable!(),
                })
                .collect(),
        );
    }
    Value::Fcn(Arc::from(pairs), FcnDom::Enumerated)
}

/// The function TLC builds as an `FcnRcdValue` over an integer interval,
/// from its pairs sorted by key (the domain is the interval): a `Tuple`
/// for `1..n` (or empty), else an `Fcn` over the interval.
pub(crate) fn fcn_over_interval(pairs: Vec<(Value, Value)>) -> Value {
    match pairs.first() {
        None | Some((Value::Int(1), _)) => fcn_from_sorted_pairs(pairs),
        Some(_) => Value::Fcn(Arc::from(pairs), FcnDom::Interval),
    }
}

/// How an `Fcn` looks its keys up (TLC: an `FcnRcdValue` with or without
/// an interval domain `intv`), see `Value::Fcn`.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum FcnDom {
    /// By equality (`FcnRcdValue` over an enumerated domain).
    Enumerated,
    /// As integers of an interval: any other key is an error.
    Interval,
}

/// How a function built as an `Fcn` relates to the canonical forms: its
/// domain is `1..n` (`Tuple`, also the empty function), a non-empty set of
/// strings (`Record`), or anything else (`Fcn`). TLC converts such an
/// `FcnRcdValue` with `toTuple` / `toRcd` wherever a sequence or a record is
/// expected.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FcnKind {
    Tuple,
    Record,
    Fcn,
}

impl FcnKind {
    /// The kind of the (sorted, distinct) pairs of an `Fcn`. Keys of one
    /// function are mutually comparable, so with untyped model values (which
    /// sort first) excluded by the first key, an integer first key means all
    /// keys are integers (then `1..n` iff the first is 1 and the last n), and
    /// a string first key means all keys are strings.
    #[inline]
    pub fn of(pairs: &[(Value, Value)]) -> FcnKind {
        match (pairs.first(), pairs.last()) {
            (None, _) => FcnKind::Tuple,
            (Some((Value::Int(1), _)), Some((Value::Int(n), _))) if *n == pairs.len() as i64 => FcnKind::Tuple,
            (Some((Value::Str(_), _)), _) => FcnKind::Record,
            _ => FcnKind::Fcn,
        }
    }

    /// The kind of `v` if it is an `Fcn`, else `FcnKind::Fcn`.
    #[inline]
    pub fn of_value(v: &Value) -> FcnKind {
        match v {
            Value::Fcn(pairs, _) => FcnKind::of(pairs),
            _ => FcnKind::Fcn,
        }
    }
}

/// Sort (key, value) pairs by key in TLC order (errors for duplicate or
/// incomparable keys).
fn sort_pairs(mut pairs: Vec<(Value, Value)>) -> crate::Result<Vec<(Value, Value)>> {
    if pairs.len() <= 1 {
        return Ok(pairs);
    }
    if pairs.iter().all(|(k, _)| matches!(k, Value::Int(_))) {
        pairs.sort_by_key(|(k, _)| match k {
            Value::Int(n) => *n,
            _ => unreachable!(),
        });
        check_distinct(&pairs)?;
        return Ok(pairs);
    }
    if pairs.iter().all(|(k, _)| matches!(k, Value::Str(_))) {
        pairs.sort_by_key(|(k, _)| match k {
            Value::Str(s) => *s,
            _ => unreachable!(),
        });
        check_distinct(&pairs)?;
        return Ok(pairs);
    }
    tlc_sort(pairs, |p| &p.0, false)
}

fn check_distinct(pairs: &[(Value, Value)]) -> crate::Result<()> {
    for w in pairs.windows(2) {
        if w[0].0 == w[1].0 {
            return dup_key(&w[1].0);
        }
    }
    Ok(())
}

fn dup_key<T>(k: &Value) -> crate::Result<T> {
    err(format!("The value\n{k}\noccurs multiple times in the function domain."))
}

/// Materialize a lazy function over its (finite) domain.
pub(crate) fn lazy_fcn_to_value(f: &dyn LazyFcn) -> crate::Result<Value> {
    let dom = f.domain()?;
    // (TLC's FcnLambdaValue.toFcnRcd asks the domain for its size first.)
    if let Value::LazySet(l) = &dom {
        if matches!(**l, LazySet::Seq(_) | LazySet::Nat | LazySet::Int | LazySet::StringSet | LazySet::Any) {
            return Err(crate::ops::overridden_size_error(&dom));
        }
    }
    let keys = crate::ops::enumerate_normalized(&dom)?;
    let mut pairs = Vec::with_capacity(keys.len());
    for k in keys {
        let v = f.apply(&k)?;
        pairs.push((k, v));
    }
    // (The keys are normalized: sorted and distinct.)
    Ok(if matches!(dom, Value::Interval(..)) { fcn_over_interval(pairs) } else { Value::Fcn(Arc::from(pairs), FcnDom::Enumerated) })
}

// ---------------------------------------------------------------------------
// TLC-style sorting (normalization of sets / function domains).

/// Sort and deduplicate set elements in TLC order (errors on incomparable
/// elements, like TLC's `SetEnumValue.normalize`).
pub(crate) fn normalize_vec(mut v: Vec<Value>) -> crate::Result<Vec<Value>> {
    if v.len() <= 1 {
        return Ok(v);
    }
    if v.iter().all(|e| matches!(e, Value::Int(_))) {
        v.sort_unstable_by_key(|e| match e {
            Value::Int(n) => *n,
            _ => unreachable!(),
        });
        v.dedup_by(|a, b| matches!((a, b), (Value::Int(x), Value::Int(y)) if x == y));
        return Ok(v);
    }
    if v.iter().all(|e| matches!(e, Value::Str(_))) {
        v.sort_unstable_by_key(|e| match e {
            Value::Str(s) => *s,
            _ => unreachable!(),
        });
        v.dedup_by(|a, b| matches!((a, b), (Value::Str(x), Value::Str(y)) if x == y));
        return Ok(v);
    }
    tlc_sort(v, |e| e, true)
}

/// Small inputs use TLC's exact binary insertion sort (`ValueVec.sort`), so
/// that errors for incomparable elements are raised exactly when TLC raises
/// them. Larger inputs are sorted with the total order and then validated
/// pairwise with `cmp_tlc` (falls back to the insertion sort if the total
/// order is unavailable, e.g. for infinite lazy elements).
pub(crate) fn tlc_sort<T>(mut v: Vec<T>, key: fn(&T) -> &Value, dedup: bool) -> crate::Result<Vec<T>> {
    const INSERTION_MAX: usize = 32;
    if v.len() <= INSERTION_MAX {
        return insertion_sort(v, key, dedup);
    }
    let mut failed = false;
    v.sort_by(|a, b| match try_total_cmp(key(a), key(b)) {
        Ok(o) => o,
        Err(_) => {
            failed = true;
            Ordering::Equal
        }
    });
    if failed {
        return insertion_sort(v, key, dedup);
    }
    let mut out: Vec<T> = Vec::with_capacity(v.len());
    for e in v {
        if let Some(last) = out.last() {
            match cmp_tlc(key(&e), key(last))? {
                Ordering::Greater => {}
                Ordering::Equal if dedup => continue,
                Ordering::Equal => return dup_key(key(&e)),
                Ordering::Less => unreachable!("total order disagrees with cmp_tlc"),
            }
        }
        out.push(e);
    }
    Ok(out)
}

fn insertion_sort<T>(v: Vec<T>, key: fn(&T) -> &Value, dedup: bool) -> crate::Result<Vec<T>> {
    let mut out: Vec<T> = Vec::with_capacity(v.len());
    for elem in v {
        let (mut lo, mut hi) = (0usize, out.len());
        let mut found = false;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            match cmp_tlc(key(&elem), key(&out[mid]))? {
                Ordering::Equal => {
                    found = true;
                    break;
                }
                Ordering::Less => hi = mid,
                Ordering::Greater => lo = mid + 1,
            }
        }
        if found {
            if dedup {
                continue;
            }
            return dup_key(key(&elem));
        }
        out.insert(lo, elem);
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Total structural order / equality / hash.

impl PartialEq for Value {
    fn eq(&self, other: &Value) -> bool {
        match (self, other) {
            (Value::Int(a), Value::Int(b)) => a == b,
            (Value::Str(a), Value::Str(b)) => a == b,
            (Value::Bool(a), Value::Bool(b)) => a == b,
            (Value::ModelValue(a), Value::ModelValue(b)) => a == b,
            (Value::Set(a), Value::Set(b)) | (Value::Tuple(a), Value::Tuple(b)) => {
                Arc::ptr_eq(a, b) || (a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x == y))
            }
            (Value::Record(a), Value::Record(b)) => {
                Arc::ptr_eq(a, b) || (a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x.0 == y.0 && x.1 == y.1))
            }
            (Value::Interval(a, b), Value::Interval(c, d)) => (b < a && d < c) || (a == c && b == d),
            (Value::Fcn(a, _), Value::Fcn(b, _)) => {
                Arc::ptr_eq(a, b) || (a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x.0 == y.0 && x.1 == y.1))
            }
            _ => self.cmp(other) == Ordering::Equal,
        }
    }
}

impl Eq for Value {}

impl PartialOrd for Value {
    fn partial_cmp(&self, other: &Value) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Value {
    fn cmp(&self, other: &Value) -> Ordering {
        match try_total_cmp(self, other) {
            Ok(o) => o,
            Err(e) => panic!("cannot compare values {self} and {other}: {e}"),
        }
    }
}

impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut sink = crate::fingerprint::HashSink(state);
        if let Err(e) = crate::fingerprint::walk(self, &mut sink, false) {
            panic!("cannot hash value {self}: {e}");
        }
    }
}
