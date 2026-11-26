//! TLC's total order (`compareTo`) and equality, with TLC's errors for
//! incomparable values (tlc-semantics.md §1.2, §2).
//!
//! Function representations compare by domain and values in either direction
//! (D-18/D-31); TLC's record receiver asymmetry is an implementation defect.

use std::cmp::Ordering;
use std::sync::Arc;

use crate::error::err;
use crate::intern::Sym;
use crate::lazy::LazySet;
use crate::plan::{ComparisonKind, FunctionComparison};
use crate::repr::{builtin, force_fcn, set_elems, Builtin, FcnRef};
use crate::value::{FcnKind, Value};
use crate::Result;

/// Whether comparing a value with a structural clone cannot fail or run effects.
///
/// This is deliberately stronger than `is_normal`: an oversized interval is
/// normal but its comparison asks for a checked cardinality. By induction,
/// scalars compare with themselves without effects; a materialized collection
/// compares equal lengths/domains and then corresponding children. Every child
/// must satisfy the same condition, including function keys. No lazy value is
/// admitted because forcing it may fail or evaluate a predicate with effects.
///
/// A caller may use this only after proving that the result has exactly the
/// operand's children, in the same order and with the same representations.
/// It then permits sharing the outer identity, whose comparison fast path can
/// replace a comparison against that structural clone.
pub fn self_comparison_is_inert(v: &Value) -> bool {
    match v {
        Value::Int(_) | Value::Bool(_) | Value::Str(_) | Value::ModelValue(_) => true,
        Value::Interval(lo, hi) => crate::repr::interval_len(*lo, *hi).is_ok(),
        Value::Set(es) | Value::Tuple(es) => es.iter().all(self_comparison_is_inert),
        Value::Record(fields) => fields.iter().all(|(_, v)| self_comparison_is_inert(v)),
        Value::Fcn(pairs, _) => pairs.iter().all(|(k, v)| self_comparison_is_inert(k) && self_comparison_is_inert(v)),
        Value::LazySet(_) | Value::LazyFcn(_) => false,
    }
}

/// TLC `compareTo`: errors on incomparable kinds (except untyped model values,
/// which sort before every non-model value).
pub fn cmp_tlc(a: &Value, b: &Value) -> Result<Ordering> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => return Ok(x.cmp(y)),
        (Value::Str(x), Value::Str(y)) => return Ok(x.cmp(y)),
        (Value::Bool(x), Value::Bool(y)) => return Ok(x.cmp(y)),
        (Value::ModelValue(x), Value::ModelValue(_)) => return mv_cmp(*x, a, b),
        (Value::Tuple(t), Value::Tuple(u)) => return cmp_tuples(t, u),
        _ => {}
    }
    if a.is_empty_fcn() || b.is_empty_fcn() {
        // The empty function of an enumerated domain compares as `<<>>`.
        let t = Value::tuple(Vec::new());
        return cmp_tlc(if a.is_empty_fcn() { &t } else { a }, if b.is_empty_fcn() { &t } else { b });
    }
    match a {
        Value::ModelValue(m) => mv_cmp(*m, a, b),
        Value::Bool(_) | Value::Int(_) | Value::Str(_) => {
            if let Value::ModelValue(m) = b {
                return mv_cmp_rev(*m, b, a);
            }
            let kind = scalar_kind(a);
            err(format!("Attempted to compare {kind} {a} with non-{kind}:\n{b}"))
        }
        Value::Set(_) | Value::Interval(..) | Value::LazySet(_) => set_cmp(a, b),
        Value::Tuple(t) => match b {
            Value::Tuple(u) => cmp_tuples(t, u),
            Value::Record(_) | Value::Fcn(..) => fcn_cmp(FcnRef::Tuple(t), FcnRef::of(b).unwrap()),
            Value::LazyFcn(_) => {
                let mut slot = None;
                cmp_tlc(a, force_fcn(b, &mut slot)?)
            }
            Value::ModelValue(m) => mv_cmp_rev(*m, b, a),
            _ => err(format!("Attempted to compare the function {a} with the value:\n{b}")),
        },
        Value::Record(r) => match b {
            Value::Record(s) => {
                let c = r.len().cmp(&s.len());
                if c != Ordering::Equal {
                    return Ok(c);
                }
                for (x, y) in r.iter().zip(s.iter()) {
                    let c = x.0.cmp(&y.0);
                    if c != Ordering::Equal {
                        return Ok(c);
                    }
                }
                for (x, y) in r.iter().zip(s.iter()) {
                    let c = cmp_tlc(&x.1, &y.1)?;
                    if c != Ordering::Equal {
                        return Ok(c);
                    }
                }
                Ok(Ordering::Equal)
            }
            // `<<>>` converts to the empty record; `r` is non-empty.
            Value::Tuple(u) if u.is_empty() => Ok(r.len().cmp(&0)),
            // A function over a set of strings converts to a record (toRcd).
            Value::Fcn(..) if FcnKind::of_value(b) == FcnKind::Record => cmp_tlc(a, &b.fcn_canonical().unwrap()),
            Value::Tuple(_) | Value::Fcn(..) => fcn_cmp(FcnRef::Record(r), FcnRef::of(b).unwrap()),
            Value::LazyFcn(_) => {
                let mut slot = None;
                cmp_tlc(a, force_fcn(b, &mut slot)?)
            }
            Value::ModelValue(m) => mv_cmp_rev(*m, b, a),
            _ => err(format!("Attempted to compare record:\n{a}\nwith non-record\n{b}")),
        },
        Value::Fcn(f, _) => match b {
            Value::Tuple(_) | Value::Record(_) | Value::Fcn(..) => fcn_cmp(FcnRef::Fcn(f), FcnRef::of(b).unwrap()),
            Value::LazyFcn(_) => {
                let mut slot = None;
                cmp_tlc(a, force_fcn(b, &mut slot)?)
            }
            Value::ModelValue(m) => mv_cmp_rev(*m, b, a),
            _ => err(format!("Attempted to compare the function {a} with the value:\n{b}")),
        },
        Value::LazyFcn(_) => {
            if let Value::ModelValue(m) = b {
                return mv_cmp_rev(*m, b, a);
            }
            let mut slot = None;
            cmp_tlc(force_fcn(a, &mut slot)?, b)
        }
    }
}

/// TLC `equals` (`=`): converts between function representations, errors for
/// incomparable kinds as TLC does (e.g. `1 = "a"`, `<<>> = {}`).
pub fn eq_tlc(a: &Value, b: &Value) -> Result<bool> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => return Ok(x == y),
        (Value::Str(x), Value::Str(y)) => return Ok(x == y),
        (Value::Bool(x), Value::Bool(y)) => return Ok(x == y),
        (Value::ModelValue(x), Value::ModelValue(_)) => return mv_eq(*x, a, b),
        (Value::Tuple(t), Value::Tuple(u)) => return eq_tuples(t, u),
        _ => {}
    }
    if a.is_empty_fcn() || b.is_empty_fcn() {
        // The empty function of an enumerated domain compares as `<<>>`.
        let t = Value::tuple(Vec::new());
        return eq_tlc(if a.is_empty_fcn() { &t } else { a }, if b.is_empty_fcn() { &t } else { b });
    }
    match a {
        Value::ModelValue(m) => mv_eq(*m, a, b),
        Value::Bool(_) => match b {
            Value::ModelValue(m) => mv_eq_rev(*m, b, a),
            _ => err(format!("Attempted to compare equality of boolean {a} with non-boolean:\n{b}")),
        },
        Value::Int(_) => match b {
            Value::ModelValue(m) => mv_eq_rev(*m, b, a),
            _ => err(format!("Attempted to check equality of integer {a} with non-integer:\n{b}")),
        },
        Value::Str(_) => match b {
            Value::ModelValue(m) => mv_eq_rev(*m, b, a),
            _ => err(format!("Attempted to check equality of string {a} with non-string:\n{b}")),
        },
        Value::Set(_) | Value::Interval(..) | Value::LazySet(_) => set_eq(a, b),
        Value::Tuple(t) => match b {
            Value::Tuple(u) => eq_tuples(t, u),
            Value::Record(_) | Value::Fcn(..) => fcn_eq(FcnRef::Tuple(t), FcnRef::of(b).unwrap()),
            Value::LazyFcn(_) => {
                let mut slot = None;
                eq_tlc(a, force_fcn(b, &mut slot)?)
            }
            Value::ModelValue(m) => mv_eq_rev(*m, b, a),
            _ => err(format!("Attempted to check equality of the function {a} with the value:\n{b}")),
        },
        Value::Record(r) => match b {
            Value::Record(s) => {
                if Arc::ptr_eq(r, s) {
                    return Ok(true);
                }
                if r.len() != s.len() || r.iter().zip(s.iter()).any(|(x, y)| x.0 != y.0) {
                    return Ok(false);
                }
                eq_seq(r.iter().map(|x| &x.1), s.iter().map(|y| &y.1))
            }
            Value::Tuple(u) if u.is_empty() => Ok(false),
            // A function over a set of strings converts to a record (toRcd).
            Value::Fcn(..) if FcnKind::of_value(b) == FcnKind::Record => eq_tlc(a, &b.fcn_canonical().unwrap()),
            Value::Tuple(_) | Value::Fcn(..) => fcn_eq(FcnRef::Record(r), FcnRef::of(b).unwrap()),
            Value::LazyFcn(_) => {
                let mut slot = None;
                eq_tlc(a, force_fcn(b, &mut slot)?)
            }
            Value::ModelValue(m) => mv_eq_rev(*m, b, a),
            _ => err(format!("Attempted to check equality of record:\n{a}\nwith non-record\n{b}")),
        },
        Value::Fcn(f, _) => match b {
            Value::Fcn(g, _) if Arc::ptr_eq(f, g) => Ok(true),
            Value::Tuple(_) | Value::Record(_) | Value::Fcn(..) => fcn_eq(FcnRef::Fcn(f), FcnRef::of(b).unwrap()),
            Value::LazyFcn(_) => {
                let mut slot = None;
                eq_tlc(a, force_fcn(b, &mut slot)?)
            }
            Value::ModelValue(m) => mv_eq_rev(*m, b, a),
            _ => err(format!("Attempted to check equality of the function {a} with the value:\n{b}")),
        },
        Value::LazyFcn(_) => {
            if let Value::ModelValue(m) = b {
                return mv_eq_rev(*m, b, a);
            }
            let mut slot = None;
            eq_tlc(force_fcn(a, &mut slot)?, b)
        }
    }
}

fn scalar_kind(v: &Value) -> &'static str {
    match v {
        Value::Bool(_) => "boolean",
        Value::Int(_) => "integer",
        Value::Str(_) => "string",
        _ => "value",
    }
}

/// `<<...>>.compareTo(<<...>>)`: by length, then elementwise (integer
/// elements compared inline, the common case of tuple keys).
fn cmp_tuples(t: &Arc<[Value]>, u: &Arc<[Value]>) -> Result<Ordering> {
    if Arc::ptr_eq(t, u) {
        return Ok(Ordering::Equal);
    }
    let c = t.len().cmp(&u.len());
    if c != Ordering::Equal {
        return Ok(c);
    }
    for (x, y) in t.iter().zip(u.iter()) {
        let c = match (x, y) {
            (Value::Int(p), Value::Int(q)) => p.cmp(q),
            _ => cmp_tlc(x, y)?,
        };
        if c != Ordering::Equal {
            return Ok(c);
        }
    }
    Ok(Ordering::Equal)
}

/// `<<...>>.equals(<<...>>)`: lengths, then elementwise (integer elements
/// compared inline).
fn eq_tuples(t: &Arc<[Value]>, u: &Arc<[Value]>) -> Result<bool> {
    if Arc::ptr_eq(t, u) {
        return Ok(true);
    }
    if t.len() != u.len() {
        return Ok(false);
    }
    for (x, y) in t.iter().zip(u.iter()) {
        let same = match (x, y) {
            (Value::Int(p), Value::Int(q)) => p == q,
            _ => eq_tlc(x, y)?,
        };
        if !same {
            return Ok(false);
        }
    }
    Ok(true)
}

fn eq_seq<'a>(a: impl Iterator<Item = &'a Value>, b: impl Iterator<Item = &'a Value>) -> Result<bool> {
    for (x, y) in a.zip(b) {
        if !eq_tlc(x, y)? {
            return Ok(false);
        }
    }
    Ok(true)
}

// ---- model values (V/ModelValue.java) ----

/// `mv.compareTo(b)`.
fn mv_cmp(m: Sym, a: &Value, b: &Value) -> Result<Ordering> {
    let ty = m.model_value_type();
    match (ty, b) {
        (None, Value::ModelValue(n)) => Ok(m.cmp(n)),
        (None, _) => Ok(Ordering::Less),
        (Some(t), Value::ModelValue(n)) => match n.model_value_type() {
            Some(u) if u != t => err(format!("Attempted to compare the differently-typed model values {a} and {b}")),
            _ => Ok(m.cmp(n)),
        },
        (Some(_), _) => err(format!("Attempted to compare the typed model value {a} and non-model value\n{b}")),
    }
}

/// `other.compareTo(mv)` for a non-model value `other`.
fn mv_cmp_rev(m: Sym, mv: &Value, other: &Value) -> Result<Ordering> {
    if m.model_value_type().is_some() {
        return err(format!("Attempted to compare the typed model value {mv} and the non-model value\n{other}"));
    }
    Ok(Ordering::Greater)
}

/// `mv.equals(b)`.
fn mv_eq(m: Sym, a: &Value, b: &Value) -> Result<bool> {
    let ty = m.model_value_type();
    match (ty, b) {
        (None, Value::ModelValue(n)) => Ok(m == *n),
        (None, _) => Ok(false),
        (Some(t), Value::ModelValue(n)) => match n.model_value_type() {
            Some(u) if u != t => err(format!("Attempted to check equality of the differently-typed model values {a} and {b}")),
            _ => Ok(m == *n),
        },
        (Some(_), _) => err(format!("Attempted to check equality of typed model value {a} and non-model value\n{b}")),
    }
}

/// `other.equals(mv)` for a non-model value `other`.
fn mv_eq_rev(m: Sym, mv: &Value, other: &Value) -> Result<bool> {
    if m.model_value_type().is_some() {
        return err(format!("Attempted to check equality of the typed model value {mv} and the non-model value\n{other}"));
    }
    Ok(false)
}

/// `elem \in set` where `elem` is a model value and `set` cannot contain it.
pub(crate) fn mv_member(m: Sym, mv: &Value, set: &Value) -> Result<bool> {
    if m.model_value_type().is_some() {
        return err(format!("Attempted to check if the typed model value {mv} is an element of\n{set}"));
    }
    Ok(false)
}

// ---- sets ----

/// TLC converts `SUBSET S` to an enumerated set to compare it with
/// another set (`SubsetValue.convertAndCache`), sizing it first: an
/// overridden value S (Nat, Seq(T), ...) fails there.
fn subset_size(a: &Value) -> Result<()> {
    if let Value::LazySet(l) = a {
        if let crate::lazy::LazySet::Subset(base) = &**l {
            if !crate::ops::is_enumerable(base) {
                return Err(crate::ops::overridden_size_error(base));
            }
        }
    }
    Ok(())
}

/// `a` as TLC compares it with a value that is not a set it can compare
/// elementwise: a set TLC keeps as an operation (union, intersection,
/// difference, `UNION S`, a set filter) converts itself to an enumerated set
/// first (`convertAndCache`), failing as its enumeration does.
fn converted(a: &Value) -> Result<std::borrow::Cow<'_, Value>> {
    use crate::lazy::LazySet;
    match a {
        Value::LazySet(l)
            if matches!(**l, LazySet::Cup(..) | LazySet::Cap(..) | LazySet::Diff(..) | LazySet::Union(_) | LazySet::Custom(_)) =>
        {
            Ok(std::borrow::Cow::Owned(Value::Set(Arc::from(crate::ops::enumerate_normalized(a)?))))
        }
        _ => Ok(std::borrow::Cow::Borrowed(a)),
    }
}

fn builtin_cmp(x: Builtin, a: &Value, b: &Value) -> Result<Ordering> {
    if let Value::ModelValue(m) = b {
        return mv_cmp_rev(*m, b, a);
    }
    match builtin(b) {
        Some(y) => match (x, y) {
            (Builtin::Seq(s), Builtin::Seq(t)) => cmp_tlc(s, t),
            _ => Ok(x.rank().cmp(&y.rank())),
        },
        // (TLC: UserValue.compareTo.)
        None => err(format!("Attempted to compare overridden value {a} with non-overridden value:\n{b}")),
    }
}

fn set_cmp(a: &Value, b: &Value) -> Result<Ordering> {
    if let Value::ModelValue(m) = b {
        return mv_cmp_rev(*m, b, a);
    }
    match (a, b) {
        (Value::LazySet(x), _) if matches!(**x, LazySet::KSubset(..)) => {
            let LazySet::KSubset(k, base) = &**x else { unreachable!() };
            return crate::ops::ksubset::ksubset_cmp(*k, base, b);
        }
        // (SubsetValue.compareTo delegates to the k-subset.)
        (Value::LazySet(x), Value::LazySet(y)) if matches!((&**x, &**y), (LazySet::Subset(_), LazySet::KSubset(..))) => {
            return Ok(set_cmp(b, a)?.reverse());
        }
        _ => {}
    }
    if let Some(x) = builtin(a) {
        return builtin_cmp(x, a, b);
    }
    if !b.is_set() || builtin(b).is_some() {
        let a = converted(a)?;
        return err(format!("Attempted to compare the set {a} with the value:\n{b}"));
    }
    match (a, b) {
        (Value::Interval(l1, h1), Value::Interval(l2, h2)) => {
            let (n1, n2) = (crate::repr::interval_len(*l1, *h1)?, crate::repr::interval_len(*l2, *h2)?);
            if n1 != n2 || n1 == 0 {
                return Ok(n1.cmp(&n2));
            }
            return Ok(l1.cmp(l2));
        }
        (Value::Set(x), Value::Set(y)) if Arc::ptr_eq(x, y) => return Ok(Ordering::Equal),
        _ => {}
    }
    if let Some(c) = cheap_size_cmp(a, b) {
        return Ok(c);
    }
    subset_size(a)?;
    subset_size(b)?;
    let ea = set_elems(a)?.unwrap();
    let eb = set_elems(b)?.unwrap();
    let c = ea.len().cmp(&eb.len());
    if c != Ordering::Equal {
        return Ok(c);
    }
    for i in 0..ea.len() {
        let c = cmp_tlc(&ea.get(i), &eb.get(i))?;
        if c != Ordering::Equal {
            return Ok(c);
        }
    }
    Ok(Ordering::Equal)
}

/// The order of two sets of different sizes when both sizes are known
/// without enumerating a lazy set (`None`: same or unknown sizes). TLC
/// compares (and tests equality of) sets by size first, after normalizing
/// both; a lazy set whose size follows from its operands (`SUBSET S`,
/// `[S -> T]`, products, record sets of enumerated sets) can always be
/// normalized, so the result is the same without materializing it (e.g.
/// sorting `{[1..n -> S] : n \in 0..k}` enumerated every function set at
/// each comparison).
fn cheap_size_cmp(a: &Value, b: &Value) -> Option<Ordering> {
    if !matches!(a, Value::LazySet(_)) && !matches!(b, Value::LazySet(_)) {
        return None;
    }
    let (n, m) = (cheap_size(a)?, cheap_size(b)?);
    // Ordering sets of functions, records or tuples converts the operands
    // first: `compareTo` calls `convertAndCache` even for two sets of the same
    // kind (their structural equality is `lazy_set_eq`, which never reaches
    // this shortcut). That build appends through the whole set and converts
    // the pieces it is built from — a function set's domain and range, a
    // product's components, a powerset's base — so any of those over the
    // bound must be left to the materializing path, which reports it. A
    // powerset itself is preallocated and keeps the unequal-size shortcut
    // when its base needs no conversion (an interval base, for instance).
    let limit = crate::limits::growth_limit() as u64;
    let converts = |v: &Value| conversion_cost(v).is_none_or(|cost| cost > limit);
    if converts(a) || converts(b) {
        return None;
    }
    (n != m).then(|| n.cmp(&m))
}

/// The largest set TLC builds while converting `v` to an enumerated set:
/// converting a set of functions materializes its domain and range, a product
/// or record set its components (and itself), and a powerset its base — the
/// powerset itself is preallocated. Already-built sets, intervals and
/// enumerated sets need nothing. `None`: a piece is not decidable without
/// enumerating it, so no shortcut may answer.
fn conversion_cost(v: &Value) -> Option<u64> {
    use crate::lazy::LazySet;
    fn components<'a>(xs: impl Iterator<Item = &'a Value>) -> Option<u64> {
        let mut cost = 0;
        for x in xs {
            cost = cost.max(conversion_cost(x)?);
        }
        Some(cost)
    }
    match v {
        Value::Set(_) | Value::Interval(..) => Some(0),
        Value::LazySet(l) => match &**l {
            LazySet::Enum(_) => Some(0),
            LazySet::FcnSet(d, r) => Some(cheap_size(v)?.max(conversion_cost(d)?).max(conversion_cost(r)?)),
            LazySet::Product(sets) => Some(cheap_size(v)?.max(components(sets.iter())?)),
            LazySet::RecordSet(fields) => Some(cheap_size(v)?.max(components(fields.iter().map(|(_, s)| s))?)),
            LazySet::Subset(base) => conversion_cost(base),
            LazySet::KSubset(_, base) => conversion_cost(base),
            _ => None,
        },
        _ => None,
    }
}

/// Size of a set computed from its operands' sizes (`None`: needs an
/// enumeration, infinite, or too large).
fn cheap_size(v: &Value) -> Option<u64> {
    use crate::lazy::LazySet;
    const MAX: u64 = i32::MAX as u64;
    let n = match v {
        Value::Set(e) => e.len() as u64,
        Value::Interval(lo, hi) => crate::repr::interval_len(*lo, *hi).ok()? as u64,
        Value::LazySet(l) => match &**l {
            LazySet::Subset(base) => {
                let n = cheap_size(base)?;
                if n >= 31 {
                    return None;
                }
                1 << n
            }
            LazySet::FcnSet(d, r) => {
                let (dn, rn) = (cheap_size(d)?, cheap_size(r)?);
                let mut sz: u64 = 1;
                for _ in 0..dn {
                    sz = sz.checked_mul(rn)?;
                    if sz > MAX {
                        return None;
                    }
                    if sz == 0 {
                        break;
                    }
                }
                sz
            }
            LazySet::Product(sets) => product_size(sets.iter())?,
            LazySet::RecordSet(fields) => product_size(fields.iter().map(|(_, s)| s))?,
            _ => return None,
        },
        _ => return None,
    };
    (n <= MAX).then_some(n)
}

fn product_size<'a>(sets: impl Iterator<Item = &'a Value>) -> Option<u64> {
    let mut sz: u64 = 1;
    for s in sets {
        sz = sz.checked_mul(cheap_size(s)?)?;
        if sz > i32::MAX as u64 {
            return None;
        }
    }
    Some(sz)
}

fn set_eq(a: &Value, b: &Value) -> Result<bool> {
    if let Value::ModelValue(m) = b {
        return mv_eq_rev(*m, b, a);
    }
    match (a, b) {
        (Value::LazySet(x), _) if matches!(**x, LazySet::KSubset(..)) => {
            let LazySet::KSubset(k, base) = &**x else { unreachable!() };
            return crate::ops::ksubset::ksubset_eq(*k, base, b);
        }
        // (SubsetValue.equals delegates to the k-subset.)
        (Value::LazySet(x), Value::LazySet(y)) if matches!((&**x, &**y), (LazySet::Subset(_), LazySet::KSubset(..))) => {
            return set_eq(b, a)
        }
        _ => {}
    }
    if let Some(x) = builtin(a) {
        return Ok(builtin_cmp(x, a, b)? == Ordering::Equal);
    }
    if !b.is_set() || builtin(b).is_some() {
        let a = converted(a)?;
        return err(format!("Attempted to check equality of the set {a} with the value:\n{b}"));
    }
    match (a, b) {
        (Value::Interval(l1, h1), Value::Interval(l2, h2)) => {
            if h1 < l1 {
                return Ok(h2 < l2);
            }
            return Ok(l1 == l2 && h1 == h2);
        }
        (Value::Set(x), Value::Set(y)) if Arc::ptr_eq(x, y) => return Ok(true),
        (Value::LazySet(x), Value::LazySet(y)) => {
            if let Some(r) = lazy_set_eq(x, y)? {
                return Ok(r);
            }
        }
        _ => {}
    }
    if cheap_size_cmp(a, b).is_some() {
        return Ok(false);
    }
    subset_size(a)?;
    subset_size(b)?;
    let ea = set_elems(a)?.unwrap();
    let eb = set_elems(b)?.unwrap();
    if ea.len() != eb.len() {
        return Ok(false);
    }
    for i in 0..ea.len() {
        if !eq_tlc(&ea.get(i), &eb.get(i))? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Equality of two lazy sets of the same kind as TLC decides it without
/// enumerating them (SetOfFcnsValue / SetOfRcdsValue / SetOfTuplesValue /
/// SubsetValue `equals`, tlaplus/tlaplus#1407): an empty domain makes
/// `[S -> T]` `{<<>>}` and an empty range (with a non-empty domain) `{}`,
/// an empty component set makes a product or record set `{}`; otherwise
/// the components decide. `None` for other kinds.
fn lazy_set_eq(x: &LazySet, y: &LazySet) -> Result<Option<bool>> {
    use crate::ops::is_empty_checked as empty;
    // Two equal-length component lists that are empty or not alike.
    let components = |xs: &[&Value], ys: &[&Value]| -> Result<bool> {
        let e1 = any_empty(xs)?;
        if e1 {
            return any_empty(ys);
        }
        if any_empty(ys)? {
            return Ok(false);
        }
        if xs.len() != ys.len() {
            return Ok(false);
        }
        for (u, v) in xs.iter().zip(ys) {
            if !eq_tlc(u, v)? {
                return Ok(false);
            }
        }
        Ok(true)
    };
    Ok(Some(match (x, y) {
        (LazySet::FcnSet(d1, r1), LazySet::FcnSet(d2, r2)) => {
            let (u1, u2) = (empty(d1)?, empty(d2)?);
            if u1 || u2 {
                return Ok(Some(u1 == u2));
            }
            let (e1, e2) = (empty(r1)?, empty(r2)?);
            if e1 || e2 {
                return Ok(Some(e1 == e2));
            }
            eq_tlc(d1, d2)? && eq_tlc(r1, r2)?
        }
        (LazySet::Product(s1), LazySet::Product(s2)) => components(&s1.iter().collect::<Vec<_>>(), &s2.iter().collect::<Vec<_>>())?,
        (LazySet::RecordSet(f1), LazySet::RecordSet(f2)) => {
            let v1: Vec<&Value> = f1.iter().map(|f| &f.1).collect();
            let v2: Vec<&Value> = f2.iter().map(|f| &f.1).collect();
            let names = f1.len() == f2.len() && f1.iter().zip(f2.iter()).all(|(a, b)| a.0 == b.0);
            if !any_empty(&v1)? && !any_empty(&v2)? && !names {
                return Ok(Some(false));
            }
            components(&v1, &v2)?
        }
        (LazySet::Subset(s), LazySet::Subset(t)) => eq_tlc(s, t)?,
        _ => return Ok(None),
    }))
}

/// Whether one of `sets` is empty (TLC's `isEmpty` on each in turn).
fn any_empty(sets: &[&Value]) -> Result<bool> {
    for s in sets {
        if crate::ops::is_empty_checked(s)? {
            return Ok(true);
        }
    }
    Ok(false)
}

// ---- functions (V/FcnRcdValue.java) ----

/// `this.compareTo(fcn)` with both sides converted to FcnRcdValue; a `Tuple`
/// plays the role of a function with an interval domain.
fn fcn_cmp(x: FcnRef, y: FcnRef) -> Result<Ordering> {
    let plan = FunctionComparison::new(x.len(), y.len(), matches!(x, FcnRef::Tuple(_)), matches!(y, FcnRef::Tuple(_)));
    if plan.length_order != Ordering::Equal {
        return Ok(plan.length_order);
    }
    for i in plan.domains {
        let c = try_total_cmp(&x.key(i), &y.key(i))?;
        if c != Ordering::Equal {
            return Ok(c);
        }
    }
    for i in plan.values {
        let c = cmp_tlc(x.val(i), y.val(i))?;
        if c != Ordering::Equal {
            return Ok(c);
        }
    }
    Ok(Ordering::Equal)
}

/// `this.equals(fcn)` with both sides converted to FcnRcdValue.
fn fcn_eq(x: FcnRef, y: FcnRef) -> Result<bool> {
    let plan = FunctionComparison::new(x.len(), y.len(), matches!(x, FcnRef::Tuple(_)), matches!(y, FcnRef::Tuple(_)));
    if plan.length_order != Ordering::Equal {
        return Ok(false);
    }
    for i in plan.domains {
        if try_total_cmp(&x.key(i), &y.key(i))? != Ordering::Equal {
            return Ok(false);
        }
    }
    for i in plan.values {
        if !eq_tlc(x.val(i), y.val(i))? {
            return Ok(false);
        }
    }
    Ok(true)
}

// ---- total order backing `Ord for Value` ----

/// Equality in the total order that never fails: `false` when the values
/// cannot be compared (a lazy value that cannot be materialized, such as the
/// non-enumerable `[D -> Seq(Nat)]`). For callers that only need to know that
/// two values are certainly equal (e.g. code deduplication), where `==` would
/// panic.
pub fn certainly_equal(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::LazySet(x), Value::LazySet(y)) if Arc::ptr_eq(x, y) => true,
        (Value::LazyFcn(x), Value::LazyFcn(y)) if Arc::ptr_eq(x, y) => true,
        _ => matches!(try_total_cmp(a, b), Ok(Ordering::Equal)),
    }
}

/// Total structural order on canonical forms (agrees with `cmp_tlc` whenever
/// `cmp_tlc` succeeds). Kinds TLC cannot compare are ordered by a fixed kind
/// rank: model values < booleans < integers < strings < sets < functions.
/// Infinite built-in sets (`Nat`, `Int`, `STRING`, `Seq(S)`) sort
/// after all finite sets. Errors only if a lazy value cannot be materialized.
pub fn try_total_cmp(a: &Value, b: &Value) -> Result<Ordering> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => return Ok(x.cmp(y)),
        (Value::Str(x), Value::Str(y)) | (Value::ModelValue(x), Value::ModelValue(y)) => return Ok(x.cmp(y)),
        (Value::Bool(x), Value::Bool(y)) => return Ok(x.cmp(y)),
        _ => {}
    }
    let (ra, rb) = (ComparisonKind::of(a), ComparisonKind::of(b));
    if ra != rb {
        return Ok(ra.cmp(&rb));
    }
    if ra == ComparisonKind::Set {
        match (builtin(a), builtin(b)) {
            (Some(x), Some(y)) => {
                return match (x, y) {
                    (Builtin::Seq(s), Builtin::Seq(t)) => try_total_cmp(s, t),
                    _ => Ok(x.rank().cmp(&y.rank())),
                }
            }
            (Some(_), None) => return Ok(Ordering::Greater),
            (None, Some(_)) => return Ok(Ordering::Less),
            (None, None) => {}
        }
        match (a, b) {
            (Value::Set(x), Value::Set(y)) => {
                if Arc::ptr_eq(x, y) {
                    return Ok(Ordering::Equal);
                }
                let c = x.len().cmp(&y.len());
                if c != Ordering::Equal {
                    return Ok(c);
                }
                return total_seq(x, y);
            }
            (Value::Interval(l1, h1), Value::Interval(l2, h2)) => {
                // Cardinalities computed in i128: `h - l + 1` overflows i64 for
                // extreme intervals (e.g. i64::MIN..=i64::MAX).
                let n1 = if h1 < l1 { 0 } else { *h1 as i128 - *l1 as i128 + 1 };
                let n2 = if h2 < l2 { 0 } else { *h2 as i128 - *l2 as i128 + 1 };
                if n1 != n2 || n1 == 0 {
                    return Ok(n1.cmp(&n2));
                }
                return Ok(l1.cmp(l2));
            }
            _ => {}
        }
        let ea = set_elems(a)?.unwrap();
        let eb = set_elems(b)?.unwrap();
        let c = ea.len().cmp(&eb.len());
        if c != Ordering::Equal {
            return Ok(c);
        }
        for i in 0..ea.len() {
            let c = try_total_cmp(&ea.get(i), &eb.get(i))?;
            if c != Ordering::Equal {
                return Ok(c);
            }
        }
        return Ok(Ordering::Equal);
    }
    // functions (an `Fcn` over `1..n` or strings needs no conversion: the
    // generic comparison below orders it like the equal `Tuple` / `Record`)
    let (mut sa, mut sb) = (None, None);
    let a = if matches!(a, Value::LazyFcn(_)) { force_fcn(a, &mut sa)? } else { a };
    let b = if matches!(b, Value::LazyFcn(_)) { force_fcn(b, &mut sb)? } else { b };
    match (a, b) {
        (Value::Tuple(x), Value::Tuple(y)) => {
            if Arc::ptr_eq(x, y) {
                return Ok(Ordering::Equal);
            }
            let c = x.len().cmp(&y.len());
            if c != Ordering::Equal {
                return Ok(c);
            }
            return total_seq(x, y);
        }
        (Value::Record(x), Value::Record(y)) => {
            let c = x.len().cmp(&y.len());
            if c != Ordering::Equal {
                return Ok(c);
            }
            for (p, q) in x.iter().zip(y.iter()) {
                let c = p.0.cmp(&q.0);
                if c != Ordering::Equal {
                    return Ok(c);
                }
            }
            for (p, q) in x.iter().zip(y.iter()) {
                let c = try_total_cmp(&p.1, &q.1)?;
                if c != Ordering::Equal {
                    return Ok(c);
                }
            }
            return Ok(Ordering::Equal);
        }
        _ => {}
    }
    let (x, y) = (FcnRef::of(a).unwrap(), FcnRef::of(b).unwrap());
    let plan = FunctionComparison::new(x.len(), y.len(), matches!(x, FcnRef::Tuple(_)), matches!(y, FcnRef::Tuple(_)));
    if plan.length_order != Ordering::Equal {
        return Ok(plan.length_order);
    }
    for i in plan.domains {
        let c = try_total_cmp(&x.key(i), &y.key(i))?;
        if c != Ordering::Equal {
            return Ok(c);
        }
    }
    for i in plan.values {
        let c = try_total_cmp(x.val(i), y.val(i))?;
        if c != Ordering::Equal {
            return Ok(c);
        }
    }
    Ok(Ordering::Equal)
}

fn total_seq(a: &[Value], b: &[Value]) -> Result<Ordering> {
    for (x, y) in a.iter().zip(b.iter()) {
        let c = try_total_cmp(x, y)?;
        if c != Ordering::Equal {
            return Ok(c);
        }
    }
    Ok(Ordering::Equal)
}
