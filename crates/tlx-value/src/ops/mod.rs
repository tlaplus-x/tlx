//! Set, function and sequence operations with TLC semantics.
//! Enumeration order follows tlc-semantics.md §1.5.
//!
//! Lazy vs eager (mirrors TLC's `Reducible` logic, `TI/Tool.java:2682-2702`):
//! - `union`: eager (a normalized `Set`) when both sides are `Set`/`Interval`;
//!   if one side is an empty `Set`/`Interval` the *other side* is returned
//!   unchanged; otherwise `LazySet::Cup` (with the enumerated side first when
//!   exactly one side is a `Set`/`Interval`, like TLC's `arg2.cup(arg1)`).
//! - `intersect`: eager when either side is a `Set`/`Interval` (filters that
//!   side, left first); otherwise `LazySet::Cap`.
//! - `difference`: eager when the left side is a `Set`/`Interval`; otherwise
//!   `LazySet::Diff`.
//! - `big_union`: eager only when the argument is a `Set` whose elements are
//!   all `Set`s (not intervals / lazy sets); otherwise `LazySet::Union`.
//! - `powerset`, `fcn_set`, `product`, `record_set`, `seq_set`: always lazy.
//!
//! Submodules: `member` (`\in`), `enumerate` (enumeration order),
//! `sets` (set algebra, cardinality, set constructors), `fcns` (functions and
//! records), `seqs` (sequences and strings as sequences).

mod enumerate;
mod fcns;
pub(crate) mod ksubset;
mod member;
mod seqs;
mod sets;

use std::sync::Arc;

use crate::error::err;
use crate::intern::Sym;
use crate::lazy::LazySet;
use crate::value::Value;
use crate::Result;

pub use enumerate::{
    bound_kind, enumerate, enumerate_normalized, for_each_constrained_subset, for_each_element, for_each_enumerated,
    for_each_enumerated_seqs, for_each_enumerated_subsets, materialization_error, normalize_enumerated, over_set_bound, size_fact,
    size_if_known, streams_normalized, BoundKind, SeqsVisitor, SizeFact, SubsetBase, SubsetVisitor,
};
pub use fcns::{apply, apply_ref, apply_tuple_ref, domain, except, fcn_merge, field, field_ref, select, single_fcn};
pub use ksubset::ksubset;
pub use member::member;
pub use seqs::{append, concat, head, len, seq_set, subseq, tail};
pub use sets::{
    big_union, cardinality, cardinality_of_normalized, difference, fcn_set, intersect, interval, is_finite_set, overridden_size_error,
    powerset, product, record_set, size, subseteq, union,
};

pub(super) fn lazy(l: LazySet) -> Value {
    Value::LazySet(Arc::new(l))
}

/// TLC's `instanceof Enumerable`: sets that can (in principle) be enumerated.
/// False for `Seq(S)`, `Nat`, `Int`, `STRING` and non-sets.
pub fn is_enumerable(s: &Value) -> bool {
    match s {
        Value::Set(_) | Value::Interval(..) => true,
        Value::LazySet(l) => !matches!(**l, LazySet::Seq(_) | LazySet::Nat | LazySet::Int | LazySet::StringSet | LazySet::Any),
        _ => false,
    }
}

/// TLC's `instanceof Reducible`: eager sets/intervals whose elements TLC
/// filters directly on `\cap` and `\` (retaining their element witnesses).
pub fn is_reducible(s: &Value) -> bool {
    matches!(s, Value::Set(_) | Value::Interval(..)) || matches!(s, Value::LazySet(l) if matches!(**l, LazySet::Enum(_)))
}

/// Advance `idx`, a strictly increasing combination of indices into `0..n`
/// (`idx.len() <= n`), to the next combination in lexicographic order;
/// returns `false`, leaving `idx` unchanged, after the last one. This is the
/// advance step of TLC's `KElementEnumerator`, shared by `ops::ksubset`'s
/// enumeration and by `SUBSET S`, which walks every size `k` in `0..=n` over
/// the same ordered element list.
pub(super) fn next_combination(idx: &mut [usize], n: usize) -> bool {
    let k = idx.len();
    debug_assert!(k <= n, "no successor of a combination longer than the source");
    let mut i = k;
    while i > 0 && idx[i - 1] == n - k + (i - 1) {
        i -= 1;
    }
    if i == 0 {
        return false;
    }
    idx[i - 1] += 1;
    for j in i..k {
        idx[j] = idx[j - 1] + 1;
    }
    true
}

/// TLC's `isEmpty` with its errors: for a value that is not a set (and for
/// `Any`), and for a set TLC must enumerate but cannot.
pub fn is_empty_checked(s: &Value) -> Result<bool> {
    match s {
        Value::LazySet(l) => match &**l {
            LazySet::Enum(es) => Ok(es.is_empty()),
            LazySet::Any => err(format!("Shouldn't call isEmpty() on value {s}")),
            LazySet::KSubset(k, base) => ksubset::no_elements(*k, base),
            LazySet::FcnSet(d, r) => Ok(!is_empty_checked(d)? && is_empty_checked(r)?),
            LazySet::Product(sets) => {
                for x in sets {
                    if is_empty_checked(x)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            LazySet::RecordSet(fields) => {
                for (_, x) in fields {
                    if is_empty_checked(x)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            // (Value.isEmpty: whether the enumeration has a first element.)
            LazySet::Union(_) | LazySet::Cup(..) | LazySet::Cap(..) | LazySet::Diff(..) | LazySet::Custom(_) => {
                let mut none = true;
                for_each_enumerated(s, &mut |_| {
                    none = false;
                    Ok(false)
                })?;
                Ok(none)
            }
            _ => Ok(is_empty_set(s)),
        },
        Value::Set(_) | Value::Interval(..) => Ok(is_empty_set(s)),
        _ => err(format!("Shouldn't call isEmpty() on value {s}")),
    }
}

/// Cheap emptiness test (TLC `isEmpty`); unknown cases count as non-empty.
pub(super) fn is_empty_set(s: &Value) -> bool {
    match s {
        Value::Set(e) => e.is_empty(),
        Value::Interval(lo, hi) => hi < lo,
        Value::LazySet(l) => match &**l {
            LazySet::Subset(_) | LazySet::Seq(_) | LazySet::Nat | LazySet::Int | LazySet::StringSet | LazySet::Any => false,
            LazySet::FcnSet(d, r) => !is_empty_set(d) && is_empty_set(r),
            LazySet::Product(sets) => sets.iter().any(is_empty_set),
            LazySet::RecordSet(fields) => fields.iter().any(|(_, s)| is_empty_set(s)),
            LazySet::Cup(a, b) => is_empty_set(a) && is_empty_set(b),
            LazySet::KSubset(k, base) => ksubset::no_elements(*k, base).unwrap_or(false),
            _ => matches!(cardinality(s), Ok(0)),
        },
        _ => false,
    }
}

// ---- symmetry ----

/// `permute` that shares the subvalues containing no moved model value
/// (they are not rebuilt) and returns `None` when nothing changes. `image`
/// maps a moved model value to its image (`None`: not moved).
pub fn permute_shared(v: &Value, image: &impl Fn(Sym) -> Option<Value>) -> Result<Option<Value>> {
    // The first element of `xs` that changes, with its index.
    fn first_changed<'v>(xs: impl Iterator<Item = &'v Value>, image: &impl Fn(Sym) -> Option<Value>) -> Result<Option<(usize, Value)>> {
        for (i, x) in xs.enumerate() {
            if let Some(y) = permute_shared(x, image)? {
                return Ok(Some((i, y)));
            }
        }
        Ok(None)
    }
    // The images of `es` (in order), or `None` when none changes.
    fn all(es: &[Value], image: &impl Fn(Sym) -> Option<Value>) -> Result<Option<Vec<Value>>> {
        let Some((i, first)) = first_changed(es.iter(), image)? else {
            return Ok(None);
        };
        let mut out = Vec::with_capacity(es.len());
        out.extend_from_slice(&es[..i]);
        out.push(first);
        for e in &es[i + 1..] {
            out.push(permute_shared(e, image)?.unwrap_or_else(|| e.clone()));
        }
        Ok(Some(out))
    }
    Ok(match v {
        Value::ModelValue(m) => image(*m),
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => None,
        Value::Set(es) => all(es, image)?.map(Value::set_from).transpose()?,
        Value::Tuple(es) => all(es, image)?.map(Value::tuple),
        Value::Record(fs) => {
            let Some((i, first)) = first_changed(fs.iter().map(|(_, x)| x), image)? else {
                return Ok(None);
            };
            let mut out: Vec<(Sym, Value)> = fs.to_vec();
            out[i].1 = first;
            for f in &mut out[i + 1..] {
                if let Some(x) = permute_shared(&f.1, image)? {
                    f.1 = x;
                }
            }
            Some(Value::Record(out.into()))
        }
        Value::Fcn(ps, d) => {
            let mut out: Option<Vec<(Value, Value)>> = None;
            let mut keys_changed = false;
            for (i, (k, x)) in ps.iter().enumerate() {
                let k2 = permute_shared(k, image)?;
                let x2 = permute_shared(x, image)?;
                if k2.is_none() && x2.is_none() {
                    continue;
                }
                keys_changed |= k2.is_some();
                let o = out.get_or_insert_with(|| ps.to_vec());
                if let Some(k2) = k2 {
                    o[i].0 = k2;
                }
                if let Some(x2) = x2 {
                    o[i].1 = x2;
                }
            }
            match out {
                None => None,
                // Keys in place: still sorted.
                Some(o) if !keys_changed => Some(Value::Fcn(o.into(), *d)),
                // (Still a function over an enumerated domain.)
                Some(o) => Some(Value::fcn_rcd_from_pairs(o)?),
            }
        }
        Value::LazySet(_) | Value::LazyFcn(_) => {
            let n = v.normalize()?;
            Some(permute_shared(&n, image)?.unwrap_or(n))
        }
    })
}

/// Apply a model-value permutation (`perm` maps a model value to its image,
/// or `None` to leave it unchanged) to every model value inside `v`
/// (TLC `Value.permute`, used for SYMMETRY). The result is canonical.
pub fn permute(v: &Value, perm: &dyn Fn(Sym) -> Option<Value>) -> Result<Value> {
    Ok(match v {
        Value::ModelValue(m) => perm(*m).unwrap_or_else(|| v.clone()),
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => v.clone(),
        Value::Set(es) => Value::set_from(es.iter().map(|e| permute(e, perm)).collect::<Result<_>>()?)?,
        Value::Tuple(es) => Value::tuple(es.iter().map(|e| permute(e, perm)).collect::<Result<_>>()?),
        Value::Record(fs) => Value::record(fs.iter().map(|(k, x)| Ok((*k, permute(x, perm)?))).collect::<Result<_>>()?),
        Value::Fcn(ps, _) => {
            Value::fcn_rcd_from_pairs(ps.iter().map(|(k, x)| Ok((permute(k, perm)?, permute(x, perm)?))).collect::<Result<_>>()?)?
        }
        Value::LazySet(_) | Value::LazyFcn(_) => permute(&v.normalize()?, perm)?,
    })
}
