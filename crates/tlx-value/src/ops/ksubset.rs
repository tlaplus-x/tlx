//! `FiniteSetsExt!kSubset(k, S)`, the set of the k-element subsets of S, as
//! TLC's lazy `KSubsetValue` (a `SubsetValue` that only holds subsets of
//! size k): membership, size, emptiness and comparisons are decided from k
//! and S where TLC decides them so, without enumerating the set (e.g.
//! `{1, 2} \in kSubset(2, 1..64)`, `kSubset(0, Nat) = {{}}`).

use std::cmp::Ordering;

use super::{enumerate_normalized, for_each_element, is_empty_checked, is_enumerable, is_finite_set, lazy, member, next_combination, size};
use crate::error::err;
use crate::lazy::LazySet;
use crate::order::{cmp_tlc, eq_tlc};
use crate::value::Value;
use crate::Result;

/// `kSubset(k, s)` (FiniteSetsExt.java `kSubset`): k must be an integer and
/// s a set (enumerable, or one of TLC's overridden sets such as Nat).
pub fn ksubset(k: &Value, s: &Value) -> Result<Value> {
    let arg = |which: &str, what: &str, v: &Value| {
        Err(crate::ValueError::of_kind(
            crate::ValueErrorKind::ArgumentError,
            format!("The {which} argument of kSubset should be a {what}, but instead it is:\n{v}"),
        ))
    };
    let Value::Int(k) = k else { return arg("first", "natural number", k) };
    if !s.is_set() {
        return arg("second", "set", s);
    }
    Ok(lazy(LazySet::KSubset(*k, s.clone())))
}

/// `KSubsetValue.hasNoElements` (also its `isEmpty`): k < 0, or more than
/// the elements of a finite base.
pub(crate) fn no_elements(k: i64, base: &Value) -> Result<bool> {
    Ok(k < 0 || (is_finite_set(base)? && size(base)? < k))
}

/// `n` choose `k`, or None beyond u128.
pub(crate) fn choose(n: i64, k: i64) -> Option<u128> {
    let k = k.min(n - k);
    let mut c: u128 = 1;
    for i in 0..k {
        // c * (n - i) / (i + 1) is exact at each step.
        c = c.checked_mul((n - i) as u128)? / (i + 1) as u128;
    }
    Some(c)
}

/// `KSubsetValue.count`: the number of k-subsets (None: beyond u128, which
/// only orders above every other count here).
fn count(k: i64, base: &Value) -> Result<Option<u128>> {
    if k < 0 {
        return Ok(Some(0));
    }
    if k == 0 {
        return Ok(Some(1));
    }
    let n = size(base)?;
    if k > n {
        return Ok(Some(0));
    }
    Ok(choose(n, k))
}

/// `KSubsetValue.size`: an error beyond TLC's int.
pub(crate) fn ksubset_size(k: i64, base: &Value) -> Result<i64> {
    match count(k, base)? {
        Some(c) if c <= i32::MAX as u128 => Ok(c as i64),
        _ => err(format!("k={k} and n={}", size(base)?)),
    }
}

/// `KSubsetValue.isFinite`.
pub(crate) fn ksubset_is_finite(k: i64, base: &Value) -> Result<bool> {
    Ok(k <= 0 || is_finite_set(base)?)
}

/// `v \in kSubset(k, base)` (`KSubsetValue.member`): a set of k elements
/// of the base (`SubsetValue.member`).
pub(crate) fn ksubset_member(v: &Value, k: i64, base: &Value) -> Result<bool> {
    if no_elements(k, base)? {
        return Ok(false);
    }
    if size(v)? != k {
        return Ok(false);
    }
    if !is_enumerable(v) {
        return err(format!(
            "Attempted to check if the non-enumerable value\n{v}\nis element of\n{}",
            lazy(LazySet::KSubset(k, base.clone()))
        ));
    }
    let mut res = true;
    for_each_element(v, &mut |e| {
        res = member(&e, base)?;
        Ok(res)
    })?;
    Ok(res)
}

/// The k-subsets in TLC's order (`SubsetValue.kElements`): the combinations
/// of the normalized base in lexicographic order of their indices, which
/// is the normalized order of the sets.
pub(crate) fn ksubset_for_each(k: i64, base: &Value, f: &mut dyn FnMut(Value) -> Result<bool>) -> Result<bool> {
    if no_elements(k, base)? {
        return Ok(true);
    }
    if k == 0 {
        return f(Value::Set(Vec::new().into()));
    }
    let n = size(base)?;
    if n < k {
        return Ok(true);
    }
    // (`numberOfKElements`, `KElementEnumerator`.)
    match choose(n, k) {
        Some(c) if c <= i64::MAX as u128 => {
            if c > i32::MAX as u128 {
                return err("Subset too large.");
            }
        }
        _ => return err(format!("k={k} and n={n}")),
    }
    let elems = enumerate_normalized(base)?;
    let (n, k) = (elems.len(), k as usize);
    let mut idx: Vec<usize> = (0..k).collect();
    loop {
        if !f(Value::Set(idx.iter().map(|&i| elems[i].clone()).collect()))? {
            return Ok(false);
        }
        if !next_combination(&mut idx, n) {
            return Ok(true);
        }
    }
}

/// `SubsetValue.convertAndCache` of a k-subset: its elements as an
/// enumerated set, sized first (`toSetEnum`).
fn converted(k: i64, base: &Value) -> Result<Value> {
    ksubset_size(k, base)?;
    let mut out = Vec::new();
    ksubset_for_each(k, base, &mut |s| {
        out.push(s);
        Ok(true)
    })?;
    Ok(Value::Set(out.into()))
}

/// `KSubsetValue.compareCardinality` with `SUBSET t`: None unless both
/// bases are finite.
fn compare_with_powerset(k: i64, base: &Value, t: &Value) -> Result<Option<Ordering>> {
    if !is_finite_set(base)? || !is_finite_set(t)? {
        return Ok(None);
    }
    let n = size(t)?;
    let p = if n < 128 { Some(1u128 << n) } else { None };
    Ok(match (count(k, base)?, p) {
        (Some(c), Some(p)) => Some(c.cmp(&p)),
        (Some(_), None) => Some(Ordering::Less),
        // (Both beyond u128: not decided.)
        (None, _) => None,
    })
}

/// `kSubset(k, base).equals(b)` (`KSubsetValue.equals`).
pub(crate) fn ksubset_eq(k: i64, base: &Value, b: &Value) -> Result<bool> {
    if let Value::LazySet(l) = b {
        match &**l {
            LazySet::KSubset(k2, base2) => {
                let (e1, e2) = (no_elements(k, base)?, no_elements(*k2, base2)?);
                if e1 || e2 {
                    return Ok(e1 && e2);
                }
                if k == 0 && *k2 == 0 {
                    return Ok(true);
                }
                return Ok(k == *k2 && eq_tlc(base, base2)?);
            }
            LazySet::Subset(t) => {
                if no_elements(k, base)? {
                    return Ok(false);
                }
                if compare_with_powerset(k, base, t)?.is_some_and(|c| c != Ordering::Equal) {
                    return Ok(false);
                }
                if k == 0 && is_empty_checked(t)? {
                    return Ok(true);
                }
            }
            _ => {}
        }
    }
    eq_tlc(&converted(k, base)?, b)
}

/// `kSubset(k, base).compareTo(b)` (`KSubsetValue.compareTo`).
pub(crate) fn ksubset_cmp(k: i64, base: &Value, b: &Value) -> Result<Ordering> {
    if let Value::LazySet(l) = b {
        match &**l {
            LazySet::KSubset(k2, base2) => {
                let (e1, e2) = (no_elements(k, base)?, no_elements(*k2, base2)?);
                if e1 || e2 {
                    return Ok(e1.cmp(&e2).reverse());
                }
                if k == *k2 {
                    if k == 0 {
                        return Ok(Ordering::Equal);
                    }
                    return cmp_tlc(base, base2);
                }
                if is_finite_set(base)? && is_finite_set(base2)? {
                    let c = match (count(k, base)?, count(*k2, base2)?) {
                        (Some(x), Some(y)) => x.cmp(&y),
                        (Some(_), None) => Ordering::Less,
                        (None, Some(_)) => Ordering::Greater,
                        (None, None) => Ordering::Equal,
                    };
                    if c != Ordering::Equal {
                        return Ok(c);
                    }
                }
                if eq_tlc(base, base2)? {
                    return Ok(k.cmp(k2));
                }
            }
            LazySet::Subset(t) => {
                if no_elements(k, base)? {
                    return Ok(Ordering::Less);
                }
                if let Some(c) = compare_with_powerset(k, base, t)?.filter(|c| *c != Ordering::Equal) {
                    return Ok(c);
                }
                if k == 0 && is_empty_checked(t)? {
                    return Ok(Ordering::Equal);
                }
            }
            _ => {}
        }
    }
    cmp_tlc(&converted(k, base)?, b)
}

/// Whether `kSubset(k, base)` prints its elements (`KSubsetValue.toString`
/// with TLC's default `expand`: fewer than 64 of them); an error of its
/// size, which a lenient print swallows (printing the definition instead).
pub(crate) fn ksubset_expands(k: i64, base: &Value) -> Result<bool> {
    Ok(ksubset_size(k, base)? < 64)
}

/// The elements of `kSubset(k, base)`, normalized (for printing).
pub(crate) fn ksubset_elements(k: i64, base: &Value) -> Result<Vec<Value>> {
    let Value::Set(es) = converted(k, base)? else { unreachable!("converted is a set") };
    Ok(es.to_vec())
}

#[cfg(test)]
mod tests {
    use super::{choose, ksubset_for_each};
    use crate::ops::next_combination;
    use crate::value::Value;

    #[test]
    fn binomials() {
        assert_eq!(choose(3, 2), Some(3));
        assert_eq!(choose(64, 2), Some(2016));
        assert_eq!(choose(64, 32), Some(1_832_624_140_942_590_534));
        assert_eq!(choose(1_000_000, 999_999), Some(1_000_000));
        assert_eq!(choose(1000, 500), None);
    }

    /// Independent oracle for the order of the `k`-element subsets of `0..n`:
    /// each `k`-bit mask is one index vector, ordered lexicographically.
    fn ordered_combinations(n: usize, k: usize) -> Vec<Vec<usize>> {
        let mut all: Vec<Vec<usize>> =
            (0u32..1 << n).filter(|m| m.count_ones() as usize == k).map(|m| (0..n).filter(|i| (m >> i) & 1 == 1).collect()).collect();
        all.sort();
        all
    }

    #[test]
    fn next_combination_walks_the_ordered_vectors() {
        for n in 0..=6 {
            for k in 0..=n {
                let mut idx: Vec<usize> = (0..k).collect();
                let mut got = vec![idx.clone()];
                while next_combination(&mut idx, n) {
                    got.push(idx.clone());
                }
                assert_eq!(got, ordered_combinations(n, k), "n={n} k={k}");
            }
        }
    }

    #[test]
    fn next_combination_leaves_the_last_one_unchanged() {
        for n in 0..=6 {
            for k in 0..=n {
                let last: Vec<usize> = (n - k..n).collect();
                let mut idx = last.clone();
                assert!(!next_combination(&mut idx, n), "n={n} k={k}");
                assert_eq!(idx, last, "n={n} k={k}");
            }
        }
    }

    fn base(n: usize) -> Value {
        Value::Set((0..n as i64).map(Value::Int).collect::<Vec<_>>().into())
    }

    /// The elements of every subset `ksubset_for_each` visits, and whether it
    /// completed (`false`: the visitor stopped it).
    fn visited(base: &Value, k: i64) -> (Vec<Vec<i64>>, bool) {
        let mut got = Vec::new();
        let done = ksubset_for_each(k, base, &mut |s| {
            let Value::Set(es) = s else { unreachable!("a k-subset is an enumerated set") };
            got.push(es.iter().map(|e| e.as_int().unwrap()).collect());
            Ok(true)
        })
        .unwrap();
        (got, done)
    }

    #[test]
    fn ksubset_for_each_visits_the_ordered_subsets() {
        for n in 0..=6 {
            // k = n+1 (like every k > n) visits nothing.
            for k in 0..=n + 1 {
                let (got, done) = visited(&base(n), k as i64);
                assert!(done, "n={n} k={k}");
                let expected: Vec<Vec<i64>> =
                    ordered_combinations(n, k).into_iter().map(|c| c.into_iter().map(|i| i as i64).collect()).collect();
                assert_eq!(got, expected, "n={n} k={k}");
            }
        }
    }

    #[test]
    fn ksubset_for_each_stops_early_and_reports_the_first_error() {
        let b = base(4);
        let mut seen = Vec::new();
        let done = ksubset_for_each(2, &b, &mut |s| {
            seen.push(s);
            Ok(false)
        })
        .unwrap();
        assert!(!done);
        assert_eq!(seen.len(), 1, "the visitor stopped on the first subset");

        let mut visits = 0;
        let e = ksubset_for_each(2, &b, &mut |_| {
            visits += 1;
            Err(crate::ValueError::new("first error"))
        })
        .unwrap_err();
        assert_eq!(e.to_string(), "first error");
        assert_eq!(visits, 1, "the first error ends the enumeration");
    }
}
