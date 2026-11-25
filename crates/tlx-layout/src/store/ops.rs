//! The collection operations of the value contract on stored handles
//! (docs/value-store.md §4.2): DOMAIN, application with
//! TLC's search schedule, EXCEPT, `:>`, `@@`, membership, field access,
//! the sequence operators, constructors. Each mirrors the interpreter's
//! operation in `tlx_value::ops` on the thawed values: the same result with
//! the same representation (witness), and an error (`RefOpError::Eval`)
//! wherever the interpreter has one. An `Eval` error makes the compiled
//! code give the whole action or predicate back to the interpreter, which
//! reports it exactly, so an operation may also return `Eval` for a case it
//! does not mirror; it must never succeed where the interpreter fails.

use std::cmp::Ordering;

use tlx_value::plan::{Schedule, Witness, SCAN_LIMIT};
use tlx_value::{FcnDom, Sym};

use super::order::{cmp_tlc, eq_tlc, fn_view, Fn};
use super::{as_int, int_handle, str_handle, tag, Body, Store, StoreError, TAG_MODEL_VALUE, TAG_STR};

pub use tlx_value::plan::Absent;

/// Why a store operation did not produce a result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RefOpError {
    /// A TLC error, or a case left to the interpreter.
    Eval,
    /// The store's budget is exhausted.
    Full,
}

impl From<StoreError> for RefOpError {
    fn from(e: StoreError) -> RefOpError {
        match e {
            StoreError::Full => RefOpError::Full,
            StoreError::NotFinite(_) => RefOpError::Eval,
            StoreError::InvalidHandle(_) => RefOpError::Eval,
        }
    }
}

type R<T> = Result<T, RefOpError>;

fn eval<T>() -> R<T> {
    Err(RefOpError::Eval)
}

/// The witness of a function node (None: not a function).
pub fn witness(s: &Store, f: u64) -> Option<Witness> {
    match &s.node(f)?.body {
        Body::Tuple(_) => Some(Witness::Tuple),
        Body::Record(_) => Some(Witness::Record),
        Body::Fcn(_, FcnDom::Enumerated) => Some(Witness::Enumerated),
        Body::Fcn(_, FcnDom::Interval) => Some(Witness::Interval),
        _ => None,
    }
}

impl Store {
    /// `DOMAIN f` (`ops::domain`): `1..n` of a tuple, `lo..hi` of an
    /// interval-backed function, or the enumerated set of a record's fields or
    /// an enumerated function's keys.
    pub fn domain(&self, f: u64) -> R<u64> {
        let Some(node) = self.node(f) else { return eval() };
        if let Body::Fcn(kv, FcnDom::Interval) = &node.body {
            let keys = &kv[..kv.len() / 2];
            if !keys.is_empty() && (as_int(keys[0]).is_none() || as_int(keys[keys.len() - 1]).is_none()) {
                return eval();
            }
        }
        let make = || -> Result<u64, StoreError> {
            match &node.body {
                Body::Tuple(t) => self.intern(Body::Interval(1, t.len() as i64)),
                Body::Record(r) => self.intern(Body::Set(r.iter().map(|(k, _)| str_handle(*k)).collect())),
                Body::Fcn(kv, dom) => {
                    let keys = &kv[..kv.len() / 2];
                    let w = if *dom == FcnDom::Interval { Witness::Interval } else { Witness::Enumerated };
                    if w.domain_is_interval() {
                        let (lo, hi) = match (keys.first(), keys.last()) {
                            (Some(&a), Some(&b)) => (as_int(a).unwrap(), as_int(b).unwrap()),
                            _ => (1, 0),
                        };
                        self.intern(Body::Interval(lo, hi))
                    } else {
                        self.intern(Body::Set(keys.into()))
                    }
                }
                _ => unreachable!(),
            }
        };
        match &node.body {
            Body::Tuple(_) | Body::Record(_) | Body::Fcn(..) => Ok(self.cached_domain(f, make)?),
            _ => eval(),
        }
    }

    /// TLC `select` (`ops::select`): the index of `k` in function `f`'s
    /// view (`order::Fn`), None when `k` is not in the domain; an error for
    /// a key the witness rejects. Follows `plan::Witness::schedule`.
    pub fn select(&self, f: u64, k: u64) -> R<Option<usize>> {
        if !self.is_valid(k) {
            return eval();
        }
        let Some(node) = self.node(f) else { return eval() };
        match &node.body {
            Body::Tuple(t) => match as_int(k) {
                Some(i) if i >= 1 && i <= t.len() as i64 => Ok(Some(i as usize - 1)),
                Some(_) => Ok(None),
                None => eval(),
            },
            Body::Record(r) => {
                if tag(k) != TAG_STR {
                    return eval();
                }
                let name = sym(k);
                Ok(if r.len() <= 8 { r.iter().position(|(n, _)| *n == name) } else { r.binary_search_by_key(&name, |(n, _)| *n).ok() })
            }
            Body::Fcn(kv, dom) => {
                let keys = &kv[..kv.len() / 2];
                let w = if *dom == FcnDom::Interval { Witness::Interval } else { Witness::Enumerated };
                match w.schedule(keys.len()) {
                    Schedule::Offset => {
                        let Some(i) = as_int(k) else { return eval() };
                        let Some(first) = keys.first() else { return Ok(None) };
                        let Some(lo) = as_int(*first) else { return eval() };
                        let off = i.wrapping_sub(lo);
                        Ok((0..keys.len() as i64).contains(&off).then_some(off as usize))
                    }
                    schedule => {
                        // An integer key of a function over `1..n` is at `key - 1`.
                        if let (Some(i), Some(1)) = (as_int(k), keys.first().and_then(|f| as_int(*f))) {
                            if i >= 1 && i <= keys.len() as i64 && as_int(keys[i as usize - 1]) == Some(i) {
                                return Ok(Some(i as usize - 1));
                            }
                        }
                        if schedule == Schedule::Scan {
                            for (i, fk) in keys.iter().enumerate() {
                                if eq_tlc(self, *fk, k)? {
                                    return Ok(Some(i));
                                }
                            }
                            return Ok(None);
                        }
                        let (mut lo, mut hi) = (0usize, keys.len());
                        while lo < hi {
                            let mid = lo + (hi - lo) / 2;
                            match cmp_tlc(self, keys[mid], k)? {
                                Ordering::Equal => return Ok(Some(mid)),
                                Ordering::Less => lo = mid + 1,
                                Ordering::Greater => hi = mid,
                            }
                        }
                        Ok(None)
                    }
                }
            }
            _ => eval(),
        }
    }

    /// The value at index `i` of function `f`'s view.
    pub fn value_at(&self, f: u64, i: usize) -> u64 {
        fn_view(self, f).expect("function").val(i)
    }

    /// `f[k]` (`ops::apply`).
    pub fn apply(&self, f: u64, k: u64) -> R<u64> {
        match self.select(f, k)? {
            Some(i) => Ok(self.value_at(f, i)),
            None => eval(),
        }
    }

    /// `r.name` (`ops::field`).
    pub fn field(&self, r: u64, name: Sym) -> R<u64> {
        self.apply(r, str_handle(name))
    }

    /// Function `f` with the value at index `i` (of its view) replaced by
    /// `v`, in the same representation (`ops::except` after `select`).
    pub fn set_at(&self, f: u64, i: usize, v: u64) -> R<u64> {
        let body = match &self.get(f).body {
            Body::Tuple(t) => {
                let mut t = t.to_vec();
                t[i] = v;
                Body::Tuple(t.into())
            }
            Body::Record(r) => {
                let mut r = r.to_vec();
                r[i].1 = v;
                Body::Record(r.into())
            }
            Body::Fcn(kv, dom) => {
                let mut kv = kv.to_vec();
                let n = kv.len() / 2;
                kv[n + i] = v;
                Body::Fcn(kv.into(), *dom)
            }
            _ => return eval(),
        };
        if self.value_at(f, i) == v {
            return Ok(f);
        }
        Ok(self.intern(body)?)
    }

    /// `k :> v` (`ops::single_fcn`): a function over the enumerated domain
    /// `{k}`.
    pub fn single(&self, k: u64, v: u64) -> R<u64> {
        Ok(self.intern(Body::Fcn(vec![k, v].into(), FcnDom::Enumerated))?)
    }

    /// `f @@ g` (`ops::fcn_merge`, TLC `combineFcn`): over the union of the
    /// domains, `f`'s values first; always a function over an enumerated
    /// domain.
    pub fn merge(&self, f: u64, g: u64) -> R<u64> {
        let (Some(x), Some(y)) = (fn_view(self, f), fn_view(self, g)) else { return eval() };
        if x.len() == 0 && y.len() == 0 {
            return Ok(self.intern(Body::Fcn(Box::new([]), FcnDom::Enumerated))?);
        }
        let pairs: Vec<(u64, u64)> = match (&self.get(f).body, &self.get(g).body) {
            (Body::Tuple(a), Body::Tuple(b)) => {
                let mut es = a.to_vec();
                if b.len() > a.len() {
                    es.extend_from_slice(&b[a.len()..]);
                }
                es.iter().enumerate().map(|(i, v)| (int_handle(i as i64 + 1).expect("index"), *v)).collect()
            }
            (Body::Record(a), Body::Record(b)) => {
                // `Value::record` of g's fields then f's: sorted by name,
                // the last of equal names (f's) wins.
                let mut fs: Vec<(Sym, u64)> = b.to_vec();
                fs.extend_from_slice(a);
                fs.sort_by_key(|f| f.0);
                let mut out: Vec<(Sym, u64)> = Vec::with_capacity(fs.len());
                for f in fs {
                    match out.last_mut() {
                        Some(last) if last.0 == f.0 => *last = f,
                        _ => out.push(f),
                    }
                }
                out.into_iter().map(|(k, v)| (str_handle(k), v)).collect()
            }
            _ => {
                let fkeys: Vec<u64> = (0..x.len()).map(|i| x.key(i)).collect();
                let mut pairs: Vec<(u64, u64)> = (0..x.len()).map(|i| (x.key(i), x.val(i))).collect();
                for j in 0..y.len() {
                    let k = y.key(j);
                    if !self.contains_key(&fkeys, k)? {
                        pairs.push((k, y.val(j)));
                    }
                }
                self.sort_pairs(pairs)?
            }
        };
        let mut kv: Vec<u64> = pairs.iter().map(|p| p.0).collect();
        kv.extend(pairs.iter().map(|p| p.1));
        Ok(self.intern(Body::Fcn(kv.into(), FcnDom::Enumerated))?)
    }

    /// `ops::fcns::contains_key`: `k` (compared first) among sorted keys.
    fn contains_key(&self, keys: &[u64], k: u64) -> R<bool> {
        if Witness::Enumerated.schedule(keys.len()) == Schedule::Scan {
            for fk in keys {
                if eq_tlc(self, k, *fk)? {
                    return Ok(true);
                }
            }
            return Ok(false);
        }
        let (mut lo, mut hi) = (0usize, keys.len());
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            match cmp_tlc(self, k, keys[mid])? {
                Ordering::Equal => return Ok(true),
                Ordering::Less => hi = mid,
                Ordering::Greater => lo = mid + 1,
            }
        }
        Ok(false)
    }

    /// `value::sort_pairs`: pairs sorted by key in TLC order, the same
    /// comparisons (so the same errors) as the interpreter: integer and
    /// string keys directly, otherwise TLC's binary insertion sort up to
    /// `SCAN_LIMIT` pairs; beyond, a sort validated pairwise (an error in
    /// a comparison the interpreter would not make is a fallback).
    fn sort_pairs(&self, mut pairs: Vec<(u64, u64)>) -> R<Vec<(u64, u64)>> {
        if pairs.len() <= 1 {
            return Ok(pairs);
        }
        if pairs.iter().all(|(k, _)| as_int(*k).is_some()) {
            pairs.sort_by_key(|(k, _)| as_int(*k).unwrap());
            return distinct(pairs, |a, b| a == b);
        }
        if pairs.iter().all(|(k, _)| tag(*k) == TAG_STR) {
            pairs.sort_by_key(|(k, _)| sym(*k));
            return distinct(pairs, |a, b| a == b);
        }
        if pairs.len() <= SCAN_LIMIT {
            let mut out: Vec<(u64, u64)> = Vec::with_capacity(pairs.len());
            for p in pairs {
                let (mut lo, mut hi) = (0usize, out.len());
                while lo < hi {
                    let mid = lo + (hi - lo) / 2;
                    match cmp_tlc(self, p.0, out[mid].0)? {
                        Ordering::Equal => return eval(),
                        Ordering::Less => hi = mid,
                        Ordering::Greater => lo = mid + 1,
                    }
                }
                out.insert(lo, p);
            }
            return Ok(out);
        }
        let mut failed = false;
        pairs.sort_by(|a, b| match cmp_tlc(self, a.0, b.0) {
            Ok(o) => o,
            Err(_) => {
                failed = true;
                Ordering::Equal
            }
        });
        if failed {
            return eval();
        }
        for w in pairs.windows(2) {
            if cmp_tlc(self, w[1].0, w[0].0)? != Ordering::Greater {
                return eval();
            }
        }
        Ok(pairs)
    }

    /// `v \in S` for a stored set `S` (`ops::member`: binary search with
    /// `v` compared first; an interval by range).
    pub fn member(&self, v: u64, set: u64) -> R<bool> {
        if !self.is_valid(v) {
            return eval();
        }
        let Some(node) = self.node(set) else { return eval() };
        match &node.body {
            Body::Set(es) => {
                let (mut lo, mut hi) = (0usize, es.len());
                while lo < hi {
                    let mid = lo + (hi - lo) / 2;
                    match cmp_tlc(self, v, es[mid])? {
                        Ordering::Equal => return Ok(true),
                        Ordering::Less => hi = mid,
                        Ordering::Greater => lo = mid + 1,
                    }
                }
                Ok(false)
            }
            Body::Interval(lo, hi) => match as_int(v) {
                Some(x) => Ok(*lo <= x && x <= *hi),
                None if matches!(self.node(v).map(|n| &n.body), Some(Body::Int(_))) => {
                    let Some(Body::Int(x)) = self.node(v).map(|n| &n.body) else { unreachable!() };
                    Ok(lo <= x && x <= hi)
                }
                None if tag(v) == TAG_MODEL_VALUE && sym(v).model_value_type().is_none() => Ok(false),
                None if lo <= hi => eval(),
                None => Ok(false),
            },
            _ => eval(),
        }
    }

    /// `k \in DOMAIN f`.
    pub fn in_domain(&self, k: u64, f: u64) -> R<bool> {
        let d = self.domain(f)?;
        self.member(k, d)
    }

    /// `Cardinality(S)` of a stored set.
    pub fn cardinality(&self, set: u64) -> R<i64> {
        match self.node(set).map(|n| &n.body) {
            Some(Body::Set(es)) => Ok(es.len() as i64),
            Some(Body::Interval(lo, hi)) => Ok(if hi < lo { 0 } else { hi - lo + 1 }),
            _ => eval(),
        }
    }

    /// The elements of sequence `s` (TLC `toTuple`: a tuple, or a function
    /// over `1..n`); None: not a sequence.
    fn seq_elems(&self, s: u64) -> Option<Vec<u64>> {
        let f = fn_view(self, s)?;
        match f {
            Fn::Tuple(t) => Some(t.to_vec()),
            Fn::Fcn(k, v) if super::fcn_alias(k) == super::Alias::Tuple => Some(v.to_vec()),
            _ => None,
        }
    }

    /// `Len(s)` (`ops::seqs::len`, strings included).
    pub fn len(&self, s: u64) -> R<i64> {
        if !self.is_valid(s) {
            return eval();
        }
        if tag(s) == TAG_STR {
            return Ok(sym(s).as_str().chars().count() as i64);
        }
        match fn_view(self, s) {
            Some(Fn::Tuple(t)) => Ok(t.len() as i64),
            Some(Fn::Fcn(k, _)) if super::fcn_alias(k) == super::Alias::Tuple => Ok(k.len() as i64),
            _ => eval(),
        }
    }

    /// `Append(s, x)`: a tuple.
    pub fn append(&self, s: u64, x: u64) -> R<u64> {
        let Some(mut es) = self.seq_elems(s) else { return eval() };
        es.push(x);
        Ok(self.intern(Body::Tuple(es.into()))?)
    }

    /// `Head(s)`.
    pub fn head(&self, s: u64) -> R<u64> {
        match self.seq_elems(s) {
            Some(es) if !es.is_empty() => Ok(es[0]),
            _ => eval(),
        }
    }

    /// `Tail(s)` of a sequence (a string's is left to the interpreter).
    pub fn tail(&self, s: u64) -> R<u64> {
        match self.seq_elems(s) {
            Some(es) if !es.is_empty() => Ok(self.intern(Body::Tuple(es[1..].into()))?),
            _ => eval(),
        }
    }

    /// The tuple `<<es...>>`.
    pub fn tuple(&self, es: &[u64]) -> R<u64> {
        Ok(self.intern(Body::Tuple(es.into()))?)
    }

    /// The record `[f1 |-> v1, ...]` (`Value::record`: fields sorted by
    /// name, the last of equal names wins; no fields is `<<>>`).
    pub fn record(&self, fields: &[(Sym, u64)]) -> R<u64> {
        if fields.is_empty() {
            return self.tuple(&[]);
        }
        let mut fs = fields.to_vec();
        if !fs.windows(2).all(|w| w[0].0 < w[1].0) {
            fs.sort_by_key(|f| f.0);
            let mut out: Vec<(Sym, u64)> = Vec::with_capacity(fs.len());
            for f in fs {
                match out.last_mut() {
                    Some(last) if last.0 == f.0 => *last = f,
                    _ => out.push(f),
                }
            }
            fs = out;
        }
        Ok(self.intern(Body::Record(fs.into()))?)
    }
}

fn sym(h: u64) -> Sym {
    super::symbol(h).expect("invalid symbol handle")
}

/// Sorted pairs with distinct keys (`check_distinct`), else an error.
fn distinct(pairs: Vec<(u64, u64)>, same: impl std::ops::Fn(u64, u64) -> bool) -> R<Vec<(u64, u64)>> {
    if pairs.windows(2).any(|w| same(w[0].0, w[1].0)) {
        return eval();
    }
    Ok(pairs)
}
