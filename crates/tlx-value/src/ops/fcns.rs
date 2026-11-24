//! Functions and records: application, DOMAIN, EXCEPT, `:>` and `@@`.

use std::cmp::Ordering;
use std::sync::Arc;

use super::member;
use crate::error::err;
use crate::intern::Sym;
use crate::lazy::LazyFcn;
use crate::order::{cmp_tlc, eq_tlc};
use crate::plan::{Direction, Schedule, Witness};
use crate::repr::{force_fcn, FcnRef};
use crate::value::{FcnDom, Value};
use crate::Result;

fn kind_name(v: &Value) -> &'static str {
    match v {
        Value::Bool(_) => "a boolean",
        Value::Int(_) => "an integer",
        Value::Str(_) => "a string",
        Value::ModelValue(_) => "a model value",
        Value::Set(_) | Value::Interval(..) | Value::LazySet(_) => "a set",
        _ => "a function",
    }
}

fn not_a_function<T>(f: &Value) -> Result<T> {
    err(format!("A non-function ({}) was applied as a function:\n{f}", kind_name(f)))
}

/// Index of `arg` in a canonical `Fcn` (TLC `FcnRcdValue.select`, the
/// schedule of `plan::Witness::schedule`: linear `equals` search below
/// `plan::SCAN_LIMIT` entries, binary `compareTo` search otherwise; over an
/// interval, an integer offset, and any other key is an error).
fn fcn_index(pairs: &[(Value, Value)], dom: FcnDom, arg: &Value) -> Result<Option<usize>> {
    let witness = if dom == FcnDom::Interval { Witness::Interval } else { Witness::Enumerated };
    let schedule = witness.schedule(pairs.len());
    let direction = Direction::Stored;
    if schedule == Schedule::Offset {
        if !witness.key_type().admits(arg) {
            return err(format!("Attempted to apply function with integer domain to the non-integer argument {arg}"));
        }
        let Value::Int(i) = arg else { unreachable!("admitted interval key") };
        let Some((Value::Int(lo), _)) = pairs.first() else { return Ok(None) };
        let off = i.wrapping_sub(*lo);
        return Ok((0..pairs.len() as i64).contains(&off).then_some(off as usize));
    }
    // Fast path: an integer key of a function over `1..n` is at `key - 1`
    // (the same result as the search).
    if let (Value::Int(i), Some((Value::Int(1), _))) = (arg, pairs.first()) {
        if *i >= 1 && *i <= pairs.len() as i64 && matches!(pairs[*i as usize - 1].0, Value::Int(k) if k == *i) {
            return Ok(Some(*i as usize - 1));
        }
    }
    let equality = |k| {
        let (a, b) = direction.operands(k, arg);
        eq_tlc(a, b)
    };
    if schedule == Schedule::Scan {
        // (An untyped model value equals a model value key exactly when it
        // is that key, without an error whatever the key's type: `mv_eq`.)
        if let Value::ModelValue(a) = arg {
            if a.model_value_type().is_none() {
                for (i, (k, _)) in pairs.iter().enumerate() {
                    let found = match k {
                        Value::ModelValue(b) => a == b,
                        _ => equality(k)?,
                    };
                    if found {
                        return Ok(Some(i));
                    }
                }
                return Ok(None);
            }
        }
        for (i, (k, _)) in pairs.iter().enumerate() {
            if equality(k)? {
                return Ok(Some(i));
            }
        }
        return Ok(None);
    }
    let (mut lo, mut hi) = (0usize, pairs.len());
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        let (a, b) = direction.operands(&pairs[mid].0, arg);
        match cmp_tlc(a, b)? {
            Ordering::Equal => return Ok(Some(mid)),
            Ordering::Less => lo = mid + 1,
            Ordering::Greater => hi = mid,
        }
    }
    Ok(None)
}

fn record_index(fields: &[(Sym, Value)], name: Sym) -> Option<usize> {
    if fields.len() <= 8 {
        fields.iter().position(|(n, _)| *n == name)
    } else {
        fields.binary_search_by_key(&name, |(n, _)| *n).ok()
    }
}

/// TLC `select`: `f[arg]` if `arg` is in the domain of `f`, `None` otherwise;
/// errors for type mismatches (e.g. a tuple applied to a string). The
/// evaluator can use this to implement TLC's EXCEPT behavior (a key outside
/// the domain leaves the function unchanged, with a warning).
pub fn select(f: &Value, arg: &Value) -> Result<Option<Value>> {
    match f {
        // (A key the witness does not admit is an error even when absent,
        // `plan::Witness::key_type`.)
        Value::Tuple(t) => match arg {
            Value::Int(i) if *i >= 1 && *i <= t.len() as i64 => Ok(Some(t[*i as usize - 1].clone())),
            Value::Int(_) => Ok(None),
            _ => err(format!("Attempted to access tuple at a non integral index: {arg}")),
        },
        Value::Record(r) => match arg {
            Value::Str(s) => Ok(record_index(r, *s).map(|i| r[i].1.clone())),
            _ => err(format!("Attempted to access record by a non-string argument: {arg}")),
        },
        Value::Fcn(p, d) => Ok(fcn_index(p, *d, arg)?.map(|i| p[i].1.clone())),
        Value::LazyFcn(l) => {
            if member(arg, &l.domain()?)? {
                Ok(Some(l.apply(arg)?))
            } else {
                Ok(None)
            }
        }
        _ => not_a_function(f),
    }
}

/// `f[arg]`
pub fn apply(f: &Value, arg: &Value) -> Result<Value> {
    match apply_ref(f, arg)? {
        Some(v) => Ok(v.clone()),
        None => match f {
            Value::LazyFcn(l) => l.apply(arg),
            _ => not_a_function(f),
        },
    }
}

/// `f[arg]` borrowed from `f`, with `apply`'s errors; `None` for a lazy
/// function (whose points are computed: use `apply`).
pub fn apply_ref<'a>(f: &'a Value, arg: &Value) -> Result<Option<&'a Value>> {
    match f {
        Value::Tuple(t) => match arg {
            Value::Int(i) if *i >= 1 && *i <= t.len() as i64 => Ok(Some(&t[*i as usize - 1])),
            Value::Int(i) => err(format!("Attempted to access index {i} of tuple\n{f}\nwhich is out of bounds.")),
            _ => err(format!("Attempted to access tuple at a non integral index: {arg}")),
        },
        Value::Record(r) => match arg {
            Value::Str(s) => match record_index(r, *s) {
                Some(i) => Ok(Some(&r[i].1)),
                None => err(format!("Attempted to access nonexistent field '{}' of record\n{f}", s.as_str())),
            },
            _ => err(format!("Attempted to access record by a non-string argument: {arg}")),
        },
        Value::Fcn(p, d) => match fcn_index(p, *d, arg)? {
            Some(i) => Ok(Some(&p[i].1)),
            None => Err(crate::ValueError::of_kind(
                crate::ValueErrorKind::FunctionDomain,
                format!("Attempted to apply function:\n{f}\nto argument {arg}, which is not in the domain of the function."),
            )),
        },
        Value::LazyFcn(_) => Ok(None),
        _ => not_a_function(f),
    }
}

/// `f[<<es...>>]` borrowed from `f` without building the tuple, when that
/// is certainly `apply_ref`'s result: `f` an explicit function over an
/// enumerated domain whose keys, as far as the search goes, are tuples
/// that compare with `es` without an error (integers, strings and booleans
/// against their own kind). `None` when unsure, including a key outside the
/// domain (`apply_ref` then gives the result or the error).
pub fn apply_tuple_ref<'a>(f: &'a Value, es: &[Value]) -> Option<&'a Value> {
    let Value::Fcn(pairs, FcnDom::Enumerated) = f else { return None };
    // (`eq_tlc` / `cmp_tlc` of tuples: lengths first, then elementwise.)
    let cmp = |k: &Value| -> Option<Ordering> {
        let Value::Tuple(kt) = k else { return None };
        let c = kt.len().cmp(&es.len());
        if c != Ordering::Equal {
            return Some(c);
        }
        for (x, y) in kt.iter().zip(es) {
            let c = match (x, y) {
                (Value::Int(a), Value::Int(b)) => a.cmp(b),
                (Value::Str(a), Value::Str(b)) => a.cmp(b),
                (Value::Bool(a), Value::Bool(b)) => a.cmp(b),
                _ => return None,
            };
            if c != Ordering::Equal {
                return Some(c);
            }
        }
        Some(Ordering::Equal)
    };
    let i = if Witness::Enumerated.schedule(pairs.len()) == Schedule::Scan {
        let mut found = None;
        for (i, (k, _)) in pairs.iter().enumerate() {
            if cmp(k)? == Ordering::Equal {
                found = Some(i);
                break;
            }
        }
        found?
    } else {
        let (mut lo, mut hi) = (0usize, pairs.len());
        loop {
            if lo >= hi {
                return None;
            }
            let mid = lo + (hi - lo) / 2;
            match cmp(&pairs[mid].0)? {
                Ordering::Equal => break mid,
                Ordering::Less => lo = mid + 1,
                Ordering::Greater => hi = mid,
            }
        }
    };
    Some(&pairs[i].1)
}

/// `DOMAIN f`
pub fn domain(f: &Value) -> Result<Value> {
    match f {
        Value::Tuple(t) => Ok(Value::Interval(1, t.len() as i64)),
        Value::Record(r) => Ok(Value::Set(r.iter().map(|(k, _)| Value::Str(*k)).collect())),
        Value::Fcn(p, dom) => {
            let w = match dom {
                FcnDom::Interval => Witness::Interval,
                FcnDom::Enumerated => Witness::Enumerated,
            };
            Ok(w.domain_value(p.iter().map(|(k, _)| k)))
        }
        Value::LazyFcn(l) => l.domain(),
        _ => err(format!("Attempted to compute DOMAIN of a non-function ({}):\n{f}", kind_name(f))),
    }
}

/// `r.field`
pub fn field(r: &Value, field: Sym) -> Result<Value> {
    match field_ref(r, field)? {
        Some(v) => Ok(v.clone()),
        None => apply(r, &Value::Str(field)),
    }
}

/// `r.field` borrowed from `r`, with `field`'s errors; `None` for a lazy
/// function (use `field`).
pub fn field_ref(r: &Value, field: Sym) -> Result<Option<&Value>> {
    match r {
        Value::Record(fields) => match record_index(fields, field) {
            Some(i) => Ok(Some(&fields[i].1)),
            None => err(format!("Attempted to access nonexistent field '{}' of record\n{r}", field.as_str())),
        },
        _ => apply_ref(r, &Value::Str(field)),
    }
}

/// A lazy function with one point overridden (`[f EXCEPT ![k] = v]` on a
/// `LazyFcn`, kept lazy like TLC's `FcnLambdaValue` excepts).
#[derive(Debug)]
struct ExceptFcn {
    base: Arc<dyn LazyFcn>,
    key: Value,
    val: Value,
}

impl LazyFcn for ExceptFcn {
    fn apply(&self, arg: &Value) -> Result<Value> {
        if eq_tlc(arg, &self.key)? {
            Ok(self.val.clone())
        } else {
            self.base.apply(arg)
        }
    }
    fn domain(&self) -> Result<Value> {
        self.base.domain()
    }
    fn kept_lazy(&self) -> bool {
        self.base.kept_lazy()
    }
}

/// `[f EXCEPT ![k] = v]` for a single key (the key must be in the domain).
///
/// Deviation from TLC: TLC's evaluator only warns and returns `f` unchanged
/// when `k` is not in the domain; here that is an error. Use `select` first
/// to reproduce TLC's behavior exactly.
pub fn except(f: &Value, key: &Value, v: Value) -> Result<Value> {
    let not_in_domain =
        || err(format!("Attempted to apply EXCEPT to the function\n{f}\nwith argument {key}, which is not in the domain of the function."));
    match f {
        Value::Tuple(t) => match key {
            Value::Int(i) if *i >= 1 && *i <= t.len() as i64 => {
                let mut elems = t.to_vec();
                elems[*i as usize - 1] = v;
                Ok(Value::Tuple(Arc::from(elems)))
            }
            Value::Int(_) => not_in_domain(),
            _ => err(format!("Attempted to access tuple at a non integral index: {key}")),
        },
        Value::Record(r) => match key {
            Value::Str(s) => match record_index(r, *s) {
                Some(i) => {
                    let mut fields = r.to_vec();
                    fields[i].1 = v;
                    Ok(Value::Record(Arc::from(fields)))
                }
                None => not_in_domain(),
            },
            _ => err(format!("Attempted to access record by a non-string argument: {key}")),
        },
        Value::Fcn(p, d) => match fcn_index(p, *d, key)? {
            Some(i) => {
                let mut pairs = p.to_vec();
                pairs[i].1 = v;
                Ok(Value::Fcn(Arc::from(pairs), *d))
            }
            None => not_in_domain(),
        },
        Value::LazyFcn(l) => {
            if !member(key, &l.domain()?)? {
                return not_in_domain();
            }
            Ok(Value::LazyFcn(Arc::new(ExceptFcn { base: l.clone(), key: key.clone(), val: v })))
        }
        _ => err(format!("Attempted to apply EXCEPT to a non-function value:\n{f}")),
    }
}

/// `d :> e` (TLC: an FcnRcdValue over the enumerated domain `{d}`)
pub fn single_fcn(d: Value, e: Value) -> Result<Value> {
    Value::fcn_rcd_from_pairs(vec![(d, e)])
}

/// Whether `k` is one of the sorted keys `keys` (search schedule of an
/// enumerated domain, `plan::Witness::schedule`). The comparison takes `k`
/// first (`plan::Direction::Probe`), which matters for the error messages
/// of incomparable values.
fn contains_key(keys: &[Value], k: &Value) -> Result<bool> {
    let direction = Direction::Probe;
    if Witness::Enumerated.schedule(keys.len()) == Schedule::Scan {
        for fk in keys {
            let (a, b) = direction.operands(fk, k);
            if eq_tlc(a, b)? {
                return Ok(true);
            }
        }
        return Ok(false);
    }
    let (mut lo, mut hi) = (0usize, keys.len());
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        let (a, b) = direction.operands(&keys[mid], k);
        match cmp_tlc(a, b)? {
            Ordering::Equal => return Ok(true),
            Ordering::Less => hi = mid,
            Ordering::Greater => lo = mid + 1,
        }
    }
    Ok(false)
}

/// `f @@ g` (TLC `combineFcn`: an FcnRcdValue over the enumerated union of
/// the domains, also for two tuples or records)
pub fn fcn_merge(f: &Value, g: &Value) -> Result<Value> {
    Ok(fcn_merge_canonical(f, g)?.into_fcn_rcd())
}

fn fcn_merge_canonical(f: &Value, g: &Value) -> Result<Value> {
    let (mut sf, mut sg) = (None, None);
    let fv = force_fcn(f, &mut sf)?;
    let gv = force_fcn(g, &mut sg)?;
    let Some(fr) = FcnRef::of(fv) else {
        return err(format!("The first argument of @@ should be a function, but instead it is:\n{f}"));
    };
    let Some(gr) = FcnRef::of(gv) else {
        return err(format!("The second argument of @@ should be a function, but instead it is:\n{g}"));
    };
    if fr.len() == 0 && gr.len() == 0 {
        // TLC builds an FcnRcdValue (TLC.combineFcn).
        return Ok(Value::empty_fcn());
    }
    match (fv, gv) {
        (Value::Tuple(a), Value::Tuple(b)) => {
            if b.len() <= a.len() {
                return Ok(fv.clone());
            }
            let mut elems = a.to_vec();
            elems.extend(b[a.len()..].iter().cloned());
            return Ok(Value::Tuple(Arc::from(elems)));
        }
        (Value::Record(_), Value::Record(b)) => {
            let mut fields = b.to_vec();
            if let Value::Record(a) = fv {
                fields.extend(a.iter().cloned()); // f's fields come last: they win
            }
            return Ok(Value::record(fields));
        }
        _ => {}
    }
    let fkeys: Vec<Value> = (0..fr.len()).map(|i| fr.key(i).into_owned()).collect();
    let mut pairs: Vec<(Value, Value)> = fkeys.iter().cloned().zip((0..fr.len()).map(|i| fr.val(i).clone())).collect();
    for j in 0..gr.len() {
        let k = gr.key(j);
        if !contains_key(&fkeys, &k)? {
            pairs.push((k.into_owned(), gr.val(j).clone()));
        }
    }
    Value::fcn_from_pairs(pairs)
}
