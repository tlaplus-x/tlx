//! Native implementations of CommunityModules operators whose TLA+
//! definitions cannot be evaluated directly (they quantify over infinite
//! sets such as `Seq(S)` or `[STRING -> STRING]`), like TLC's Java
//! overrides. Each follows the module's TLA+ definition.
//!
//! The operator families with their own helpers live in child modules
//! (CODE-03): `csv` (`CSVRead`/`CSVWrite`/`CSVWriteRecord`), `graph`
//! (`SimplePath`, `AreConnectedIn`, `IsStronglyConnected`,
//! `ConnectedComponents`) and `process` (`IOExec`/`IOEnvExec` and their
//! templates), next to `json` and `stats`. Their public paths are re-exported
//! here, so the extraction moves no API.

use tlx_value::{ops, order, Sym, Value};

use crate::error::{EResult, EvalError};

mod csv;
mod graph;
pub mod json;
mod process;
pub mod stats;

pub use csv::{csv_read, csv_records, csv_write, csv_write_record};
pub use graph::{are_connected_in, connected_components, is_strongly_connected, simple_path};
pub(crate) use process::PreparedCommand;
pub use process::{io_env_exec, io_env_exec_template, io_exec, io_exec_template};

/// `IOEnv` (IOUtils): the process environment as a record.
pub fn io_env() -> Value {
    let mut fields: Vec<(Sym, Value)> = std::env::vars().map(|(k, v)| (Sym::new(&k), Value::str(&v))).collect();
    fields.sort_by(|a, b| a.0.cmp(&b.0));
    fields.dedup_by(|a, b| a.0 == b.0);
    Value::record(fields)
}

/// `atoi(str)` (IOUtils; the module defines it as `CHOOSE i \in Int :
/// ToString(i) = str`).
pub fn atoi(s: &Value) -> EResult<Value> {
    // IOUtils.java `atoi`: Java's Integer.parseInt (an optional sign, then
    // decimal digits, within 32 bits), else an argument error.
    if let Value::Str(t) = s {
        let t = t.as_str();
        let digits = t.strip_prefix(['+', '-']).unwrap_or(t);
        if !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()) {
            if let Ok(i) = t.parse::<i32>() {
                return Ok(Value::Int(i64::from(i)));
            }
        }
    }
    Err(EvalError::of_kind(
        tlx_runtime::ErrorKind::ArgumentError,
        format!("The argument of atoi should be a string, but instead it is:\n{s}"),
    ))
}

/// `IsInjective(f)` (Functions.java): no two arguments of `f` have equal
/// values. As TLC, a set of records `[a : S, b : T]` (an easy slip for
/// `[a |-> S, b |-> T]`) counts as the function from its fields to their
/// sets (TLC's `SetOfRcdsValue.values`).
pub fn is_injective(f: &Value) -> EResult<Value> {
    let values: Vec<Value> = match f {
        Value::Tuple(_) | Value::Record(_) | Value::Fcn(..) | Value::LazyFcn(_) => {
            let f = crate::eval::force_lazy_fcn(f.clone())?;
            ops::enumerate_normalized(&ops::domain(&f)?)?.iter().map(|x| ops::apply(&f, x)).collect::<tlx_value::Result<_>>()?
        }
        Value::LazySet(s) if matches!(&**s, tlx_value::LazySet::RecordSet(_)) => {
            let tlx_value::LazySet::RecordSet(fields) = &**s else { unreachable!() };
            fields.iter().map(|(_, v)| v.clone()).collect()
        }
        _ => {
            return Err(EvalError::of_kind(
                tlx_runtime::ErrorKind::ArgumentError,
                format!("The argument of IsInjective should be a function, but instead it is:\n{f}"),
            ))
        }
    };
    for (i, x) in values.iter().enumerate() {
        for y in &values[i + 1..] {
            if tlx_value::order::eq_tlc(x, y)? {
                return Ok(Value::FALSE);
            }
        }
    }
    Ok(Value::TRUE)
}

/// `AllSubSeqs(s)` (SequencesExt.java): every subsequence of `s`, each
/// keeping the elements in index order (the TLA+ definition folds a
/// function over `SUBSET DOMAIN s`, whose CHOOSE order can reverse them).
pub fn all_sub_seqs(s: &Value) -> EResult<Value> {
    let s = crate::eval::force_seq(s.clone())?;
    let Value::Tuple(elems) = &s else {
        return Err(EvalError::new(format!("The argument of AllSubSeqs should be a sequence, but instead it is:\n{s}")));
    };
    if elems.len() >= 31 {
        // TLC allocates an int-sized array of 2^n subsequences and fails too.
        return Err(EvalError::new(format!("AllSubSeqs cannot enumerate 2^{} subsequences", elems.len())));
    }
    let mut out = Vec::with_capacity(1usize << elems.len());
    for mask in 0u32..(1u32 << elems.len()) {
        let mut sub = Vec::new();
        for (i, e) in elems.iter().enumerate() {
            if mask & (1 << i) != 0 {
                sub.push(e.clone());
            }
        }
        out.push(Value::tuple(sub));
    }
    Ok(Value::set_from(out)?)
}

/// `choose(n, k)` (Combinatorics.java `chse`): TLC's binomial coefficient
/// over 32-bit integers. The module's definition goes through `factorial` and
/// overflows from 13! on; the Java method computes the coefficient without
/// that intermediate overflow (`choose(20, 10) = 184756`), returns 0 for
/// `k > n`, and reports an overflow error for a result above `i32::MAX`.
///
/// TLC's own arithmetic is defective for large arguments: the Java method
/// wraps in `long` arithmetic (`choose(5287, 459)` returns a spurious 32-bit
/// value) and its `int` Pascal-table index overflows (`choose(50000, 2)`
/// fails with an index error). tlx computes the exact coefficient instead and
/// reports the overflow error as soon as a partial coefficient cannot fit
/// (D-32).
pub fn choose(n: &Value, k: &Value) -> EResult<Value> {
    let n = natural(n, "first")?;
    let k = natural(k, "second")?;
    // `k > n` is 0 in the override (and in TLA+).
    if k > n {
        return Ok(Value::Int(0));
    }
    let top = k;
    let k = k.min(n - k);
    // C(n, k) = prod_{i=1..k} (n - k + i) / i. The partial results are the
    // increasing coefficients C(n - k + i, i), so while one fits 32 bits the
    // product of it and a factor (at most n) fits an i64, and the division is
    // exact.
    let mut result: i32 = 1;
    for i in 1..=k {
        let p = i64::from(result) * i64::from(n - k + i);
        let Ok(q) = i32::try_from(p / i64::from(i)) else {
            // EC 2178, an `EvalException` the override raises itself (not the
            // wrapped method error of `java_override`).
            return Err(EvalError::of_kind(tlx_runtime::ErrorKind::Overflow, format!("Overflow when computing {n}choose{top}")));
        };
        result = q;
    }
    Ok(Value::Int(i64::from(result)))
}

/// Argument `which` of `choose` as TLC's `IntValue.val`: a non-negative
/// 32-bit integer, else EC 2169.
fn natural(v: &Value, which: &str) -> EResult<i32> {
    if let Value::Int(i) = v {
        if let Ok(i) = i32::try_from(*i) {
            if i >= 0 {
                return Ok(i);
            }
        }
    }
    Err(EvalError::of_kind(
        tlx_runtime::ErrorKind::ArgumentError,
        format!("The {which} argument of choose should be a natural number, but instead it is:\n{v}"),
    ))
}

/// `ReplaceAllSubSeqs(r, s, t)` (SequencesExt.java `replaceAllSubSeq`): TLC's
/// Java override handles three strings itself (`StringUtils.replace`; an empty
/// `s` interleaves `r` before every character). Every other call evaluates the
/// module definition, whose ordered guards are reproduced here: `s = t`
/// returns `r`, `r = s` returns `t`, an empty `s` interleaves `r` before every
/// element of `t`, and otherwise `s` is searched in `t` and its leftmost
/// non-overlapping occurrences are replaced (the definition's partition with
/// the maximum number of leftmost matches). The definition's membership test
/// compares `s` with overlapping windows of `t` too, so its comparison errors
/// are observable; the implementation compares every window.
pub fn replace_all_sub_seqs(r: &Value, s: &Value, t: &Value) -> EResult<Value> {
    // TLC's `@Evaluation` override matches three strings on the values it is
    // given, and the definition's two identity guards compare the values
    // without reading a function's entries: return `r` or `t` unchanged.
    // Coercing them to sequences here would evaluate entries the caller never
    // reads (and can make an unreachable entry's error observable).
    if let (Value::Str(r), Value::Str(s), Value::Str(t)) = (r, s, t) {
        return Ok(Value::Str(replace_all_str(r, s, t)));
    }
    if order::eq_tlc(s, t)? {
        return Ok(r.clone());
    }
    if order::eq_tlc(r, s)? {
        return Ok(t.clone());
    }
    // `Len(s) = 0`: the interleaving consumes both `r` and `t` as sequences,
    // so force them only in this branch.
    if ops::len(s)? == 0 {
        let rf = crate::eval::force_seq(r.clone())?;
        let tf = crate::eval::force_seq(t.clone())?;
        if let (Value::Tuple(r), Value::Tuple(t)) = (&rf, &tf) {
            return Ok(Value::tuple(interleave_seq(r, t)));
        }
        return Err(definition_error(r, s, t));
    }
    // `Len(s) > 0 && s \in SubSeqs(t)`: the definition's sequence view.
    let sf = crate::eval::force_seq(s.clone())?;
    let tf = crate::eval::force_seq(t.clone())?;
    let (Value::Tuple(sv), Value::Tuple(tv)) = (&sf, &tf) else {
        return Err(definition_error(r, s, t));
    };
    if !subseqs_contains(sv, tv)? {
        // `OTHER -> t`, the original value (not the sequence view).
        return Ok(t.clone());
    }
    partition_comparable(tv)?;
    let rf = crate::eval::force_seq(r.clone())?;
    let Value::Tuple(rv) = &rf else {
        // The partition branch concatenates `r` with `\o`, so it must be a
        // sequence (a match exists, so `r` is always inserted).
        return Err(definition_error(r, s, t));
    };
    Ok(Value::tuple(greedy_replace(rv, sv, tv)?))
}

/// The error of a module definition whose comparison or concatenation tlx
/// cannot perform (TLC reports its own evaluation error at that point).
fn definition_error(r: &Value, s: &Value, t: &Value) -> EvalError {
    EvalError::of_kind(
        tlx_runtime::ErrorKind::General,
        format!("ReplaceAllSubSeqs: the arguments of the definition are not all sequences:\n{r}\n{s}\n{t}"),
    )
}

/// The definition's `s \in SubSeqs(t)` for a non-empty `s`: TLC's equality
/// compares lengths first, so only windows of `Len(s)` can be equal. Every
/// window is compared (the definition's later partition branch compares `t`
/// with every sequence over `Range(t)`), so a comparison error is observable
/// even when an earlier window already matched.
fn subseqs_contains(s: &[Value], t: &[Value]) -> EResult<bool> {
    if s.len() > t.len() {
        return Ok(false);
    }
    let mut found = false;
    for i in 0..=t.len() - s.len() {
        let mut same = true;
        for (x, y) in s.iter().zip(&t[i..i + s.len()]) {
            if !order::eq_tlc(x, y)? {
                same = false;
                break;
            }
        }
        found |= same;
    }
    Ok(found)
}

/// The definition's partition branch builds
/// `{f \in BoundedSeq(BoundedSeq(Range(t), Len(t)), Len(t)) : FlattenSeq(f) = t}`,
/// which compares `t` with every sequence over `Range(t)`. Two elements of
/// `t` that are not comparable make one of those comparisons error (put one
/// where the other belongs after the common prefix), so the branch is an
/// error exactly when `t` has such a pair.
fn partition_comparable(t: &[Value]) -> EResult<()> {
    let homogeneous = |f: fn(&Value) -> bool| t.iter().all(f);
    // A homogeneous atomic sequence is always comparable.
    if homogeneous(|v| matches!(v, Value::Int(_)))
        || homogeneous(|v| matches!(v, Value::Str(_)))
        || homogeneous(|v| matches!(v, Value::Bool(_)))
    {
        return Ok(());
    }
    for (i, x) in t.iter().enumerate() {
        for y in &t[i + 1..] {
            order::eq_tlc(x, y)?;
        }
    }
    Ok(())
}

/// The definition's partition result: the leftmost non-overlapping
/// occurrences of `s` in `t` replaced by `r` (`s` occurs in `t`).
fn greedy_replace(r: &[Value], s: &[Value], t: &[Value]) -> EResult<Vec<Value>> {
    let mut out = Vec::with_capacity(t.len() + r.len());
    let (mut i, mut done) = (0, 0);
    while i + s.len() <= t.len() {
        let mut matched = true;
        for (x, y) in t[i..i + s.len()].iter().zip(s) {
            if !order::eq_tlc(x, y)? {
                matched = false;
                break;
            }
        }
        if matched {
            out.extend_from_slice(&t[done..i]);
            out.extend_from_slice(r);
            i += s.len();
            done = i;
        } else {
            i += 1;
        }
    }
    out.extend_from_slice(&t[done..]);
    Ok(out)
}

/// `r` interleaved before every element of `t` (the empty-`s` branch:
/// `FlattenSeq(FlattenSeq(Interleave(...)))`).
fn interleave_seq(r: &[Value], t: &[Value]) -> Vec<Value> {
    let mut out = Vec::with_capacity(r.len() * (t.len() + 1) + t.len());
    out.extend_from_slice(r);
    for (i, x) in t.iter().enumerate() {
        if i != 0 {
            out.extend_from_slice(r);
        }
        out.push(x.clone());
    }
    out
}

/// `StringUtils.replace(t, s, r)`, or with an empty `s` the interleaving of
/// `r` before every character of `t` (TLC's `replaceAllSubSeq`).
fn replace_all_str(r: &Sym, s: &Sym, t: &Sym) -> Sym {
    let (r, s, t) = (r.as_str(), s.as_str(), t.as_str());
    let mut out = String::with_capacity(t.len() + r.len());
    if s.is_empty() {
        out.push_str(r);
        for (i, c) in t.chars().enumerate() {
            if i != 0 {
                out.push_str(r);
            }
            out.push(c);
        }
        return Sym::new(&out);
    }
    let mut end = 0;
    while let Some(pos) = t[end..].find(s) {
        out.push_str(&t[end..end + pos]);
        out.push_str(r);
        end += pos + s.len();
    }
    out.push_str(&t[end..]);
    Sym::new(&out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn seq(xs: &[i64]) -> Value {
        Value::tuple(xs.iter().map(|x| Value::Int(*x)).collect())
    }

    fn mixed(xs: &[Value]) -> Value {
        Value::tuple(xs.to_vec())
    }

    /// `choose(n, k)` printed, or the error message.
    fn choose_of(n: i64, k: i64) -> String {
        match choose(&Value::Int(n), &Value::Int(k)) {
            Ok(v) => v.to_string(),
            Err(e) => format!("ERROR: {e}"),
        }
    }

    /// `ReplaceAllSubSeqs(r, s, t)` printed, or the error message.
    fn replace_of(r: Value, s: Value, t: Value) -> String {
        match replace_all_sub_seqs(&r, &s, &t) {
            Ok(v) => v.to_string(),
            Err(e) => format!("ERROR: {e}"),
        }
    }

    #[test]
    fn choose_matches_tlc_binomial() {
        // TLC's Java override: no intermediate factorial overflow.
        assert_eq!(choose_of(20, 10), "184756");
        assert_eq!(choose_of(30, 15), "155117520");
        assert_eq!(choose_of(33, 16), "1166803110");
        // Exact where TLC's `int` Pascal-table index overflows (D-32).
        assert_eq!(choose_of(50000, 2), "1249975000");
        // The boundary cases, in TLC's order (and TLA+'s values).
        assert_eq!(choose_of(0, 0), "1");
        assert_eq!(choose_of(5, 0), "1");
        assert_eq!(choose_of(5, 5), "1");
        assert_eq!(choose_of(5, 1), "5");
        assert_eq!(choose_of(5, 4), "5");
        assert_eq!(choose_of(0, 1), "0");
        assert_eq!(choose_of(1, 2), "0");
        assert_eq!(choose_of(5, 6), "0");
    }

    #[test]
    fn choose_reports_tlc_errors() {
        assert_eq!(choose_of(34, 17), "ERROR: Overflow when computing 34choose17");
        assert_eq!(choose_of(34, 16), "ERROR: Overflow when computing 34choose16");
        assert_eq!(choose_of(62, 31), "ERROR: Overflow when computing 62choose31");
        // The exact coefficient has 2,246 bits; TLC's wrapped `long`
        // arithmetic returns a spurious 32-bit value (D-32).
        assert_eq!(choose_of(5287, 459), "ERROR: Overflow when computing 5287choose459");
        assert_eq!(choose_of(-1, 0), "ERROR: The first argument of choose should be a natural number, but instead it is:\n-1");
        assert_eq!(choose_of(5, -1), "ERROR: The second argument of choose should be a natural number, but instead it is:\n-1");
    }

    #[test]
    fn replace_all_sub_seqs_identity_guards() {
        // `s = t -> r` and `r = s -> t` precede the search (the two oracle
        // cases of the review).
        assert_eq!(replace_of(Value::str("hit"), seq(&[1]), seq(&[1])), "\"hit\"");
        assert_eq!(replace_of(mixed(&[Value::str("A")]), mixed(&[Value::str("A")]), seq(&[1, 2])), "<<1, 2>>");
        // The same guards' comparison errors are preserved.
        assert_eq!(
            replace_of(mixed(&[Value::str("A")]), seq(&[1]), seq(&[1, 1])),
            "ERROR: Attempted to check equality of string \"A\" with non-string:\n1"
        );
        assert_eq!(
            replace_of(seq(&[1]), seq(&[1]), Value::Int(5)),
            "ERROR: Attempted to check equality of the function <<1>> with the value:\n5"
        );
    }

    #[test]
    fn replace_all_sub_seqs_compares_every_window() {
        // The definition's `s \in SubSeqs(t)` compares overlapping windows
        // too: here the match at index 0 does not hide the comparison of 1
        // with "a" at index 1 (the reviewer's fourth case).
        assert_eq!(
            replace_of(
                seq(&[0]),
                mixed(&[Value::Int(1), Value::str("a")]),
                mixed(&[Value::Int(1), Value::str("a"), Value::Int(1), Value::str("a")])
            ),
            "ERROR: Attempted to check equality of integer 1 with non-integer:\n\"a\""
        );
        // All occurrences are replaced leftmost without overlap.
        assert_eq!(replace_of(seq(&[0]), seq(&[1]), seq(&[1, 2, 1])), "<<0, 2, 0>>");
        // The partition branch compares `t` with every sequence over
        // `Range(t)`: heterogeneous compound elements are an error even
        // though every membership window is comparable with `s`.
        assert_eq!(
            replace_of(
                mixed(&[mixed(&[Value::Int(1), Value::str("b")])]),
                mixed(&[mixed(&[Value::Int(1), Value::str("a")])]),
                mixed(&[
                    mixed(&[Value::Int(1), Value::str("a")]),
                    mixed(&[Value::Int(2), Value::str("x")]),
                    mixed(&[Value::Int(2), Value::Int(3)]),
                ])
            ),
            "ERROR: Attempted to check equality of string \"x\" with non-string:\n3"
        );
    }

    #[test]
    fn replace_all_sub_seqs_prefixed_overlap() {
        // The definition breaks ties on *chunk* positions, so a merged prefix
        // can make a later input occurrence tie with the earlier one and
        // CHOOSE replaces the later one in TLC (D-34); tlx replaces the
        // leftmost occurrence, as the module comment promises.
        assert_eq!(replace_of(seq(&[0]), seq(&[1, 1]), seq(&[0, 1, 1, 1])), "<<0, 0, 1>>");
    }

    #[test]
    fn replace_all_sub_seqs_strings() {
        assert_eq!(replace_of(Value::str("x"), Value::str("a"), Value::str("banana")), "\"bxnxnx\"");
        assert_eq!(replace_of(Value::str("x"), Value::str("q"), Value::str("ab")), "\"ab\"");
        assert_eq!(replace_of(Value::str("x"), Value::str("aa"), Value::str("aaa")), "\"xa\"");
        assert_eq!(replace_of(Value::str("aa"), Value::str("a"), Value::str("aaa")), "\"aaaaaa\"");
        assert_eq!(replace_of(Value::str("ba"), Value::str("a"), Value::str("aaa")), "\"bababa\"");
        assert_eq!(replace_of(Value::str("x"), Value::str("ab"), Value::str("abab")), "\"xx\"");
        // An empty search string interleaves the replacement (TLC's override).
        assert_eq!(replace_of(Value::str("x"), Value::str(""), Value::str("ab")), "\"xaxb\"");
        assert_eq!(replace_of(Value::str("x"), Value::str(""), Value::str("")), "\"x\"");
        assert_eq!(replace_of(Value::str(""), Value::str(""), Value::str("a")), "\"a\"");
        // Unicode scalar values are not split; TLC splits the surrogate pair
        // and prints "x?x?" (D-33).
        assert_eq!(replace_of(Value::str("x"), Value::str(""), Value::str("\u{1F600}")), "\"x\u{1F600}\"");
    }

    #[test]
    fn replace_all_sub_seqs_sequences() {
        assert_eq!(replace_of(seq(&[2]), seq(&[1]), seq(&[1, 1])), "<<2, 2>>");
        assert_eq!(replace_of(seq(&[2, 2]), seq(&[1, 1]), seq(&[1, 1, 1])), "<<2, 2, 1>>");
        assert_eq!(replace_of(seq(&[2]), seq(&[1]), seq(&[1, 2])), "<<2, 2>>");
        assert_eq!(replace_of(seq(&[2]), seq(&[3]), seq(&[1, 3])), "<<1, 2>>");
        assert_eq!(replace_of(seq(&[1]), seq(&[2]), seq(&[3, 4])), "<<3, 4>>");
        assert_eq!(replace_of(seq(&[1]), seq(&[1, 1]), seq(&[1])), "<<1>>");
        assert_eq!(replace_of(seq(&[5]), seq(&[1, 2]), seq(&[1, 2])), "<<5>>");
        // An empty search string interleaves the replacement, before every
        // element and before the end (the module's FlattenSeq(FlattenSeq(...))).
        assert_eq!(replace_of(seq(&[2]), seq(&[]), seq(&[1, 3])), "<<2, 1, 2, 3>>");
        assert_eq!(replace_of(seq(&[1, 2]), seq(&[]), seq(&[3, 4])), "<<1, 2, 3, 1, 2, 4>>");
        assert_eq!(replace_of(seq(&[4]), seq(&[]), seq(&[])), "<<4>>");
        assert_eq!(replace_of(seq(&[]), seq(&[]), seq(&[3])), "<<3>>");
    }
}
