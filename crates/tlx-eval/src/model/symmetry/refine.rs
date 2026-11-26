//! Partition-refinement fast paths (Rules 1-3) and branch-and-bound
//! lex-leader search (Case A keyed functions & Case B general recursive values).

use std::cmp::Ordering;

use tlx_base::partition::Partition;
use tlx_value::order::{self_comparison_is_inert, try_total_cmp};
use tlx_value::{Sym, Value};

use crate::error::EResult;

use super::factor::FactorizedGroup;
use super::{cmp_images_mode, cmp_images_with_mode, CmpMode, ImageOrder, PermMap};

/// Scratch buffers reused across deterministic refinement steps.
#[derive(Default)]
pub(super) struct RefineScratch {
    pub(super) in_set: Vec<bool>,
    pub(super) payload_idx: Vec<Option<usize>>,
    pub(super) sort_scratch: Vec<u16>,
    pub(super) img_buf: Vec<u16>,
}

/// Scratch buffers reused across factorized canonicalization calls.
#[derive(Default)]
pub(super) struct FactorScratch {
    pub(super) part: Partition,
    pub(super) refine: RefineScratch,
}

/// Outcome of attempting zero-branching deterministic refinement on `v`.
pub(super) enum DetOutcome<'a> {
    /// `v` was fully refined in place (or had no unpinned atoms).
    Done,
    /// `v` (or a component inside a `Tuple`/`Record` chain) needs branching;
    /// `pending` lists the remaining sub-values of `v` in lex order.
    NeedBranch(Vec<&'a Value>),
}

/// Whether `v` contains any model value moved by `fg` (or a lazy value that
/// may contain one).
pub(super) fn has_any_moved_atom(v: &Value, fg: &FactorizedGroup) -> bool {
    match v {
        Value::ModelValue(m) => fg.lookup(*m).is_some(),
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => false,
        Value::Set(es) | Value::Tuple(es) => es.iter().any(|e| has_any_moved_atom(e, fg)),
        Value::Record(fs) => fs.iter().any(|(_, e)| has_any_moved_atom(e, fg)),
        Value::Fcn(ps, _) => ps.iter().any(|(k, e)| has_any_moved_atom(k, fg) || has_any_moved_atom(e, fg)),
        Value::LazySet(_) | Value::LazyFcn(_) => true,
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum CmpKind {
    Bool,
    Int,
    Str,
    TypedMv(char),
    Set,
    Tuple,
    Record,
    Fcn,
}

#[inline]
fn scalar_cmp_kind(v: &Value) -> Option<Option<CmpKind>> {
    match v {
        Value::Bool(_) => Some(Some(CmpKind::Bool)),
        Value::Int(_) => Some(Some(CmpKind::Int)),
        Value::Str(_) => Some(Some(CmpKind::Str)),
        Value::ModelValue(m) => Some(m.model_value_type().map(CmpKind::TypedMv)),
        _ => None,
    }
}

/// Fast zero-allocation compatibility check for slices of values (most TLA+
/// sets and functions have scalar keys/payloads); falls back to recursive
/// structural compatibility when structured values appear.
fn iter_orbit_cmp_compatible<'a>(mut iter: impl Iterator<Item = &'a Value> + Clone, fg: &FactorizedGroup) -> bool {
    let mut scalar_kind: Option<CmpKind> = None;
    let mut has_structured = false;
    for v in iter.clone() {
        match scalar_cmp_kind(v) {
            Some(None) => {}
            Some(Some(k)) => {
                if let Some(prev) = scalar_kind {
                    if prev != k {
                        return false;
                    }
                } else {
                    scalar_kind = Some(k);
                }
            }
            None => {
                if scalar_kind.is_some() {
                    return false;
                }
                has_structured = true;
                break;
            }
        }
    }
    if !has_structured {
        return true;
    }
    let vals: Vec<&Value> = iter.by_ref().collect();
    values_orbit_cmp_compatible(&vals, fg)
}

/// Check column-by-column compatibility of fixed-arity items (same-length
/// `Tuple`s or same-field `Record`s), partitioning each cohort by any
/// moved-atom-free column so tagged variants (e.g. `<<0, FALSE>>` vs
/// `<<1, 42>>`) do not force cross-variant tail checks.
fn cohorts_columns_orbit_cmp_compatible<'a, T: Copy>(
    initial: Vec<Vec<T>>,
    ncols: usize,
    fg: &FactorizedGroup,
    col_of: impl Fn(T, usize) -> &'a Value,
) -> bool {
    let mut cohorts = initial;
    let mut col_vals: Vec<&Value> = Vec::new();
    for col in 0..ncols {
        let mut next: Vec<Vec<T>> = Vec::new();
        for cohort in cohorts {
            if cohort.len() < 2 {
                continue;
            }
            col_vals.clear();
            col_vals.extend(cohort.iter().map(|&item| col_of(item, col)));
            if !values_orbit_cmp_compatible(&col_vals, fg) {
                return false;
            }
            if col + 1 == ncols {
                continue;
            }
            if col_vals.iter().all(|v| !has_any_moved_atom(v, fg)) {
                let mut groups: Vec<(&Value, Vec<T>)> = Vec::new();
                for (item, &cv) in cohort.into_iter().zip(col_vals.iter()) {
                    if let Some((_, g)) = groups.iter_mut().find(|(rep, _)| tlx_value::order::eq_tlc(cv, rep).ok() == Some(true)) {
                        g.push(item);
                    } else {
                        groups.push((cv, vec![item]));
                    }
                }
                for (_, g) in groups {
                    if g.len() >= 2 {
                        next.push(g);
                    }
                }
            } else {
                next.push(cohort);
            }
        }
        if next.is_empty() {
            return true;
        }
        cohorts = next;
    }
    true
}

/// Whether `cmp_tlc(p(a), q(b))` is guaranteed to succeed for all `a, b` in
/// `vals` and all permutations `p, q` preserving model-value types.
fn values_orbit_cmp_compatible(vals: &[&Value], fg: &FactorizedGroup) -> bool {
    let mut kind: Option<CmpKind> = None;
    for &v in vals {
        let vk = match v {
            Value::Bool(_) => CmpKind::Bool,
            Value::Int(_) => CmpKind::Int,
            Value::Str(_) => CmpKind::Str,
            Value::ModelValue(m) => match m.model_value_type() {
                Some(t) => CmpKind::TypedMv(t),
                None => continue,
            },
            Value::Interval(..) => {
                if !self_comparison_is_inert(v) {
                    return false;
                }
                CmpKind::Set
            }
            Value::Set(_) => CmpKind::Set,
            Value::Tuple(_) => CmpKind::Tuple,
            Value::Record(_) => CmpKind::Record,
            Value::Fcn(..) => CmpKind::Fcn,
            Value::LazySet(_) | Value::LazyFcn(_) => return false,
        };
        if let Some(prev) = kind {
            if prev != vk {
                return false;
            }
        } else {
            kind = Some(vk);
        }
    }
    match kind {
        None | Some(CmpKind::Bool | CmpKind::Int | CmpKind::Str | CmpKind::TypedMv(_)) => true,
        Some(CmpKind::Set) => {
            static INT_REP: Value = Value::Int(0);
            let mut elems: Vec<&Value> = Vec::new();
            for &v in vals {
                match v {
                    Value::Set(es) => elems.extend(es.iter()),
                    Value::Interval(lo, hi) if lo <= hi => elems.push(&INT_REP),
                    _ => {}
                }
            }
            elems.len() <= 1 || values_orbit_cmp_compatible(&elems, fg)
        }
        Some(CmpKind::Tuple) => {
            let mut by_len: Vec<(usize, Vec<&[Value]>)> = Vec::new();
            for &v in vals {
                if let Value::Tuple(es) = v {
                    if es.is_empty() {
                        continue;
                    }
                    if let Some((_, g)) = by_len.iter_mut().find(|(len, _)| *len == es.len()) {
                        g.push(es);
                    } else {
                        by_len.push((es.len(), vec![es]));
                    }
                }
            }
            by_len.into_iter().all(|(len, g)| g.len() < 2 || cohorts_columns_orbit_cmp_compatible(vec![g], len, fg, |es, col| &es[col]))
        }
        Some(CmpKind::Record) => {
            let mut groups: Vec<Vec<&[(Sym, Value)]>> = Vec::new();
            for &v in vals {
                if let Value::Record(fs) = v {
                    if let Some(g) =
                        groups.iter_mut().find(|g| g[0].len() == fs.len() && g[0].iter().zip(fs.iter()).all(|((a, _), (b, _))| a == b))
                    {
                        g.push(fs);
                    } else {
                        groups.push(vec![fs]);
                    }
                }
            }
            groups.into_iter().all(|g| {
                let ncols = g[0].len();
                g.len() < 2 || cohorts_columns_orbit_cmp_compatible(vec![g], ncols, fg, |fs, col| &fs[col].1)
            })
        }
        Some(CmpKind::Fcn) => {
            let mut by_len: Vec<(usize, Vec<&[(Value, Value)]>)> = Vec::new();
            for &v in vals {
                if let Value::Fcn(ps, _) = v {
                    if ps.is_empty() {
                        continue;
                    }
                    if let Some((_, g)) = by_len.iter_mut().find(|(len, _)| *len == ps.len()) {
                        g.push(ps);
                    } else {
                        by_len.push((ps.len(), vec![ps]));
                    }
                }
            }
            let mut keys: Vec<&Value> = Vec::new();
            let mut payloads: Vec<&Value> = Vec::new();
            for (len, fcns) in by_len {
                if fcns.len() < 2 {
                    continue;
                }
                keys.clear();
                for ps in &fcns {
                    keys.extend(ps.iter().map(|(k, _)| k));
                }
                if !values_orbit_cmp_compatible(&keys, fg) {
                    return false;
                }
                // When every function of this length has a fixed (moved-atom-free)
                // domain, `fcn_cmp` compares domains first and only compares
                // payloads at corresponding keys for equal domains (just like
                // records), so e.g. `(enabled :> Bool) @@ (epoch :> Int)` is safe.
                if keys.iter().all(|k| !has_any_moved_atom(k, fg)) {
                    let mut dom_groups: Vec<Vec<&[(Value, Value)]>> = Vec::new();
                    for ps in fcns {
                        if let Some(g) = dom_groups.iter_mut().find(|g| {
                            g[0].iter().zip(ps.iter()).all(|((k1, _), (k2, _))| tlx_value::order::eq_tlc(k1, k2).ok() == Some(true))
                        }) {
                            g.push(ps);
                        } else {
                            dom_groups.push(vec![ps]);
                        }
                    }
                    for g in dom_groups {
                        if g.len() >= 2 && !cohorts_columns_orbit_cmp_compatible(vec![g], len, fg, |ps, col| &ps[col].1) {
                            return false;
                        }
                    }
                } else {
                    payloads.clear();
                    for ps in &fcns {
                        payloads.extend(ps.iter().map(|(_, val)| val));
                    }
                    if !values_orbit_cmp_compatible(&payloads, fg) {
                        return false;
                    }
                }
            }
            true
        }
    }
}

/// Whether `cmp_tlc(p(v), q(v))` is guaranteed to succeed (never raise an
/// incomparable-value error) for every pair of permutations `p, q` in `fg`.
pub(super) fn is_orbit_cmp_safe(v: &Value, fg: &FactorizedGroup) -> bool {
    match v {
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::ModelValue(_) => true,
        Value::Interval(..) => self_comparison_is_inert(v),
        Value::LazySet(_) | Value::LazyFcn(_) => false,
        Value::Tuple(es) => es.iter().all(|e| is_orbit_cmp_safe(e, fg)),
        Value::Record(fs) => fs.iter().all(|(_, e)| is_orbit_cmp_safe(e, fg)),
        Value::Set(es) => {
            if es.is_empty() {
                return true;
            }
            if !has_any_moved_atom(v, fg) {
                return self_comparison_is_inert(v);
            }
            es.iter().all(|e| is_orbit_cmp_safe(e, fg)) && iter_orbit_cmp_compatible(es.iter(), fg)
        }
        Value::Fcn(ps, _) => {
            if ps.is_empty() {
                return true;
            }
            if !has_any_moved_atom(v, fg) {
                return self_comparison_is_inert(v);
            }
            if !ps.iter().any(|(k, _)| has_any_moved_atom(k, fg)) {
                return ps.iter().all(|(k, val)| self_comparison_is_inert(k) && is_orbit_cmp_safe(val, fg));
            }
            ps.iter().all(|(k, val)| is_orbit_cmp_safe(k, fg) && is_orbit_cmp_safe(val, fg))
                && iter_orbit_cmp_compatible(ps.iter().map(|(k, _)| k), fg)
                && iter_orbit_cmp_compatible(ps.iter().map(|(_, val)| val), fg)
        }
    }
}

/// Whether `v` contains any moved model value that is currently unpinned in
/// `part` (or a lazy value that may contain one).
fn has_unpinned_atom(v: &Value, fg: &FactorizedGroup, part: &Partition) -> bool {
    match v {
        Value::ModelValue(m) => fg.lookup(*m).is_some_and(|(g, k)| !part.is_pinned(fg, g, k)),
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => false,
        Value::Set(es) | Value::Tuple(es) => es.iter().any(|e| has_unpinned_atom(e, fg, part)),
        Value::Record(fs) => fs.iter().any(|(_, e)| has_unpinned_atom(e, fg, part)),
        Value::Fcn(ps, _) => ps.iter().any(|(k, e)| has_unpinned_atom(k, fg, part) || has_unpinned_atom(e, fg, part)),
        Value::LazySet(_) | Value::LazyFcn(_) => !part.is_complete(),
    }
}

/// Collect all distinct unpinned `(factor_idx, key_idx)` occurring in `v`
/// (or all unpinned atoms of `part` when `v` contains a lazy value).
fn collect_unpinned_atoms(v: &Value, fg: &FactorizedGroup, part: &Partition, out: &mut Vec<(usize, usize)>) {
    fn walk(v: &Value, fg: &FactorizedGroup, part: &Partition, out: &mut Vec<(usize, usize)>) -> bool {
        match v {
            Value::ModelValue(m) => {
                if let Some((g, k)) = fg.lookup(*m) {
                    if !part.is_pinned(fg, g, k) && !out.contains(&(g, k)) {
                        out.push((g, k));
                    }
                }
                false
            }
            Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => false,
            Value::Set(es) | Value::Tuple(es) => es.iter().any(|e| walk(e, fg, part, out)),
            Value::Record(fs) => fs.iter().any(|(_, e)| walk(e, fg, part, out)),
            Value::Fcn(ps, _) => ps.iter().any(|(k, e)| walk(k, fg, part, out) || walk(e, fg, part, out)),
            Value::LazySet(_) | Value::LazyFcn(_) => true,
        }
    }
    out.clear();
    if walk(v, fg, part, out) {
        out.clear();
        for (g, f) in fg.factors.iter().enumerate() {
            for k in 0..f.keys.len() {
                if !part.is_pinned(fg, g, k) {
                    out.push((g, k));
                }
            }
        }
    }
}

/// Whether `v` contains any unpinned atom of factor `target_g` (or a lazy value).
fn has_unpinned_in_factor(v: &Value, fg: &FactorizedGroup, part: &Partition, target_g: usize) -> bool {
    match v {
        Value::ModelValue(m) => fg.lookup(*m).is_some_and(|(g, k)| g == target_g && !part.is_pinned(fg, g, k)),
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => false,
        Value::Set(es) | Value::Tuple(es) => es.iter().any(|e| has_unpinned_in_factor(e, fg, part, target_g)),
        Value::Record(fs) => fs.iter().any(|(_, e)| has_unpinned_in_factor(e, fg, part, target_g)),
        Value::Fcn(ps, _) => {
            ps.iter().any(|(k, e)| has_unpinned_in_factor(k, fg, part, target_g) || has_unpinned_in_factor(e, fg, part, target_g))
        }
        Value::LazySet(_) | Value::LazyFcn(_) => true,
    }
}

/// Check if `es` is a pure key set eligible for Rule 2 (zero-branching block
/// splitting): every element is either a `ModelValue` (compatible types) or a
/// moved-atom-free scalar of a single scalar kind (when all touched factors are
/// untyped or `mode == CmpMode::Total`).
fn set_is_rule2_eligible(es: &[Value], fg: &FactorizedGroup, mode: CmpMode) -> bool {
    let mut mv_ty: Option<Option<char>> = None;
    let mut has_non_mv = false;
    let mut non_mv_disc: Option<u8> = None;
    let mut touched_typed_factor = false;
    for e in es {
        match e {
            Value::ModelValue(m) => {
                let ty = m.model_value_type();
                if fg.lookup(*m).is_some() && ty.is_some() {
                    touched_typed_factor = true;
                }
                if mode == CmpMode::Tlc {
                    match (mv_ty, ty) {
                        (Some(Some(prev)), Some(cur)) if prev != cur => return false,
                        (None, _) | (Some(None), Some(_)) => mv_ty = Some(ty),
                        _ => {}
                    }
                }
            }
            Value::Bool(_) => {
                has_non_mv = true;
                if mode == CmpMode::Tlc && non_mv_disc.is_some_and(|d| d != 1) {
                    return false;
                }
                non_mv_disc = Some(1);
            }
            Value::Int(_) => {
                has_non_mv = true;
                if mode == CmpMode::Tlc && non_mv_disc.is_some_and(|d| d != 2) {
                    return false;
                }
                non_mv_disc = Some(2);
            }
            Value::Str(_) => {
                has_non_mv = true;
                if mode == CmpMode::Tlc && non_mv_disc.is_some_and(|d| d != 3) {
                    return false;
                }
                non_mv_disc = Some(3);
            }
            _ => return false,
        }
    }
    if mode == CmpMode::Tlc && has_non_mv && (touched_typed_factor || matches!(mv_ty, Some(Some(_)))) {
        return false;
    }
    true
}

/// Check if `ps` is a non-empty function whose keys are distinct `ModelValue`s
/// all belonging to a single factor `g`. If so, returns `Some(g)` and populates
/// `in_dom` and `payload_idx` (both length `|K_g|`).
fn single_factor_fcn_domain(
    ps: &[(Value, Value)],
    fg: &FactorizedGroup,
    in_dom: &mut Vec<bool>,
    payload_idx: &mut Vec<Option<usize>>,
) -> Option<usize> {
    let (Value::ModelValue(m0), _) = ps.first()? else { return None };
    let (g, _) = fg.lookup(*m0)?;
    let n = fg.factors[g].keys.len();
    in_dom.clear();
    in_dom.resize(n, false);
    payload_idx.clear();
    payload_idx.resize(n, None);
    for (i, (k, _)) in ps.iter().enumerate() {
        let Value::ModelValue(m) = k else { return None };
        let (kg, ki) = fg.lookup(*m)?;
        if kg != g || in_dom[ki] {
            return None;
        }
        in_dom[ki] = true;
        payload_idx[ki] = Some(i);
    }
    Some(g)
}

/// True iff `v1` (with `k1` acting as self-key) and `v2` (with `k2` acting as
/// self-key) have identical structure, contain no unpinned atom other than
/// their respective self-key, and contain no lazy values.
fn same_self_template(fg: &FactorizedGroup, part: &Partition, k1: Sym, v1: &Value, k2: Sym, v2: &Value) -> bool {
    match (v1, v2) {
        (Value::ModelValue(m1), Value::ModelValue(m2)) => {
            if *m1 == k1 && *m2 == k2 {
                return true;
            }
            if *m1 == k1 || *m2 == k2 {
                return false;
            }
            *m1 == *m2 && fg.lookup(*m1).is_none_or(|(g, ki)| part.is_pinned(fg, g, ki))
        }
        (Value::Bool(a), Value::Bool(b)) => a == b,
        (Value::Int(a), Value::Int(b)) => a == b,
        (Value::Str(a), Value::Str(b)) => a == b,
        (Value::Interval(l1, h1), Value::Interval(l2, h2)) => l1 == l2 && h1 == h2,
        (Value::Tuple(a), Value::Tuple(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| same_self_template(fg, part, k1, x, k2, y))
        }
        (Value::Record(a), Value::Record(b)) => {
            a.len() == b.len() && a.iter().zip(b.iter()).all(|((f1, x), (f2, y))| f1 == f2 && same_self_template(fg, part, k1, x, k2, y))
        }
        (Value::Set(a), Value::Set(b)) if a.len() == 1 && b.len() == 1 => same_self_template(fg, part, k1, &a[0], k2, &b[0]),
        _ => false,
    }
}

/// True iff every domain block `B \subseteq D` of factor `g` is invariant under
/// every permutation preserving `part`: singleton blocks contain no unpinned
/// atoms, and non-singleton blocks share one self-equivariant payload template
/// (e.g. `[k \in D |-> k]`, `[k \in D |-> [id |-> k, state |-> "idle"]]`,
/// `[k \in D |-> {k}]`).
fn is_block_self_equivariant(
    fg: &FactorizedGroup,
    part: &Partition,
    g: usize,
    ps: &[(Value, Value)],
    in_dom: &[bool],
    payload_idx: &[Option<usize>],
) -> bool {
    // Fast O(|D|) path for the common identity map `[k \in D |-> k]`.
    if ps.iter().all(|(k, val)| k == val) {
        return true;
    }
    let f = &fg.factors[g];
    let off = f.offset;
    let n = f.keys.len();
    let dom = part.dom();
    let block_hi = part.block_hi();
    let mut lo = 0usize;
    while lo < n {
        let hi = block_hi[off + lo] as usize;
        let k0 = dom[off + lo] as usize;
        if in_dom[k0] {
            let v0 = &ps[payload_idx[k0].unwrap()].1;
            if hi - lo == 1 {
                if has_unpinned_atom(v0, fg, part) {
                    return false;
                }
            } else {
                let s0 = f.keys[k0];
                if !same_self_template(fg, part, s0, v0, s0, v0) {
                    return false;
                }
                for pos in (lo + 1)..hi {
                    let ki = dom[off + pos] as usize;
                    let si = f.keys[ki];
                    let vi = &ps[payload_idx[ki].unwrap()].1;
                    if !same_self_template(fg, part, s0, v0, si, vi) {
                        return false;
                    }
                }
            }
        }
        lo = hi;
    }
    true
}

/// Attempt zero-branching deterministic refinement of `part` on `v`.
pub(super) fn refine_deterministic<'a>(
    fg: &FactorizedGroup,
    part: &mut Partition,
    v: &'a Value,
    mode: CmpMode,
    scratch: &mut RefineScratch,
) -> EResult<DetOutcome<'a>> {
    if part.is_complete() {
        return Ok(DetOutcome::Done);
    }
    match v {
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => Ok(DetOutcome::Done),
        Value::ModelValue(m) => {
            if let Some((g, k)) = fg.lookup(*m) {
                part.pin_smallest(fg, g, k);
            }
            Ok(DetOutcome::Done)
        }
        Value::Tuple(es) => {
            for (idx, e) in es.iter().enumerate() {
                if part.is_complete() {
                    return Ok(DetOutcome::Done);
                }
                match refine_deterministic(fg, part, e, mode, scratch)? {
                    DetOutcome::Done => {}
                    DetOutcome::NeedBranch(mut pending) => {
                        pending.extend(es[idx + 1..].iter());
                        return Ok(DetOutcome::NeedBranch(pending));
                    }
                }
            }
            Ok(DetOutcome::Done)
        }
        Value::Record(fs) => {
            for (idx, (_, e)) in fs.iter().enumerate() {
                if part.is_complete() {
                    return Ok(DetOutcome::Done);
                }
                match refine_deterministic(fg, part, e, mode, scratch)? {
                    DetOutcome::Done => {}
                    DetOutcome::NeedBranch(mut pending) => {
                        pending.extend(fs[idx + 1..].iter().map(|(_, x)| x));
                        return Ok(DetOutcome::NeedBranch(pending));
                    }
                }
            }
            Ok(DetOutcome::Done)
        }
        Value::Set(es) => Ok(refine_set(fg, part, v, es, mode, scratch)),
        Value::Fcn(ps, _) => refine_fcn(fg, part, v, ps, mode, scratch),
        Value::LazySet(_) | Value::LazyFcn(_) => Ok(DetOutcome::NeedBranch(vec![v])),
    }
}

/// Rule 2: refine each factor's blocks into `(B \cap es)` before `(B \setminus es)`.
fn refine_set<'a>(
    fg: &FactorizedGroup,
    part: &mut Partition,
    v: &'a Value,
    es: &[Value],
    mode: CmpMode,
    scratch: &mut RefineScratch,
) -> DetOutcome<'a> {
    if es.is_empty() || !has_unpinned_atom(v, fg, part) {
        return DetOutcome::Done;
    }
    if !set_is_rule2_eligible(es, fg, mode) {
        return DetOutcome::NeedBranch(vec![v]);
    }
    for (g, f) in fg.factors.iter().enumerate() {
        let n = f.keys.len();
        scratch.in_set.clear();
        scratch.in_set.resize(n, false);
        let mut any = false;
        for e in es {
            if let Value::ModelValue(m) = e {
                if let Some((eg, ek)) = fg.lookup(*m) {
                    if eg == g {
                        scratch.in_set[ek] = true;
                        any = true;
                    }
                }
            }
        }
        if any {
            part.split_by_pred(fg, g, |k| scratch.in_set[k], &mut scratch.sort_scratch);
        }
    }
    DetOutcome::Done
}

/// Rule 3: refine a key-indexed function `[D -> payload]` (`D \subseteq K_g`)
/// in `O(|B| log |B|)` when payloads have no unpinned atoms, keep a single
/// compact stabilizer for identity/self-equivariant payloads, or refine
/// payloads sequentially when `D` is already pinned to singletons.
fn refine_fcn<'a>(
    fg: &FactorizedGroup,
    part: &mut Partition,
    v: &'a Value,
    ps: &'a [(Value, Value)],
    mode: CmpMode,
    scratch: &mut RefineScratch,
) -> EResult<DetOutcome<'a>> {
    if ps.is_empty() || !has_unpinned_atom(v, fg, part) {
        return Ok(DetOutcome::Done);
    }
    let Some(g) = single_factor_fcn_domain(ps, fg, &mut scratch.in_set, &mut scratch.payload_idx) else {
        return Ok(DetOutcome::NeedBranch(vec![v]));
    };
    if ps.len() < fg.factors[g].keys.len() {
        part.split_by_pred(fg, g, |k| scratch.in_set[k], &mut scratch.sort_scratch);
    }
    let payloads_have_unpinned = ps.iter().any(|(_, val)| has_unpinned_atom(val, fg, part));
    if !payloads_have_unpinned {
        let payloads_have_moved = ps.iter().any(|(_, val)| has_any_moved_atom(val, fg));
        let RefineScratch { in_set, payload_idx, sort_scratch, img_buf } = scratch;
        if !payloads_have_moved {
            part.try_refine_by_cmp(
                fg,
                g,
                |k| in_set[k],
                |k1, k2| mode.cmp(&ps[payload_idx[k1 as usize].unwrap()].1, &ps[payload_idx[k2 as usize].unwrap()].1),
                sort_scratch,
            )?;
        } else {
            part.fill_img_vec(fg, img_buf);
            let pmap = PermMap::Table(fg, img_buf);
            part.try_refine_by_cmp(
                fg,
                g,
                |k| in_set[k],
                |k1, k2| {
                    cmp_images_mode(mode, pmap, &ps[payload_idx[k1 as usize].unwrap()].1, pmap, &ps[payload_idx[k2 as usize].unwrap()].1)
                },
                sort_scratch,
            )?;
        }
        return Ok(DetOutcome::Done);
    }
    let off = fg.factors[g].offset;
    let n = fg.factors[g].keys.len();
    let dom = part.dom();
    let block_lo = part.block_lo();
    let block_hi = part.block_hi();
    let all_dom_pinned = (0..n).all(|pos| !scratch.in_set[dom[off + pos] as usize] || block_hi[off + pos] - block_lo[off + pos] == 1);
    if all_dom_pinned {
        let tgt = part.tgt();
        let mut ordered_vals: Vec<(u16, &'a Value)> = Vec::with_capacity(ps.len());
        for pos in 0..n {
            let k = dom[off + pos] as usize;
            if let Some(pi) = scratch.payload_idx[k] {
                ordered_vals.push((tgt[off + pos], &ps[pi].1));
            }
        }
        ordered_vals.sort_unstable_by_key(|&(t, _)| t);
        for (idx, &(_, val)) in ordered_vals.iter().enumerate() {
            if part.is_complete() {
                return Ok(DetOutcome::Done);
            }
            match refine_deterministic(fg, part, val, mode, scratch)? {
                DetOutcome::Done => {}
                DetOutcome::NeedBranch(mut pending) => {
                    pending.extend(ordered_vals[idx + 1..].iter().map(|&(_, x)| x));
                    return Ok(DetOutcome::NeedBranch(pending));
                }
            }
        }
        return Ok(DetOutcome::Done);
    }
    // Identity-on-domain (`[k \in D |-> k]`) and self-equivariant payloads
    // (`[k \in D |-> [id |-> k, ...]]`): every permutation preserving the
    // domain-refined partition gives the exact same image; retain 1 partition!
    if is_block_self_equivariant(fg, part, g, ps, &scratch.in_set, &scratch.payload_idx) {
        return Ok(DetOutcome::Done);
    }
    Ok(DetOutcome::NeedBranch(vec![v]))
}

/// Minimize `v` starting from a single `part`, returning all minimal refined
/// partitions that achieve the exact minimum image of `v` under `mode`.
fn minimize_single_value(fg: &FactorizedGroup, mut part: Partition, v: &Value, mode: CmpMode) -> EResult<Vec<Partition>> {
    let mut scratch = RefineScratch::default();
    match refine_deterministic(fg, &mut part, v, mode, &mut scratch)? {
        DetOutcome::Done => Ok(vec![part]),
        DetOutcome::NeedBranch(pending) => {
            let mut cands = vec![part];
            for item in pending {
                cands = minimize_across_candidates(fg, cands, item, mode)?;
            }
            Ok(cands)
        }
    }
}

/// Result of lex-short-circuiting minimization of a payload against an upper
/// bound `(best_img, best_val)`:
/// - `Pruned`: every completion is strictly `Greater` than `best_val` (already
///   decided at an earlier `Tuple`/`Record` component without touching later
///   components).
/// - `Kept`: minimal refined partitions with image `<= best_val`.
enum BoundedMin {
    Pruned,
    Kept { parts: Vec<Partition>, strictly_less: bool },
}

/// Minimize `payload` starting from `part`, short-circuiting through nested
/// `Tuple`/`Record` components and length mismatches against `(best_img, best_val)`
/// before refining any subsequent component.
fn minimize_bounded(
    fg: &FactorizedGroup,
    part: Partition,
    payload: &Value,
    bound: Option<(&[u16], &Value)>,
    mode: CmpMode,
) -> EResult<BoundedMin> {
    let Some((best_img, best_val)) = bound else {
        return Ok(BoundedMin::Kept { parts: minimize_single_value(fg, part, payload, mode)?, strictly_less: true });
    };
    match (payload, best_val) {
        (Value::Tuple(es), Value::Tuple(bs)) => match es.len().cmp(&bs.len()) {
            Ordering::Greater => Ok(BoundedMin::Pruned),
            Ordering::Less => Ok(BoundedMin::Kept { parts: minimize_single_value(fg, part, payload, mode)?, strictly_less: true }),
            Ordering::Equal => {
                let mut cands = vec![part];
                let mut less = false;
                for (e, b) in es.iter().zip(bs.iter()) {
                    if !less {
                        match minimize_bounded_candidates(fg, cands, e, best_img, b, mode)? {
                            BoundedMin::Pruned => return Ok(BoundedMin::Pruned),
                            BoundedMin::Kept { parts, strictly_less } => {
                                cands = parts;
                                less = strictly_less;
                            }
                        }
                    } else {
                        cands = minimize_across_candidates(fg, cands, e, mode)?;
                    }
                }
                Ok(BoundedMin::Kept { parts: cands, strictly_less: less })
            }
        },
        (Value::Record(rs), Value::Record(bs)) => {
            let mut hdr = rs.len().cmp(&bs.len());
            if hdr == Ordering::Equal {
                for ((f1, _), (f2, _)) in rs.iter().zip(bs.iter()) {
                    hdr = f1.cmp(f2);
                    if hdr != Ordering::Equal {
                        break;
                    }
                }
            }
            match hdr {
                Ordering::Greater => Ok(BoundedMin::Pruned),
                Ordering::Less => Ok(BoundedMin::Kept { parts: minimize_single_value(fg, part, payload, mode)?, strictly_less: true }),
                Ordering::Equal => {
                    let mut cands = vec![part];
                    let mut less = false;
                    for ((_, e), (_, b)) in rs.iter().zip(bs.iter()) {
                        if !less {
                            match minimize_bounded_candidates(fg, cands, e, best_img, b, mode)? {
                                BoundedMin::Pruned => return Ok(BoundedMin::Pruned),
                                BoundedMin::Kept { parts, strictly_less } => {
                                    cands = parts;
                                    less = strictly_less;
                                }
                            }
                        } else {
                            cands = minimize_across_candidates(fg, cands, e, mode)?;
                        }
                    }
                    Ok(BoundedMin::Kept { parts: cands, strictly_less: less })
                }
            }
        }
        (Value::Fcn(ps, _), Value::Fcn(bs, _)) if !ps.is_empty() && !bs.is_empty() && ps.len() != bs.len() => {
            if ps.len() > bs.len() {
                Ok(BoundedMin::Pruned)
            } else {
                Ok(BoundedMin::Kept { parts: minimize_single_value(fg, part, payload, mode)?, strictly_less: true })
            }
        }
        (Value::Set(xs), Value::Set(ys)) if xs.len() != ys.len() => {
            if xs.len() > ys.len() {
                Ok(BoundedMin::Pruned)
            } else {
                Ok(BoundedMin::Kept { parts: minimize_single_value(fg, part, payload, mode)?, strictly_less: true })
            }
        }
        _ => {
            let parts = minimize_single_value(fg, part, payload, mode)?;
            let mut cur_img = Vec::new();
            parts[0].fill_img_vec(fg, &mut cur_img);
            match cmp_images_mode(mode, PermMap::Table(fg, &cur_img), payload, PermMap::Table(fg, best_img), best_val)? {
                Ordering::Greater => Ok(BoundedMin::Pruned),
                Ordering::Less => Ok(BoundedMin::Kept { parts, strictly_less: true }),
                Ordering::Equal => Ok(BoundedMin::Kept { parts, strictly_less: false }),
            }
        }
    }
}

/// Apply `minimize_bounded` across a set of tied candidate partitions, keeping
/// only those achieving the global minimum `<= best_val` on `elem`.
fn minimize_bounded_candidates(
    fg: &FactorizedGroup,
    candidates: Vec<Partition>,
    elem: &Value,
    best_img: &[u16],
    best_elem: &Value,
    mode: CmpMode,
) -> EResult<BoundedMin> {
    let mut best_parts: Vec<Partition> = Vec::new();
    let mut cur_best_img: Vec<u16> = Vec::new();
    let mut cand_img: Vec<u16> = Vec::new();
    let mut strictly_less = false;

    for part in candidates {
        let bound = if strictly_less { (cur_best_img.as_slice(), elem) } else { (best_img, best_elem) };
        match minimize_bounded(fg, part, elem, Some(bound), mode)? {
            BoundedMin::Pruned => {}
            BoundedMin::Kept { parts, strictly_less: beat } => {
                if beat {
                    parts[0].fill_img_vec(fg, &mut cur_best_img);
                    best_parts = parts;
                    strictly_less = true;
                } else if best_parts.is_empty() {
                    parts[0].fill_img_vec(fg, &mut cur_best_img);
                    best_parts = parts;
                } else {
                    parts[0].fill_img_vec(fg, &mut cand_img);
                    match cmp_images_mode(mode, PermMap::Table(fg, &cand_img), elem, PermMap::Table(fg, &cur_best_img), elem)? {
                        Ordering::Greater => {}
                        Ordering::Equal => best_parts.extend(parts),
                        Ordering::Less => {
                            std::mem::swap(&mut cur_best_img, &mut cand_img);
                            best_parts = parts;
                            strictly_less = true;
                        }
                    }
                }
            }
        }
    }
    if best_parts.is_empty() {
        Ok(BoundedMin::Pruned)
    } else {
        Ok(BoundedMin::Kept { parts: best_parts, strictly_less })
    }
}

/// Given `candidates` that all tie on earlier variables, refine and prune to
/// the subset achieving the global minimum image of `v` under `mode`.
pub(super) fn minimize_across_candidates(
    fg: &FactorizedGroup,
    candidates: Vec<Partition>,
    v: &Value,
    mode: CmpMode,
) -> EResult<Vec<Partition>> {
    match v {
        Value::Tuple(es) => {
            let mut cands = candidates;
            for e in es.iter() {
                if cands.len() == 1 && cands[0].is_complete() {
                    break;
                }
                cands = minimize_across_candidates(fg, cands, e, mode)?;
            }
            return Ok(cands);
        }
        Value::Record(fs) => {
            let mut cands = candidates;
            for (_, e) in fs.iter() {
                if cands.len() == 1 && cands[0].is_complete() {
                    break;
                }
                cands = minimize_across_candidates(fg, cands, e, mode)?;
            }
            return Ok(cands);
        }
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => return Ok(candidates),
        _ => {}
    }

    let mut best_parts: Vec<Partition> = Vec::new();
    let mut best_img: Vec<u16> = Vec::new();
    let mut cur_img: Vec<u16> = Vec::new();
    let mut best_order: Option<ImageOrder> = None;
    let mut scratch = RefineScratch::default();

    for mut part in candidates {
        let refined = match refine_deterministic(fg, &mut part, v, mode, &mut scratch)? {
            DetOutcome::Done => vec![part],
            DetOutcome::NeedBranch(pending) => {
                if pending.len() == 1 && std::ptr::eq(pending[0], v) {
                    branch_single_value(fg, part, v, mode)?
                } else {
                    let mut sub = vec![part];
                    for item in pending {
                        sub = minimize_across_candidates(fg, sub, item, mode)?;
                    }
                    sub
                }
            }
        };
        if refined.is_empty() {
            continue;
        }
        if best_parts.is_empty() {
            refined[0].fill_img_vec(fg, &mut best_img);
            best_parts = refined;
            best_order = None;
            continue;
        }
        refined[0].fill_img_vec(fg, &mut cur_img);
        match cmp_images_with_mode(mode, PermMap::Table(fg, &cur_img), v, PermMap::Table(fg, &best_img), v, &mut best_order)? {
            Ordering::Greater => {}
            Ordering::Equal => best_parts.extend(refined),
            Ordering::Less => {
                std::mem::swap(&mut best_img, &mut cur_img);
                best_parts = refined;
                best_order = None;
            }
        }
    }
    Ok(best_parts)
}

/// Branch-and-bound minimization of a single irreducible value `v` starting
/// from `part`: dispatches key-domain functions to slot-by-slot Case A and
/// arbitrary recursive values to active-atom Case B.
fn branch_single_value(fg: &FactorizedGroup, part: Partition, v: &Value, mode: CmpMode) -> EResult<Vec<Partition>> {
    if let Value::Fcn(ps, _) = v {
        let mut in_dom = Vec::new();
        let mut payload_idx = Vec::new();
        if let Some(g) = single_factor_fcn_domain(ps, fg, &mut in_dom, &mut payload_idx) {
            return branch_keyed_fcn(fg, part, g, ps, &in_dom, &payload_idx, mode);
        }
    }
    branch_general_value(fg, part, v, mode)
}

/// Read-only context for Case A (`[D -> payload]` slot-by-slot DFS).
struct FcnCtx<'c, 'v> {
    fg: &'c FactorizedGroup,
    g: usize,
    ps: &'v [(Value, Value)],
    payload_idx: &'c [Option<usize>],
    dom_slots: Vec<u16>,
    mode: CmpMode,
}

/// Best complete assignment tracked across Case A DFS.
struct FcnBest<'v> {
    epoch: u64,
    rep_img: Vec<u16>,
    slot_payloads: Vec<&'v Value>,
    parts: Vec<Partition>,
}

/// Case A: slot-by-slot lex-leader branch-and-bound for `Value::Fcn` with
/// domain `D \subseteq K_g` and payloads containing unpinned atoms.
fn branch_keyed_fcn<'v>(
    fg: &FactorizedGroup,
    part: Partition,
    g: usize,
    ps: &'v [(Value, Value)],
    in_dom: &[bool],
    payload_idx: &[Option<usize>],
    mode: CmpMode,
) -> EResult<Vec<Partition>> {
    let off = fg.factors[g].offset;
    let n = fg.factors[g].keys.len();
    let dom = part.dom();
    let tgt = part.tgt();
    let mut dom_slots: Vec<u16> = Vec::with_capacity(ps.len());
    for pos in 0..n {
        if in_dom[dom[off + pos] as usize] {
            dom_slots.push(tgt[off + pos]);
        }
    }
    dom_slots.sort_unstable();

    let ctx = FcnCtx { fg, g, ps, payload_idx, dom_slots, mode };
    let mut cur_payloads: Vec<&'v Value> = Vec::with_capacity(ctx.dom_slots.len());
    let mut best: Option<FcnBest<'v>> = None;
    fcn_dfs(&ctx, part, 0, None, &mut cur_payloads, &mut best)?;
    Ok(best.map_or_else(Vec::new, |b| b.parts))
}

/// Compare the longest prefix of `a` and `b` whose ordering is invariant
/// across all completions of `part` (lengths, record field names, and leading
/// `Tuple`/`Record` components containing no unpinned atoms).
///
/// Returns `Some(ord)` only when every completion of `part` yields that exact
/// `Ordering`, and `None` as soon as an unpinned component makes the ordering
/// completion-dependent.
fn cmp_fixed_prefix(
    mode: CmpMode,
    fg: &FactorizedGroup,
    part: &Partition,
    pmap: PermMap<'_>,
    a: &Value,
    b: &Value,
) -> tlx_value::Result<Option<Ordering>> {
    if !has_unpinned_atom(a, fg, part) && !has_unpinned_atom(b, fg, part) {
        return cmp_images_mode(mode, pmap, a, pmap, b).map(Some);
    }
    match (a, b) {
        (Value::Tuple(es), Value::Tuple(bs)) => {
            let c = es.len().cmp(&bs.len());
            if c != Ordering::Equal {
                return Ok(Some(c));
            }
            for (x, y) in es.iter().zip(bs.iter()) {
                match cmp_fixed_prefix(mode, fg, part, pmap, x, y)? {
                    Some(Ordering::Equal) => {}
                    other => return Ok(other),
                }
            }
            Ok(Some(Ordering::Equal))
        }
        (Value::Record(rs), Value::Record(bs)) => {
            let c = rs.len().cmp(&bs.len());
            if c != Ordering::Equal {
                return Ok(Some(c));
            }
            for ((f1, _), (f2, _)) in rs.iter().zip(bs.iter()) {
                let c = f1.cmp(f2);
                if c != Ordering::Equal {
                    return Ok(Some(c));
                }
            }
            for ((_, x), (_, y)) in rs.iter().zip(bs.iter()) {
                match cmp_fixed_prefix(mode, fg, part, pmap, x, y)? {
                    Some(Ordering::Equal) => {}
                    other => return Ok(other),
                }
            }
            Ok(Some(Ordering::Equal))
        }
        (Value::Fcn(ps, _), Value::Fcn(qs, _)) if !ps.is_empty() && !qs.is_empty() => {
            let c = ps.len().cmp(&qs.len());
            Ok((c != Ordering::Equal).then_some(c))
        }
        (Value::Set(xs), Value::Set(ys)) => {
            let c = xs.len().cmp(&ys.len());
            Ok((c != Ordering::Equal).then_some(c))
        }
        _ => Ok(None),
    }
}

/// Filter `items` to keep every candidate that is not strictly dominated by
/// another candidate's completion-invariant fixed prefix (discarding only
/// proven losers before touching their unpinned tails).
fn filter_min_fixed_prefix<'v, T>(
    ctx: &FcnCtx<'_, 'v>,
    part: &Partition,
    items: Vec<T>,
    payload_of: impl Fn(&T) -> &'v Value,
) -> EResult<Vec<T>> {
    if items.len() <= 1 {
        return Ok(items);
    }
    let mut img = Vec::new();
    part.fill_img_vec(ctx.fg, &mut img);
    let pmap = PermMap::Table(ctx.fg, &img);
    let mut kept: Vec<T> = Vec::with_capacity(items.len());
    for item in items {
        let mut dominated = false;
        let mut i = 0;
        while i < kept.len() {
            match cmp_fixed_prefix(ctx.mode, ctx.fg, part, pmap, payload_of(&item), payload_of(&kept[i]))? {
                Some(Ordering::Greater) => {
                    dominated = true;
                    break;
                }
                Some(Ordering::Less) => {
                    kept.remove(i);
                }
                Some(Ordering::Equal) | None => {
                    i += 1;
                }
            }
        }
        if !dominated {
            kept.push(item);
        }
    }
    Ok(kept)
}

fn fcn_dfs<'v>(
    ctx: &FcnCtx<'_, 'v>,
    part: Partition,
    slot_idx: usize,
    beat_epoch: Option<u64>,
    cur_payloads: &mut Vec<&'v Value>,
    best: &mut Option<FcnBest<'v>>,
) -> EResult<()> {
    if slot_idx == ctx.dom_slots.len() {
        let strictly_less = match best {
            None => true,
            Some(b) => beat_epoch == Some(b.epoch),
        };
        if strictly_less {
            let next_epoch = best.as_ref().map_or(1, |b| b.epoch + 1);
            let mut rep_img = Vec::new();
            part.fill_img_vec(ctx.fg, &mut rep_img);
            *best = Some(FcnBest { epoch: next_epoch, rep_img, slot_payloads: cur_payloads.clone(), parts: vec![part] });
        } else {
            best.as_mut().unwrap().parts.push(part);
        }
        return Ok(());
    }

    let off = ctx.fg.factors[ctx.g].offset;
    let n = ctx.fg.factors[ctx.g].keys.len();
    let target_t = ctx.dom_slots[slot_idx];
    let pos = (0..n).find(|&p| part.tgt()[off + p] == target_t).expect("target slot exists");
    let lo = part.block_lo()[off + pos] as usize;
    let hi = part.block_hi()[off + pos] as usize;

    if hi - lo == 1 {
        let k = part.dom()[off + lo] as usize;
        let payload = &ctx.ps[ctx.payload_idx[k].unwrap()].1;
        return fcn_step_run(ctx, part, slot_idx, 1, payload, beat_epoch, cur_payloads, best);
    }

    let block_len = hi - lo;
    let contiguous = pos == lo
        && slot_idx + block_len <= ctx.dom_slots.len()
        && ctx.dom_slots[slot_idx..slot_idx + block_len] == part.tgt()[off + lo..off + hi];
    let can_bulk = contiguous
        && (lo..hi).all(|p| {
            let val = &ctx.ps[ctx.payload_idx[part.dom()[off + p] as usize].unwrap()].1;
            !matches!(val, Value::LazySet(_) | Value::LazyFcn(_)) && !has_unpinned_in_factor(val, ctx.fg, &part, ctx.g)
        });
    if can_bulk {
        let mut classes: Vec<(Vec<u16>, &'v Value)> = Vec::new();
        for p in lo..hi {
            let k = part.dom()[off + p];
            let val = &ctx.ps[ctx.payload_idx[k as usize].unwrap()].1;
            if let Some((keys, _)) = classes.iter_mut().find(|(_, rep)| {
                self_comparison_is_inert(val) && self_comparison_is_inert(rep) && try_total_cmp(val, rep).ok() == Some(Ordering::Equal)
            }) {
                keys.push(k);
            } else {
                classes.push((vec![k], val));
            }
        }
        let classes = filter_min_fixed_prefix(ctx, &part, classes, |(_, p)| p)?;
        for (keys, payload) in classes {
            let mut next_part = part.clone();
            next_part.bulk_place_first(ctx.fg, ctx.g, lo, &keys);
            fcn_step_run(ctx, next_part, slot_idx, keys.len(), payload, beat_epoch, cur_payloads, best)?;
        }
        return Ok(());
    }

    let keys: Vec<u16> = part.dom()[off + lo..off + hi].to_vec();
    let keys = filter_min_fixed_prefix(ctx, &part, keys, |&k| &ctx.ps[ctx.payload_idx[k as usize].unwrap()].1)?;
    for k in keys {
        let mut next_part = part.clone();
        next_part.pin_to_slot(ctx.fg, ctx.g, k as usize, pos);
        let payload = &ctx.ps[ctx.payload_idx[k as usize].unwrap()].1;
        fcn_step_run(ctx, next_part, slot_idx, 1, payload, beat_epoch, cur_payloads, best)?;
    }
    Ok(())
}

/// Minimize `payload` across `run_len` consecutive output slots starting at
/// `slot_idx`, short-circuiting through nested `Tuple`/`Record` payloads against
/// `best` before refining later components or recursing into `slot_idx + run_len`.
#[allow(clippy::too_many_arguments)] // single internal DFS step carrying branch state
fn fcn_step_run<'v>(
    ctx: &FcnCtx<'_, 'v>,
    part: Partition,
    slot_idx: usize,
    run_len: usize,
    payload: &'v Value,
    beat_epoch: Option<u64>,
    cur_payloads: &mut Vec<&'v Value>,
    best: &mut Option<FcnBest<'v>>,
) -> EResult<()> {
    let mut next_beat = beat_epoch;
    let sub_parts = match best.as_ref() {
        Some(b) if beat_epoch != Some(b.epoch) => {
            match minimize_bounded(ctx.fg, part, payload, Some((&b.rep_img, b.slot_payloads[slot_idx])), ctx.mode)? {
                BoundedMin::Pruned => return Ok(()),
                BoundedMin::Kept { parts, strictly_less } => {
                    if strictly_less {
                        next_beat = Some(b.epoch);
                    } else if run_len > 1 {
                        let mut cur_img = Vec::new();
                        parts[0].fill_img_vec(ctx.fg, &mut cur_img);
                        for r in 1..run_len {
                            match cmp_images_mode(
                                ctx.mode,
                                PermMap::Table(ctx.fg, &cur_img),
                                payload,
                                PermMap::Table(ctx.fg, &b.rep_img),
                                b.slot_payloads[slot_idx + r],
                            )? {
                                Ordering::Greater => return Ok(()),
                                Ordering::Less => {
                                    next_beat = Some(b.epoch);
                                    break;
                                }
                                Ordering::Equal => {}
                            }
                        }
                    }
                    parts
                }
            }
        }
        _ => minimize_single_value(ctx.fg, part, payload, ctx.mode)?,
    };
    for _ in 0..run_len {
        cur_payloads.push(payload);
    }
    for sp in sub_parts {
        fcn_dfs(ctx, sp, slot_idx + run_len, next_beat, cur_payloads, best)?;
    }
    cur_payloads.truncate(cur_payloads.len() - run_len);
    Ok(())
}

/// True iff every adjacent transposition generating the free blocks of `part`
/// that intersect `active` fixes `v` (`tau(v) == v`). Since adjacent swaps
/// generate `prod_B Sym(B)`, this implies every completion of `part` yields the
/// exact same image of `v`, so `part` itself compactly represents all minimizers
/// while leaving all free blocks open for subsequent variables.
fn is_invariant_under_block_swaps(
    fg: &FactorizedGroup,
    part: &Partition,
    v: &Value,
    active: &[(usize, usize)],
    mode: CmpMode,
) -> EResult<bool> {
    part.try_all_active_block_swaps(fg, active, |swap_img| {
        Ok(cmp_images_mode(mode, PermMap::Table(fg, swap_img), v, PermMap::Id, v)? == Ordering::Equal)
    })
}

/// Case B: active-atom branch-and-bound for general recursive values (record-key
/// bags, multi-key sets/tuples, `LazySet`, `LazyFcn`). Only branches on unpinned
/// atoms that actually occur in `v`, leaving all other blocks and factors intact.
pub(super) fn branch_general_value(fg: &FactorizedGroup, part: Partition, v: &Value, mode: CmpMode) -> EResult<Vec<Partition>> {
    let mut active = Vec::new();
    collect_unpinned_atoms(v, fg, &part, &mut active);
    if active.is_empty() {
        return Ok(vec![part]);
    }
    if is_invariant_under_block_swaps(fg, &part, v, &active, mode)? {
        return Ok(vec![part]);
    }

    struct GenBest {
        img: Vec<u16>,
        order: Option<ImageOrder>,
        parts: Vec<Partition>,
    }

    let mut best: Option<GenBest> = None;
    let mut cur_img = Vec::new();
    part.try_for_each_active_completion(fg, &active, |leaf| -> EResult<()> {
        leaf.fill_img_vec(fg, &mut cur_img);
        match &mut best {
            None => best = Some(GenBest { img: cur_img.clone(), order: None, parts: vec![leaf] }),
            Some(b) => match cmp_images_with_mode(mode, PermMap::Table(fg, &cur_img), v, PermMap::Table(fg, &b.img), v, &mut b.order)? {
                Ordering::Greater => {}
                Ordering::Equal => b.parts.push(leaf),
                Ordering::Less => {
                    b.img.clear();
                    b.img.extend_from_slice(&cur_img);
                    b.order = None;
                    b.parts.clear();
                    b.parts.push(leaf);
                }
            },
        }
        Ok(())
    })?;
    Ok(best.map_or_else(Vec::new, |b| b.parts))
}
