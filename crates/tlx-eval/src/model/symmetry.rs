//! SYMMETRY sets: permutations of model values.
//!
//! When the declared or automatically inferred `SYMMETRY` group is a disjoint
//! product of full symmetric groups `S_{n_1} x ... x S_{n_k}` over pairwise-
//! disjoint model-value sets `K_g`, canonicalization runs partition refinement
//! and lex-leader backtracking (`factor`, `refine`) instead of closing and
//! scanning all `|G|` explicit permutations. Arbitrary non-full subgroups
//! (cyclic, alternating, diagonal, non-bijective, or mixed model-value types)
//! retain the explicit `Vec<FastPerm>` fallback.

mod factor;
mod refine;
#[cfg(test)]
mod tests;

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, OnceLock};

use tlx_base::partition::{Partition, INLINE_KEYS};
use tlx_value::order::{cmp_tlc, try_total_cmp};
use tlx_value::{ops, Sym, Value};

use crate::error::{EResult, EvalError};

pub(in crate::model) use factor::symmetry_group;
use factor::{recognize_disjoint_factors, FactorizedGroup, FallbackOrder};
use refine::{
    branch_general_value, has_any_moved_atom, is_orbit_cmp_safe, minimize_across_candidates, refine_deterministic, DetOutcome,
    FactorScratch,
};

/// A permutation of model values: maps each moved model value to its image
/// (fixed points are left out).
pub(super) type Perm = HashMap<Sym, Value>;

/// Largest group order for which `InterpModel::symmetry_maps()` materializes
/// explicit `Perm` maps on demand (for `tlx-compile`). Larger disjoint products
/// stay purely factorized without enumerating `|G|`.
const MAX_MATERIALIZED_ORDER: u128 = 720;

/// Functions and sets with at most this many elements are compared with
/// their images without building them (`cmp_images`).
const MAX_KEYS: usize = 64;

/// Comparison order used when selecting the least orbit representative.
#[derive(Clone, Copy, PartialEq, Eq)]
enum CmpMode {
    /// TLC's `compareTo` (`cmp_tlc`), reporting errors on incomparable values.
    Tlc,
    /// Total structural order (`try_total_cmp`), used for projected orbits with
    /// internal sentinels that may have different types from retained values.
    Total,
}

impl CmpMode {
    #[inline]
    fn cmp(self, a: &Value, b: &Value) -> tlx_value::Result<Ordering> {
        match self {
            CmpMode::Tlc => cmp_tlc(a, b),
            CmpMode::Total => try_total_cmp(a, b),
        }
    }
}

/// A permutation in a form fast to apply: the moved model values (by
/// symbol id) and their images.
#[derive(Clone)]
pub(super) struct FastPerm(pub(super) Vec<(u32, Value)>);

impl FastPerm {
    pub(super) fn new(p: &Perm) -> FastPerm {
        FastPerm(p.iter().map(|(k, v)| (k.id(), v.clone())).collect())
    }

    #[inline]
    fn get(&self, m: Sym) -> Option<&Value> {
        let id = m.id();
        self.0.iter().find(|(k, _)| *k == id).map(|(_, v)| v)
    }

    /// The images of the model values `support` (symbol ids) into `out`,
    /// for telling apart the permutations that act differently on them;
    /// false if one is not a model value.
    fn images(&self, support: &[u32], out: &mut Vec<u32>) -> bool {
        out.clear();
        for &id in support {
            out.push(match self.0.iter().find(|(k, _)| *k == id) {
                Some((_, Value::ModelValue(m))) => m.id(),
                Some(_) => return false,
                None => id,
            });
        }
        true
    }

    /// The image of `v` under the permutation, or `None` when `v` contains
    /// no moved model value (so unchanged subvalues are shared, not rebuilt).
    pub(super) fn apply(&self, v: &Value) -> tlx_value::Result<Option<Value>> {
        ops::permute_shared(v, &|m| self.get(m).cloned())
    }
}

/// A winning permutation returned by `Group`: either borrowed from an explicit
/// subgroup table or stored as a compact target-index table (inline on stack
/// for `<= INLINE_KEYS` total moved atoms, zero heap allocation).
pub(super) struct ChosenPerm<'a>(ChosenPermInner<'a>);

enum ChosenPermInner<'a> {
    Borrowed(&'a FastPerm),
    FactorInline { fg: &'a FactorizedGroup, img: [u16; INLINE_KEYS] },
    FactorHeap { fg: &'a FactorizedGroup, img: Vec<u16> },
}

impl<'a> ChosenPerm<'a> {
    fn borrowed(p: &'a FastPerm) -> Self {
        Self(ChosenPermInner::Borrowed(p))
    }

    fn factor_inline(fg: &'a FactorizedGroup, img: [u16; INLINE_KEYS]) -> Self {
        Self(ChosenPermInner::FactorInline { fg, img })
    }

    fn factor_heap(fg: &'a FactorizedGroup, img: Vec<u16>) -> Self {
        Self(ChosenPermInner::FactorHeap { fg, img })
    }

    pub(super) fn apply(&self, v: &Value) -> tlx_value::Result<Option<Value>> {
        match &self.0 {
            ChosenPermInner::Borrowed(p) => p.apply(v),
            ChosenPermInner::FactorInline { fg, img } => PermMap::Table(fg, &img[..fg.total_keys]).apply(v),
            ChosenPermInner::FactorHeap { fg, img } => PermMap::Table(fg, img).apply(v),
        }
    }
}

/// A permutation view used during zero-allocation `cmp_images_mode`.
#[derive(Clone, Copy)]
enum PermMap<'a> {
    Id,
    Fast(&'a FastPerm),
    /// Direct factorized key-index -> target-index lookup table.
    Table(&'a FactorizedGroup, &'a [u16]),
}

impl<'a> PermMap<'a> {
    #[inline]
    fn is_id(self) -> bool {
        matches!(self, PermMap::Id)
    }

    #[inline]
    fn get(self, m: Sym) -> Option<&'a Value> {
        match self {
            PermMap::Id => None,
            PermMap::Fast(p) => p.get(m),
            PermMap::Table(fg, img) => {
                let (g, k) = fg.lookup(m)?;
                let f = &fg.factors[g];
                let t = img[f.offset + k] as usize;
                (t != k).then_some(&f.values[t])
            }
        }
    }

    fn apply(self, v: &Value) -> tlx_value::Result<Option<Value>> {
        match self {
            PermMap::Id => Ok(None),
            PermMap::Fast(p) => p.apply(v),
            PermMap::Table(..) => ops::permute_shared(v, &|m| self.get(m).cloned()),
        }
    }
}

/// Whether `v` is eligible for `BagCache` (non-empty record-key bag with at
/// most `MAX_KEYS` entries).
fn is_record_key_bag(v: &Value) -> bool {
    matches!(v, Value::Fcn(ps, _) if !ps.is_empty() && ps.len() <= MAX_KEYS && ps.iter().all(|(k, _)| matches!(k, Value::Record(_))))
}

/// `cmp_tlc(p(a), q(b))` (or `try_total_cmp` when `mode == CmpMode::Total`),
/// comparing component by component without building the images where their
/// structure follows from `a` and `b`.
fn cmp_images_mode(mode: CmpMode, p: PermMap, a: &Value, q: PermMap, b: &Value) -> tlx_value::Result<Ordering> {
    #[cfg(test)]
    CMP_CALLS.with(|n| n.set(n.get() + 1));
    if a.is_empty_fcn() || b.is_empty_fcn() {
        return cmp_built(mode, p, a, q, b);
    }
    let scalar = |v: &Value| matches!(v, Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..));
    match (a, b) {
        (Value::ModelValue(m), Value::ModelValue(n)) => mode.cmp(mv_image(p, *m, a), mv_image(q, *n, b)),
        _ if scalar(a) && scalar(b) => mode.cmp(a, b),
        (Value::Tuple(t), Value::Tuple(u)) => {
            if t.len() != u.len() {
                return Ok(t.len().cmp(&u.len()));
            }
            cmp_seq(mode, t.iter().zip(u.iter()).map(|(x, y)| (p, x, q, y)))
        }
        (Value::Record(r), Value::Record(s)) => {
            if r.len() != s.len() {
                return Ok(r.len().cmp(&s.len()));
            }
            for (x, y) in r.iter().zip(s.iter()) {
                let c = x.0.cmp(&y.0);
                if c != Ordering::Equal {
                    return Ok(c);
                }
            }
            cmp_seq(mode, r.iter().zip(s.iter()).map(|(x, y)| (p, &x.1, q, &y.1)))
        }
        (Value::Fcn(ps, _), Value::Fcn(qs, _)) => {
            if ps.len() != qs.len() {
                return Ok(ps.len().cmp(&qs.len()));
            }
            let c = cmp_sorted(mode, p, &|i| &ps[i].0, Some(&|i| &ps[i].1), q, &|i| &qs[i].0, Some(&|i| &qs[i].1), ps.len(), None)?;
            c.map_or_else(|| cmp_built(mode, p, a, q, b), Ok)
        }
        (Value::Set(xs), Value::Set(ys)) => {
            if xs.len() != ys.len() {
                return Ok(xs.len().cmp(&ys.len()));
            }
            let c = cmp_sorted(mode, p, &|i| &xs[i], None, q, &|i| &ys[i], None, xs.len(), None)?;
            c.map_or_else(|| cmp_built(mode, p, a, q, b), Ok)
        }
        _ => cmp_built(mode, p, a, q, b),
    }
}

/// `cmp_images_mode(mode, p, a, q, b)` where the order of the images under `q`
/// of the elements (keys) of `b` is kept in `qo`.
fn cmp_images_with_mode(
    mode: CmpMode,
    p: PermMap,
    a: &Value,
    q: PermMap,
    b: &Value,
    qo: &mut Option<ImageOrder>,
) -> tlx_value::Result<Ordering> {
    let c = match (a, b) {
        (Value::Fcn(ps, _), Value::Fcn(qs, _)) if ps.len() == qs.len() && !ps.is_empty() && ps.len() <= MAX_KEYS => {
            let kb: Keys = &|i| &qs[i].0;
            let ob = qo.get_or_insert_with(|| ImageOrder::new(q, qs.len(), kb).expect("at most MAX_KEYS"));
            cmp_sorted(mode, p, &|i| &ps[i].0, Some(&|i| &ps[i].1), q, kb, Some(&|i| &qs[i].1), ps.len(), Some(ob))?
        }
        (Value::Set(xs), Value::Set(ys)) if xs.len() == ys.len() && ys.len() <= MAX_KEYS => {
            let kb: Keys = &|i| &ys[i];
            let ob = qo.get_or_insert_with(|| ImageOrder::new(q, ys.len(), kb).expect("at most MAX_KEYS"));
            cmp_sorted(mode, p, &|i| &xs[i], None, q, kb, None, xs.len(), Some(ob))?
        }
        _ => None,
    };
    match c {
        Some(c) => Ok(c),
        None => cmp_images_mode(mode, p, a, q, b),
    }
}

fn cmp_seq<'v, 'p>(
    mode: CmpMode,
    pairs: impl Iterator<Item = (PermMap<'p>, &'v Value, PermMap<'p>, &'v Value)>,
) -> tlx_value::Result<Ordering> {
    for (p, x, q, y) in pairs {
        let c = cmp_images_mode(mode, p, x, q, y)?;
        if c != Ordering::Equal {
            return Ok(c);
        }
    }
    Ok(Ordering::Equal)
}

fn mv_image<'v>(p: PermMap<'v>, m: Sym, v: &'v Value) -> &'v Value {
    p.get(m).unwrap_or(v)
}

fn cmp_built(mode: CmpMode, p: PermMap, a: &Value, q: PermMap, b: &Value) -> tlx_value::Result<Ordering> {
    let (x, y) = (p.apply(a)?, q.apply(b)?);
    mode.cmp(x.as_ref().unwrap_or(a), y.as_ref().unwrap_or(b))
}

type Keys<'k, 'v> = &'k dyn Fn(usize) -> &'v Value;

#[allow(clippy::too_many_arguments)] // mode, two (permutation, keys, values) triples, size and cached order
fn cmp_sorted<'v>(
    mode: CmpMode,
    p: PermMap,
    ka: Keys<'_, 'v>,
    va: Option<Keys<'_, 'v>>,
    q: PermMap,
    kb: Keys<'_, 'v>,
    vb: Option<Keys<'_, 'v>>,
    n: usize,
    ob: Option<&mut ImageOrder>,
) -> tlx_value::Result<Option<Ordering>> {
    let Some(mut oa) = ImageOrder::new(p, n, ka) else {
        return Ok(None);
    };
    let mut own;
    let ob = match ob {
        Some(o) => o,
        None => {
            let Some(o) = ImageOrder::new(q, n, kb) else {
                return Ok(None);
            };
            own = o;
            &mut own
        }
    };
    for j in 0..n {
        let (i, k) = (oa.at(mode, p, n, ka, j)?, ob.at(mode, q, n, kb, j)?);
        let c = cmp_images_mode(mode, p, ka(i), q, kb(k))?;
        if c != Ordering::Equal {
            return Ok(Some(c));
        }
    }
    if let (Some(va), Some(vb)) = (va, vb) {
        for j in 0..n {
            let c = cmp_images_mode(mode, p, va(oa.src[j] as usize), q, vb(ob.src[j] as usize))?;
            if c != Ordering::Equal {
                return Ok(Some(c));
            }
        }
    }
    Ok(Some(Ordering::Equal))
}

/// The order of the images under a permutation of `n` sorted, distinct
/// values: `src[j]` is the index of the value whose image is the `j`th
/// least, known for `j < known`.
struct ImageOrder {
    src: [u8; MAX_KEYS],
    known: usize,
    used: u64,
}

impl ImageOrder {
    fn new(p: PermMap, n: usize, key: Keys) -> Option<ImageOrder> {
        if n > MAX_KEYS {
            return None;
        }
        let mut o = ImageOrder { src: [0; MAX_KEYS], known: 0, used: 0 };
        for (i, s) in o.src[..n].iter_mut().enumerate() {
            *s = i as u8;
        }
        if p.is_id() {
            o.known = n;
            return Some(o);
        }
        for i in 0..n {
            let j = match key(i) {
                Value::ModelValue(m) => match p.get(*m) {
                    None => i,
                    Some(img) => match (0..n).find(|&j| key(j) == img) {
                        Some(j) => j,
                        None => return Some(ImageOrder { src: [0; MAX_KEYS], known: 0, used: 0 }),
                    },
                },
                Value::Bool(_) | Value::Int(_) | Value::Str(_) => i,
                _ => return Some(ImageOrder { src: [0; MAX_KEYS], known: 0, used: 0 }),
            };
            o.src[j] = i as u8;
        }
        o.known = n;
        Some(o)
    }

    fn at(&mut self, mode: CmpMode, p: PermMap, n: usize, key: Keys, j: usize) -> tlx_value::Result<usize> {
        if j < self.known {
            return Ok(self.src[j] as usize);
        }
        debug_assert_eq!(j, self.known);
        let mut least: Option<usize> = None;
        for i in (0..n).filter(|&i| self.used & (1u64 << i) == 0) {
            let less = match least {
                None => true,
                Some(m) => cmp_images_mode(mode, p, key(i), p, key(m))? == Ordering::Less,
            };
            if less {
                least = Some(i);
            }
        }
        let i = least.expect("an unused value");
        self.src[j] = i as u8;
        self.used |= 1u64 << i;
        self.known += 1;
        Ok(i)
    }
}

/// The variables of the state `vals` by increasing size (number of nodes;
/// ties by position), which permutations of model values preserve.
pub(super) fn size_order(vals: &[Value]) -> Vec<usize> {
    fn size(v: &Value) -> usize {
        match v {
            Value::Set(es) | Value::Tuple(es) => 1 + es.iter().map(size).sum::<usize>(),
            Value::Record(fs) => 1 + fs.iter().map(|(_, x)| size(x)).sum::<usize>(),
            Value::Fcn(ps, _) => 1 + ps.iter().map(|(k, x)| size(k) + size(x)).sum::<usize>(),
            _ => 1,
        }
    }
    let mut order: Vec<(usize, usize)> = vals.iter().enumerate().map(|(i, v)| (size(v), i)).collect();
    order.sort_unstable();
    order.into_iter().map(|(_, i)| i).collect()
}

#[derive(Clone, Default)]
enum GroupKind {
    #[default]
    Empty,
    Factorized(FactorizedGroup),
    Explicit {
        perms: Vec<FastPerm>,
        moved: Vec<u32>,
        raw: Vec<Perm>,
    },
}

/// The SYMMETRY group (without the identity) in the forms the
/// fingerprints use.
#[derive(Clone, Default)]
pub(super) struct Group {
    kind: GroupKind,
    /// On-demand materialized `Perm` maps for `InterpModel::symmetry_maps()`
    /// when `kind` is `Factorized` with `order <= MAX_MATERIALIZED_ORDER`.
    maps: Arc<OnceLock<Vec<Perm>>>,
    /// Cache keys must not alias another group (or a rebuilt model).
    id: u64,
}

enum FactorChoice<R> {
    Done(Option<R>),
    FallbackOrdered,
}

impl Group {
    fn next_id() -> u64 {
        static NEXT_ID: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(1);
        NEXT_ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    }

    #[cfg(test)]
    fn from_factors(factors: Vec<Vec<Sym>>) -> Group {
        Self::from_factors_with_fallback(factors, FallbackOrder::DisjointFull).unwrap()
    }

    /// Build a group from disjoint full symmetric-group factors, for a
    /// certified reduction that enlarges a declared `SYMMETRY`.
    pub(in crate::model) fn from_factor_sets(factors: Vec<Vec<Sym>>) -> EResult<Group> {
        Self::from_factors_with_fallback(factors, FallbackOrder::DisjointFull)
    }

    fn from_factors_with_fallback(factors: Vec<Vec<Sym>>, fallback: FallbackOrder) -> EResult<Group> {
        if factors.is_empty() {
            return Ok(Group::default());
        }
        Ok(Group {
            kind: GroupKind::Factorized(FactorizedGroup::new(factors, fallback)?),
            maps: Arc::new(OnceLock::new()),
            id: Self::next_id(),
        })
    }

    /// Build a group from a generator list, recognizing disjoint symmetric-group
    /// products without running group closure, and falling back to explicit
    /// closure for arbitrary subgroups.
    pub(super) fn from_generators(gens: Vec<Perm>) -> EResult<Group> {
        if gens.iter().all(HashMap::is_empty) {
            return Ok(Group::default());
        }
        if let Some(factors) = recognize_disjoint_factors(&gens) {
            let mut fg = FactorizedGroup::new(factors, FallbackOrder::DisjointFull)?;
            let flat_gens: Vec<Vec<u16>> = gens.iter().filter(|p| !p.is_empty()).map(|p| fg.perm_to_img(p)).collect();
            fg.set_fallback(FallbackOrder::ExplicitGens(flat_gens));
            return Ok(Group { kind: GroupKind::Factorized(fg), maps: Arc::new(OnceLock::new()), id: Self::next_id() });
        }
        Ok(Self::explicit(closure(gens)))
    }

    fn explicit(raw: Vec<Perm>) -> Group {
        if raw.is_empty() {
            return Group::default();
        }
        let perms: Vec<FastPerm> = raw.iter().map(FastPerm::new).collect();
        let mut moved: Vec<u32> = perms.iter().flat_map(|p| p.0.iter().map(|(k, _)| *k)).collect();
        moved.sort_unstable();
        moved.dedup();
        Group { kind: GroupKind::Explicit { perms, moved, raw }, maps: Arc::new(OnceLock::new()), id: Self::next_id() }
    }

    pub(super) fn is_empty(&self) -> bool {
        matches!(self.kind, GroupKind::Empty)
    }

    /// The model values moved by at least one element of this group.
    pub(super) fn moved_syms(&self) -> HashSet<Sym> {
        match &self.kind {
            GroupKind::Empty => HashSet::new(),
            GroupKind::Factorized(fg) => fg.factors.iter().flat_map(|f| f.keys.iter().copied()).collect(),
            GroupKind::Explicit { raw, .. } => raw.iter().flat_map(|p| p.keys().copied()).collect(),
        }
    }

    /// Read-only per-factor sorted `Sym` slices when this group is a disjoint
    /// product of full symmetric groups `S_{n_1} x ... x S_{n_k}`.
    pub(super) fn symmetry_factors(&self) -> Option<Vec<&[Sym]>> {
        match &self.kind {
            GroupKind::Factorized(fg) => Some(fg.factors.iter().map(|f| f.keys.as_slice()).collect()),
            _ => None,
        }
    }

    /// The non-identity permutation maps for `InterpModel::symmetry_maps()`,
    /// materialized on demand for factorized groups while `|G| <= 720`.
    pub(super) fn symmetry_maps(&self) -> &[Perm] {
        match &self.kind {
            GroupKind::Empty => &[],
            GroupKind::Explicit { raw, .. } => raw,
            GroupKind::Factorized(fg) => {
                if fg.order > MAX_MATERIALIZED_ORDER {
                    return &[];
                }
                self.maps.get_or_init(|| fg.materialize_perms())
            }
        }
    }

    /// Indices into `symmetry_maps()` in the order the fallible ordered walk
    /// visits the non-identity permutations (`for_each_perm_tlc_order`). The
    /// interpreter uses this order whenever a TLC comparison may fail, so a
    /// compiled path that decides on encodings must visit permutations the
    /// same way: the first incomparable pair it reaches (and the resulting
    /// evaluation error) depends on it.
    ///
    /// `None` when the group is too large to materialize (no explicit maps).
    pub(super) fn symmetry_maps_tlc_order(&self) -> Option<Vec<usize>> {
        match &self.kind {
            GroupKind::Empty => Some(Vec::new()),
            GroupKind::Explicit { perms, .. } => Some((0..perms.len()).collect()),
            GroupKind::Factorized(fg) => {
                if fg.order > MAX_MATERIALIZED_ORDER {
                    return None;
                }
                let mut order = Vec::with_capacity(fg.order.saturating_sub(1) as usize);
                fg.for_each_perm_tlc_order(|img| {
                    let rank = fg.rank_of_img(img).expect("a non-identity permutation has a rank");
                    order.push(rank);
                    Ok(std::ops::ControlFlow::Continue(()))
                })
                .ok()?;
                Some(order)
            }
        }
    }

    /// The permutation giving the least state (in TLC's value order, comparing
    /// the variables one by one in `order`) of the orbit of `vals`, or `None`
    /// when that is `vals` itself.
    pub(super) fn least_perm(&self, vals: &mut StateVals, order: &[usize]) -> EResult<Option<ChosenPerm<'_>>> {
        self.choose_perm(vals, order, CmpMode::Tlc, false)
    }

    /// Like `least_perm`, with VIEW's fixed variable order enabling first-variable
    /// record-key bag caching.
    pub(super) fn least_view_perm(&self, vals: &mut StateVals, order: &[usize]) -> EResult<Option<ChosenPerm<'_>>> {
        self.choose_perm(vals, order, CmpMode::Tlc, true)
    }

    /// Canonicalize a single projected value under `try_total_cmp` (used by
    /// `InterpModel::projected_orbit` when internal sentinels may mix types).
    pub(super) fn least_total_perm(&self, val: &Value) -> EResult<Option<ChosenPerm<'_>>> {
        match &self.kind {
            GroupKind::Empty => Ok(None),
            GroupKind::Factorized(_) => {
                let slice = std::slice::from_ref(val);
                self.choose_perm(&mut StateVals::Given(slice), &[0], CmpMode::Total, false)
            }
            GroupKind::Explicit { perms, .. } => {
                let mut best: Option<(usize, Value)> = None;
                for (i, p) in perms.iter().enumerate() {
                    let Some(image) = p.apply(val)? else { continue };
                    let cur = best.as_ref().map_or(val, |(_, v)| v);
                    if try_total_cmp(&image, cur)?.is_lt() {
                        best = Some((i, image));
                    }
                }
                Ok(best.map(|(i, _)| ChosenPerm::borrowed(&perms[i])))
            }
        }
    }

    /// Canonicalize a state under `try_total_cmp` (used by compiled escape
    /// mode for genuine outlier states under factorized symmetry).
    pub(super) fn least_total_state_perm(&self, vals: &[Value], order: &[usize]) -> EResult<Option<ChosenPerm<'_>>> {
        match &self.kind {
            GroupKind::Empty => Ok(None),
            GroupKind::Factorized(_) => self.choose_perm(&mut StateVals::Given(vals), order, CmpMode::Total, false),
            GroupKind::Explicit { perms, moved, .. } => {
                // Explicit groups are small (`<= 720`): compare under `try_total_cmp`.
                let mut best: Option<usize> = None;
                let mut support = Vec::new();
                let mut sv = StateVals::Given(vals);
                let dedup = !collect_support(moved, &mut sv, order, &mut support);
                let mut key = Vec::new();
                let mut seen: Vec<Vec<u32>> = Vec::new();
                'perm: for (pi, p) in perms.iter().enumerate() {
                    if dedup && p.images(&support, &mut key) {
                        if key == support || seen.contains(&key) {
                            continue;
                        }
                        seen.push(key.clone());
                    }
                    let q = best.map_or(PermMap::Id, |q| PermMap::Fast(&perms[q]));
                    for &i in order {
                        match cmp_images_mode(CmpMode::Total, PermMap::Fast(p), &vals[i], q, &vals[i])? {
                            Ordering::Greater => continue 'perm,
                            Ordering::Equal => {}
                            Ordering::Less => {
                                best = Some(pi);
                                continue 'perm;
                            }
                        }
                    }
                }
                Ok(best.map(|i| ChosenPerm::borrowed(&perms[i])))
            }
        }
    }

    /// Flat target-index image table of the TLC-least permutation for a
    /// factorized group of any order (including `|G| > 720`), or `None` when
    /// identity is least or the group is not factorized.
    pub(super) fn least_factor_perm(&self, vals: &mut StateVals, order: &[usize], cache_bags: bool) -> EResult<Option<Vec<u16>>> {
        let GroupKind::Factorized(fg) = &self.kind else {
            return Ok(None);
        };
        match self.choose_factorized(fg, vals, order, CmpMode::Tlc, cache_bags, |win| {
            let mut img = vec![0u16; fg.total_keys];
            win.fill_img_slice(fg, &mut img);
            img
        })? {
            FactorChoice::Done(img) => Ok(img),
            FactorChoice::FallbackOrdered => choose_factorized_lazy_ordered(fg, vals, order),
        }
    }

    /// Index in `symmetry_maps()` of the permutation giving the least state of
    /// `vals` (used by `tlx-compile` `SymView` when `|G| <= 720`).
    pub(super) fn least_perm_index(&self, vals: &mut StateVals, order: &[usize], cache_bags: bool) -> EResult<Option<usize>> {
        match &self.kind {
            GroupKind::Empty => Ok(None),
            GroupKind::Explicit { perms, moved, .. } => self.choose_explicit(perms, moved, vals, order, cache_bags),
            GroupKind::Factorized(fg) => match self.choose_factorized(fg, vals, order, CmpMode::Tlc, cache_bags, |win| fg.rank_of(win))? {
                FactorChoice::Done(rank) => Ok(rank.flatten()),
                FactorChoice::FallbackOrdered => Ok(choose_factorized_lazy_ordered(fg, vals, order)?.and_then(|img| fg.rank_of_img(&img))),
            },
        }
    }

    fn choose_perm(&self, vals: &mut StateVals, order: &[usize], mode: CmpMode, cache_bags: bool) -> EResult<Option<ChosenPerm<'_>>> {
        match &self.kind {
            GroupKind::Empty => Ok(None),
            GroupKind::Explicit { perms, moved, .. } => {
                debug_assert!(mode == CmpMode::Tlc);
                Ok(self.choose_explicit(perms, moved, vals, order, cache_bags)?.map(|i| ChosenPerm::borrowed(&perms[i])))
            }
            GroupKind::Factorized(fg) => match self.choose_factorized(fg, vals, order, mode, cache_bags, |win| fg.to_chosen_perm(win))? {
                FactorChoice::Done(p) => Ok(p),
                FactorChoice::FallbackOrdered => {
                    Ok(choose_factorized_lazy_ordered(fg, vals, order)?.map(|img| ChosenPerm::factor_heap(fg, img)))
                }
            },
        }
    }

    fn choose_factorized<R>(
        &self,
        fg: &FactorizedGroup,
        vals: &mut StateVals,
        order: &[usize],
        mode: CmpMode,
        cache_bags: bool,
        finish: impl FnOnce(&Partition) -> R,
    ) -> EResult<FactorChoice<R>> {
        let check_cmp_safe = mode == CmpMode::Tlc;
        LEAST_BUF.with(|b| {
            let mut b = b.borrow_mut();
            let LeastBuf { bags, factor, .. } = &mut *b;
            let FactorScratch { part, refine } = factor;
            part.reset(fg);

            let mut cands: Option<Vec<Partition>> = None;

            for (idx, &var) in order.iter().enumerate() {
                if let Some(cs) = &cands {
                    if cs.len() == 1 && cs[0].is_complete() {
                        break;
                    }
                    let v = vals.get(var);
                    if check_cmp_safe && !is_orbit_cmp_safe(v, fg) {
                        return Ok(FactorChoice::FallbackOrdered);
                    }
                    let next = minimize_across_candidates(fg, cands.take().unwrap(), v, mode)?;
                    cands = Some(next);
                    continue;
                }
                if part.is_complete() {
                    break;
                }
                let v = vals.get(var);
                if check_cmp_safe && !is_orbit_cmp_safe(v, fg) {
                    return Ok(FactorChoice::FallbackOrdered);
                }
                if cache_bags && idx == 0 && mode == CmpMode::Tlc && fg.order >= 6 && is_record_key_bag(v) && has_any_moved_atom(v, fg) {
                    let cached = bags.factor_candidates(self.id, fg, v)?;
                    cands = Some(cached.to_vec());
                    continue;
                }
                match refine_deterministic(fg, part, v, mode, refine)? {
                    DetOutcome::Done => {}
                    DetOutcome::NeedBranch(pending) => {
                        let mut cs = vec![part.clone()];
                        for item in pending {
                            cs = minimize_across_candidates(fg, cs, item, mode)?;
                        }
                        cands = Some(cs);
                    }
                }
            }

            let out = match cands {
                None => {
                    if part.contains_identity(fg) {
                        None
                    } else {
                        part.canonicalize_unpinned_blocks(fg);
                        Some(finish(part))
                    }
                }
                Some(mut cs) => {
                    if cs.iter().any(|p| p.contains_identity(fg)) {
                        None
                    } else {
                        let win = &mut cs[0];
                        win.canonicalize_unpinned_blocks(fg);
                        Some(finish(win))
                    }
                }
            };
            Ok(FactorChoice::Done(out))
        })
    }

    fn choose_explicit(
        &self,
        perms: &[FastPerm],
        moved: &[u32],
        vals: &mut StateVals,
        order: &[usize],
        cache_bags: bool,
    ) -> EResult<Option<usize>> {
        LEAST_BUF.with(|b| {
            let mut b = b.borrow_mut();
            let LeastBuf { support, key, seen, orders, bags, .. } = &mut *b;
            support.clear();
            let dedup = !collect_support(moved, vals, order, support);
            if let Some((&first, rest)) = order.split_first() {
                let v = vals.get(first);
                if cache_bags && !dedup && perms.len() >= 5 && is_record_key_bag(v) {
                    let candidates = bags.explicit_candidates(self.id, perms, v)?;
                    let mut best = candidates[0];
                    orders.clear();
                    orders.resize_with(vals.len(), || None);
                    'candidate: for &pi in &candidates[1..] {
                        let p = pi.map_or(PermMap::Id, |i| PermMap::Fast(&perms[i]));
                        let q = best.map_or(PermMap::Id, |i| PermMap::Fast(&perms[i]));
                        for &i in rest {
                            let v = vals.get(i);
                            match cmp_images_with_mode(CmpMode::Tlc, p, v, q, v, &mut orders[i])? {
                                Ordering::Greater => continue 'candidate,
                                Ordering::Equal => {}
                                Ordering::Less => {
                                    best = pi;
                                    orders.iter_mut().for_each(|o| *o = None);
                                    continue 'candidate;
                                }
                            }
                        }
                    }
                    return Ok(best);
                }
            }
            seen.clear();
            orders.clear();
            orders.resize_with(vals.len(), || None);
            let mut best: Option<usize> = None;
            'perm: for (pi, p) in perms.iter().enumerate() {
                if dedup && p.images(support, key) {
                    if *key == *support || seen.contains(key) {
                        continue;
                    }
                    seen.push(key.clone());
                }
                let q = best.map_or(PermMap::Id, |q| PermMap::Fast(&perms[q]));
                for &i in order {
                    let v = vals.get(i);
                    match cmp_images_with_mode(CmpMode::Tlc, PermMap::Fast(p), v, q, v, &mut orders[i])? {
                        Ordering::Greater => continue 'perm,
                        Ordering::Equal => {}
                        Ordering::Less => {
                            best = Some(pi);
                            orders.iter_mut().for_each(|o| *o = None);
                            continue 'perm;
                        }
                    }
                }
            }
            Ok(best)
        })
    }
}

/// Cap on distinct support images retained in the fallible ordered walk so
/// pathological large groups with incomparable payloads never retain factorial
/// memory.
const MAX_FALLBACK_SEEN: usize = 4096;

fn collect_factor_support(
    fg: &FactorizedGroup,
    vals: &mut StateVals,
    order: &[usize],
    out: &mut Vec<(usize, u16)>,
    obs_per_factor: &mut [usize],
) -> bool {
    fn walk(v: &Value, fg: &FactorizedGroup, out: &mut Vec<(usize, u16)>, obs_per_factor: &mut [usize]) -> bool {
        match v {
            Value::ModelValue(m) => {
                if let Some((g, k)) = fg.lookup(*m) {
                    let entry = (fg.factors[g].offset + k, k as u16);
                    if !out.contains(&entry) {
                        out.push(entry);
                        obs_per_factor[g] += 1;
                    }
                }
                out.len() == fg.total_keys
            }
            Value::Set(es) | Value::Tuple(es) => es.iter().any(|e| walk(e, fg, out, obs_per_factor)),
            Value::Record(fs) => fs.iter().any(|(_, e)| walk(e, fg, out, obs_per_factor)),
            Value::Fcn(ps, _) => ps.iter().any(|(k, e)| walk(k, fg, out, obs_per_factor) || walk(e, fg, out, obs_per_factor)),
            Value::LazySet(_) | Value::LazyFcn(_) => true,
            Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => false,
        }
    }
    order.iter().any(|&i| walk(vals.get(i), fg, out, obs_per_factor))
}

/// Lazily walk permutations of `fg` in exact TLC normalized union & composition
/// order (without materializing `Perm` maps or capping at order 720) when
/// `!is_orbit_cmp_safe`, returning the winning flat image table (or `None` for
/// identity).
fn choose_factorized_lazy_ordered(fg: &FactorizedGroup, vals: &mut StateVals, order: &[usize]) -> EResult<Option<Vec<u16>>> {
    let mut support: Vec<(usize, u16)> = Vec::new();
    let mut obs_per_factor: Vec<usize> = vec![0; fg.factors.len()];
    let has_lazy_or_full = collect_factor_support(fg, vals, order, &mut support, &mut obs_per_factor);
    // A bijection on factor `g` is uniquely determined once `|K_g| - 1` atoms
    // are observed; skip `seen` completely when every factor has at most one
    // unobserved atom (zero duplicate restrictions are possible).
    let dedup = !has_lazy_or_full && fg.factors.iter().enumerate().any(|(g, f)| obs_per_factor[g] + 1 < f.keys.len());
    // Exact number of distinct non-identity restrictions to `support` across
    // the whole product group: `prod_g P(|K_g|, obs_g) - 1`. Once `seen` holds
    // all of them, every remaining permutation would duplicate an already-tested
    // image and the walk can stop immediately.
    let total_nonid_restrictions = if dedup {
        let mut total: u128 = 1;
        for (g, f) in fg.factors.iter().enumerate() {
            let n = f.keys.len() as u128;
            let s = obs_per_factor[g] as u128;
            for k in 0..s {
                total = total.saturating_mul(n - k);
            }
        }
        total.saturating_sub(1)
    } else {
        u128::MAX
    };
    let mut seen: HashSet<Vec<u16>> = HashSet::new();
    let mut orders: Vec<Option<ImageOrder>> = std::iter::repeat_with(|| None).take(vals.len()).collect();
    let mut best_img: Option<Vec<u16>> = None;
    fg.for_each_perm_tlc_order(|img| {
        use std::ops::ControlFlow;
        if dedup {
            if support.iter().all(|&(flat, k)| img[flat] == k) {
                return Ok(ControlFlow::Continue(()));
            }
            let key: Vec<u16> = support.iter().map(|&(flat, _)| img[flat]).collect();
            if seen.contains(&key) {
                return Ok(ControlFlow::Continue(()));
            }
            if seen.len() < MAX_FALLBACK_SEEN {
                seen.insert(key);
            }
        }
        let q = best_img.as_deref().map_or(PermMap::Id, |b| PermMap::Table(fg, b));
        for &i in order {
            let v = vals.get(i);
            match cmp_images_with_mode(CmpMode::Tlc, PermMap::Table(fg, img), v, q, v, &mut orders[i])? {
                Ordering::Greater => break,
                Ordering::Equal => {}
                Ordering::Less => {
                    best_img = Some(img.to_vec());
                    orders.iter_mut().for_each(|o| *o = None);
                    break;
                }
            }
        }
        if dedup && seen.len() as u128 >= total_nonid_restrictions {
            Ok(ControlFlow::Break(()))
        } else {
            Ok(ControlFlow::Continue(()))
        }
    })?;
    Ok(best_img)
}

fn collect_support(moved: &[u32], vals: &mut StateVals, order: &[usize], out: &mut Vec<u32>) -> bool {
    fn walk(v: &Value, moved: &[u32], out: &mut Vec<u32>) -> bool {
        match v {
            Value::ModelValue(m) => {
                let id = m.id();
                if moved.binary_search(&id).is_ok() && !out.contains(&id) {
                    out.push(id);
                }
                out.len() == moved.len()
            }
            Value::Set(es) | Value::Tuple(es) => es.iter().any(|e| walk(e, moved, out)),
            Value::Record(fs) => fs.iter().any(|(_, e)| walk(e, moved, out)),
            Value::Fcn(ps, _) => ps.iter().any(|(k, e)| walk(k, moved, out) || walk(e, moved, out)),
            Value::LazySet(_) | Value::LazyFcn(_) => true,
            Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => false,
        }
    }
    order.iter().any(|&i| walk(vals.get(i), moved, out))
}

/// The values of a state, given or decoded as they are needed.
pub enum StateVals<'a> {
    Given(&'a [Value]),
    /// `decode(i)` is the value of variable `i`; `vals` those decoded so far.
    Decoded {
        vals: Vec<Option<Value>>,
        decode: &'a dyn Fn(usize) -> Value,
    },
}

impl<'a> StateVals<'a> {
    pub fn decoded(n: usize, decode: &'a dyn Fn(usize) -> Value) -> StateVals<'a> {
        StateVals::Decoded { vals: vec![None; n], decode }
    }

    pub(super) fn len(&self) -> usize {
        match self {
            StateVals::Given(v) => v.len(),
            StateVals::Decoded { vals, .. } => vals.len(),
        }
    }

    fn get(&mut self, i: usize) -> &Value {
        match self {
            StateVals::Given(v) => &v[i],
            StateVals::Decoded { vals, decode } => vals[i].get_or_insert_with(|| decode(i)),
        }
    }
}

/// Cached minimal candidates for a first-variable record-key bag under VIEW.
enum BagCandidates {
    Explicit(Arc<[Option<usize>]>),
    Factorized(Arc<[Partition]>),
}

struct BagEntry {
    group: u64,
    bag: Arc<[(Value, Value)]>,
    candidates: BagCandidates,
    bytes: usize,
}

#[derive(Default)]
struct BagCache {
    slots: Vec<Option<BagEntry>>,
    bytes: usize,
    published: tlx_runtime::cache_mem::Published,
}

impl BagCache {
    const SLOTS: usize = 1024;

    fn budget_and_slot(&mut self, group_id: u64, bag: &Arc<[(Value, Value)]>) -> (usize, usize) {
        let budget = (tlx_runtime::cache_mem::share() / 8).min(4 << 20);
        if self.bytes > budget {
            self.slots.clear();
            self.bytes = 0;
            self.published.update(0);
        }
        let hash = tlx_base::hash::fmix64(Arc::as_ptr(bag) as *const () as usize as u64 ^ group_id.rotate_left(17));
        let slot = hash as usize & (Self::SLOTS - 1);
        (budget, slot)
    }

    fn insert(&mut self, slot: usize, budget: usize, group_id: u64, bag: &Arc<[(Value, Value)]>, value: &Value, candidates: BagCandidates) {
        let cand_bytes = match &candidates {
            BagCandidates::Explicit(c) => std::mem::size_of_val(&**c),
            BagCandidates::Factorized(c) => {
                std::mem::size_of_val(&**c).saturating_add(c.iter().map(Partition::heap_bytes).fold(0usize, usize::saturating_add))
            }
        };
        let bytes = retained_bytes(value, budget).saturating_add(cand_bytes);
        let table_bytes = Self::SLOTS * std::mem::size_of::<Option<BagEntry>>();
        if bytes.saturating_add(table_bytes) <= budget {
            if self.slots.is_empty() {
                self.slots.resize_with(Self::SLOTS, || None);
                self.bytes = table_bytes;
            }
            let old = self.slots[slot].take().map_or(0, |e| e.bytes);
            self.bytes -= old;
            if self.bytes.saturating_add(bytes) > budget {
                self.slots.iter_mut().for_each(|e| *e = None);
                self.bytes = table_bytes;
            }
            self.slots[slot] = Some(BagEntry { group: group_id, bag: bag.clone(), candidates, bytes });
            self.bytes += bytes;
            self.published.update(self.bytes);
        }
    }

    fn explicit_candidates(&mut self, group_id: u64, perms: &[FastPerm], value: &Value) -> EResult<Arc<[Option<usize>]>> {
        let Value::Fcn(bag, _) = value else { unreachable!("record-key bag") };
        let (budget, slot) = self.budget_and_slot(group_id, bag);
        if let Some(Some(e)) = self.slots.get(slot) {
            if e.group == group_id && Arc::ptr_eq(&e.bag, bag) {
                if let BagCandidates::Explicit(c) = &e.candidates {
                    return Ok(c.clone());
                }
            }
        }
        let mut candidates = vec![None];
        let mut best = None;
        let mut order = None;
        for (i, p) in perms.iter().enumerate() {
            let q = best.map_or(PermMap::Id, |bi: usize| PermMap::Fast(&perms[bi]));
            match cmp_images_with_mode(CmpMode::Tlc, PermMap::Fast(p), value, q, value, &mut order)? {
                Ordering::Greater => {}
                Ordering::Equal => candidates.push(Some(i)),
                Ordering::Less => {
                    candidates.clear();
                    candidates.push(Some(i));
                    best = Some(i);
                    order = None;
                }
            }
        }
        let candidates: Arc<[Option<usize>]> = candidates.into();
        self.insert(slot, budget, group_id, bag, value, BagCandidates::Explicit(candidates.clone()));
        Ok(candidates)
    }

    fn factor_candidates(&mut self, group_id: u64, fg: &FactorizedGroup, value: &Value) -> EResult<Arc<[Partition]>> {
        let Value::Fcn(bag, _) = value else { unreachable!("record-key bag") };
        let (budget, slot) = self.budget_and_slot(group_id, bag);
        if let Some(Some(e)) = self.slots.get(slot) {
            if e.group == group_id && Arc::ptr_eq(&e.bag, bag) {
                if let BagCandidates::Factorized(c) = &e.candidates {
                    return Ok(c.clone());
                }
            }
        }
        let mut part = Partition::default();
        part.reset(fg);
        let parts = branch_general_value(fg, part, value, CmpMode::Tlc)?;
        let candidates: Arc<[Partition]> = parts.into();
        self.insert(slot, budget, group_id, bag, value, BagCandidates::Factorized(candidates.clone()));
        Ok(candidates)
    }
}

fn retained_bytes(v: &Value, cap: usize) -> usize {
    let mut bytes = std::mem::size_of::<Value>();
    match v {
        Value::Tuple(es) | Value::Set(es) => {
            for e in es.iter() {
                bytes = bytes.saturating_add(retained_bytes(e, cap));
                if bytes > cap {
                    break;
                }
            }
        }
        Value::Record(fs) => {
            for (_, e) in fs.iter() {
                bytes = bytes.saturating_add(std::mem::size_of::<Sym>() + retained_bytes(e, cap));
                if bytes > cap {
                    break;
                }
            }
        }
        Value::Fcn(ps, _) => {
            for (k, v) in ps.iter() {
                bytes = bytes.saturating_add(retained_bytes(k, cap)).saturating_add(retained_bytes(v, cap));
                if bytes > cap {
                    break;
                }
            }
        }
        Value::LazySet(_) | Value::LazyFcn(_) => return cap.saturating_add(1),
        _ => {}
    }
    bytes
}

#[derive(Default)]
struct LeastBuf {
    support: Vec<u32>,
    key: Vec<u32>,
    seen: Vec<Vec<u32>>,
    orders: Vec<Option<ImageOrder>>,
    bags: BagCache,
    factor: FactorScratch,
}

thread_local! {
    static LEAST_BUF: std::cell::RefCell<LeastBuf> = std::cell::RefCell::default();
}

/// The fingerprint of a sequence of fingerprints.
pub(super) fn combine_fps(fps: &[u64]) -> EResult<u64> {
    let mut fp = tlx_value::fingerprint::Fingerprinter::new();
    for &h in fps {
        fp.add(&Value::Int(h as i64))?;
    }
    Ok(fp.finish())
}

/// The permutation a function over model values denotes.
fn perm_of(f: &Value) -> EResult<Perm> {
    let mut m = HashMap::new();
    for k in ops::enumerate_normalized(&ops::domain(f)?)? {
        let Value::ModelValue(sym) = k else {
            return Err(EvalError::new(format!("SYMMETRY permutations must map model values, found {k}")));
        };
        let img = ops::apply(f, &k)?;
        if img != k {
            m.insert(sym, img);
        }
    }
    Ok(m)
}

fn compose(p: &Perm, q: &Perm) -> Perm {
    let mut r = HashMap::new();
    let keys: HashSet<Sym> = p.keys().chain(q.keys()).copied().collect();
    for k in keys {
        let mid = q.get(&k).cloned().unwrap_or(Value::ModelValue(k));
        let img = match &mid {
            Value::ModelValue(m) => p.get(m).cloned().unwrap_or(mid.clone()),
            _ => mid.clone(),
        };
        if img != Value::ModelValue(k) {
            r.insert(k, img);
        }
    }
    r
}

fn closure(gens: Vec<Perm>) -> Vec<Perm> {
    let mut perms: Vec<Perm> = Vec::new();
    for g in gens {
        if !g.is_empty() && !perms.contains(&g) {
            perms.push(g);
        }
    }
    close_under_composition(&mut perms);
    perms
}

fn close_under_composition(perms: &mut Vec<Perm>) {
    let generators = perms.len();
    let mut start = 0;
    loop {
        let end = perms.len();
        for i in 0..generators {
            for j in start..end {
                let c = compose(&perms[i], &perms[j]);
                if !c.is_empty() && !perms.contains(&c) {
                    perms.push(c);
                }
            }
        }
        if perms.len() == end {
            break;
        }
        start = end;
    }
}

#[cfg(test)]
thread_local! {
    static CMP_CALLS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
