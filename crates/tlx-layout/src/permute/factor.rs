//! Factorized symmetric-group product plans.
//!
//! [`FactorPlan`]s apply any element of a disjoint product of symmetric groups
//! to an encoded value without materializing the full group (`|G|` explicit
//! permutation vectors), driven by a flat per-key image table.

use std::sync::Arc;

use tlx_base::partition::FactorLayout;
use tlx_value::{Sym, Value};

use super::explicit::sort_elems;
use crate::dynval;
use crate::layout::{bitset_universe, rank, words, BitPos, FieldGroup, FieldLayout, FieldLoc, MapDims, SlotLayout};
use crate::shape::{binom, FcnWitness};
use crate::Shape;

/// One full symmetric-group factor `Sym(K_g)` over `keys` sorted strictly
/// ascending in TLC order (`Sym::cmp`).
#[derive(Clone, Debug)]
pub struct FactorDesc {
    pub keys: Box<[Sym]>,
    /// Pre-built `Value::ModelValue(k)` matching `keys` for zero-alloc lookup.
    pub values: Box<[Value]>,
    /// Start offset of this factor in flat per-key target-index tables (`img`).
    pub offset: usize,
}

/// Read-only descriptor of a disjoint product `S_{n_1} x ... x S_{n_k}` used to
/// compile and apply per-variable [`FactorPlan`]s without materializing `|G|`
/// explicit permutation tables.
#[derive(Clone, Debug)]
pub struct FactorGroupSpec {
    pub factors: Box<[FactorDesc]>,
    /// Sorted by `sym.id()`: `(sym_id, factor_idx, key_idx)`.
    key_index: Box<[(u32, u16, u16)]>,
    min_id: u32,
    max_id: u32,
    pub total_keys: usize,
}

impl FactorGroupSpec {
    /// Build a factorized group descriptor from per-factor sorted `Sym` slices.
    pub fn new(raw_factors: &[&[Sym]]) -> Self {
        let mut factors = Vec::with_capacity(raw_factors.len());
        let mut key_index = Vec::new();
        let mut offset = 0usize;
        for (g, &keys) in raw_factors.iter().enumerate() {
            debug_assert!(keys.len() >= 2);
            debug_assert!(keys.windows(2).all(|w| w[0] < w[1]));
            for (k, &s) in keys.iter().enumerate() {
                key_index.push((s.id(), g as u16, k as u16));
            }
            let values: Box<[Value]> = keys.iter().copied().map(Value::ModelValue).collect();
            factors.push(FactorDesc { keys: keys.into(), values, offset });
            offset += keys.len();
        }
        key_index.sort_unstable_by_key(|&(id, _, _)| id);
        let min_id = key_index.first().map_or(u32::MAX, |&(id, _, _)| id);
        let max_id = key_index.last().map_or(0, |&(id, _, _)| id);
        Self { factors: factors.into(), key_index: key_index.into(), min_id, max_id, total_keys: offset }
    }

    #[inline]
    pub fn lookup(&self, m: Sym) -> Option<(usize, usize)> {
        let id = m.id();
        if id < self.min_id || id > self.max_id {
            return None;
        }
        if self.key_index.len() <= 8 {
            for &(k, g, ki) in self.key_index.iter() {
                if k == id {
                    return Some((g as usize, ki as usize));
                }
                if k > id {
                    return None;
                }
            }
            return None;
        }
        let idx = self.key_index.binary_search_by_key(&id, |&(k, _, _)| k).ok()?;
        let (_, g, k) = self.key_index[idx];
        Some((g as usize, k as usize))
    }

    /// Fill `dst[..self.total_keys]` with the identity target-index table.
    #[inline]
    pub fn fill_identity_img(&self, dst: &mut [u16]) {
        for f in self.factors.iter() {
            let off = f.offset;
            for i in 0..f.keys.len() {
                dst[off + i] = i as u16;
            }
        }
    }

    pub fn identity_img(&self) -> Vec<u16> {
        let mut img = vec![0u16; self.total_keys];
        self.fill_identity_img(&mut img);
        img
    }

    /// Image of model value `m` under flat image table `img`, or `None` when
    /// fixed (for `tlx_value::ops::permute_shared`).
    #[inline]
    pub fn map_sym(&self, m: Sym, img: &[u16]) -> Option<&Value> {
        let (g, k) = self.lookup(m)?;
        let f = &self.factors[g];
        let t = img[f.offset + k] as usize;
        (t != k).then_some(&f.values[t])
    }
}

impl FactorLayout for FactorGroupSpec {
    #[inline]
    fn total_keys(&self) -> usize {
        self.total_keys
    }

    #[inline]
    fn num_factors(&self) -> usize {
        self.factors.len()
    }

    #[inline]
    fn factor_range(&self, g: usize) -> (usize, usize) {
        let f = &self.factors[g];
        (f.offset, f.keys.len())
    }
}

/// Compiled atom-code mapping for `Shape::Atom(u)` under a [`FactorGroupSpec`].
#[derive(Clone, Debug)]
pub struct AtomTable {
    /// For each atom code `c in 0..u.len()`: `Some((factor_idx, key_idx))` if
    /// moved by `G`, else `None` (fixed atom).
    pub code_to_key: Box<[Option<(u16, u16)>]>,
    /// Indexed by `factor.offset + key_idx`: atom code in `u` (`u64::MAX` if
    /// that factor does not occur in `u`).
    pub key_to_code: Box<[u64]>,
    /// Factor indices that occur in `u`.
    pub active_factors: Box<[u16]>,
    /// `Some(g)` iff `u` consists solely of factor `g`'s keys with `code == key_idx`.
    pub direct_factor: Option<u16>,
}

impl AtomTable {
    /// Compile an atom table for sorted universe `u`.
    /// Returns `None` if `u` is not closed under `fg` (contains a proper
    /// non-empty subset of some factor `K_g`), `Some(None)` if `u` contains no
    /// moved atoms, and `Some(Some(table))` otherwise.
    pub fn compile(u: &[Value], fg: &FactorGroupSpec) -> Option<Option<Arc<AtomTable>>> {
        let mut code_to_key = vec![None; u.len()];
        let mut key_to_code = vec![u64::MAX; fg.total_keys];
        let mut counts = vec![0usize; fg.factors.len()];
        for (code, v) in u.iter().enumerate() {
            if let Value::ModelValue(m) = v {
                if let Some((g, k)) = fg.lookup(*m) {
                    code_to_key[code] = Some((g as u16, k as u16));
                    key_to_code[fg.factors[g].offset + k] = code as u64;
                    counts[g] += 1;
                }
            }
        }
        let mut active_factors = Vec::new();
        for (g, &cnt) in counts.iter().enumerate() {
            if cnt == 0 {
                continue;
            }
            if cnt != fg.factors[g].keys.len() {
                return None;
            }
            active_factors.push(g as u16);
        }
        if active_factors.is_empty() {
            return Some(None);
        }
        let direct_factor = if active_factors.len() == 1 {
            let g = active_factors[0] as usize;
            let f = &fg.factors[g];
            if u.len() == f.keys.len() && (0..f.keys.len()).all(|k| key_to_code[f.offset + k] == k as u64) {
                Some(g as u16)
            } else {
                None
            }
        } else {
            None
        };
        Some(Some(Arc::new(AtomTable {
            code_to_key: code_to_key.into(),
            key_to_code: key_to_code.into(),
            active_factors: active_factors.into(),
            direct_factor,
        })))
    }

    #[inline]
    pub fn map_code(&self, fg: &FactorGroupSpec, img: &[u16], code: u64) -> u64 {
        if let Some(g) = self.direct_factor {
            return img[fg.factors[g as usize].offset + code as usize] as u64;
        }
        match self.code_to_key[code as usize] {
            None => code,
            Some((g, k)) => {
                let off = fg.factors[g as usize].offset;
                self.key_to_code[off + img[off + k as usize] as usize]
            }
        }
    }
}

/// How a `Shape::Fcn` domain permutes under a [`FactorGroupSpec`].
#[derive(Clone, Debug)]
pub enum DomMap {
    /// Domain contains no moved atoms (slot `i` stays at slot `i`).
    Fixed(usize),
    /// Domain is identically factor `factor`'s sorted key list `K_g`.
    DirectFactor { factor: u16, len: usize },
    /// Domain is a closed set of atoms (multi-factor or mixed with fixed atoms).
    AtomDom(Arc<AtomTable>),
    /// Compound finite domain mapped via a [`RankPlan`].
    Ranked { slot_to_rank: Box<[u64]>, rank_to_slot: Box<[u32]>, plan: Box<RankPlan> },
    /// General compound domain (rare: non-bitset-sized shape) mapped via sorted binary search.
    ValueDom(Arc<[Value]>),
}

impl DomMap {
    #[inline]
    pub fn len(&self) -> usize {
        match self {
            DomMap::Fixed(n) | DomMap::DirectFactor { len: n, .. } => *n,
            DomMap::AtomDom(t) => t.code_to_key.len(),
            DomMap::Ranked { slot_to_rank, .. } => slot_to_rank.len(),
            DomMap::ValueDom(d) => d.len(),
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn is_identity(&self) -> bool {
        matches!(self, DomMap::Fixed(_))
    }

    #[inline]
    pub fn map_slot(&self, fg: &FactorGroupSpec, img: &[u16], slot: usize) -> usize {
        match self {
            DomMap::Fixed(_) => slot,
            DomMap::DirectFactor { factor, .. } => img[fg.factors[*factor as usize].offset + slot] as usize,
            DomMap::AtomDom(t) => t.map_code(fg, img, slot as u64) as usize,
            DomMap::Ranked { slot_to_rank, rank_to_slot, plan } => {
                let nr = plan.map_rank(fg, img, slot_to_rank[slot]);
                rank_to_slot[nr as usize] as usize
            }
            DomMap::ValueDom(dom) => {
                let v = &dom[slot];
                match tlx_value::ops::permute_shared(v, &|m| fg.map_sym(m, img).cloned()) {
                    Ok(Some(p)) => dom.iter().position(|d| d.exact_eq(&p)).expect("closed domain"),
                    _ => slot,
                }
            }
        }
    }

    pub fn for_each_moved_key(&self, fg: &FactorGroupSpec, f: &mut impl FnMut(usize, usize)) {
        match self {
            DomMap::Fixed(_) => {}
            DomMap::DirectFactor { factor, len } => {
                let g = *factor as usize;
                for k in 0..*len {
                    f(g, k);
                }
            }
            DomMap::AtomDom(t) => {
                for &g in t.active_factors.iter() {
                    let g = g as usize;
                    for k in 0..fg.factors[g].keys.len() {
                        f(g, k);
                    }
                }
            }
            DomMap::Ranked { slot_to_rank, plan, .. } => {
                for &r in slot_to_rank.iter() {
                    plan.for_each_moved_key(fg, r, f);
                }
            }
            DomMap::ValueDom(dom) => {
                for v in dom.iter() {
                    for_each_moved_in_value(v, fg, f);
                }
            }
        }
    }

    fn compile(dom: &[Value], fg: &FactorGroupSpec) -> Option<DomMap> {
        if dom.is_empty() || !dom.iter().any(|d| value_has_moved(d, fg)) {
            return Some(DomMap::Fixed(dom.len()));
        }
        if dom.iter().all(|d| matches!(d, Value::ModelValue(_) | Value::Str(_))) {
            let table = AtomTable::compile(dom, fg)?.expect("moved atoms present");
            if let Some(factor) = table.direct_factor {
                return Some(DomMap::DirectFactor { factor, len: dom.len() });
            }
            return Some(DomMap::AtomDom(table));
        }
        // Compound domain keys: closed under prod_g Sym(K_g) iff closed under
        // every adjacent transposition generator (k, k+1) of each factor.
        let mut gen_img = fg.identity_img();
        for factor in fg.factors.iter() {
            let off = factor.offset;
            for k in 0..factor.keys.len() - 1 {
                gen_img[off + k] = (k + 1) as u16;
                gen_img[off + k + 1] = k as u16;
                for d in dom {
                    let pk = tlx_value::ops::permute_shared(d, &|m| fg.map_sym(m, &gen_img).cloned()).ok()?;
                    if let Some(pk) = pk {
                        if !dom.iter().any(|x| x.exact_eq(&pk)) {
                            return None;
                        }
                    }
                }
                gen_img[off + k] = k as u16;
                gen_img[off + k + 1] = (k + 1) as u16;
            }
        }
        // Try building an O(1) RankPlan over the domain's joined finite shape.
        let mut joined = Shape::Never;
        for d in dom {
            joined = joined.join(&Shape::of(d));
        }
        if let Some(card) = bitset_universe(&joined) {
            if let Some(plan) = RankPlan::compile(&joined, fg) {
                let mut slot_to_rank = Vec::with_capacity(dom.len());
                let mut rank_to_slot = vec![u32::MAX; card as usize];
                let mut ok = true;
                for (i, d) in dom.iter().enumerate() {
                    if let Ok(r) = rank(&joined, d) {
                        if (r as usize) < rank_to_slot.len() && rank_to_slot[r as usize] == u32::MAX {
                            slot_to_rank.push(r);
                            rank_to_slot[r as usize] = i as u32;
                            continue;
                        }
                    }
                    ok = false;
                    break;
                }
                if ok {
                    return Some(DomMap::Ranked {
                        slot_to_rank: slot_to_rank.into(),
                        rank_to_slot: rank_to_slot.into(),
                        plan: Box::new(plan),
                    });
                }
            }
        }
        Some(DomMap::ValueDom(dom.into()))
    }
}

/// Pure integer permutation of ranks in a finite bitset-sized universe
/// (`<= MAX_BITSET_UNIVERSE`) under a [`FactorGroupSpec`].
#[derive(Clone, Debug)]
pub enum RankPlan {
    Identity,
    Atom(Arc<AtomTable>),
    Product { cards: Box<[u64]>, plans: Box<[RankPlan]> },
    Fcn { dom: DomMap, range_card: u64, range: Box<RankPlan> },
    Map { universe: usize, key: Box<RankPlan>, range_card: u64, range: Box<RankPlan> },
    Seq { elem_card: u64, elem: Box<RankPlan>, shorter: Box<[u64]> },
    SetMask { elem: Box<RankPlan> },
    SetComb { n: u64, by_size: Box<[u64]>, elem: Box<RankPlan> },
    Union { base: Box<[u64]>, arms: Box<[RankPlan]> },
}

impl RankPlan {
    /// Compile a factorized rank permutation plan for finite shape `shape`.
    /// Returns `None` if `shape` has no finite universe or is not closed under `fg`.
    pub fn compile(shape: &Shape, fg: &FactorGroupSpec) -> Option<RankPlan> {
        let _card = shape.cardinality()?;
        Some(match shape {
            Shape::Never | Shape::Bool | Shape::Int { .. } => RankPlan::Identity,
            Shape::Atom(u) => match AtomTable::compile(u, fg)? {
                None => RankPlan::Identity,
                Some(t) => RankPlan::Atom(t),
            },
            Shape::Record(fs) => {
                let plans: Vec<RankPlan> = fs.iter().map(|(_, f)| RankPlan::compile(f, fg)).collect::<Option<_>>()?;
                let cards: Vec<u64> = fs.iter().map(|(_, f)| f.cardinality().unwrap()).collect();
                compact_rank_product(cards, plans)
            }
            Shape::Tuple(es) => {
                let plans: Vec<RankPlan> = es.iter().map(|e| RankPlan::compile(e, fg)).collect::<Option<_>>()?;
                let cards: Vec<u64> = es.iter().map(|e| e.cardinality().unwrap()).collect();
                compact_rank_product(cards, plans)
            }
            Shape::Fcn { dom, range, witness, key_variants } => {
                if *witness == FcnWitness::Dynamic || !key_variants.is_empty() {
                    return None;
                }
                let dm = DomMap::compile(dom, fg)?;
                let rp = RankPlan::compile(range, fg)?;
                if dm.is_identity() && rp.is_identity() {
                    RankPlan::Identity
                } else {
                    RankPlan::Fcn { dom: dm, range_card: range.cardinality()?, range: Box::new(rp) }
                }
            }
            Shape::Map { key, range, witness } => {
                if *witness == FcnWitness::Dynamic {
                    return None;
                }
                let universe = bitset_universe(key)? as usize;
                let kp = RankPlan::compile(key, fg)?;
                let rp = RankPlan::compile(range, fg)?;
                if kp.is_identity() && rp.is_identity() {
                    RankPlan::Identity
                } else {
                    RankPlan::Map { universe, key: Box::new(kp), range_card: range.cardinality()?, range: Box::new(rp) }
                }
            }
            Shape::Seq { elem, max_len } => {
                let ep = RankPlan::compile(elem, fg)?;
                if ep.is_identity() || *max_len == 0 {
                    RankPlan::Identity
                } else {
                    let c = elem.cardinality()?;
                    let mut acc = 0u64;
                    let shorter: Box<[u64]> = (0..=*max_len)
                        .map(|l| {
                            let r = acc;
                            if l < *max_len {
                                acc = acc.wrapping_add(c.wrapping_pow(l as u32));
                            }
                            r
                        })
                        .collect();
                    RankPlan::Seq { elem_card: c, elem: Box::new(ep), shorter }
                }
            }
            Shape::Set { elem, max_card } => {
                let ep = RankPlan::compile(elem, fg)?;
                if ep.is_identity() || *max_card == 0 {
                    RankPlan::Identity
                } else {
                    let n = elem.cardinality()?;
                    if *max_card as u64 >= n {
                        RankPlan::SetMask { elem: Box::new(ep) }
                    } else {
                        let by_size: Box<[u64]> = (0..=*max_card as u64)
                            .scan(0u64, |acc, k| {
                                let r = *acc;
                                *acc = acc.wrapping_add(binom(n, k).unwrap_or(0));
                                Some(r)
                            })
                            .collect();
                        RankPlan::SetComb { n, by_size, elem: Box::new(ep) }
                    }
                }
            }
            Shape::Union(arms) => {
                let plans: Vec<RankPlan> = arms.iter().map(|a| RankPlan::compile(a, fg)).collect::<Option<_>>()?;
                if plans.iter().all(RankPlan::is_identity) {
                    RankPlan::Identity
                } else {
                    let mut acc = 0u64;
                    let base: Box<[u64]> = arms
                        .iter()
                        .map(|a| {
                            let r = acc;
                            acc += a.cardinality().unwrap();
                            r
                        })
                        .collect();
                    RankPlan::Union { base, arms: plans.into() }
                }
            }
            Shape::Dyn | Shape::Ref(_) => return None,
        })
    }

    #[inline]
    pub fn is_identity(&self) -> bool {
        matches!(self, RankPlan::Identity)
    }

    #[inline]
    pub fn atom_table(&self) -> Option<&Arc<AtomTable>> {
        match self {
            RankPlan::Atom(t) => Some(t),
            _ => None,
        }
    }

    /// Map rank `r` under `img` in pure integer arithmetic.
    pub fn map_rank(&self, fg: &FactorGroupSpec, img: &[u16], mut r: u64) -> u64 {
        match self {
            RankPlan::Identity => r,
            RankPlan::Atom(t) => t.map_code(fg, img, r),
            RankPlan::Product { cards, plans } => {
                let n = cards.len();
                let mut digits = [0u64; 16];
                if n <= digits.len() {
                    for i in (0..n).rev() {
                        let c = cards[i];
                        digits[i] = r % c;
                        r /= c;
                    }
                    let mut out = 0u64;
                    for i in 0..n {
                        out = out * cards[i] + plans[i].map_rank(fg, img, digits[i]);
                    }
                    out
                } else {
                    let mut v = vec![0u64; n];
                    for i in (0..n).rev() {
                        let c = cards[i];
                        v[i] = r % c;
                        r /= c;
                    }
                    let mut out = 0u64;
                    for i in 0..n {
                        out = out * cards[i] + plans[i].map_rank(fg, img, v[i]);
                    }
                    out
                }
            }
            RankPlan::Fcn { dom, range_card, range } => {
                let n = dom.len();
                let c = *range_card;
                let mut src = vec![0u64; n];
                for i in (0..n).rev() {
                    src[i] = r % c;
                    r /= c;
                }
                let mut dst = vec![0u64; n];
                for (i, &v) in src.iter().enumerate() {
                    let t = dom.map_slot(fg, img, i);
                    dst[t] = range.map_rank(fg, img, v);
                }
                dst.iter().fold(0u64, |acc, &d| acc * c + d)
            }
            RankPlan::Map { universe, key, range_card, range } => {
                let c = *range_card + 1;
                let mut src = vec![0u64; *universe];
                for i in (0..*universe).rev() {
                    src[i] = r % c;
                    r /= c;
                }
                let mut dst = vec![0u64; *universe];
                for (i, &d) in src.iter().enumerate() {
                    if d != 0 {
                        let nk = key.map_rank(fg, img, i as u64) as usize;
                        dst[nk] = 1 + range.map_rank(fg, img, d - 1);
                    }
                }
                dst.iter().fold(0u64, |acc, &d| acc * c + d)
            }
            RankPlan::Seq { elem_card, elem, shorter } => {
                let len = shorter.partition_point(|&b| b <= r) - 1;
                let mut rem = r - shorter[len];
                let c = *elem_card;
                let mut digits = vec![0u64; len];
                for i in (0..len).rev() {
                    digits[i] = rem % c;
                    rem /= c;
                }
                let mut m = 0u64;
                for &d in &digits {
                    m = m * c + elem.map_rank(fg, img, d);
                }
                shorter[len] + m
            }
            RankPlan::SetMask { elem } => {
                let mut out = 0u64;
                while r != 0 {
                    let b = r.trailing_zeros() as u64;
                    r &= r - 1;
                    out |= 1u64 << elem.map_rank(fg, img, b);
                }
                out
            }
            RankPlan::SetComb { n, by_size, elem } => {
                let k = by_size.partition_point(|&b| b <= r) - 1;
                let mut rem = r - by_size[k];
                let mut ranks = Vec::with_capacity(k);
                for i in (1..=k as u64).rev() {
                    let (mut lo, mut hi) = (i - 1, *n - 1);
                    while lo < hi {
                        let mid = lo + (hi - lo).div_ceil(2);
                        if binom(mid, i).unwrap_or(u64::MAX) <= rem {
                            lo = mid;
                        } else {
                            hi = mid - 1;
                        }
                    }
                    rem -= binom(lo, i).unwrap();
                    ranks.push(elem.map_rank(fg, img, lo));
                }
                ranks.sort_unstable();
                let mut out = by_size[k];
                for (i, &c) in ranks.iter().enumerate() {
                    out += binom(c, i as u64 + 1).unwrap();
                }
                out
            }
            RankPlan::Union { base, arms } => {
                let i = base.partition_point(|&b| b <= r) - 1;
                base[i] + arms[i].map_rank(fg, img, r - base[i])
            }
        }
    }

    /// Visit every moved `(factor_idx, key_idx)` occurring in the value of rank `r`.
    pub fn for_each_moved_key(&self, fg: &FactorGroupSpec, mut r: u64, f: &mut impl FnMut(usize, usize)) {
        match self {
            RankPlan::Identity => {}
            RankPlan::Atom(t) => {
                if let Some((g, k)) = t.code_to_key[r as usize] {
                    f(g as usize, k as usize);
                }
            }
            RankPlan::Product { cards, plans } => {
                for i in (0..cards.len()).rev() {
                    let c = cards[i];
                    let d = r % c;
                    r /= c;
                    plans[i].for_each_moved_key(fg, d, f);
                }
            }
            RankPlan::Fcn { dom, range_card, range } => {
                let n = dom.len();
                let c = *range_card;
                for _ in 0..n {
                    let d = r % c;
                    r /= c;
                    range.for_each_moved_key(fg, d, f);
                }
                dom.for_each_moved_key(fg, f);
            }
            RankPlan::Map { universe, key, range_card, range } => {
                let c = *range_card + 1;
                for i in (0..*universe).rev() {
                    let d = r % c;
                    r /= c;
                    if d != 0 {
                        key.for_each_moved_key(fg, i as u64, f);
                        range.for_each_moved_key(fg, d - 1, f);
                    }
                }
            }
            RankPlan::Seq { elem_card, elem, shorter } => {
                let len = shorter.partition_point(|&b| b <= r) - 1;
                let mut rem = r - shorter[len];
                let c = *elem_card;
                for _ in 0..len {
                    let d = rem % c;
                    rem /= c;
                    elem.for_each_moved_key(fg, d, f);
                }
            }
            RankPlan::SetMask { elem } => {
                while r != 0 {
                    let b = r.trailing_zeros() as u64;
                    r &= r - 1;
                    elem.for_each_moved_key(fg, b, f);
                }
            }
            RankPlan::SetComb { n, by_size, elem } => {
                let k = by_size.partition_point(|&b| b <= r) - 1;
                let mut rem = r - by_size[k];
                for i in (1..=k as u64).rev() {
                    let (mut lo, mut hi) = (i - 1, *n - 1);
                    while lo < hi {
                        let mid = lo + (hi - lo).div_ceil(2);
                        if binom(mid, i).unwrap_or(u64::MAX) <= rem {
                            lo = mid;
                        } else {
                            hi = mid - 1;
                        }
                    }
                    rem -= binom(lo, i).unwrap();
                    elem.for_each_moved_key(fg, lo, f);
                }
            }
            RankPlan::Union { base, arms } => {
                let i = base.partition_point(|&b| b <= r) - 1;
                arms[i].for_each_moved_key(fg, r - base[i], f);
            }
        }
    }
}

/// Deterministic, allocation-free 64-bit value digest for `Shape::Dyn` orbit
/// comparison and fingerprinting without interning candidates into `dynval`.
#[inline]
fn orbit_dyn_digest(v: &Value) -> u64 {
    use std::hash::BuildHasher;
    tlx_base::hash::fmix64(tlx_base::hash::FxBuildHasher::default().hash_one(v))
}

/// One compiled word-aligned unit of a [`FactorPlan::Product`] (`Record`/`Tuple`).
#[derive(Clone)]
pub enum ProductUnit {
    /// Contiguous invariant words: `dst[offset..offset + len] = src[offset..offset + len]`.
    Copy { offset: usize, len: usize },
    /// One word-aligned field with moved atoms at `offset`, indexing into
    /// `FactorPlan::Product::fields[field_idx]`.
    Word { field_idx: usize, offset: usize },
    /// One packed `u64` word at `word`: invariant bits are preserved via
    /// `src[word] & fixed_mask`, and each `(pos, field_idx)` atom bitfield
    /// indexes its owned `FactorPlan::Atom` in `FactorPlan::Product::fields`.
    Packed { word: usize, fixed_mask: u64, atoms: Box<[(BitPos, usize)]> },
}

/// Factorized per-shape permutation plan compiled once per variable for a
/// [`FactorGroupSpec`], applicable for any permutation `img: &[u16]` without
/// materializing `|G|` explicit [`PermPlan`] vectors.
#[derive(Clone)]
pub enum FactorPlan {
    /// Unaffected by any permutation in `G`: copy `n` words.
    Copy(usize),
    /// An atom word mapped through `AtomTable`.
    Atom(Arc<AtomTable>),
    /// A bitset over a `Shape::Atom` universe.
    BitsetAtom { table: Arc<AtomTable>, words: usize },
    /// A bitset over a compound finite universe (`<= MAX_BITSET_UNIVERSE`).
    BitsetRank { rank: Box<RankPlan>, words: usize },
    /// A sorted-array set of `elem_words`-word elements.
    Sorted { elem: Box<FactorPlan>, elem_words: usize, words: usize },
    /// A sequence of word-aligned elements.
    Seq { elem: Box<FactorPlan>, elem_words: usize, words: usize },
    /// A sequence of packed sub-word atoms.
    SeqBits { bits: u8, table: Arc<AtomTable>, words: usize },
    /// A record or tuple: `fields` in field order for refinement, and merged
    /// word-aligned `units` for fast permutation application.
    Product { fields: Box<[(FieldLoc, FactorPlan)]>, units: Box<[ProductUnit]>, words: usize },
    /// A fixed-domain function `[dom -> range]` with optional trailing words.
    Fcn { dom: DomMap, slot: SlotLayout, range: Box<FactorPlan>, extra: usize, dynamic_witness: bool, words: usize },
    /// A partial map over a bitset key universe.
    Map { key: Box<RankPlan>, dims: MapDims, range: Box<FactorPlan>, dynamic_witness: bool, words: usize },
    /// A union: arm index word, then arm payload padded to `words`.
    Union { arms: Box<[FactorPlan]>, words: usize },
    /// A `Dyn` handle.
    Dyn,
    /// A value store handle.
    Ref(crate::store::StoreRef),
}

impl FactorPlan {
    /// Compile a factorized permutation plan for `shape` under `fg`.
    /// Returns `None` if `shape` is not closed under `fg`.
    pub fn compile(shape: &Shape, fg: &FactorGroupSpec) -> Option<FactorPlan> {
        let n = words(shape);
        Some(match shape {
            Shape::Never | Shape::Bool | Shape::Int { .. } => FactorPlan::Copy(n),
            Shape::Atom(u) => match AtomTable::compile(u, fg)? {
                None => FactorPlan::Copy(n),
                Some(table) => FactorPlan::Atom(table),
            },
            Shape::Set { elem, .. } if bitset_universe(elem).is_some() => {
                let rp = RankPlan::compile(elem, fg)?;
                match rp {
                    RankPlan::Identity => FactorPlan::Copy(n),
                    RankPlan::Atom(table) => FactorPlan::BitsetAtom { table, words: n },
                    other => FactorPlan::BitsetRank { rank: Box::new(other), words: n },
                }
            }
            Shape::Set { elem, .. } => match FactorPlan::compile(elem, fg)? {
                FactorPlan::Copy(_) => FactorPlan::Copy(n),
                p => FactorPlan::Sorted { elem: Box::new(p), elem_words: words(elem), words: n },
            },
            Shape::Seq { elem, .. } => match FactorPlan::compile(elem, fg)? {
                FactorPlan::Copy(_) => FactorPlan::Copy(n),
                p => match SlotLayout::of(elem) {
                    SlotLayout::Words(ew) => FactorPlan::Seq { elem: Box::new(p), elem_words: ew, words: n },
                    SlotLayout::Bits(bits) => {
                        let FactorPlan::Atom(table) = p else {
                            unreachable!("packed non-copy scalar must be Atom");
                        };
                        FactorPlan::SeqBits { bits, table, words: n }
                    }
                },
            },
            Shape::Record(fs) => {
                let parts: Vec<&Shape> = fs.iter().map(|(_, f)| f).collect();
                compile_factor_product(&parts, fg, n)?
            }
            Shape::Tuple(es) => {
                let parts: Vec<&Shape> = es.iter().collect();
                compile_factor_product(&parts, fg, n)?
            }
            Shape::Fcn { dom, range, witness, key_variants } => {
                let extra = witness.extra_words() + key_variants.len();
                let dynamic_witness = *witness == FcnWitness::Dynamic;
                let dm = if key_variants.is_empty() {
                    DomMap::compile(dom, fg)?
                } else {
                    if dom.iter().any(|k| value_has_moved(k, fg))
                        || key_variants.iter().any(|(_, vs)| vs.iter().any(|k| value_has_moved(k, fg)))
                    {
                        return None;
                    }
                    DomMap::Fixed(dom.len())
                };
                let rp = FactorPlan::compile(range, fg)?;
                let slot = SlotLayout::of(range);
                if (dm.is_identity() && rp.is_identity()) || matches!(slot, SlotLayout::Words(0)) {
                    FactorPlan::Copy(n)
                } else {
                    FactorPlan::Fcn { dom: dm, slot, range: Box::new(rp), extra, dynamic_witness, words: n }
                }
            }
            Shape::Map { key, range, witness } => {
                let kp = RankPlan::compile(key, fg)?;
                let rp = FactorPlan::compile(range, fg)?;
                let dims = MapDims::of_parts(key, range);
                let dynamic_witness = *witness == FcnWitness::Dynamic;
                if kp.is_identity() && rp.is_identity() {
                    FactorPlan::Copy(n)
                } else {
                    FactorPlan::Map { key: Box::new(kp), dims, range: Box::new(rp), dynamic_witness, words: n }
                }
            }
            Shape::Union(arms) => {
                let plans: Vec<FactorPlan> = arms.iter().map(|a| FactorPlan::compile(a, fg)).collect::<Option<_>>()?;
                if plans.iter().all(FactorPlan::is_identity) {
                    FactorPlan::Copy(n)
                } else {
                    FactorPlan::Union { arms: plans.into(), words: n }
                }
            }
            Shape::Dyn => FactorPlan::Dyn,
            Shape::Ref(store) => FactorPlan::Ref(store.clone()),
        })
    }

    #[inline]
    pub fn is_identity(&self) -> bool {
        matches!(self, FactorPlan::Copy(_))
    }

    #[inline]
    pub fn words(&self) -> usize {
        match self {
            FactorPlan::Copy(n) => *n,
            FactorPlan::Atom(_) | FactorPlan::Dyn | FactorPlan::Ref(_) => 1,
            FactorPlan::BitsetAtom { words, .. }
            | FactorPlan::BitsetRank { words, .. }
            | FactorPlan::Sorted { words, .. }
            | FactorPlan::Seq { words, .. }
            | FactorPlan::SeqBits { words, .. }
            | FactorPlan::Product { words, .. }
            | FactorPlan::Fcn { words, .. }
            | FactorPlan::Map { words, .. }
            | FactorPlan::Union { words, .. } => *words,
        }
    }

    /// True iff this plan or any descendant contains a multi-word (`>= 2` words)
    /// bitset (for `Set` or `Map`), where little-endian multi-word bitset order
    /// differs from plain slice `.cmp()`.
    pub fn has_wide_bitset(&self) -> bool {
        match self {
            FactorPlan::Copy(_) | FactorPlan::Atom(_) | FactorPlan::SeqBits { .. } | FactorPlan::Dyn | FactorPlan::Ref(_) => false,
            FactorPlan::BitsetAtom { words, .. } | FactorPlan::BitsetRank { words, .. } => *words > 1,
            FactorPlan::Sorted { elem, .. } | FactorPlan::Seq { elem, .. } => elem.has_wide_bitset(),
            FactorPlan::Product { fields, .. } => fields.iter().any(|(_, p)| p.has_wide_bitset()),
            FactorPlan::Fcn { range, .. } => range.has_wide_bitset(),
            FactorPlan::Map { dims, range, .. } => dims.bitset_words > 1 || range.has_wide_bitset(),
            FactorPlan::Union { arms, .. } => arms.iter().any(FactorPlan::has_wide_bitset),
        }
    }

    /// True iff this plan or any descendant contains a `Shape::Dyn` slot.
    pub fn has_dyn(&self) -> bool {
        match self {
            FactorPlan::Dyn => true,
            FactorPlan::Sorted { elem, .. } | FactorPlan::Seq { elem, .. } => elem.has_dyn(),
            FactorPlan::Product { fields, .. } => fields.iter().any(|(_, p)| p.has_dyn()),
            FactorPlan::Fcn { range, .. } | FactorPlan::Map { range, .. } => range.has_dyn(),
            FactorPlan::Union { arms, .. } => arms.iter().any(FactorPlan::has_dyn),
            _ => false,
        }
    }

    /// Apply permutation `img` to `src` into `dst` (safe, validates handles).
    pub fn apply(&self, fg: &FactorGroupSpec, img: &[u16], src: &[u64], dst: &mut [u64]) {
        // SAFETY: `TRUSTED = false` validates any decoded handle.
        unsafe { self.apply_impl::<false, false>(fg, img, src, dst) }
    }

    /// Apply permutation `img` to trusted encoded words `src` into `dst`.
    ///
    /// # Safety
    /// `src` must be a valid encoding of this plan's shape; active Dyn handles
    /// must satisfy `dynval::lookup_unchecked`'s publication contract.
    pub unsafe fn apply_unchecked(&self, fg: &FactorGroupSpec, img: &[u16], src: &[u64], dst: &mut [u64]) {
        // SAFETY: caller upholds valid encoding and handle publication contract.
        unsafe { self.apply_impl::<true, false>(fg, img, src, dst) }
    }

    /// Apply permutation `img` to trusted encoded words `src` into `dst` in
    /// orbit-canonical form: `Ref` slots write semantic digests directly without
    /// mutating the value store, and trailing dynamic witness words are zeroed.
    ///
    /// # Safety
    /// Same contract as [`Self::apply_unchecked`].
    pub unsafe fn apply_orbit_unchecked(&self, fg: &FactorGroupSpec, img: &[u16], src: &[u64], dst: &mut [u64]) {
        // SAFETY: caller upholds valid encoding and handle publication contract.
        unsafe { self.apply_impl::<true, true>(fg, img, src, dst) }
    }

    unsafe fn apply_impl<const TRUSTED: bool, const ORBIT_CANON: bool>(
        &self,
        fg: &FactorGroupSpec,
        img: &[u16],
        src: &[u64],
        dst: &mut [u64],
    ) {
        // SAFETY: recursive child slices follow the validated layout contract.
        unsafe {
            match self {
                FactorPlan::Copy(0) => {}
                FactorPlan::Copy(1) => dst[0] = src[0],
                FactorPlan::Copy(n) => dst[..*n].copy_from_slice(&src[..*n]),
                FactorPlan::Atom(table) => dst[0] = table.map_code(fg, img, src[0]),
                FactorPlan::BitsetAtom { table, words } => {
                    dst[..*words].fill(0);
                    for (i, &w) in src[..*words].iter().enumerate() {
                        let mut b = w;
                        while b != 0 {
                            let r = (i * 64 + b.trailing_zeros() as usize) as u64;
                            b &= b - 1;
                            let t = table.map_code(fg, img, r) as usize;
                            dst[t / 64] |= 1u64 << (t % 64);
                        }
                    }
                }
                FactorPlan::BitsetRank { rank, words } => {
                    dst[..*words].fill(0);
                    for (i, &w) in src[..*words].iter().enumerate() {
                        let mut b = w;
                        while b != 0 {
                            let r = (i * 64 + b.trailing_zeros() as usize) as u64;
                            b &= b - 1;
                            let t = rank.map_rank(fg, img, r) as usize;
                            dst[t / 64] |= 1u64 << (t % 64);
                        }
                    }
                }
                FactorPlan::Sorted { elem, elem_words, words } => {
                    let (n, ew) = (src[0] as usize, *elem_words);
                    dst[0] = src[0];
                    for i in 0..n {
                        let o = 1 + i * ew;
                        elem.apply_impl::<TRUSTED, ORBIT_CANON>(fg, img, &src[o..o + ew], &mut dst[o..o + ew]);
                    }
                    dst[1 + n * ew..*words].fill(0);
                    sort_elems(&mut dst[1..1 + n * ew], ew);
                }
                FactorPlan::Seq { elem, elem_words, words } => {
                    let (n, ew) = (src[0] as usize, *elem_words);
                    dst[0] = src[0];
                    for i in 0..n {
                        let o = 1 + i * ew;
                        elem.apply_impl::<TRUSTED, ORBIT_CANON>(fg, img, &src[o..o + ew], &mut dst[o..o + ew]);
                    }
                    dst[1 + n * ew..*words].fill(0);
                }
                FactorPlan::SeqBits { bits, table, words } => {
                    let n = src[0] as usize;
                    dst[0] = src[0];
                    dst[1..*words].fill(0);
                    for i in 0..n {
                        let raw = SlotLayout::extract(*bits, &src[1..], i);
                        SlotLayout::set_zeroed(*bits, &mut dst[1..], i, table.map_code(fg, img, raw));
                    }
                }
                FactorPlan::Product { fields, units, .. } => {
                    for unit in units.iter() {
                        match unit {
                            ProductUnit::Copy { offset, len: 1 } => dst[*offset] = src[*offset],
                            ProductUnit::Copy { offset, len } => {
                                let o = *offset;
                                dst[o..o + *len].copy_from_slice(&src[o..o + *len]);
                            }
                            ProductUnit::Word { field_idx, offset } => {
                                fields[*field_idx].1.apply_impl::<TRUSTED, ORBIT_CANON>(fg, img, &src[*offset..], &mut dst[*offset..]);
                            }
                            ProductUnit::Packed { word, fixed_mask, atoms } => {
                                let sw = src[*word];
                                let mut w = sw & *fixed_mask;
                                for &(pos, field_idx) in atoms.iter() {
                                    let FactorPlan::Atom(table) = &fields[field_idx].1 else {
                                        unreachable!("packed atom unit must reference Atom field");
                                    };
                                    let raw = (sw >> pos.shift) & pos.mask();
                                    w |= table.map_code(fg, img, raw) << pos.shift;
                                }
                                dst[*word] = w;
                            }
                        }
                    }
                }
                FactorPlan::Fcn { dom, slot, range, extra, dynamic_witness, words } => {
                    let len = dom.len();
                    let payload_words = slot.array_words(len);
                    match *slot {
                        SlotLayout::Words(rw) => {
                            for i in 0..len {
                                let t = dom.map_slot(fg, img, i);
                                range.apply_impl::<TRUSTED, ORBIT_CANON>(
                                    fg,
                                    img,
                                    &src[i * rw..(i + 1) * rw],
                                    &mut dst[t * rw..(t + 1) * rw],
                                );
                            }
                        }
                        SlotLayout::Bits(bits) => {
                            dst[..payload_words].fill(0);
                            for i in 0..len {
                                let t = dom.map_slot(fg, img, i);
                                let raw = SlotLayout::extract(bits, src, i);
                                let mapped = match range.as_ref() {
                                    FactorPlan::Copy(_) => raw,
                                    FactorPlan::Atom(table) => table.map_code(fg, img, raw),
                                    _ => unreachable!("packed scalar plan must be Copy or Atom"),
                                };
                                SlotLayout::set_zeroed(bits, dst, t, mapped);
                            }
                        }
                    }
                    if *extra > 0 {
                        if ORBIT_CANON {
                            dst[payload_words..*words].fill(0);
                        } else {
                            dst[payload_words..*words].copy_from_slice(&src[payload_words..*words]);
                        }
                    }
                    let _ = dynamic_witness;
                }
                FactorPlan::Map { key, dims, range, dynamic_witness, words } => {
                    let bw = dims.bitset_words;
                    dst[..*words].fill(0);
                    match dims.slot {
                        SlotLayout::Words(rw) => {
                            for (i, &w) in src[..bw].iter().enumerate() {
                                let mut b = w;
                                while b != 0 {
                                    let r = i * 64 + b.trailing_zeros() as usize;
                                    b &= b - 1;
                                    let t = key.map_rank(fg, img, r as u64) as usize;
                                    dst[t / 64] |= 1u64 << (t % 64);
                                    range.apply_impl::<TRUSTED, ORBIT_CANON>(
                                        fg,
                                        img,
                                        &src[bw + r * rw..bw + (r + 1) * rw],
                                        &mut dst[bw + t * rw..bw + (t + 1) * rw],
                                    );
                                }
                            }
                        }
                        SlotLayout::Bits(bits) => {
                            for (i, &w) in src[..bw].iter().enumerate() {
                                let mut b = w;
                                while b != 0 {
                                    let r = i * 64 + b.trailing_zeros() as usize;
                                    b &= b - 1;
                                    let t = key.map_rank(fg, img, r as u64) as usize;
                                    dst[t / 64] |= 1u64 << (t % 64);
                                    let raw = SlotLayout::extract(bits, &src[bw..], r);
                                    let mapped = match range.as_ref() {
                                        FactorPlan::Copy(_) => raw,
                                        FactorPlan::Atom(table) => table.map_code(fg, img, raw),
                                        _ => unreachable!("packed scalar plan must be Copy or Atom"),
                                    };
                                    SlotLayout::set_zeroed(bits, &mut dst[bw..], t, mapped);
                                }
                            }
                        }
                    }
                    if *dynamic_witness {
                        dst[*words - 1] = if ORBIT_CANON { 0 } else { src[*words - 1] };
                    }
                }
                FactorPlan::Union { arms, words } => {
                    dst[..*words].fill(0);
                    dst[0] = src[0];
                    arms[src[0] as usize].apply_impl::<TRUSTED, ORBIT_CANON>(fg, img, &src[1..*words], &mut dst[1..*words]);
                }
                FactorPlan::Dyn => {
                    let v = if TRUSTED { dynval::lookup_unchecked(src[0]) } else { dynval::lookup(src[0]) };
                    if ORBIT_CANON {
                        dst[0] = match tlx_value::ops::permute_shared(&v, &|m| fg.map_sym(m, img).cloned()) {
                            Ok(Some(p)) => orbit_dyn_digest(&p),
                            _ => orbit_dyn_digest(&v),
                        };
                    } else {
                        dst[0] = match tlx_value::ops::permute_shared(&v, &|m| fg.map_sym(m, img).cloned()) {
                            Ok(Some(p)) => dynval::intern_exact(&p),
                            _ => src[0],
                        };
                    }
                }
                FactorPlan::Ref(store) => {
                    let v = if TRUSTED { store.thaw(src[0]) } else { store.try_thaw(src[0]).expect("valid value store handle") };
                    match tlx_value::ops::permute_shared(&v, &|m| fg.map_sym(m, img).cloned()) {
                        Ok(Some(p)) => {
                            dst[0] = if ORBIT_CANON {
                                crate::store::digest_of_value(&p).unwrap_or_else(|_| store.digest(src[0]))
                            } else {
                                store.freeze(&p).unwrap_or(src[0])
                            };
                        }
                        _ => {
                            dst[0] = if ORBIT_CANON { store.digest(src[0]) } else { src[0] };
                        }
                    }
                }
            }
        }
    }
}

/// Merge adjacent `Identity` factors in a `RankPlan::Product` so mixed-radix
/// decomposition does the minimum number of divisions per rank.
fn compact_rank_product(cards: Vec<u64>, plans: Vec<RankPlan>) -> RankPlan {
    if plans.iter().all(RankPlan::is_identity) {
        return RankPlan::Identity;
    }
    let mut out_cards: Vec<u64> = Vec::with_capacity(cards.len());
    let mut out_plans: Vec<RankPlan> = Vec::with_capacity(plans.len());
    for (c, p) in cards.into_iter().zip(plans) {
        if c == 1 && p.is_identity() {
            continue;
        }
        if p.is_identity() && out_plans.last().is_some_and(RankPlan::is_identity) {
            if let Some(prod) = out_cards.last().and_then(|prev| prev.checked_mul(c)) {
                *out_cards.last_mut().unwrap() = prod;
                continue;
            }
        }
        out_cards.push(c);
        out_plans.push(p);
    }
    if out_plans.iter().all(RankPlan::is_identity) {
        return RankPlan::Identity;
    }
    RankPlan::Product { cards: out_cards.into(), plans: out_plans.into() }
}

fn compile_factor_product(parts: &[&Shape], fg: &FactorGroupSpec, n: usize) -> Option<FactorPlan> {
    let fl = FieldLayout::of_shapes(parts.iter().copied());
    let plans: Vec<FactorPlan> = parts.iter().map(|p| FactorPlan::compile(p, fg)).collect::<Option<_>>()?;
    if plans.iter().all(FactorPlan::is_identity) {
        return Some(FactorPlan::Copy(n));
    }
    let mut units: Vec<ProductUnit> = Vec::new();
    let push_copy = |units: &mut Vec<ProductUnit>, offset: usize, len: usize| {
        if len == 0 {
            return;
        }
        if let Some(ProductUnit::Copy { offset: o0, len: l0 }) = units.last_mut() {
            if *o0 + *l0 == offset {
                *l0 += len;
                return;
            }
        }
        units.push(ProductUnit::Copy { offset, len });
    };
    for group in fl.word_groups() {
        match group {
            FieldGroup::Word { index, offset, words: w } => {
                if plans[*index].is_identity() {
                    push_copy(&mut units, *offset, *w);
                } else {
                    units.push(ProductUnit::Word { field_idx: *index, offset: *offset });
                }
            }
            FieldGroup::Packed { word, fields } => {
                let mut fixed_mask = 0u64;
                let mut atoms = Vec::new();
                for &(i, pos) in fields.iter() {
                    match &plans[i] {
                        FactorPlan::Copy(_) => fixed_mask |= pos.shifted_mask(),
                        FactorPlan::Atom(_) => atoms.push((pos, i)),
                        _ => unreachable!("packed scalar plan must be Copy or Atom"),
                    }
                }
                if atoms.is_empty() {
                    push_copy(&mut units, *word, 1);
                } else {
                    units.push(ProductUnit::Packed { word: *word, fixed_mask, atoms: atoms.into() });
                }
            }
        }
    }
    let fields: Box<[(FieldLoc, FactorPlan)]> = fl.locs.iter().copied().zip(plans).collect();
    Some(FactorPlan::Product { fields, units: units.into(), words: n })
}

fn value_has_moved(v: &Value, fg: &FactorGroupSpec) -> bool {
    match v {
        Value::ModelValue(m) => fg.lookup(*m).is_some(),
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => false,
        Value::Set(es) | Value::Tuple(es) => es.iter().any(|e| value_has_moved(e, fg)),
        Value::Record(fs) => fs.iter().any(|(_, e)| value_has_moved(e, fg)),
        Value::Fcn(ps, _) => ps.iter().any(|(k, e)| value_has_moved(k, fg) || value_has_moved(e, fg)),
        Value::LazySet(_) | Value::LazyFcn(_) => true,
    }
}

fn for_each_moved_in_value(v: &Value, fg: &FactorGroupSpec, f: &mut impl FnMut(usize, usize)) {
    match v {
        Value::ModelValue(m) => {
            if let Some((g, k)) = fg.lookup(*m) {
                f(g, k);
            }
        }
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => {}
        Value::Set(es) | Value::Tuple(es) => {
            for e in es.iter() {
                for_each_moved_in_value(e, fg, f);
            }
        }
        Value::Record(fs) => {
            for (_, e) in fs.iter() {
                for_each_moved_in_value(e, fg, f);
            }
        }
        Value::Fcn(ps, _) => {
            for (k, e) in ps.iter() {
                for_each_moved_in_value(k, fg, f);
                for_each_moved_in_value(e, fg, f);
            }
        }
        Value::LazySet(_) | Value::LazyFcn(_) => {
            for (g, factor) in fg.factors.iter().enumerate() {
                for k in 0..factor.keys.len() {
                    f(g, k);
                }
            }
        }
    }
}
