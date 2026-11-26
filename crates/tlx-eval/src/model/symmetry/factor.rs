//! Factorized representation of disjoint symmetric-group products
//! `prod_g Sym(K_g)` and ordered block partitions `Partition`.

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::ops::ControlFlow;
use std::sync::Arc;

use tlx_sema::builtins::Builtin;
use tlx_sema::hir::{DefKind, Expr, ExprKind, OpRef};
use tlx_value::{ops, Sym, Value};

use crate::env::Env;
use crate::error::{EResult, EvalError};
use crate::eval::Ctx;
use crate::interp::Interp;

#[cfg(test)]
use super::FastPerm;
use super::{perm_of, ChosenPerm, Group, Perm, MAX_MATERIALIZED_ORDER};

/// Inline storage capacity (total moved keys across all factors) for `Partition`
/// and `ChosenPerm`: covers `S_3` through `S_16` and products such as `S_4^3`
/// or `S_5^3` with zero heap allocation on the hot path.
pub(super) const INLINE_KEYS: usize = 16;

/// Original generator presentation retained when a `FactorizedGroup` was
/// constructed from overlapping `Permutations(...)` unions or raw generators,
/// so fallible (`!is_orbit_cmp_safe`) states walk permutations in exact
/// `close_under_composition` order without storing generators for normal
/// disjoint `Permutations` products.
#[derive(Clone)]
pub(super) enum FallbackOrder {
    /// Disjoint union of full `Permutations(K_g)` factors matching `factors`
    /// (already sorted by `(len, first_key)`): lazy weight-by-weight BFS visits
    /// the exact `close_under_composition` sequence with zero extra memory.
    DisjointFull,
    /// Overlapping `Permutations(S_1) \cup ... \cup Permutations(S_m)` where
    /// each `S_i` is sorted ascending in TLC order and deduplicated by `(len, S_i)`.
    OverlappingSets(Vec<Vec<Sym>>),
    /// Explicit flat-image generator list in normalized declaration order.
    ExplicitGens(Vec<Vec<u16>>),
}

/// Evaluate a SYMMETRY definition into a `Group`, recognizing disjoint
/// products of full symmetric groups (`Permutations(S1) \cup Permutations(S2)`)
/// without expanding `|S|!` or running `O(|G|^2)` group closure.
pub(in crate::model) fn symmetry_group(ip: &Arc<Interp>, e: &Expr) -> EResult<Group> {
    let mut raw_factors: Vec<Vec<Sym>> = Vec::new();
    if collect_perm_factors(ip, e, &mut raw_factors, 0)? {
        let mut normalized_sets: Vec<Vec<Sym>> = raw_factors
            .into_iter()
            .filter(|s| s.len() >= 2)
            .map(|mut s| {
                s.sort_unstable();
                s.dedup();
                s
            })
            .filter(|s| s.len() >= 2)
            .collect();
        normalized_sets.sort_by(|a, b| a.len().cmp(&b.len()).then_with(|| a.cmp(b)));
        normalized_sets.dedup();
        if let Some(factors) = merge_uniform_factors(&normalized_sets) {
            if factors.is_empty() {
                return Ok(Group::default());
            }
            let fallback =
                if normalized_sets == factors { FallbackOrder::DisjointFull } else { FallbackOrder::OverlappingSets(normalized_sets) };
            return Group::from_factors_with_fallback(factors, fallback);
        }
    }
    let set = ip.eval(e, &Env::default(), &Ctx::NONE)?;
    let mut gens = Vec::new();
    for f in ops::enumerate_normalized(&set)? {
        let m = perm_of(&f)?;
        if !m.is_empty() && !gens.contains(&m) {
            gens.push(m);
        }
    }
    Group::from_generators(gens)
}

/// Syntactically recognize `Permutations(S)`, unions (`\cup`), empty sets, and
/// 0-ary aliases without expanding `|S|!`. Returns `Ok(false)` when `e` is not
/// of this form so the caller falls back to full evaluation.
fn collect_perm_factors(ip: &Arc<Interp>, e: &Expr, out: &mut Vec<Vec<Sym>>, nesting: usize) -> EResult<bool> {
    if nesting > 100 {
        return Ok(false);
    }
    if let ExprKind::SetEnum(es) = &*e.kind {
        return Ok(es.is_empty());
    }
    let (op, args) = match &*e.kind {
        ExprKind::Builtin { op, args } => (*op, args),
        ExprKind::Apply { op: OpRef::Def(d), args } => {
            let d = ip.redirect_def(*d);
            if ip.def_value.contains_key(&d) {
                return Ok(false);
            }
            let def = &ip.prog.defs[d.idx()];
            if let Some(op) = def.builtin {
                (op, args)
            } else if args.is_empty() && def.params.is_empty() {
                match &def.kind {
                    DefKind::Op(body) => return collect_perm_factors(ip, body, out, nesting + 1),
                    _ => return Ok(false),
                }
            } else {
                return Ok(false);
            }
        }
        _ => return Ok(false),
    };
    if ip.is_builtin_overridden(op) {
        return Ok(false);
    }
    match (op, &args[..]) {
        (Builtin::Cup, [a, b]) => Ok(collect_perm_factors(ip, a, out, nesting + 1)? && collect_perm_factors(ip, b, out, nesting + 1)?),
        (Builtin::Permutations, [set]) => {
            let set = ip.eval(set, &Env::default(), &Ctx::NONE)?;
            let values = ops::enumerate_normalized(&set)?;
            let mut syms = Vec::with_capacity(values.len());
            for v in &values {
                let Value::ModelValue(m) = v else {
                    return Err(EvalError::new(format!("SYMMETRY permutations must map model values, found {v}")));
                };
                syms.push(*m);
            }
            if syms.len() >= 2 {
                out.push(syms);
            }
            Ok(true)
        }
        _ => Ok(false),
    }
}

/// Merge overlapping `Sym(S_i)` sets into pairwise-disjoint connected
/// components sorted in TLC order (`Sym::cmp`). Returns `None` if any merged
/// component mixes model-value types (so the caller falls back to explicit
/// closure to preserve typed-vs-untyped `cmp_tlc` behavior).
fn merge_uniform_factors(raw: &[Vec<Sym>]) -> Option<Vec<Vec<Sym>>> {
    let mut all: Vec<Sym> = raw.iter().flat_map(|s| s.iter().copied()).collect();
    all.sort_unstable();
    all.dedup();
    if all.is_empty() {
        return Some(Vec::new());
    }
    let mut uf = UnionFind::new(all.len());
    for set in raw {
        let Some(&first) = set.first() else { continue };
        let i0 = all.binary_search(&first).unwrap();
        for &m in &set[1..] {
            let i = all.binary_search(&m).unwrap();
            uf.union(i0, i);
        }
    }
    let mut groups: HashMap<usize, Vec<Sym>> = HashMap::new();
    for (i, &m) in all.iter().enumerate() {
        groups.entry(uf.find(i)).or_default().push(m);
    }
    let mut factors = Vec::new();
    for mut g in groups.into_values() {
        if g.len() < 2 {
            continue;
        }
        g.sort_unstable();
        let ty = g[0].model_value_type();
        if g[1..].iter().any(|m| m.model_value_type() != ty) {
            return None;
        }
        factors.push(g);
    }
    factors.sort_by_key(|g| (g.len(), g[0]));
    Some(factors)
}

/// Recognize whether an arbitrary generator list generates a disjoint product
/// of full symmetric groups `prod_g Sym(K_g)` without closing the group.
pub(super) fn recognize_disjoint_factors(gens: &[Perm]) -> Option<Vec<Vec<Sym>>> {
    let mut moved: Vec<Sym> = Vec::new();
    let mut parsed: Vec<Vec<(Sym, Sym)>> = Vec::new();
    for p in gens {
        if p.is_empty() {
            continue;
        }
        let mut pairs = Vec::with_capacity(p.len());
        let mut imgs = HashSet::with_capacity(p.len());
        for (&k, v) in p {
            let Value::ModelValue(img) = v else { return None };
            if !imgs.insert(*img) {
                return None;
            }
            pairs.push((k, *img));
            moved.push(k);
            moved.push(*img);
        }
        if pairs.iter().any(|(_, img)| !p.contains_key(img)) {
            return None;
        }
        parsed.push(pairs);
    }
    if parsed.is_empty() {
        return Some(Vec::new());
    }
    moved.sort_unstable();
    moved.dedup();
    let idx_of = |s: Sym| moved.binary_search(&s).unwrap();

    let mut orbit_uf = UnionFind::new(moved.len());
    for p in &parsed {
        for &(k, img) in p {
            orbit_uf.union(idx_of(k), idx_of(img));
        }
    }
    let mut orbits: HashMap<usize, Vec<usize>> = HashMap::new();
    for i in 0..moved.len() {
        orbits.entry(orbit_uf.find(i)).or_default().push(i);
    }

    let mut transp_uf = UnionFind::new(moved.len());
    let mut orbit_transps: HashMap<usize, Vec<(usize, usize)>> = HashMap::new();
    for p in &parsed {
        if p.len() == 2 && p[1].0 == p[0].1 && p[1].1 == p[0].0 {
            let (a, b) = (idx_of(p[0].0), idx_of(p[0].1));
            let root = orbit_uf.find(a);
            if orbit_uf.find(b) == root {
                transp_uf.union(a, b);
                orbit_transps.entry(root).or_default().push((a, b));
            }
        }
    }

    let mut factors = Vec::with_capacity(orbits.len());
    for (root, members) in orbits {
        if members.len() < 2 {
            continue;
        }
        let t0 = transp_uf.find(members[0]);
        let connected = members[1..].iter().all(|&i| transp_uf.find(i) == t0);
        if !connected {
            let ts = orbit_transps.get(&root)?;
            if !has_full_cycle_with_adj_transp(&parsed, &mut orbit_uf, &idx_of, root, &members, ts) {
                return None;
            }
        }
        let mut syms: Vec<Sym> = members.into_iter().map(|i| moved[i]).collect();
        syms.sort_unstable();
        let ty = syms[0].model_value_type();
        if syms[1..].iter().any(|m| m.model_value_type() != ty) {
            return None;
        }
        factors.push(syms);
    }
    factors.sort_by_key(|g| (g.len(), g[0]));
    Some(factors)
}

fn has_full_cycle_with_adj_transp(
    parsed: &[Vec<(Sym, Sym)>],
    orbit_uf: &mut UnionFind,
    idx_of: &impl Fn(Sym) -> usize,
    root: usize,
    members: &[usize],
    transps: &[(usize, usize)],
) -> bool {
    let n = members.len();
    parsed.iter().any(|p| {
        if p.len() != n || orbit_uf.find(idx_of(p[0].0)) != root {
            return false;
        }
        let mut map: HashMap<usize, usize> = HashMap::with_capacity(n);
        for &(k, img) in p {
            let (ki, ii) = (idx_of(k), idx_of(img));
            if orbit_uf.find(ki) != root {
                return false;
            }
            map.insert(ki, ii);
        }
        let start = members[0];
        let mut cur = start;
        let mut steps = 0;
        while let Some(&next) = map.get(&cur) {
            cur = next;
            steps += 1;
            if cur == start || steps > n {
                break;
            }
        }
        cur == start && steps == n && transps.iter().any(|&(a, b)| map.get(&a) == Some(&b) || map.get(&b) == Some(&a))
    })
}

struct UnionFind {
    parent: Vec<usize>,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        Self { parent: (0..n).collect() }
    }

    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]];
            x = self.parent[x];
        }
        x
    }

    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.parent[rb] = ra;
        }
    }
}

/// One full symmetric-group factor `Sym(K_g)` over `keys` sorted strictly
/// ascending in TLC order (`Sym::cmp`).
#[derive(Clone)]
pub(super) struct Factor {
    pub(super) keys: Vec<Sym>,
    /// Pre-built `Value::ModelValue(k)` matching `keys` so `PermMap::get`
    /// returns `&Value` with zero allocation.
    pub(super) values: Vec<Value>,
    /// Start offset of this factor in flat per-key arrays (`Partition`, tables).
    pub(super) offset: usize,
}

/// A disjoint product of full symmetric groups `prod_g Sym(K_g)`.
#[derive(Clone)]
pub(super) struct FactorizedGroup {
    pub(super) factors: Vec<Factor>,
    /// Sorted by `sym.id()` for fast lookup: `(sym_id, factor_idx, key_idx)`.
    key_index: Vec<(u32, u16, u16)>,
    min_id: u32,
    max_id: u32,
    pub(super) total_keys: usize,
    /// Exact group order `prod_g |K_g|!`, saturating at `u128::MAX`.
    pub(super) order: u128,
    /// Original presentation for exact TLC fallible-comparison walk order.
    fallback: FallbackOrder,
}

impl FactorizedGroup {
    pub(super) fn new(raw_factors: Vec<Vec<Sym>>, fallback: FallbackOrder) -> EResult<FactorizedGroup> {
        // Factor ids are zero-based, but partition blocks also store the exclusive
        // end of each factor in a u16.
        if raw_factors.len() > usize::from(u16::MAX) + 1 {
            return Err(EvalError::new(format!("SYMMETRY has {} factors, exceeding the limit of 65536", raw_factors.len())));
        }
        if let Some(keys) = raw_factors.iter().find(|keys| keys.len() > usize::from(u16::MAX)) {
            return Err(EvalError::new(format!("SYMMETRY factor has {} model values, exceeding the limit of 65535", keys.len())));
        }
        let mut factors = Vec::with_capacity(raw_factors.len());
        let mut key_index = Vec::new();
        let mut offset = 0usize;
        let mut order: u128 = 1;
        for (g, keys) in raw_factors.into_iter().enumerate() {
            debug_assert!(keys.len() >= 2);
            for k in 2..=(keys.len() as u128) {
                order = order.saturating_mul(k);
            }
            for (k, &s) in keys.iter().enumerate() {
                key_index.push((s.id(), g as u16, k as u16));
            }
            let values = keys.iter().copied().map(Value::ModelValue).collect();
            let len = keys.len();
            factors.push(Factor { keys, values, offset });
            offset += len;
        }
        key_index.sort_unstable_by_key(|&(id, _, _)| id);
        let min_id = key_index.first().map_or(u32::MAX, |&(id, _, _)| id);
        let max_id = key_index.last().map_or(0, |&(id, _, _)| id);
        Ok(FactorizedGroup { factors, key_index, min_id, max_id, total_keys: offset, order, fallback })
    }

    /// Encode a single `Perm` into this group's flat image table.
    pub(super) fn perm_to_img(&self, p: &Perm) -> Vec<u16> {
        let mut img = self.identity_img();
        for (&k, v) in p {
            if let (Some((g, ki)), Value::ModelValue(m)) = (self.lookup(k), v) {
                if let Some((mg, mi)) = self.lookup(*m) {
                    debug_assert_eq!(g, mg);
                    img[self.factors[g].offset + ki] = mi as u16;
                }
            }
        }
        img
    }

    pub(super) fn identity_img(&self) -> Vec<u16> {
        let mut img = vec![0u16; self.total_keys];
        for f in &self.factors {
            for i in 0..f.keys.len() {
                img[f.offset + i] = i as u16;
            }
        }
        img
    }

    pub(super) fn set_fallback(&mut self, fallback: FallbackOrder) {
        self.fallback = fallback;
    }

    #[inline]
    pub(super) fn lookup(&self, m: Sym) -> Option<(usize, usize)> {
        let id = m.id();
        if id < self.min_id || id > self.max_id {
            return None;
        }
        if self.key_index.len() <= 8 {
            for &(k, g, ki) in &self.key_index {
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

    /// Materialize all `order - 1` non-identity `Perm`s in exact mixed-radix
    /// lexicographical order matching `rank_of` (only called when `order <= 720`).
    pub(super) fn materialize_perms(&self) -> Vec<Perm> {
        debug_assert!(self.order <= MAX_MATERIALIZED_ORDER);
        let per_factor: Vec<Vec<Vec<u16>>> = self.factors.iter().map(|f| lex_permutations(f.keys.len())).collect();
        let mut out = Vec::with_capacity(self.order.saturating_sub(1) as usize);
        let mut chosen: Vec<usize> = vec![0; self.factors.len()];
        fn emit(fg: &FactorizedGroup, per_factor: &[Vec<Vec<u16>>], rev_g: usize, chosen: &mut [usize], out: &mut Vec<Perm>) {
            if rev_g == 0 {
                if chosen.iter().all(|&i| i == 0) {
                    return;
                }
                let mut m = HashMap::new();
                for (fi, f) in fg.factors.iter().enumerate() {
                    let img = &per_factor[fi][chosen[fi]];
                    for (k, &t) in img.iter().enumerate() {
                        if t as usize != k {
                            m.insert(f.keys[k], f.values[t as usize].clone());
                        }
                    }
                }
                out.push(m);
                return;
            }
            let g = rev_g - 1;
            for i in 0..per_factor[g].len() {
                chosen[g] = i;
                emit(fg, per_factor, g, chosen, out);
            }
        }
        emit(self, &per_factor, self.factors.len(), &mut chosen, &mut out);
        out
    }

    /// Mixed-radix Lehmer rank of a flat image table `img` minus 1 (`None` for
    /// identity), matching `materialize_perms()` index.
    pub(super) fn rank_of_img(&self, img: &[u16]) -> Option<usize> {
        debug_assert!(self.order <= MAX_MATERIALIZED_ORDER);
        let mut rank: usize = 0;
        for f in self.factors.iter().rev() {
            let n = f.keys.len();
            let mut fact = 1usize;
            for x in 2..=n {
                fact *= x;
            }
            rank = rank * fact + lehmer_rank(&img[f.offset..f.offset + n]);
        }
        (rank > 0).then_some(rank - 1)
    }

    /// Mixed-radix Lehmer rank of `part`'s canonical representative permutation
    /// minus 1 (`None` for the identity), matching `materialize_perms()` index.
    /// Computes one factor at a time so products with `total_keys > INLINE_KEYS`
    /// (e.g. nine disjoint pairs: order 512, 18 keys) never overflow fixed scratch.
    pub(super) fn rank_of(&self, part: &Partition) -> Option<usize> {
        debug_assert!(self.order <= MAX_MATERIALIZED_ORDER);
        let mut rank: usize = 0;
        let dom = part.dom();
        let tgt = part.tgt();
        // Order <= 720 implies every factor has length <= 6 (7! = 5040 > 720).
        let mut img = [0u16; 6];
        for f in self.factors.iter().rev() {
            let n = f.keys.len();
            debug_assert!(n <= img.len());
            for pos in 0..n {
                let k = dom[f.offset + pos] as usize;
                img[k] = tgt[f.offset + pos];
            }
            let mut fact = 1usize;
            for x in 2..=n {
                fact *= x;
            }
            rank = rank * fact + lehmer_rank(&img[..n]);
        }
        (rank > 0).then_some(rank - 1)
    }

    /// Lazily visit every non-identity permutation in exact TLC normalized
    /// generator & `close_under_composition` order without capping at order 720.
    /// Stops early if `visit` returns `ControlFlow::Break(())` or once all
    /// `self.order - 1` non-identity permutations have been visited.
    pub(super) fn for_each_perm_tlc_order(&self, mut visit: impl FnMut(&[u16]) -> EResult<ControlFlow<()>>) -> EResult<()> {
        match &self.fallback {
            FallbackOrder::DisjointFull => {
                fn visit_round(
                    fg: &FactorizedGroup,
                    w: usize,
                    min_factor: usize,
                    img: &mut [u16],
                    visit: &mut impl FnMut(&[u16]) -> EResult<ControlFlow<()>>,
                ) -> EResult<ControlFlow<()>> {
                    if w == 0 {
                        return visit(img);
                    }
                    let k = fg.factors.len();
                    for g in min_factor..=(k - w) {
                        let f = &fg.factors[g];
                        let off = f.offset;
                        let n = f.keys.len();
                        for i in 0..n {
                            img[off + i] = i as u16;
                        }
                        while next_permutation(&mut img[off..off + n]) {
                            if visit_round(fg, w - 1, g + 1, img, visit)?.is_break() {
                                return Ok(ControlFlow::Break(()));
                            }
                        }
                        for i in 0..n {
                            img[off + i] = i as u16;
                        }
                    }
                    Ok(ControlFlow::Continue(()))
                }

                let mut img = self.identity_img();
                for w in 1..=self.factors.len() {
                    if visit_round(self, w, 0, &mut img, &mut visit)?.is_break() {
                        break;
                    }
                }
                Ok(())
            }
            FallbackOrder::OverlappingSets(sets) => {
                let id_img = self.identity_img();
                let target = self.order.saturating_sub(1);
                let mut perms: Vec<Vec<u16>> = Vec::new();
                let mut left_set: Vec<Option<usize>> = Vec::new();
                let mut seen: HashSet<Vec<u16>> = HashSet::new();
                for (set_idx, s) in sets.iter().enumerate() {
                    let mapped: Vec<(usize, u16)> = s
                        .iter()
                        .map(|&m| {
                            let (g, ki) = self.lookup(m).expect("generator key in merged factor");
                            (self.factors[g].offset + ki, ki as u16)
                        })
                        .collect();
                    let mut p: Vec<u16> = (0..s.len() as u16).collect();
                    while next_permutation(&mut p) {
                        let mut img = id_img.clone();
                        for (idx, &t) in p.iter().enumerate() {
                            img[mapped[idx].0] = mapped[t as usize].1;
                        }
                        if img != id_img && seen.insert(img.clone()) {
                            if visit(&img)?.is_break() {
                                return Ok(());
                            }
                            perms.push(img);
                            left_set.push(Some(set_idx));
                            if perms.len() as u128 >= target {
                                return Ok(());
                            }
                        }
                    }
                }
                self.stream_bfs_closure(id_img, perms, left_set, seen, &mut visit)
            }
            FallbackOrder::ExplicitGens(gens) => {
                let id_img = self.identity_img();
                let target = self.order.saturating_sub(1);
                let mut perms: Vec<Vec<u16>> = Vec::with_capacity(gens.len());
                let mut left_set: Vec<Option<usize>> = Vec::with_capacity(gens.len());
                let mut seen: HashSet<Vec<u16>> = HashSet::with_capacity(gens.len());
                for g in gens {
                    if *g != id_img && seen.insert(g.clone()) {
                        if visit(g)?.is_break() {
                            return Ok(());
                        }
                        perms.push(g.clone());
                        left_set.push(None);
                        if perms.len() as u128 >= target {
                            return Ok(());
                        }
                    }
                }
                self.stream_bfs_closure(id_img, perms, left_set, seen, &mut visit)
            }
        }
    }

    /// Stream the exact `close_under_composition` BFS rounds starting from
    /// already-visited generators `perms`, invoking `visit` as soon as each
    /// composed image is discovered and stopping immediately once all
    /// `self.order - 1` non-identity permutations are found or `visit` breaks.
    ///
    /// When generators come from closed `Sym(S_k)` subgroups (`left_set[idx] == Some(k)`),
    /// any composition `g_i * (g_k * tail)` with `left_set[i] == left_set[j] == Some(k)`
    /// collapses inside `Sym(S_k)` to an already-visited element of an earlier
    /// round and is skipped without changing the first-visit sequence.
    fn stream_bfs_closure(
        &self,
        id_img: Vec<u16>,
        mut perms: Vec<Vec<u16>>,
        mut left_set: Vec<Option<usize>>,
        mut seen: HashSet<Vec<u16>>,
        visit: &mut impl FnMut(&[u16]) -> EResult<ControlFlow<()>>,
    ) -> EResult<()> {
        let target = self.order.saturating_sub(1);
        if perms.len() as u128 >= target {
            return Ok(());
        }
        let generators = perms.len();
        let mut start = 0usize;
        let mut composed = vec![0u16; self.total_keys];
        loop {
            let end = perms.len();
            for i in 0..generators {
                let si = left_set[i];
                for j in start..end {
                    if si.is_some() && si == left_set[j] {
                        continue;
                    }
                    #[cfg(test)]
                    BFS_COMPOSITIONS.with(|c| c.set(c.get() + 1));
                    let p = &perms[i];
                    let q = &perms[j];
                    for f in &self.factors {
                        let off = f.offset;
                        for k in 0..f.keys.len() {
                            composed[off + k] = p[off + q[off + k] as usize];
                        }
                    }
                    if composed != id_img && !seen.contains(&composed) {
                        if visit(&composed)?.is_break() {
                            return Ok(());
                        }
                        let next = composed.clone();
                        seen.insert(next.clone());
                        perms.push(next);
                        left_set.push(si);
                        if perms.len() as u128 >= target {
                            return Ok(());
                        }
                    }
                }
            }
            if perms.len() == end {
                break;
            }
            start = end;
        }
        Ok(())
    }
}

#[cfg(test)]
thread_local! {
    pub(super) static BFS_COMPOSITIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

pub(super) fn lex_permutations(n: usize) -> Vec<Vec<u16>> {
    let mut cur: Vec<u16> = (0..n as u16).collect();
    let mut out = Vec::new();
    loop {
        out.push(cur.clone());
        if !next_permutation(&mut cur) {
            break;
        }
    }
    out
}

fn next_permutation(a: &mut [u16]) -> bool {
    let n = a.len();
    if n < 2 {
        return false;
    }
    let mut i = n - 2;
    while a[i] >= a[i + 1] {
        if i == 0 {
            return false;
        }
        i -= 1;
    }
    let mut j = n - 1;
    while a[j] <= a[i] {
        j -= 1;
    }
    a.swap(i, j);
    a[i + 1..].reverse();
    true
}

fn lehmer_rank(img: &[u16]) -> usize {
    let n = img.len();
    let mut rank = 0usize;
    let mut fact = 1usize;
    for i in (0..n).rev() {
        let mut smaller = 0usize;
        for j in (i + 1)..n {
            if img[j] < img[i] {
                smaller += 1;
            }
        }
        rank += smaller * fact;
        fact *= n - i;
    }
    rank
}

/// Backing storage for the 5 flat per-key arrays of `Partition`:
/// `dom`, `tgt`, `pos_of`, `block_lo`, `block_hi` laid out contiguously with
/// stride `stride = fg.total_keys`.
#[derive(Clone)]
enum PartBuf {
    Inline { buf: [u16; INLINE_KEYS * 5], stride: usize },
    Heap { buf: Vec<u16>, stride: usize },
}

impl Default for PartBuf {
    fn default() -> Self {
        PartBuf::Inline { buf: [0; INLINE_KEYS * 5], stride: 0 }
    }
}

impl PartBuf {
    #[inline]
    fn stride(&self) -> usize {
        match self {
            PartBuf::Inline { stride, .. } | PartBuf::Heap { stride, .. } => *stride,
        }
    }

    #[inline]
    fn raw(&self) -> &[u16] {
        match self {
            PartBuf::Inline { buf, stride } => &buf[..stride * 5],
            PartBuf::Heap { buf, .. } => buf,
        }
    }

    #[inline]
    fn split_mut(&mut self) -> (&mut [u16], &mut [u16], &mut [u16], &mut [u16], &mut [u16]) {
        let s = self.stride();
        let raw = match self {
            PartBuf::Inline { buf, .. } => &mut buf[..s * 5],
            PartBuf::Heap { buf, .. } => buf.as_mut_slice(),
        };
        let (dom, rest) = raw.split_at_mut(s);
        let (tgt, rest) = rest.split_at_mut(s);
        let (pos_of, rest) = rest.split_at_mut(s);
        let (block_lo, block_hi) = rest.split_at_mut(s);
        (dom, tgt, pos_of, block_lo, block_hi)
    }

    fn alloc(&mut self, stride: usize) {
        if stride <= INLINE_KEYS {
            *self = PartBuf::Inline { buf: [0; INLINE_KEYS * 5], stride };
        } else {
            let need = stride * 5;
            match self {
                PartBuf::Heap { buf, stride: s } => {
                    buf.resize(need, 0);
                    *s = stride;
                }
                PartBuf::Inline { .. } => {
                    *self = PartBuf::Heap { buf: vec![0; need], stride };
                }
            }
        }
    }

    fn heap_bytes(&self) -> usize {
        match self {
            PartBuf::Inline { .. } => 0,
            PartBuf::Heap { buf, .. } => buf.capacity() * std::mem::size_of::<u16>(),
        }
    }
}

/// Ordered block partition of every factor `K_g`: each block `[lo, hi)` maps
/// the domain keys `dom[off + lo .. off + hi]` bijectively onto the target
/// slots `tgt[off + lo .. off + hi]`, which are always kept sorted ascending.
#[derive(Clone, Default)]
pub(super) struct Partition {
    buf: PartBuf,
    /// Number of slots sitting in blocks of size `>= 2`; `0` means complete.
    pub(super) unpinned: usize,
}

impl Partition {
    #[inline]
    pub(super) fn dom(&self) -> &[u16] {
        let s = self.buf.stride();
        &self.buf.raw()[..s]
    }

    #[inline]
    pub(super) fn tgt(&self) -> &[u16] {
        let s = self.buf.stride();
        &self.buf.raw()[s..2 * s]
    }

    #[inline]
    pub(super) fn pos_of(&self) -> &[u16] {
        let s = self.buf.stride();
        &self.buf.raw()[2 * s..3 * s]
    }

    #[inline]
    pub(super) fn block_lo(&self) -> &[u16] {
        let s = self.buf.stride();
        &self.buf.raw()[3 * s..4 * s]
    }

    #[inline]
    pub(super) fn block_hi(&self) -> &[u16] {
        let s = self.buf.stride();
        &self.buf.raw()[4 * s..5 * s]
    }

    #[cfg(test)]
    pub(super) fn set_singleton(&mut self, idx: usize, dom_k: u16, tgt_t: u16, local_pos: u16) {
        let (dom, tgt, pos_of, block_lo, block_hi) = self.buf.split_mut();
        dom[idx] = dom_k;
        tgt[idx] = tgt_t;
        pos_of[idx] = local_pos;
        block_lo[idx] = local_pos;
        block_hi[idx] = local_pos + 1;
    }

    pub(super) fn reset(&mut self, fg: &FactorizedGroup) {
        let total = fg.total_keys;
        self.buf.alloc(total);
        let (dom, tgt, pos_of, block_lo, block_hi) = self.buf.split_mut();
        for f in &fg.factors {
            let off = f.offset;
            let n = f.keys.len() as u16;
            for i in 0..n {
                let idx = off + i as usize;
                dom[idx] = i;
                tgt[idx] = i;
                pos_of[idx] = i;
                block_lo[idx] = 0;
                block_hi[idx] = n;
            }
        }
        self.unpinned = total;
    }

    #[inline]
    pub(super) fn is_complete(&self) -> bool {
        self.unpinned == 0
    }

    #[inline]
    pub(super) fn is_pinned(&self, fg: &FactorizedGroup, g: usize, k: usize) -> bool {
        let off = fg.factors[g].offset;
        let pos = self.pos_of()[off + k] as usize;
        self.block_hi()[off + pos] - self.block_lo()[off + pos] == 1
    }

    /// Pin domain key `(g, k)` to the target slot at position `slot_pos` within
    /// its current block `[lo, hi)`, keeping remaining target slots sorted.
    pub(super) fn pin_to_slot(&mut self, fg: &FactorizedGroup, g: usize, k: usize, slot_pos: usize) {
        let off = fg.factors[g].offset;
        let (dom, tgt, pos_of, block_lo, block_hi) = self.buf.split_mut();
        let p = pos_of[off + k] as usize;
        let lo = block_lo[off + p] as usize;
        let hi = block_hi[off + p] as usize;
        debug_assert!(slot_pos >= lo && slot_pos < hi);
        if hi - lo == 1 {
            return;
        }
        if p != lo {
            let other = dom[off + lo] as usize;
            dom[off + lo] = k as u16;
            dom[off + p] = other as u16;
            pos_of[off + k] = lo as u16;
            pos_of[off + other] = p as u16;
        }
        if slot_pos != lo {
            let t = tgt[off + slot_pos];
            tgt.copy_within((off + lo)..(off + slot_pos), off + lo + 1);
            tgt[off + lo] = t;
        }
        block_hi[off + lo] = (lo + 1) as u16;
        for q in (lo + 1)..hi {
            block_lo[off + q] = (lo + 1) as u16;
        }
        self.unpinned -= 1 + usize::from(hi - (lo + 1) == 1);
    }

    /// Rule 1: pin `(g, k)` to the smallest target slot in its current block.
    #[inline]
    pub(super) fn pin_smallest(&mut self, fg: &FactorizedGroup, g: usize, k: usize) {
        let off = fg.factors[g].offset;
        let p = self.pos_of()[off + k] as usize;
        let lo = self.block_lo()[off + p] as usize;
        self.pin_to_slot(fg, g, k, lo);
    }

    /// Rule 2: refine every block `B` of factor `g` into `(B \cap S)` followed
    /// by `(B \setminus S)`, mapping members onto the smallest target slots.
    pub(super) fn split_by_mask(&mut self, fg: &FactorizedGroup, g: usize, in_set: &[bool], scratch: &mut Vec<u16>) {
        let off = fg.factors[g].offset;
        let n = fg.factors[g].keys.len();
        let (dom, _, pos_of, block_lo, block_hi) = self.buf.split_mut();
        let mut lo = 0usize;
        while lo < n {
            let hi = block_hi[off + lo] as usize;
            if hi - lo > 1 {
                scratch.clear();
                let mut write = lo;
                for pos in lo..hi {
                    let k = dom[off + pos];
                    if in_set[k as usize] {
                        dom[off + write] = k;
                        write += 1;
                    } else {
                        scratch.push(k);
                    }
                }
                let mid = write;
                if mid > lo && mid < hi {
                    dom[off + mid..off + hi].copy_from_slice(scratch);
                    for pos in lo..hi {
                        let k = dom[off + pos] as usize;
                        pos_of[off + k] = pos as u16;
                    }
                    for pos in lo..mid {
                        block_hi[off + pos] = mid as u16;
                    }
                    for pos in mid..hi {
                        block_lo[off + pos] = mid as u16;
                    }
                    self.unpinned -= usize::from(mid - lo == 1) + usize::from(hi - mid == 1);
                }
            }
            lo = hi;
        }
    }

    /// Place `chosen` (a non-empty subset of `dom[off + lo .. off + hi]`) into
    /// `[lo, lo + chosen.len())` and the remainder into `[lo + chosen.len(), hi)`.
    pub(super) fn bulk_place_first(&mut self, fg: &FactorizedGroup, g: usize, lo: usize, chosen: &[u16]) {
        let off = fg.factors[g].offset;
        let (dom, _, pos_of, block_lo, block_hi) = self.buf.split_mut();
        let hi = block_hi[off + lo] as usize;
        let m = chosen.len();
        debug_assert!(m > 0 && lo + m <= hi);
        if lo + m == hi {
            return;
        }
        let mut rest = Vec::with_capacity(hi - lo - m);
        for pos in lo..hi {
            let k = dom[off + pos];
            if !chosen.contains(&k) {
                rest.push(k);
            }
        }
        let mid = lo + m;
        dom[off + lo..off + mid].copy_from_slice(chosen);
        dom[off + mid..off + hi].copy_from_slice(&rest);
        for pos in lo..hi {
            let k = dom[off + pos] as usize;
            pos_of[off + k] = pos as u16;
        }
        for pos in lo..mid {
            block_hi[off + pos] = mid as u16;
        }
        for pos in mid..hi {
            block_lo[off + pos] = mid as u16;
        }
        self.unpinned -= usize::from(mid - lo == 1) + usize::from(hi - mid == 1);
    }

    /// Rule 3: for every block `B \subseteq D` of factor `g` with `|B| >= 2`,
    /// stably sort `B` by fallible `cmp` and split into tied sub-blocks.
    pub(super) fn refine_by_cmp<F>(
        &mut self,
        fg: &FactorizedGroup,
        g: usize,
        in_dom: &[bool],
        mut cmp: F,
        scratch: &mut Vec<u16>,
    ) -> EResult<()>
    where
        F: FnMut(u16, u16) -> tlx_value::Result<Ordering>,
    {
        let off = fg.factors[g].offset;
        let n = fg.factors[g].keys.len();
        let (dom, _, pos_of, block_lo, block_hi) = self.buf.split_mut();
        let mut lo = 0usize;
        while lo < n {
            let hi = block_hi[off + lo] as usize;
            if hi - lo > 1 && in_dom[dom[off + lo] as usize] {
                fallible_stable_sort(&mut dom[off + lo..off + hi], &mut cmp, scratch)?;
                for pos in lo..hi {
                    let k = dom[off + pos] as usize;
                    pos_of[off + k] = pos as u16;
                }
                let mut sub_lo = lo;
                while sub_lo < hi {
                    let mut sub_hi = sub_lo + 1;
                    while sub_hi < hi && cmp(dom[off + sub_hi - 1], dom[off + sub_hi])? == Ordering::Equal {
                        sub_hi += 1;
                    }
                    if sub_lo > lo || sub_hi < hi {
                        for pos in sub_lo..sub_hi {
                            block_lo[off + pos] = sub_lo as u16;
                            block_hi[off + pos] = sub_hi as u16;
                        }
                        if sub_hi - sub_lo == 1 {
                            self.unpinned -= 1;
                        }
                    }
                    sub_lo = sub_hi;
                }
            }
            lo = hi;
        }
        Ok(())
    }

    /// Fill `img` (length `fg.total_keys`) with `img[off + k] = target(k)` for
    /// this partition's current representative bijection `dom[pos] -> tgt[pos]`.
    pub(super) fn fill_img(&self, fg: &FactorizedGroup, img: &mut Vec<u16>) {
        img.resize(fg.total_keys, 0);
        self.fill_img_slice(fg, img);
    }

    /// Fill `dst` (`dst.len() >= fg.total_keys`) with `dst[off + k] = target(k)`.
    pub(super) fn fill_img_slice(&self, fg: &FactorizedGroup, dst: &mut [u16]) {
        let dom = self.dom();
        let tgt = self.tgt();
        for f in &fg.factors {
            let off = f.offset;
            for pos in 0..f.keys.len() {
                let k = dom[off + pos] as usize;
                dst[off + k] = tgt[off + pos];
            }
        }
    }

    /// Build a zero-allocation `ChosenPerm` for `fg.total_keys <= INLINE_KEYS`,
    /// or heap-backed for larger groups.
    pub(super) fn to_chosen_perm<'a>(&self, fg: &'a FactorizedGroup) -> ChosenPerm<'a> {
        if fg.total_keys <= INLINE_KEYS {
            let mut img = [0u16; INLINE_KEYS];
            self.fill_img_slice(fg, &mut img);
            ChosenPerm::factor_inline(fg, img)
        } else {
            let mut img = vec![0u16; fg.total_keys];
            self.fill_img_slice(fg, &mut img);
            ChosenPerm::factor_heap(fg, img)
        }
    }

    /// True iff the identity permutation is consistent with this partition
    /// (every domain key `k` lies in a block whose target set contains `k`).
    pub(super) fn contains_identity(&self, fg: &FactorizedGroup) -> bool {
        let dom = self.dom();
        let tgt = self.tgt();
        let block_lo = self.block_lo();
        let block_hi = self.block_hi();
        for f in &fg.factors {
            let off = f.offset;
            for pos in 0..f.keys.len() {
                let k = dom[off + pos];
                let lo = block_lo[off + pos] as usize;
                let hi = block_hi[off + pos] as usize;
                if hi - lo == 1 {
                    if tgt[off + lo] != k {
                        return false;
                    }
                } else if tgt[off + lo..off + hi].binary_search(&k).is_err() {
                    return false;
                }
            }
        }
        true
    }

    /// Sort `dom[lo..hi]` ascending inside any remaining unpinned block so the
    /// representative permutation maximizes fixed points and is deterministic.
    pub(super) fn canonicalize_unpinned_blocks(&mut self, fg: &FactorizedGroup) {
        let (dom, _, pos_of, _, block_hi) = self.buf.split_mut();
        for f in &fg.factors {
            let off = f.offset;
            let n = f.keys.len();
            let mut lo = 0usize;
            while lo < n {
                let hi = block_hi[off + lo] as usize;
                if hi - lo > 1 {
                    dom[off + lo..off + hi].sort_unstable();
                    for pos in lo..hi {
                        let k = dom[off + pos] as usize;
                        pos_of[off + k] = pos as u16;
                    }
                }
                lo = hi;
            }
        }
    }

    /// Materialize the winning representative permutation as a `FastPerm` (tests).
    #[cfg(test)]
    pub(super) fn to_fast_perm(&self, fg: &FactorizedGroup) -> FastPerm {
        let dom = self.dom();
        let tgt = self.tgt();
        let mut entries = Vec::new();
        for f in &fg.factors {
            let off = f.offset;
            for pos in 0..f.keys.len() {
                let k = dom[off + pos] as usize;
                let t = tgt[off + pos] as usize;
                if k != t {
                    entries.push((f.keys[k].id(), f.values[t].clone()));
                }
            }
        }
        FastPerm(entries)
    }

    /// Approximate heap bytes for `BagCache` memory accounting.
    pub(super) fn heap_bytes(&self) -> usize {
        self.buf.heap_bytes()
    }
}

/// Fallible stable sort: insertion sort for small slices (`<= 16`), bottom-up
/// merge sort using `scratch` for larger blocks.
fn fallible_stable_sort<F>(slice: &mut [u16], cmp: &mut F, scratch: &mut Vec<u16>) -> EResult<()>
where
    F: FnMut(u16, u16) -> tlx_value::Result<Ordering>,
{
    let n = slice.len();
    if n <= 16 {
        for i in 1..n {
            let key = slice[i];
            let mut j = i;
            while j > 0 && cmp(key, slice[j - 1])? == Ordering::Less {
                slice[j] = slice[j - 1];
                j -= 1;
            }
            slice[j] = key;
        }
        return Ok(());
    }
    scratch.resize(n, 0);
    let mut width = 1usize;
    while width < n {
        let mut lo = 0usize;
        while lo < n {
            let mid = (lo + width).min(n);
            let hi = (lo + 2 * width).min(n);
            let (mut i, mut j, mut out) = (lo, mid, lo);
            while i < mid && j < hi {
                if cmp(slice[j], slice[i])? == Ordering::Less {
                    scratch[out] = slice[j];
                    j += 1;
                } else {
                    scratch[out] = slice[i];
                    i += 1;
                }
                out += 1;
            }
            while i < mid {
                scratch[out] = slice[i];
                i += 1;
                out += 1;
            }
            while j < hi {
                scratch[out] = slice[j];
                j += 1;
                out += 1;
            }
            slice[lo..hi].copy_from_slice(&scratch[lo..hi]);
            lo = hi;
        }
        width *= 2;
    }
    Ok(())
}
