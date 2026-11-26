//! SYMMETRY on encodings: factorized partition-refinement canonicalization for
//! disjoint symmetric-group products `S_{n_1} x ... x S_{n_k}`, with explicit
//! `Vec<PermPlan>` fallback for arbitrary non-full subgroups.

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::sync::Arc;

use tlx_base::partition::{ImgBuf, Partition, INLINE_KEYS};
use tlx_eval::InterpModel;
use tlx_layout::pack::{FieldLoc, SlotLayout};
use tlx_layout::permute::{AtomPerm, AtomTable, DomMap, FactorGroupSpec, FactorPlan, PermPlan};
use tlx_layout::{Layout, LayoutNode};
use tlx_native::fp_words;
use tlx_runtime::ModelError;
use tlx_value::{Sym, Value};

use super::SemFp;

/// Compiled encoded-word SYMMETRY engine: factorized partition refinement for
/// disjoint symmetric-group products of any order (`|G| <= 720` and `|G| > 720`),
/// or explicit per-element `PermPlan` iteration for arbitrary non-full subgroups.
pub(super) enum SymmetryEngine {
    Factorized(FactorSymmetry),
    Explicit(SymmetryPlans),
}

/// Per-variable factorized symmetry plans for `prod_g Sym(K_g)`.
pub(super) struct FactorSymmetry {
    pub(super) fg: FactorGroupSpec,
    /// Precomputed identity image table for `fg` (zero-alloc identity evaluation).
    id_img: Box<[u16]>,
    /// One factor plan per variable in the layout (no `|G|` materialization).
    pub(super) plans: Vec<FactorPlan>,
    /// Precomputed: whether variable `i` contains any `>= 2`-word bitset.
    wide_bitset: Box<[bool]>,
    /// Precomputed: whether variable `i` contains any `Shape::Dyn` slot.
    has_dyn_var: Box<[bool]>,
    /// Precomputed: whether any variable in the layout contains `Shape::Dyn`.
    has_dyn: bool,
    /// Non-identity variables ordered for `orbit_fp`: zero-branching
    /// deterministic plans (`Atom`, `BitsetAtom`, invariant-payload `Fcn`/`Map`)
    /// first, then remaining variables narrowest-first.
    orbit_order: Box<[usize]>,
    /// Precomputed: every variable is `!has_dyn_or_ref() && is_orbit_cmp_safe()`,
    /// so `SymView` word-level TLC comparison is total and error-free.
    pub(super) all_orbit_cmp_safe: bool,
}

impl FactorSymmetry {
    fn new(fg: FactorGroupSpec, plans: Vec<FactorPlan>, layout: &Layout) -> Self {
        let id_img: Box<[u16]> = fg.identity_img().into();
        let wide_bitset: Box<[bool]> = plans.iter().map(FactorPlan::has_wide_bitset).collect();
        let has_dyn_var: Box<[bool]> = plans.iter().map(FactorPlan::has_dyn).collect();
        let has_dyn = has_dyn_var.iter().any(|&b| b);
        let orbit_order = build_orbit_order(layout, &plans);
        let all_orbit_cmp_safe = (0..layout.vars.len()).all(|i| {
            let n = layout.node(i);
            !n.has_dyn_or_ref() && n.is_orbit_cmp_safe()
        });
        Self { fg, id_img, plans, wide_bitset, has_dyn_var, has_dyn, orbit_order, all_orbit_cmp_safe }
    }
}

fn refinement_tier(plan: &FactorPlan) -> u8 {
    match plan {
        FactorPlan::Atom(_) => 0,
        FactorPlan::BitsetAtom { .. } => 1,
        FactorPlan::Fcn { dom: DomMap::DirectFactor { .. }, range, .. } if range.is_identity() => 2,
        FactorPlan::Map { key, range, .. } if range.is_identity() && key.atom_table().is_some_and(|t| t.direct_factor.is_some()) => 2,
        _ => 3,
    }
}

fn build_orbit_order(layout: &Layout, plans: &[FactorPlan]) -> Box<[usize]> {
    let width = |i: usize| layout.offsets.get(i + 1).copied().unwrap_or(layout.words) - layout.offsets[i];
    let mut order: Vec<usize> = (0..plans.len()).filter(|&i| !plans[i].is_identity()).collect();
    order.sort_by_key(|&i| (refinement_tier(&plans[i]), width(i), i));
    order.into()
}

/// Plans applying each SYMMETRY element to the state layout, with the order
/// its permutations must be visited in a fallible-by-value selection.
pub(super) struct SymmetryPlans {
    /// One plan per variable, indexed like `InterpModel::symmetry_maps()`.
    pub(super) group: Vec<Vec<PermPlan>>,
    /// Indices into `group` in the interpreter's fallible comparison order
    /// (`InterpModel::symmetry_maps_tlc_order`).
    pub(super) visit: Vec<usize>,
}

/// Compile encoded-word SYMMETRY support for `layout` (`None` if the model has
/// no symmetry or some variable's shape is not closed under the group).
pub(super) fn compile_symmetry(base: &InterpModel, layout: &Layout, notes: &mut Vec<String>) -> Option<SymmetryEngine> {
    if let Some(factors) = base.symmetry_factors() {
        let fg = FactorGroupSpec::new(&factors);
        let mut plans = Vec::with_capacity(layout.vars.len());
        for (i, s) in layout.vars.iter().enumerate() {
            match FactorPlan::compile(s, &fg) {
                Some(p) => plans.push(p),
                None => {
                    let name = base.ip.prog.vars.get(i).map_or("VIEW", |v| &*v.name);
                    notes.push(format!("symmetry: cannot permute the encoding of {name} ({s:?})"));
                    return None;
                }
            }
        }
        return Some(SymmetryEngine::Factorized(FactorSymmetry::new(fg, plans, layout)));
    }
    let maps = base.symmetry_maps();
    if maps.is_empty() {
        return None;
    }
    // The by-value fallback (and the error a comparison of incompatible values
    // raises) depends on the order permutations are visited; keep it.
    let visit = base.symmetry_maps_tlc_order()?;
    let mut group = Vec::with_capacity(maps.len());
    for m in maps {
        let m = m.clone();
        let perm: AtomPerm = Arc::new(move |v: &Value| match v {
            Value::ModelValue(s) => m.get(s).cloned().unwrap_or_else(|| v.clone()),
            _ => v.clone(),
        });
        let mut plans = Vec::with_capacity(layout.vars.len());
        for (i, s) in layout.vars.iter().enumerate() {
            match PermPlan::compile(s, &perm) {
                Some(p) => plans.push(p),
                None => {
                    let name = base.ip.prog.vars.get(i).map_or("VIEW", |v| &*v.name);
                    notes.push(format!("symmetry: cannot permute the encoding of {name} ({s:?})"));
                    return None;
                }
            }
        }
        group.push(plans);
    }
    if visit.len() != group.len() {
        // The orders must agree on the permutation set; otherwise fall back to
        // the interpreter rather than silently skipping orbit members.
        return None;
    }
    Some(SymmetryEngine::Explicit(SymmetryPlans { group, visit }))
}

/// The variables in the order `orbit_fp` compares them: by increasing
/// width (ties by position). Narrow variables are cheap to permute/refine,
/// often pinning all factors before wide variables are touched.
pub(super) fn symmetry_order(layout: &Layout) -> Vec<usize> {
    let n = layout.vars.len();
    let width = |i: usize| layout.offsets.get(i + 1).copied().unwrap_or(layout.words) - layout.offsets[i];
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by_key(|&i| (width(i), i));
    order
}

// ---------------------------------------------------------------------------
// Word comparison & item application
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
enum WordOrder {
    /// Canonical orbit order for `Fingerprint::Symmetry` / `ProjectionOrbit`.
    /// Plain unsigned slice `.cmp()`, using little-endian multi-word order on
    /// `>= 2`-word bitsets so Rule 2 is exact at every bitset width.
    Orbit,
    /// Exact TLC value order (`LayoutNode::cmp_tlc_words`) for `SymView`.
    Tlc,
}

#[derive(Clone, Copy)]
struct WorkItem<'a> {
    plan: &'a FactorPlan,
    node: &'a LayoutNode,
    /// Original encoded words (real `Ref` handles for `apply_orbit_unchecked`).
    raw: &'a [u64],
    /// Canonicalized words (`Ref` handles replaced by digests, dynamic witness
    /// words zeroed); identical to `raw` when `SemFp` is inactive or in `Tlc` mode.
    canon: &'a [u64],
    wide_bitset: bool,
}

#[inline]
fn cmp_words_mode(mode: WordOrder, plan: &FactorPlan, node: &LayoutNode, wide_bitset: bool, a: &[u64], b: &[u64]) -> Ordering {
    match mode {
        WordOrder::Orbit => {
            if !wide_bitset {
                a[..plan.words()].cmp(&b[..plan.words()])
            } else {
                cmp_orbit_wide(plan, a, b)
            }
        }
        WordOrder::Tlc => node.cmp_tlc_words(a, b).expect("orbit_cmp_safe guarantees total cmp_tlc_words"),
    }
}

fn cmp_orbit_wide(plan: &FactorPlan, a: &[u64], b: &[u64]) -> Ordering {
    match plan {
        FactorPlan::BitsetAtom { words, .. } | FactorPlan::BitsetRank { words, .. } => {
            a[..*words].iter().rev().cmp(b[..*words].iter().rev())
        }
        FactorPlan::Map { dims, range, words, .. } => {
            let bw = dims.bitset_words;
            let c = a[..bw].iter().rev().cmp(b[..bw].iter().rev());
            if c != Ordering::Equal {
                return c;
            }
            if !range.has_wide_bitset() {
                return a[bw..*words].cmp(&b[bw..*words]);
            }
            let SlotLayout::Words(rw) = dims.slot else {
                return a[bw..*words].cmp(&b[bw..*words]);
            };
            for (wi, &w) in a[..bw].iter().enumerate() {
                let mut m = w;
                while m != 0 {
                    let r = wi * 64 + m.trailing_zeros() as usize;
                    m &= m - 1;
                    let o = bw + r * rw;
                    let c = cmp_orbit_wide(range, &a[o..o + rw], &b[o..o + rw]);
                    if c != Ordering::Equal {
                        return c;
                    }
                }
            }
            Ordering::Equal
        }
        FactorPlan::Product { fields, .. } => {
            for (loc, p) in fields.iter() {
                let c = match *loc {
                    FieldLoc::Bits(pos) => pos.extract(a).cmp(&pos.extract(b)),
                    FieldLoc::Words(o) => {
                        let w = p.words();
                        if p.has_wide_bitset() {
                            cmp_orbit_wide(p, &a[o..o + w], &b[o..o + w])
                        } else {
                            a[o..o + w].cmp(&b[o..o + w])
                        }
                    }
                };
                if c != Ordering::Equal {
                    return c;
                }
            }
            Ordering::Equal
        }
        FactorPlan::Fcn { dom, slot, range, .. } => {
            if !range.has_wide_bitset() {
                return a[..plan.words()].cmp(&b[..plan.words()]);
            }
            let SlotLayout::Words(rw) = *slot else {
                return a[..plan.words()].cmp(&b[..plan.words()]);
            };
            for i in 0..dom.len() {
                let o = i * rw;
                let c = cmp_orbit_wide(range, &a[o..o + rw], &b[o..o + rw]);
                if c != Ordering::Equal {
                    return c;
                }
            }
            Ordering::Equal
        }
        FactorPlan::Seq { elem, elem_words, .. } => {
            let c = a[0].cmp(&b[0]);
            if c != Ordering::Equal {
                return c;
            }
            let len = a[0] as usize;
            let ew = *elem_words;
            for i in 0..len {
                let o = 1 + i * ew;
                let c = cmp_orbit_wide(elem, &a[o..o + ew], &b[o..o + ew]);
                if c != Ordering::Equal {
                    return c;
                }
            }
            Ordering::Equal
        }
        FactorPlan::Union { arms, .. } => {
            let c = a[0].cmp(&b[0]);
            if c != Ordering::Equal {
                return c;
            }
            let arm = &arms[a[0] as usize];
            if arm.has_wide_bitset() {
                cmp_orbit_wide(arm, &a[1..], &b[1..])
            } else {
                a[1..1 + arm.words()].cmp(&b[1..1 + arm.words()])
            }
        }
        _ => a[..plan.words()].cmp(&b[..plan.words()]),
    }
}

#[inline]
fn apply_item(mode: WordOrder, fg: &FactorGroupSpec, img: &[u16], item: WorkItem<'_>, dst: &mut [u64]) {
    match mode {
        WordOrder::Orbit => {
            // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
            unsafe { item.plan.apply_orbit_unchecked(fg, img, item.raw, dst) };
            if item.node.has_dynamic_witness() {
                item.node.canonicalize_orbit_words(dst);
            }
        }
        WordOrder::Tlc => {
            // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
            unsafe { item.plan.apply_unchecked(fg, img, item.raw, dst) };
        }
    }
}

#[inline]
fn map_scalar_part(fg: &FactorGroupSpec, table: &AtomTable, part: &Partition, raw: u64) -> u64 {
    match table.code_to_key[raw as usize] {
        None => raw,
        Some((g, k)) => {
            let g = g as usize;
            let t = part.pinned_target(fg, g, k as usize).expect("scalar atom must be pinned") as usize;
            table.key_to_code[fg.factors[g].offset + t]
        }
    }
}

// ---------------------------------------------------------------------------
// Unpinned atom inspection on encoded words
// ---------------------------------------------------------------------------

fn visit_moved_in_value(v: &Value, fg: &FactorGroupSpec, f: &mut impl FnMut(usize, usize)) {
    match v {
        Value::ModelValue(m) => {
            if let Some((g, k)) = fg.lookup(*m) {
                f(g, k);
            }
        }
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => {}
        Value::Set(es) | Value::Tuple(es) => {
            for e in es.iter() {
                visit_moved_in_value(e, fg, f);
            }
        }
        Value::Record(fs) => {
            for (_, e) in fs.iter() {
                visit_moved_in_value(e, fg, f);
            }
        }
        Value::Fcn(ps, _) => {
            for (k, e) in ps.iter() {
                visit_moved_in_value(k, fg, f);
                visit_moved_in_value(e, fg, f);
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

fn for_each_moved_words(fg: &FactorGroupSpec, plan: &FactorPlan, raw: &[u64], f: &mut impl FnMut(usize, usize)) {
    match plan {
        FactorPlan::Copy(_) => {}
        FactorPlan::Atom(table) => {
            if let Some((g, k)) = table.code_to_key[raw[0] as usize] {
                f(g as usize, k as usize);
            }
        }
        FactorPlan::BitsetAtom { table, words } => {
            for (wi, &w) in raw[..*words].iter().enumerate() {
                let mut b = w;
                while b != 0 {
                    let r = wi * 64 + b.trailing_zeros() as usize;
                    b &= b - 1;
                    if let Some((g, k)) = table.code_to_key[r] {
                        f(g as usize, k as usize);
                    }
                }
            }
        }
        FactorPlan::BitsetRank { rank, words } => {
            for (wi, &w) in raw[..*words].iter().enumerate() {
                let mut b = w;
                while b != 0 {
                    let r = (wi * 64 + b.trailing_zeros() as usize) as u64;
                    b &= b - 1;
                    rank.for_each_moved_key(fg, r, f);
                }
            }
        }
        FactorPlan::Sorted { elem, elem_words, .. } | FactorPlan::Seq { elem, elem_words, .. } => {
            let len = raw[0] as usize;
            let ew = *elem_words;
            for i in 0..len {
                for_each_moved_words(fg, elem, &raw[1 + i * ew..1 + (i + 1) * ew], f);
            }
        }
        FactorPlan::SeqBits { bits, table, .. } => {
            let len = raw[0] as usize;
            for i in 0..len {
                let c = SlotLayout::extract(*bits, &raw[1..], i) as usize;
                if let Some((g, k)) = table.code_to_key[c] {
                    f(g as usize, k as usize);
                }
            }
        }
        FactorPlan::Product { fields, .. } => {
            for (loc, fp) in fields.iter() {
                if fp.is_identity() {
                    continue;
                }
                match *loc {
                    FieldLoc::Words(o) => for_each_moved_words(fg, fp, &raw[o..o + fp.words()], f),
                    FieldLoc::Bits(pos) => {
                        if let FactorPlan::Atom(t) = fp {
                            if let Some((g, k)) = t.code_to_key[pos.extract(raw) as usize] {
                                f(g as usize, k as usize);
                            }
                        }
                    }
                }
            }
        }
        FactorPlan::Fcn { dom, slot, range, .. } => {
            dom.for_each_moved_key(fg, f);
            if !range.is_identity() {
                match *slot {
                    SlotLayout::Words(rw) => {
                        for i in 0..dom.len() {
                            for_each_moved_words(fg, range, &raw[i * rw..(i + 1) * rw], f);
                        }
                    }
                    SlotLayout::Bits(bits) => {
                        if let FactorPlan::Atom(t) = range.as_ref() {
                            for i in 0..dom.len() {
                                let c = SlotLayout::extract(bits, raw, i) as usize;
                                if let Some((g, k)) = t.code_to_key[c] {
                                    f(g as usize, k as usize);
                                }
                            }
                        }
                    }
                }
            }
        }
        FactorPlan::Map { key, dims, range, .. } => {
            let bw = dims.bitset_words;
            for (wi, &w) in raw[..bw].iter().enumerate() {
                let mut b = w;
                while b != 0 {
                    let r = wi * 64 + b.trailing_zeros() as usize;
                    b &= b - 1;
                    key.for_each_moved_key(fg, r as u64, f);
                    if !range.is_identity() {
                        match dims.slot {
                            SlotLayout::Words(rw) => {
                                let o = bw + r * rw;
                                for_each_moved_words(fg, range, &raw[o..o + rw], f);
                            }
                            SlotLayout::Bits(bits) => {
                                if let FactorPlan::Atom(t) = range.as_ref() {
                                    let c = SlotLayout::extract(bits, &raw[bw..], r) as usize;
                                    if let Some((g, k)) = t.code_to_key[c] {
                                        f(g as usize, k as usize);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        FactorPlan::Union { arms, .. } => {
            let arm = &arms[raw[0] as usize];
            for_each_moved_words(fg, arm, &raw[1..1 + arm.words()], f);
        }
        FactorPlan::Dyn => {
            // SAFETY: active Dyn handles were published before fingerprinting.
            let v = unsafe { tlx_layout::dynval::lookup_unchecked(raw[0]) };
            visit_moved_in_value(&v, fg, f);
        }
        FactorPlan::Ref(store) => {
            let v = store.thaw(raw[0]);
            visit_moved_in_value(&v, fg, f);
        }
    }
}

fn has_unpinned_words(fg: &FactorGroupSpec, plan: &FactorPlan, raw: &[u64], part: &Partition) -> bool {
    if part.is_complete() || plan.is_identity() {
        return false;
    }
    let mut found = false;
    for_each_moved_words(fg, plan, raw, &mut |g, k| {
        if !found && !part.is_pinned(fg, g, k) {
            found = true;
        }
    });
    found
}

fn has_unpinned_in_factor_words(fg: &FactorGroupSpec, plan: &FactorPlan, raw: &[u64], part: &Partition, target_g: usize) -> bool {
    if part.is_complete() || plan.is_identity() {
        return false;
    }
    let mut found = false;
    for_each_moved_words(fg, plan, raw, &mut |g, k| {
        if !found && g == target_g && !part.is_pinned(fg, g, k) {
            found = true;
        }
    });
    found
}

fn collect_unpinned_words(fg: &FactorGroupSpec, plan: &FactorPlan, raw: &[u64], part: &Partition, out: &mut Vec<(usize, usize)>) {
    out.clear();
    if part.is_complete() || plan.is_identity() {
        return;
    }
    for_each_moved_words(fg, plan, raw, &mut |g, k| {
        if !part.is_pinned(fg, g, k) && !out.contains(&(g, k)) {
            out.push((g, k));
        }
    });
}

// ---------------------------------------------------------------------------
// Deterministic refinement (Rules 1-3) + Branch-and-Bound (Case A & Case B)
// ---------------------------------------------------------------------------

#[derive(Default)]
struct FactorScratch {
    part: Partition,
    sort: Vec<u16>,
    img: ImgBuf,
    payload_buf: Vec<u64>,
    /// Reusable comparison scratch for complete-candidate fast path.
    cand_cur: Vec<u64>,
    cand_best: Vec<u64>,
    /// Output canonicalized state buffer (`orbit_fp`) & per-variable canonicalization scratch.
    out_buf: Vec<u64>,
    var_canon_buf: Vec<u64>,
}

enum DetOutcome<'a> {
    Done,
    /// A single irreducible `WorkItem` needs branching, with no remaining
    /// sibling items (avoids allocating a `Vec<PendingItem>`).
    BranchOne(WorkItem<'a>),
    NeedBranch(Vec<PendingItem<'a>>),
}

#[derive(Clone, Copy)]
enum PendingItem<'a> {
    Word(WorkItem<'a>),
    PackedAtom { table: &'a AtomTable, raw_code: u64 },
}

fn append_product_tail<'a>(fields: &'a [(FieldLoc, FactorPlan)], start: usize, item: WorkItem<'a>, out: &mut Vec<PendingItem<'a>>) {
    for (idx, (loc, fp)) in fields.iter().enumerate().skip(start) {
        if fp.is_identity() {
            continue;
        }
        match *loc {
            FieldLoc::Bits(pos) => {
                if let FactorPlan::Atom(table) = fp {
                    out.push(PendingItem::PackedAtom { table, raw_code: pos.extract(item.raw) });
                }
            }
            FieldLoc::Words(o) => {
                let w = fp.words();
                let child_node = item.node.product_child(idx).expect("product child node");
                out.push(PendingItem::Word(WorkItem {
                    plan: fp,
                    node: child_node,
                    raw: &item.raw[o..o + w],
                    canon: &item.canon[o..o + w],
                    wide_bitset: item.wide_bitset && fp.has_wide_bitset(),
                }));
            }
        }
    }
}

fn product_has_non_identity_tail(fields: &[(FieldLoc, FactorPlan)], start: usize) -> bool {
    fields
        .iter()
        .skip(start)
        .any(|(loc, fp)| !fp.is_identity() && matches!((*loc, fp), (FieldLoc::Words(_), _) | (FieldLoc::Bits(_), FactorPlan::Atom(_))))
}

/// Lazy iterator over set bit indices in a bitset word slice.
struct BitsetIter<'a> {
    words: &'a [u64],
    word_idx: usize,
    cur: u64,
}

impl<'a> BitsetIter<'a> {
    #[inline]
    fn new(words: &'a [u64]) -> Self {
        Self { words, word_idx: 0, cur: words.first().copied().unwrap_or(0) }
    }
}

impl Iterator for BitsetIter<'_> {
    type Item = usize;

    #[inline]
    fn next(&mut self) -> Option<usize> {
        while self.cur == 0 {
            self.word_idx += 1;
            self.cur = *self.words.get(self.word_idx)?;
        }
        let bit = self.cur.trailing_zeros() as usize;
        self.cur &= self.cur - 1;
        Some(self.word_idx * 64 + bit)
    }
}

/// Deterministically refine an ordered sequence of child `WorkItem`s. When a
/// child branches, its pending work precedes every remaining sibling in
/// iterator order so later siblings break ties; deterministic and single-child
/// (`BranchOne` at the end of the iterator) paths remain allocation-free.
fn refine_ordered_children<'a>(
    fg: &FactorGroupSpec,
    part: &mut Partition,
    mut children: impl Iterator<Item = WorkItem<'a>>,
    mode: WordOrder,
    scratch: &mut FactorScratch,
) -> DetOutcome<'a> {
    while let Some(child) = children.next() {
        if part.is_complete() {
            return DetOutcome::Done;
        }
        match refine_deterministic(fg, part, child, mode, scratch) {
            DetOutcome::Done => {}
            DetOutcome::BranchOne(sub) => {
                let Some(next_sibling) = children.next() else {
                    return DetOutcome::BranchOne(sub);
                };
                let mut pending = Vec::with_capacity(2 + children.size_hint().0);
                pending.push(PendingItem::Word(sub));
                pending.push(PendingItem::Word(next_sibling));
                pending.extend(children.map(PendingItem::Word));
                return DetOutcome::NeedBranch(pending);
            }
            DetOutcome::NeedBranch(mut pending) => {
                pending.extend(children.map(PendingItem::Word));
                return DetOutcome::NeedBranch(pending);
            }
        }
    }
    DetOutcome::Done
}

fn refine_deterministic<'a>(
    fg: &FactorGroupSpec,
    part: &mut Partition,
    item: WorkItem<'a>,
    mode: WordOrder,
    scratch: &mut FactorScratch,
) -> DetOutcome<'a> {
    if part.is_complete() || item.plan.is_identity() {
        return DetOutcome::Done;
    }
    match item.plan {
        FactorPlan::Copy(_) => DetOutcome::Done,
        FactorPlan::Atom(table) => {
            if let Some((g, k)) = table.code_to_key[item.raw[0] as usize] {
                part.pin_smallest(fg, g as usize, k as usize);
            }
            DetOutcome::Done
        }
        FactorPlan::BitsetAtom { table, words } => {
            if let Some(g) = table.direct_factor {
                if *words == 1 {
                    let mask = item.raw[0];
                    if mask != 0 {
                        part.split_by_pred(fg, g as usize, |k| (mask >> k) & 1 != 0, &mut scratch.sort);
                    }
                    return DetOutcome::Done;
                }
            }
            for &g in table.active_factors.iter() {
                let g = g as usize;
                let off = fg.factors[g].offset;
                part.split_by_pred(
                    fg,
                    g,
                    |k| {
                        let code = table.key_to_code[off + k] as usize;
                        (item.raw[code / 64] >> (code % 64)) & 1 != 0
                    },
                    &mut scratch.sort,
                );
            }
            DetOutcome::Done
        }
        FactorPlan::Product { fields, .. } => {
            for (idx, (loc, fp)) in fields.iter().enumerate() {
                if part.is_complete() {
                    return DetOutcome::Done;
                }
                if fp.is_identity() {
                    continue;
                }
                match *loc {
                    FieldLoc::Bits(pos) => {
                        if let FactorPlan::Atom(table) = fp {
                            if let Some((g, k)) = table.code_to_key[pos.extract(item.raw) as usize] {
                                part.pin_smallest(fg, g as usize, k as usize);
                            }
                        }
                    }
                    FieldLoc::Words(o) => {
                        let w = fp.words();
                        let child_node = item.node.product_child(idx).expect("product child node");
                        let child = WorkItem {
                            plan: fp,
                            node: child_node,
                            raw: &item.raw[o..o + w],
                            canon: &item.canon[o..o + w],
                            wide_bitset: item.wide_bitset && fp.has_wide_bitset(),
                        };
                        match refine_deterministic(fg, part, child, mode, scratch) {
                            DetOutcome::Done => {}
                            DetOutcome::BranchOne(sub) => {
                                if !product_has_non_identity_tail(fields, idx + 1) {
                                    return DetOutcome::BranchOne(sub);
                                }
                                let mut pending = vec![PendingItem::Word(sub)];
                                append_product_tail(fields, idx + 1, item, &mut pending);
                                return DetOutcome::NeedBranch(pending);
                            }
                            DetOutcome::NeedBranch(mut pending) => {
                                append_product_tail(fields, idx + 1, item, &mut pending);
                                return DetOutcome::NeedBranch(pending);
                            }
                        }
                    }
                }
            }
            DetOutcome::Done
        }
        FactorPlan::SeqBits { bits, table, .. } => {
            let len = item.raw[0] as usize;
            for i in 0..len {
                if part.is_complete() {
                    break;
                }
                let c = SlotLayout::extract(*bits, &item.raw[1..], i) as usize;
                if let Some((g, k)) = table.code_to_key[c] {
                    part.pin_smallest(fg, g as usize, k as usize);
                }
            }
            DetOutcome::Done
        }
        FactorPlan::Seq { elem, elem_words, .. } => {
            let len = item.raw[0] as usize;
            let ew = *elem_words;
            let elem_node = item.node.seq_elem().expect("seq elem node");
            let elem_wide = item.wide_bitset && elem.has_wide_bitset();
            let children = (0..len).map(|i| {
                let o = 1 + i * ew;
                WorkItem { plan: elem, node: elem_node, raw: &item.raw[o..o + ew], canon: &item.canon[o..o + ew], wide_bitset: elem_wide }
            });
            refine_ordered_children(fg, part, children, mode, scratch)
        }
        FactorPlan::Union { arms, .. } => {
            let idx = item.raw[0] as usize;
            let arm = &arms[idx];
            let arm_node = item.node.union_arm(idx).expect("union arm node");
            let w = arm.words();
            refine_deterministic(
                fg,
                part,
                WorkItem {
                    plan: arm,
                    node: arm_node,
                    raw: &item.raw[1..1 + w],
                    canon: &item.canon[1..1 + w],
                    wide_bitset: item.wide_bitset && arm.has_wide_bitset(),
                },
                mode,
                scratch,
            )
        }
        FactorPlan::Fcn { dom, slot, range, .. } => match dom {
            DomMap::Fixed(len) => refine_fixed_slots(fg, part, *len, *slot, range, item, mode, scratch),
            DomMap::DirectFactor { factor, len } => {
                refine_keyed_slots(fg, part, *factor as usize, *len, None, *slot, range, item, mode, scratch)
            }
            DomMap::AtomDom(_) | DomMap::Ranked { .. } | DomMap::ValueDom(_) => {
                if !has_unpinned_words(fg, item.plan, item.raw, part) {
                    DetOutcome::Done
                } else {
                    DetOutcome::BranchOne(item)
                }
            }
        },
        FactorPlan::Map { key, dims, range, .. } => {
            let bw = dims.bitset_words;
            if item.raw[..bw].iter().all(|&w| w == 0) {
                return DetOutcome::Done;
            }
            if key.is_identity() {
                return refine_fixed_map_slots(fg, part, *dims, range, item, mode, scratch);
            }
            if let Some(table) = key.atom_table() {
                if let Some(g) = table.direct_factor {
                    let g = g as usize;
                    let n = fg.factors[g].keys.len();
                    if bw == 1 {
                        let mask = item.raw[0];
                        part.split_by_pred(fg, g, |k| (mask >> k) & 1 != 0, &mut scratch.sort);
                    } else {
                        part.split_by_pred(fg, g, |k| (item.raw[k / 64] >> (k % 64)) & 1 != 0, &mut scratch.sort);
                    }
                    return refine_keyed_slots(fg, part, g, n, Some(bw), dims.slot, range, item, mode, scratch);
                }
                for &g in table.active_factors.iter() {
                    let g = g as usize;
                    let off = fg.factors[g].offset;
                    part.split_by_pred(
                        fg,
                        g,
                        |k| {
                            let code = table.key_to_code[off + k] as usize;
                            (item.raw[code / 64] >> (code % 64)) & 1 != 0
                        },
                        &mut scratch.sort,
                    );
                }
            }
            if !has_unpinned_words(fg, item.plan, item.raw, part) {
                DetOutcome::Done
            } else {
                DetOutcome::BranchOne(item)
            }
        }
        FactorPlan::BitsetRank { .. } | FactorPlan::Sorted { .. } | FactorPlan::Dyn | FactorPlan::Ref(_) => {
            if !has_unpinned_words(fg, item.plan, item.raw, part) {
                DetOutcome::Done
            } else {
                DetOutcome::BranchOne(item)
            }
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn refine_fixed_slots<'a>(
    fg: &FactorGroupSpec,
    part: &mut Partition,
    len: usize,
    slot: SlotLayout,
    range: &'a FactorPlan,
    item: WorkItem<'a>,
    mode: WordOrder,
    scratch: &mut FactorScratch,
) -> DetOutcome<'a> {
    if range.is_identity() {
        return DetOutcome::Done;
    }
    match slot {
        SlotLayout::Bits(bits) => {
            if let FactorPlan::Atom(table) = range {
                for i in 0..len {
                    if part.is_complete() {
                        break;
                    }
                    let c = SlotLayout::extract(bits, item.raw, i) as usize;
                    if let Some((g, k)) = table.code_to_key[c] {
                        part.pin_smallest(fg, g as usize, k as usize);
                    }
                }
            }
            DetOutcome::Done
        }
        SlotLayout::Words(rw) => {
            let range_node = item.node.range_node().expect("fcn range node");
            let range_wide = item.wide_bitset && range.has_wide_bitset();
            let children = (0..len).map(|i| {
                let o = i * rw;
                WorkItem {
                    plan: range,
                    node: range_node,
                    raw: &item.raw[o..o + rw],
                    canon: &item.canon[o..o + rw],
                    wide_bitset: range_wide,
                }
            });
            refine_ordered_children(fg, part, children, mode, scratch)
        }
    }
}

fn refine_fixed_map_slots<'a>(
    fg: &FactorGroupSpec,
    part: &mut Partition,
    dims: tlx_layout::layout::MapDims,
    range: &'a FactorPlan,
    item: WorkItem<'a>,
    mode: WordOrder,
    scratch: &mut FactorScratch,
) -> DetOutcome<'a> {
    if range.is_identity() {
        return DetOutcome::Done;
    }
    let bw = dims.bitset_words;
    match dims.slot {
        SlotLayout::Bits(bits) => {
            if let FactorPlan::Atom(table) = range {
                for (wi, &w) in item.raw[..bw].iter().enumerate() {
                    let mut b = w;
                    while b != 0 {
                        if part.is_complete() {
                            return DetOutcome::Done;
                        }
                        let r = wi * 64 + b.trailing_zeros() as usize;
                        b &= b - 1;
                        let c = SlotLayout::extract(bits, &item.raw[bw..], r) as usize;
                        if let Some((g, k)) = table.code_to_key[c] {
                            part.pin_smallest(fg, g as usize, k as usize);
                        }
                    }
                }
            }
            DetOutcome::Done
        }
        SlotLayout::Words(rw) => {
            let range_node = item.node.range_node().expect("map range node");
            let range_wide = item.wide_bitset && range.has_wide_bitset();
            let children = BitsetIter::new(&item.raw[..bw]).map(|r| {
                let o = bw + r * rw;
                WorkItem {
                    plan: range,
                    node: range_node,
                    raw: &item.raw[o..o + rw],
                    canon: &item.canon[o..o + rw],
                    wide_bitset: range_wide,
                }
            });
            refine_ordered_children(fg, part, children, mode, scratch)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn refine_keyed_slots<'a>(
    fg: &FactorGroupSpec,
    part: &mut Partition,
    g: usize,
    n: usize,
    bw_opt: Option<usize>,
    slot: SlotLayout,
    range: &'a FactorPlan,
    item: WorkItem<'a>,
    mode: WordOrder,
    scratch: &mut FactorScratch,
) -> DetOutcome<'a> {
    let bw = bw_opt.unwrap_or(0);
    let payload_raw = &item.raw[bw..];
    let payload_canon = &item.canon[bw..];
    let is_present = |k: usize| -> bool { bw_opt.is_none() || ((item.raw[k / 64] >> (k % 64)) & 1 != 0) };

    if range.is_identity() {
        match slot {
            SlotLayout::Bits(bits) => {
                part.refine_by_cmp(
                    fg,
                    g,
                    is_present,
                    |k1, k2| {
                        SlotLayout::extract(bits, payload_canon, k1 as usize).cmp(&SlotLayout::extract(bits, payload_canon, k2 as usize))
                    },
                    &mut scratch.sort,
                );
            }
            SlotLayout::Words(rw) => {
                let range_node = item.node.range_node().expect("range node");
                let range_wide = item.wide_bitset && range.has_wide_bitset();
                part.refine_by_cmp(
                    fg,
                    g,
                    is_present,
                    |k1, k2| {
                        let o1 = k1 as usize * rw;
                        let o2 = k2 as usize * rw;
                        cmp_words_mode(mode, range, range_node, range_wide, &payload_canon[o1..o1 + rw], &payload_canon[o2..o2 + rw])
                    },
                    &mut scratch.sort,
                );
            }
        }
        return DetOutcome::Done;
    }

    let off = fg.factors[g].offset;
    let all_dom_pinned = {
        let dom = part.dom();
        let blo = part.block_lo();
        let bhi = part.block_hi();
        (0..n).all(|pos| !is_present(dom[off + pos] as usize) || bhi[off + pos] - blo[off + pos] == 1)
    };

    // Check if any present slot payload contains an unpinned atom.
    let payloads_have_unpinned = match slot {
        SlotLayout::Bits(bits) => match range {
            FactorPlan::Atom(table) => (0..n).any(|k| {
                is_present(k)
                    && table.code_to_key[SlotLayout::extract(bits, payload_raw, k) as usize]
                        .is_some_and(|(cg, ck)| !part.is_pinned(fg, cg as usize, ck as usize))
            }),
            _ => false,
        },
        SlotLayout::Words(rw) => (0..n).any(|k| is_present(k) && has_unpinned_words(fg, range, &payload_raw[k * rw..(k + 1) * rw], part)),
    };

    if !payloads_have_unpinned {
        if all_dom_pinned {
            return DetOutcome::Done;
        }
        part.fill_img_buf(fg, &mut scratch.img);
        let img = scratch.img.as_slice();
        match slot {
            SlotLayout::Bits(bits) => {
                let FactorPlan::Atom(table) = range else { unreachable!() };
                part.refine_by_cmp(
                    fg,
                    g,
                    is_present,
                    |k1, k2| {
                        let v1 = table.map_code(fg, img, SlotLayout::extract(bits, payload_raw, k1 as usize));
                        let v2 = table.map_code(fg, img, SlotLayout::extract(bits, payload_raw, k2 as usize));
                        v1.cmp(&v2)
                    },
                    &mut scratch.sort,
                );
            }
            SlotLayout::Words(rw) => {
                let range_node = item.node.range_node().expect("range node");
                let range_wide = item.wide_bitset && range.has_wide_bitset();
                scratch.payload_buf.resize(n * rw, 0);
                for k in 0..n {
                    if is_present(k) {
                        let o = k * rw;
                        let sub = WorkItem {
                            plan: range,
                            node: range_node,
                            raw: &payload_raw[o..o + rw],
                            canon: &payload_canon[o..o + rw],
                            wide_bitset: range_wide,
                        };
                        apply_item(mode, fg, img, sub, &mut scratch.payload_buf[o..o + rw]);
                    }
                }
                let pbuf = &scratch.payload_buf;
                part.refine_by_cmp(
                    fg,
                    g,
                    is_present,
                    |k1, k2| {
                        let o1 = k1 as usize * rw;
                        let o2 = k2 as usize * rw;
                        cmp_words_mode(mode, range, range_node, range_wide, &pbuf[o1..o1 + rw], &pbuf[o2..o2 + rw])
                    },
                    &mut scratch.sort,
                );
            }
        }
        return DetOutcome::Done;
    }

    // If every present domain key is already pinned to a singleton, refine
    // their payloads sequentially in ascending target-slot order.
    if all_dom_pinned {
        let mut ord_inline = [(0u16, 0usize); INLINE_KEYS];
        let mut ord_heap: Vec<(u16, usize)> = Vec::new();
        let mut ord_len = 0usize;
        {
            let dom = part.dom();
            let tgt = part.tgt();
            if n <= INLINE_KEYS {
                for pos in 0..n {
                    let k = dom[off + pos] as usize;
                    if is_present(k) {
                        ord_inline[ord_len] = (tgt[off + pos], k);
                        ord_len += 1;
                    }
                }
                ord_inline[..ord_len].sort_unstable_by_key(|&(t, _)| t);
            } else {
                ord_heap.reserve(n);
                for pos in 0..n {
                    let k = dom[off + pos] as usize;
                    if is_present(k) {
                        ord_heap.push((tgt[off + pos], k));
                    }
                }
                ord_heap.sort_unstable_by_key(|&(t, _)| t);
            }
        }
        let ordered: &[(u16, usize)] = if n <= INLINE_KEYS { &ord_inline[..ord_len] } else { &ord_heap };
        match slot {
            SlotLayout::Bits(bits) => {
                let FactorPlan::Atom(table) = range else { unreachable!() };
                for &(_, k) in ordered {
                    if part.is_complete() {
                        break;
                    }
                    let c = SlotLayout::extract(bits, payload_raw, k) as usize;
                    if let Some((cg, ck)) = table.code_to_key[c] {
                        part.pin_smallest(fg, cg as usize, ck as usize);
                    }
                }
                return DetOutcome::Done;
            }
            SlotLayout::Words(rw) => {
                let range_node = item.node.range_node().expect("range node");
                let range_wide = item.wide_bitset && range.has_wide_bitset();
                let children = ordered.iter().map(|&(_, k)| {
                    let o = k * rw;
                    WorkItem {
                        plan: range,
                        node: range_node,
                        raw: &payload_raw[o..o + rw],
                        canon: &payload_canon[o..o + rw],
                        wide_bitset: range_wide,
                    }
                });
                return refine_ordered_children(fg, part, children, mode, scratch);
            }
        }
    }

    // Self-equivariant identity fast path: `[k \in D |-> k]`.
    if let FactorPlan::Atom(table) = range {
        if table.direct_factor == Some(g as u16) {
            let dom = part.dom();
            let block_hi = part.block_hi();
            let mut self_id = true;
            let mut lo = 0usize;
            while lo < n {
                let hi = block_hi[off + lo] as usize;
                let k0 = dom[off + lo] as usize;
                if is_present(k0) {
                    if hi - lo == 1 {
                        let c = match slot {
                            SlotLayout::Bits(bits) => SlotLayout::extract(bits, payload_raw, k0) as usize,
                            SlotLayout::Words(_) => payload_raw[k0] as usize,
                        };
                        if !part.is_pinned(fg, g, c) {
                            self_id = false;
                            break;
                        }
                    } else {
                        for pos in lo..hi {
                            let k = dom[off + pos] as usize;
                            let c = match slot {
                                SlotLayout::Bits(bits) => SlotLayout::extract(bits, payload_raw, k) as usize,
                                SlotLayout::Words(_) => payload_raw[k] as usize,
                            };
                            if c != k {
                                self_id = false;
                                break;
                            }
                        }
                        if !self_id {
                            break;
                        }
                    }
                }
                lo = hi;
            }
            if self_id {
                return DetOutcome::Done;
            }
        }
    }

    DetOutcome::BranchOne(item)
}

/// Fast zero-allocation comparison when every candidate partition is already
/// complete (`is_complete()`): no refinement or branching is needed, and
/// direct-factor `Fcn` variables compare slot-by-slot so losers are pruned on
/// the first differing slot without permuting the rest of a wide function.
fn minimize_complete_candidates(
    fg: &FactorGroupSpec,
    candidates: Vec<Partition>,
    item: WorkItem<'_>,
    mode: WordOrder,
    scratch: &mut FactorScratch,
) -> Vec<Partition> {
    if candidates.len() <= 1 || item.plan.is_identity() {
        return candidates;
    }
    if let FactorPlan::Fcn { dom: DomMap::DirectFactor { factor, len }, slot: SlotLayout::Words(rw), range, .. } = item.plan {
        let g = *factor as usize;
        let off = fg.factors[g].offset;
        let n = *len;
        let rw = *rw;
        let range_node = item.node.range_node().expect("fcn range node");
        let range_wide = item.wide_bitset && range.has_wide_bitset();
        let mut cands = candidates;
        let mut cur_img = ImgBuf::default();
        let mut cur_slot = std::mem::take(&mut scratch.cand_cur);
        let mut best_slot = std::mem::take(&mut scratch.cand_best);
        cur_slot.resize(rw, 0);
        best_slot.resize(rw, 0);
        for target_t in 0..n as u16 {
            if cands.len() <= 1 {
                break;
            }
            let mut next_best: Vec<Partition> = Vec::with_capacity(cands.len());
            for part in cands {
                let dom = part.dom();
                let tgt = part.tgt();
                let pos = (0..n).find(|&p| tgt[off + p] == target_t).expect("target slot");
                let k = dom[off + pos] as usize;
                let o = k * rw;
                let sub = WorkItem {
                    plan: range,
                    node: range_node,
                    raw: &item.raw[o..o + rw],
                    canon: &item.canon[o..o + rw],
                    wide_bitset: range_wide,
                };
                if range.is_identity() {
                    cur_slot.copy_from_slice(sub.canon);
                } else {
                    part.fill_img_buf(fg, &mut cur_img);
                    apply_item(mode, fg, cur_img.as_slice(), sub, &mut cur_slot);
                }
                if next_best.is_empty() {
                    best_slot.copy_from_slice(&cur_slot);
                    next_best.push(part);
                } else {
                    match cmp_words_mode(mode, range, range_node, range_wide, &cur_slot, &best_slot) {
                        Ordering::Greater => {}
                        Ordering::Equal => next_best.push(part),
                        Ordering::Less => {
                            best_slot.copy_from_slice(&cur_slot);
                            next_best.clear();
                            next_best.push(part);
                        }
                    }
                }
            }
            cands = next_best;
        }
        scratch.cand_cur = cur_slot;
        scratch.cand_best = best_slot;
        return cands;
    }

    let w = item.plan.words();
    let mut cur_img = ImgBuf::default();
    let mut cur_words = std::mem::take(&mut scratch.cand_cur);
    let mut best_words = std::mem::take(&mut scratch.cand_best);
    cur_words.resize(w, 0);
    best_words.resize(w, 0);
    let mut best_parts: Vec<Partition> = Vec::with_capacity(candidates.len());
    for part in candidates {
        part.fill_img_buf(fg, &mut cur_img);
        apply_item(mode, fg, cur_img.as_slice(), item, &mut cur_words);
        if best_parts.is_empty() {
            best_words.copy_from_slice(&cur_words);
            best_parts.push(part);
        } else {
            match cmp_words_mode(mode, item.plan, item.node, item.wide_bitset, &cur_words, &best_words) {
                Ordering::Greater => {}
                Ordering::Equal => best_parts.push(part),
                Ordering::Less => {
                    best_words.copy_from_slice(&cur_words);
                    best_parts.clear();
                    best_parts.push(part);
                }
            }
        }
    }
    scratch.cand_cur = cur_words;
    scratch.cand_best = best_words;
    best_parts
}

/// Refine and prune a set of tied candidate partitions on `pending`.
fn minimize_across_candidates(
    fg: &FactorGroupSpec,
    candidates: Vec<Partition>,
    pending: PendingItem<'_>,
    mode: WordOrder,
    scratch: &mut FactorScratch,
) -> Vec<Partition> {
    match pending {
        PendingItem::PackedAtom { table, raw_code } => {
            let mut best_val = u64::MAX;
            let mut best_parts = Vec::new();
            for mut part in candidates {
                if let Some((g, k)) = table.code_to_key[raw_code as usize] {
                    part.pin_smallest(fg, g as usize, k as usize);
                }
                let val = map_scalar_part(fg, table, &part, raw_code);
                match val.cmp(&best_val) {
                    Ordering::Greater => {}
                    Ordering::Equal => best_parts.push(part),
                    Ordering::Less => {
                        best_val = val;
                        best_parts.clear();
                        best_parts.push(part);
                    }
                }
            }
            best_parts
        }
        PendingItem::Word(item) => {
            if item.plan.is_identity() {
                return candidates;
            }
            if candidates.iter().all(Partition::is_complete) {
                return minimize_complete_candidates(fg, candidates, item, mode, scratch);
            }
            // Decompose fixed-order composites field-by-field to prune losers early.
            match item.plan {
                FactorPlan::Product { fields, .. } => {
                    let mut cands = candidates;
                    for (idx, (loc, fp)) in fields.iter().enumerate() {
                        if cands.len() == 1 && cands[0].is_complete() {
                            break;
                        }
                        if fp.is_identity() {
                            continue;
                        }
                        match *loc {
                            FieldLoc::Bits(pos) => {
                                if let FactorPlan::Atom(table) = fp {
                                    cands = minimize_across_candidates(
                                        fg,
                                        cands,
                                        PendingItem::PackedAtom { table, raw_code: pos.extract(item.raw) },
                                        mode,
                                        scratch,
                                    );
                                }
                            }
                            FieldLoc::Words(o) => {
                                let w = fp.words();
                                let child_node = item.node.product_child(idx).expect("product child node");
                                cands = minimize_across_candidates(
                                    fg,
                                    cands,
                                    PendingItem::Word(WorkItem {
                                        plan: fp,
                                        node: child_node,
                                        raw: &item.raw[o..o + w],
                                        canon: &item.canon[o..o + w],
                                        wide_bitset: item.wide_bitset && fp.has_wide_bitset(),
                                    }),
                                    mode,
                                    scratch,
                                );
                            }
                        }
                    }
                    return cands;
                }
                FactorPlan::Union { arms, .. } => {
                    let idx = item.raw[0] as usize;
                    let arm = &arms[idx];
                    let arm_node = item.node.union_arm(idx).expect("union arm node");
                    let w = arm.words();
                    return minimize_across_candidates(
                        fg,
                        candidates,
                        PendingItem::Word(WorkItem {
                            plan: arm,
                            node: arm_node,
                            raw: &item.raw[1..1 + w],
                            canon: &item.canon[1..1 + w],
                            wide_bitset: item.wide_bitset && arm.has_wide_bitset(),
                        }),
                        mode,
                        scratch,
                    );
                }
                FactorPlan::Seq { elem, elem_words, .. } => {
                    let len = item.raw[0] as usize;
                    let ew = *elem_words;
                    let elem_node = item.node.seq_elem().expect("seq elem node");
                    let elem_wide = item.wide_bitset && elem.has_wide_bitset();
                    let mut cands = candidates;
                    for i in 0..len {
                        if cands.len() == 1 && cands[0].is_complete() {
                            break;
                        }
                        let o = 1 + i * ew;
                        cands = minimize_across_candidates(
                            fg,
                            cands,
                            PendingItem::Word(WorkItem {
                                plan: elem,
                                node: elem_node,
                                raw: &item.raw[o..o + ew],
                                canon: &item.canon[o..o + ew],
                                wide_bitset: elem_wide,
                            }),
                            mode,
                            scratch,
                        );
                    }
                    return cands;
                }
                _ => {}
            }

            let w = item.plan.words();
            let mut best_parts: Vec<Partition> = Vec::with_capacity(candidates.len());
            let mut cur_img = ImgBuf::default();
            let mut cur_inline = [0u64; 16];
            let mut best_inline = [0u64; 16];
            let mut cur_heap: Vec<u64> = if w > 16 { vec![0u64; w] } else { Vec::new() };
            let mut best_heap: Vec<u64> = if w > 16 { vec![0u64; w] } else { Vec::new() };
            let cur_words: &mut [u64] = if w <= 16 { &mut cur_inline[..w] } else { &mut cur_heap };
            let best_words: &mut [u64] = if w <= 16 { &mut best_inline[..w] } else { &mut best_heap };

            for mut part in candidates {
                match refine_deterministic(fg, &mut part, item, mode, scratch) {
                    DetOutcome::Done => {
                        part.fill_img_buf(fg, &mut cur_img);
                        apply_item(mode, fg, cur_img.as_slice(), item, cur_words);
                        if best_parts.is_empty() {
                            best_words.copy_from_slice(cur_words);
                            best_parts.push(part);
                        } else {
                            match cmp_words_mode(mode, item.plan, item.node, item.wide_bitset, cur_words, best_words) {
                                Ordering::Greater => {}
                                Ordering::Equal => best_parts.push(part),
                                Ordering::Less => {
                                    best_words.copy_from_slice(cur_words);
                                    best_parts.clear();
                                    best_parts.push(part);
                                }
                            }
                        }
                    }
                    DetOutcome::BranchOne(sub) => {
                        let refined = branch_single_word(fg, part, sub, mode, scratch);
                        if refined.is_empty() {
                            continue;
                        }
                        refined[0].fill_img_buf(fg, &mut cur_img);
                        apply_item(mode, fg, cur_img.as_slice(), item, cur_words);
                        if best_parts.is_empty() {
                            best_words.copy_from_slice(cur_words);
                            best_parts = refined;
                        } else {
                            match cmp_words_mode(mode, item.plan, item.node, item.wide_bitset, cur_words, best_words) {
                                Ordering::Greater => {}
                                Ordering::Equal => best_parts.extend(refined),
                                Ordering::Less => {
                                    best_words.copy_from_slice(cur_words);
                                    best_parts = refined;
                                }
                            }
                        }
                    }
                    DetOutcome::NeedBranch(sub_pending) => {
                        let mut refined = vec![part];
                        for p in sub_pending {
                            refined = minimize_across_candidates(fg, refined, p, mode, scratch);
                        }
                        if refined.is_empty() {
                            continue;
                        }
                        refined[0].fill_img_buf(fg, &mut cur_img);
                        apply_item(mode, fg, cur_img.as_slice(), item, cur_words);
                        if best_parts.is_empty() {
                            best_words.copy_from_slice(cur_words);
                            best_parts = refined;
                        } else {
                            match cmp_words_mode(mode, item.plan, item.node, item.wide_bitset, cur_words, best_words) {
                                Ordering::Greater => {}
                                Ordering::Equal => best_parts.extend(refined),
                                Ordering::Less => {
                                    best_words.copy_from_slice(cur_words);
                                    best_parts = refined;
                                }
                            }
                        }
                    }
                }
            }
            best_parts
        }
    }
}

/// Branch-and-bound minimization of a single irreducible `WorkItem`:
/// dispatches direct-factor `Fcn`/`Map` to slot-by-slot Case A, and general
/// recursive encodings to active-atom Case B.
fn branch_single_word(
    fg: &FactorGroupSpec,
    part: Partition,
    item: WorkItem<'_>,
    mode: WordOrder,
    scratch: &mut FactorScratch,
) -> Vec<Partition> {
    match item.plan {
        FactorPlan::Fcn { dom: DomMap::DirectFactor { factor, len }, slot, range, .. } => {
            let g = *factor as usize;
            let n = *len;
            if n <= INLINE_KEYS {
                let mut dom_slots = [0u16; INLINE_KEYS];
                for (i, d) in dom_slots[..n].iter_mut().enumerate() {
                    *d = i as u16;
                }
                return branch_keyed(
                    fg,
                    part,
                    g,
                    *slot,
                    range,
                    item.node.range_node().unwrap(),
                    item.raw,
                    item.canon,
                    &dom_slots[..n],
                    mode,
                    scratch,
                );
            }
            let dom_slots: Vec<u16> = (0..n as u16).collect();
            return branch_keyed(
                fg,
                part,
                g,
                *slot,
                range,
                item.node.range_node().unwrap(),
                item.raw,
                item.canon,
                &dom_slots,
                mode,
                scratch,
            );
        }
        FactorPlan::Map { key, dims, range, .. } => {
            if let Some(table) = key.atom_table() {
                if let Some(factor) = table.direct_factor {
                    let g = factor as usize;
                    let bw = dims.bitset_words;
                    let off = fg.factors[g].offset;
                    let n = fg.factors[g].keys.len();
                    if n <= INLINE_KEYS {
                        let mut dom_slots = [0u16; INLINE_KEYS];
                        let mut m = 0usize;
                        {
                            let dom = part.dom();
                            let tgt = part.tgt();
                            for pos in 0..n {
                                let k = dom[off + pos] as usize;
                                if (item.raw[k / 64] >> (k % 64)) & 1 != 0 {
                                    dom_slots[m] = tgt[off + pos];
                                    m += 1;
                                }
                            }
                        }
                        dom_slots[..m].sort_unstable();
                        return branch_keyed(
                            fg,
                            part,
                            g,
                            dims.slot,
                            range,
                            item.node.range_node().unwrap(),
                            &item.raw[bw..],
                            &item.canon[bw..],
                            &dom_slots[..m],
                            mode,
                            scratch,
                        );
                    }
                    let mut dom_slots: Vec<u16> = Vec::with_capacity(n);
                    {
                        let dom = part.dom();
                        let tgt = part.tgt();
                        for pos in 0..n {
                            let k = dom[off + pos] as usize;
                            if (item.raw[k / 64] >> (k % 64)) & 1 != 0 {
                                dom_slots.push(tgt[off + pos]);
                            }
                        }
                    }
                    dom_slots.sort_unstable();
                    return branch_keyed(
                        fg,
                        part,
                        g,
                        dims.slot,
                        range,
                        item.node.range_node().unwrap(),
                        &item.raw[bw..],
                        &item.canon[bw..],
                        &dom_slots,
                        mode,
                        scratch,
                    );
                }
            }
        }
        _ => {}
    }
    branch_general_words(fg, part, item, mode)
}

/// Case A: slot-by-slot lex-leader branch-and-bound for `Fcn`/`Map` keyed by
/// factor `g`.
#[allow(clippy::too_many_arguments)]
fn branch_keyed(
    fg: &FactorGroupSpec,
    part: Partition,
    g: usize,
    slot: SlotLayout,
    range: &FactorPlan,
    range_node: &LayoutNode,
    payload_raw: &[u64],
    payload_canon: &[u64],
    dom_slots: &[u16],
    mode: WordOrder,
    scratch: &mut FactorScratch,
) -> Vec<Partition> {
    match slot {
        SlotLayout::Bits(bits) => {
            let FactorPlan::Atom(table) = range else { unreachable!("non-copy packed range must be Atom") };
            struct BitsCtx<'a> {
                fg: &'a FactorGroupSpec,
                g: usize,
                bits: u8,
                table: &'a AtomTable,
                payload_raw: &'a [u64],
                dom_slots: &'a [u16],
            }
            struct BitsBest {
                epoch: u64,
                scalars_inline: [u64; INLINE_KEYS],
                scalars_heap: Vec<u64>,
                parts: Vec<Partition>,
            }
            impl BitsBest {
                #[inline]
                fn scalars(&self, len: usize) -> &[u64] {
                    if len <= INLINE_KEYS {
                        &self.scalars_inline[..len]
                    } else {
                        &self.scalars_heap
                    }
                }
                fn set_best(&mut self, cur: &[u64], part: Partition) {
                    self.epoch += 1;
                    if cur.len() <= INLINE_KEYS {
                        self.scalars_inline[..cur.len()].copy_from_slice(cur);
                    } else {
                        self.scalars_heap.clear();
                        self.scalars_heap.extend_from_slice(cur);
                    }
                    self.parts.clear();
                    self.parts.push(part);
                }
            }
            fn step_bits_run(
                ctx: &BitsCtx<'_>,
                mut next: Partition,
                slot_idx: usize,
                run_len: usize,
                raw: u64,
                beat_epoch: Option<u64>,
                cur: &mut [u64],
                best: &mut Option<BitsBest>,
            ) {
                if let Some((cg, ck)) = ctx.table.code_to_key[raw as usize] {
                    next.pin_smallest(ctx.fg, cg as usize, ck as usize);
                }
                let val = map_scalar_part(ctx.fg, ctx.table, &next, raw);
                let mut next_beat = beat_epoch;
                if let Some(b) = best.as_ref() {
                    if beat_epoch != Some(b.epoch) {
                        let b_scalars = b.scalars(ctx.dom_slots.len());
                        for r in 0..run_len {
                            match val.cmp(&b_scalars[slot_idx + r]) {
                                Ordering::Greater => return,
                                Ordering::Less => {
                                    next_beat = Some(b.epoch);
                                    break;
                                }
                                Ordering::Equal => {}
                            }
                        }
                    }
                }
                for r in 0..run_len {
                    cur[slot_idx + r] = val;
                }
                dfs_bits(ctx, next, slot_idx + run_len, next_beat, cur, best);
            }
            fn dfs_bits(
                ctx: &BitsCtx<'_>,
                part: Partition,
                slot_idx: usize,
                beat_epoch: Option<u64>,
                cur: &mut [u64],
                best: &mut Option<BitsBest>,
            ) {
                if slot_idx == ctx.dom_slots.len() {
                    match best {
                        None => {
                            let mut scalars_inline = [0u64; INLINE_KEYS];
                            let scalars_heap = if cur.len() <= INLINE_KEYS {
                                scalars_inline[..cur.len()].copy_from_slice(cur);
                                Vec::new()
                            } else {
                                cur.to_vec()
                            };
                            *best = Some(BitsBest { epoch: 1, scalars_inline, scalars_heap, parts: vec![part] });
                        }
                        Some(b) if beat_epoch == Some(b.epoch) => b.set_best(cur, part),
                        Some(b) => b.parts.push(part),
                    }
                    return;
                }
                let off = ctx.fg.factors[ctx.g].offset;
                let n = ctx.fg.factors[ctx.g].keys.len();
                let target_t = ctx.dom_slots[slot_idx];
                let pos = (0..n).find(|&p| part.tgt()[off + p] == target_t).expect("target slot exists");
                let lo = part.block_lo()[off + pos] as usize;
                let hi = part.block_hi()[off + pos] as usize;
                let block_len = hi - lo;

                if block_len == 1 {
                    let k = part.dom()[off + lo] as usize;
                    let raw = SlotLayout::extract(ctx.bits, ctx.payload_raw, k);
                    step_bits_run(ctx, part, slot_idx, 1, raw, beat_epoch, cur, best);
                    return;
                }

                // When the whole unpinned block maps to contiguous target slots
                // and no payload depends on an unpinned atom of factor `g`,
                // keys with identical raw codes are interchangeable and belong
                // together in one contiguous run.
                let contiguous = pos == lo
                    && slot_idx + block_len <= ctx.dom_slots.len()
                    && ctx.dom_slots[slot_idx..slot_idx + block_len] == part.tgt()[off + lo..off + hi];
                let can_bulk = contiguous
                    && (lo..hi).all(|p| {
                        let k = part.dom()[off + p] as usize;
                        let raw = SlotLayout::extract(ctx.bits, ctx.payload_raw, k) as usize;
                        match ctx.table.code_to_key[raw] {
                            Some((cg, ck)) if cg as usize == ctx.g => part.is_pinned(ctx.fg, ctx.g, ck as usize),
                            _ => true,
                        }
                    });
                if can_bulk {
                    if block_len <= INLINE_KEYS {
                        let mut class_raw = [0u64; INLINE_KEYS];
                        let mut class_of = [0u8; INLINE_KEYS];
                        let mut num_classes = 0usize;
                        let mut dom_keys = [0u16; INLINE_KEYS];
                        dom_keys[..block_len].copy_from_slice(&part.dom()[off + lo..off + hi]);
                        for idx in 0..block_len {
                            let raw = SlotLayout::extract(ctx.bits, ctx.payload_raw, dom_keys[idx] as usize);
                            if let Some(c) = (0..num_classes).find(|&c| class_raw[c] == raw) {
                                class_of[idx] = c as u8;
                            } else {
                                class_of[idx] = num_classes as u8;
                                class_raw[num_classes] = raw;
                                num_classes += 1;
                            }
                        }
                        let mut chosen = [0u16; INLINE_KEYS];
                        for (c, &raw_val) in class_raw.iter().enumerate().take(num_classes) {
                            let mut m = 0usize;
                            for idx in 0..block_len {
                                if class_of[idx] as usize == c {
                                    chosen[m] = dom_keys[idx];
                                    m += 1;
                                }
                            }
                            let mut next = part.clone();
                            next.bulk_place_first(ctx.fg, ctx.g, lo, &chosen[..m]);
                            step_bits_run(ctx, next, slot_idx, m, raw_val, beat_epoch, cur, best);
                        }
                    } else {
                        let mut classes: Vec<(Vec<u16>, u64)> = Vec::new();
                        for p in lo..hi {
                            let k = part.dom()[off + p];
                            let raw = SlotLayout::extract(ctx.bits, ctx.payload_raw, k as usize);
                            if let Some((keys, _)) = classes.iter_mut().find(|(_, r)| *r == raw) {
                                keys.push(k);
                            } else {
                                classes.push((vec![k], raw));
                            }
                        }
                        for (keys, raw) in classes {
                            let mut next = part.clone();
                            next.bulk_place_first(ctx.fg, ctx.g, lo, &keys);
                            step_bits_run(ctx, next, slot_idx, keys.len(), raw, beat_epoch, cur, best);
                        }
                    }
                    return;
                }

                let mut keys_inline = [0u16; INLINE_KEYS];
                let heap_keys: Vec<u16> = if block_len <= INLINE_KEYS {
                    keys_inline[..block_len].copy_from_slice(&part.dom()[off + lo..off + hi]);
                    Vec::new()
                } else {
                    part.dom()[off + lo..off + hi].to_vec()
                };
                let cand_keys: &[u16] = if block_len <= INLINE_KEYS { &keys_inline[..block_len] } else { &heap_keys };
                for &k in cand_keys {
                    let mut next = part.clone();
                    next.pin_to_slot(ctx.fg, ctx.g, k as usize, pos);
                    let raw = SlotLayout::extract(ctx.bits, ctx.payload_raw, k as usize);
                    step_bits_run(ctx, next, slot_idx, 1, raw, beat_epoch, cur, best);
                }
            }
            let ctx = BitsCtx { fg, g, bits, table, payload_raw, dom_slots };
            let mut cur_inline = [0u64; INLINE_KEYS];
            let mut cur_heap: Vec<u64> = if dom_slots.len() > INLINE_KEYS { vec![0u64; dom_slots.len()] } else { Vec::new() };
            let cur: &mut [u64] = if dom_slots.len() <= INLINE_KEYS { &mut cur_inline[..dom_slots.len()] } else { &mut cur_heap };
            let mut best = None;
            dfs_bits(&ctx, part, 0, None, cur, &mut best);
            best.map_or_else(Vec::new, |b| b.parts)
        }
        SlotLayout::Words(rw) => {
            const INLINE_RUN_WORDS: usize = 64;
            struct WordsCtx<'a> {
                fg: &'a FactorGroupSpec,
                g: usize,
                rw: usize,
                range: &'a FactorPlan,
                range_node: &'a LayoutNode,
                range_wide: bool,
                payload_raw: &'a [u64],
                payload_canon: &'a [u64],
                dom_slots: &'a [u16],
                mode: WordOrder,
            }
            struct WordsBest {
                epoch: u64,
                /// Concatenated canonicalized permuted slot words (`dom_slots.len() * rw`).
                slot_words_inline: [u64; INLINE_RUN_WORDS],
                slot_words_heap: Vec<u64>,
                parts: Vec<Partition>,
            }
            impl WordsBest {
                #[inline]
                fn slot_words(&self, total: usize) -> &[u64] {
                    if total <= INLINE_RUN_WORDS {
                        &self.slot_words_inline[..total]
                    } else {
                        &self.slot_words_heap
                    }
                }
                fn set_best(&mut self, cur: &[u64], part: Partition) {
                    self.epoch += 1;
                    if cur.len() <= INLINE_RUN_WORDS {
                        self.slot_words_inline[..cur.len()].copy_from_slice(cur);
                    } else {
                        self.slot_words_heap.clear();
                        self.slot_words_heap.extend_from_slice(cur);
                    }
                    self.parts.clear();
                    self.parts.push(part);
                }
            }

            #[allow(clippy::too_many_arguments)]
            fn step_run(
                ctx: &WordsCtx<'_>,
                mut part: Partition,
                slot_idx: usize,
                run_len: usize,
                k: usize,
                beat_epoch: Option<u64>,
                cur_words: &mut [u64],
                best: &mut Option<WordsBest>,
                scratch: &mut FactorScratch,
            ) {
                let o = k * ctx.rw;
                let item = WorkItem {
                    plan: ctx.range,
                    node: ctx.range_node,
                    raw: &ctx.payload_raw[o..o + ctx.rw],
                    canon: &ctx.payload_canon[o..o + ctx.rw],
                    wide_bitset: ctx.range_wide,
                };
                let mut min_inline = [0u64; 16];
                let mut min_heap: Vec<u64> = if ctx.rw > 16 { vec![0u64; ctx.rw] } else { Vec::new() };
                let min_w: &mut [u64] = if ctx.rw <= 16 { &mut min_inline[..ctx.rw] } else { &mut min_heap };
                let mut img = ImgBuf::default();
                let total_w = ctx.dom_slots.len() * ctx.rw;

                // Fast zero-allocation path when deterministic refinement suffices.
                let det = refine_deterministic(ctx.fg, &mut part, item, ctx.mode, scratch);
                match det {
                    DetOutcome::Done => {
                        part.fill_img_buf(ctx.fg, &mut img);
                        apply_item(ctx.mode, ctx.fg, img.as_slice(), item, min_w);
                        let mut next_beat = beat_epoch;
                        if let Some(b) = best.as_ref() {
                            if beat_epoch != Some(b.epoch) {
                                let bw = b.slot_words(total_w);
                                for r in 0..run_len {
                                    let bo = (slot_idx + r) * ctx.rw;
                                    match cmp_words_mode(ctx.mode, ctx.range, ctx.range_node, ctx.range_wide, min_w, &bw[bo..bo + ctx.rw]) {
                                        Ordering::Greater => return,
                                        Ordering::Less => {
                                            next_beat = Some(b.epoch);
                                            break;
                                        }
                                        Ordering::Equal => {}
                                    }
                                }
                            }
                        }
                        for r in 0..run_len {
                            let dst_o = (slot_idx + r) * ctx.rw;
                            cur_words[dst_o..dst_o + ctx.rw].copy_from_slice(min_w);
                        }
                        dfs_words(ctx, part, slot_idx + run_len, next_beat, cur_words, best, scratch);
                    }
                    DetOutcome::BranchOne(sub) => {
                        let sub_parts = branch_single_word(ctx.fg, part, sub, ctx.mode, scratch);
                        if sub_parts.is_empty() {
                            return;
                        }
                        sub_parts[0].fill_img_buf(ctx.fg, &mut img);
                        apply_item(ctx.mode, ctx.fg, img.as_slice(), item, min_w);
                        let mut next_beat = beat_epoch;
                        if let Some(b) = best.as_ref() {
                            if beat_epoch != Some(b.epoch) {
                                let bw = b.slot_words(total_w);
                                for r in 0..run_len {
                                    let bo = (slot_idx + r) * ctx.rw;
                                    match cmp_words_mode(ctx.mode, ctx.range, ctx.range_node, ctx.range_wide, min_w, &bw[bo..bo + ctx.rw]) {
                                        Ordering::Greater => return,
                                        Ordering::Less => {
                                            next_beat = Some(b.epoch);
                                            break;
                                        }
                                        Ordering::Equal => {}
                                    }
                                }
                            }
                        }
                        for r in 0..run_len {
                            let dst_o = (slot_idx + r) * ctx.rw;
                            cur_words[dst_o..dst_o + ctx.rw].copy_from_slice(min_w);
                        }
                        for sp in sub_parts {
                            dfs_words(ctx, sp, slot_idx + run_len, next_beat, cur_words, best, scratch);
                        }
                    }
                    DetOutcome::NeedBranch(pending) => {
                        let mut sub_parts = vec![part];
                        for p in pending {
                            sub_parts = minimize_across_candidates(ctx.fg, sub_parts, p, ctx.mode, scratch);
                        }
                        if sub_parts.is_empty() {
                            return;
                        }
                        sub_parts[0].fill_img_buf(ctx.fg, &mut img);
                        apply_item(ctx.mode, ctx.fg, img.as_slice(), item, min_w);
                        let mut next_beat = beat_epoch;
                        if let Some(b) = best.as_ref() {
                            if beat_epoch != Some(b.epoch) {
                                let bw = b.slot_words(total_w);
                                for r in 0..run_len {
                                    let bo = (slot_idx + r) * ctx.rw;
                                    match cmp_words_mode(ctx.mode, ctx.range, ctx.range_node, ctx.range_wide, min_w, &bw[bo..bo + ctx.rw]) {
                                        Ordering::Greater => return,
                                        Ordering::Less => {
                                            next_beat = Some(b.epoch);
                                            break;
                                        }
                                        Ordering::Equal => {}
                                    }
                                }
                            }
                        }
                        for r in 0..run_len {
                            let dst_o = (slot_idx + r) * ctx.rw;
                            cur_words[dst_o..dst_o + ctx.rw].copy_from_slice(min_w);
                        }
                        for sp in sub_parts {
                            dfs_words(ctx, sp, slot_idx + run_len, next_beat, cur_words, best, scratch);
                        }
                    }
                }
            }

            fn dfs_words(
                ctx: &WordsCtx<'_>,
                part: Partition,
                slot_idx: usize,
                beat_epoch: Option<u64>,
                cur_words: &mut [u64],
                best: &mut Option<WordsBest>,
                scratch: &mut FactorScratch,
            ) {
                if slot_idx == ctx.dom_slots.len() {
                    match best {
                        None => {
                            let mut slot_words_inline = [0u64; INLINE_RUN_WORDS];
                            let slot_words_heap = if cur_words.len() <= INLINE_RUN_WORDS {
                                slot_words_inline[..cur_words.len()].copy_from_slice(cur_words);
                                Vec::new()
                            } else {
                                cur_words.to_vec()
                            };
                            *best = Some(WordsBest { epoch: 1, slot_words_inline, slot_words_heap, parts: vec![part] });
                        }
                        Some(b) if beat_epoch == Some(b.epoch) => b.set_best(cur_words, part),
                        Some(b) => b.parts.push(part),
                    }
                    return;
                }
                let off = ctx.fg.factors[ctx.g].offset;
                let n = ctx.fg.factors[ctx.g].keys.len();
                let target_t = ctx.dom_slots[slot_idx];
                let pos = (0..n).find(|&p| part.tgt()[off + p] == target_t).expect("target slot exists");
                let lo = part.block_lo()[off + pos] as usize;
                let hi = part.block_hi()[off + pos] as usize;
                let block_len = hi - lo;

                if block_len == 1 {
                    let k = part.dom()[off + lo] as usize;
                    step_run(ctx, part, slot_idx, 1, k, beat_epoch, cur_words, best, scratch);
                    return;
                }

                let contiguous = pos == lo
                    && slot_idx + block_len <= ctx.dom_slots.len()
                    && ctx.dom_slots[slot_idx..slot_idx + block_len] == part.tgt()[off + lo..off + hi];
                // Group payloads by exact semantic equality so equal values with
                // distinct encodings (e.g. dynamic function witnesses or distinct
                // `intern_exact` `Dyn` handles) stay in one unpinned class, while
                // avoiding any reliance on 64-bit digest equality for `Dyn`/`Ref`.
                let can_bulk = contiguous
                    && (lo..hi).all(|p| {
                        let k = part.dom()[off + p] as usize;
                        !has_unpinned_in_factor_words(ctx.fg, ctx.range, &ctx.payload_raw[k * ctx.rw..(k + 1) * ctx.rw], &part, ctx.g)
                    });
                if can_bulk {
                    let has_dyn_or_ref = ctx.range_node.has_dyn_or_ref();
                    let payload_equiv = |k1: usize, k2: usize| -> bool {
                        if has_dyn_or_ref {
                            let r1 = &ctx.payload_raw[k1 * ctx.rw..(k1 + 1) * ctx.rw];
                            let r2 = &ctx.payload_raw[k2 * ctx.rw..(k2 + 1) * ctx.rw];
                            if r1 == r2 {
                                return true;
                            }
                            // Exact semantic check without digest collision risk.
                            // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
                            unsafe { ctx.range_node.decode_unchecked(r1) == ctx.range_node.decode_unchecked(r2) }
                        } else {
                            let c1 = &ctx.payload_canon[k1 * ctx.rw..(k1 + 1) * ctx.rw];
                            let c2 = &ctx.payload_canon[k2 * ctx.rw..(k2 + 1) * ctx.rw];
                            cmp_words_mode(ctx.mode, ctx.range, ctx.range_node, ctx.range_wide, c1, c2) == Ordering::Equal
                        }
                    };
                    if block_len <= INLINE_KEYS {
                        let mut dom_keys = [0u16; INLINE_KEYS];
                        dom_keys[..block_len].copy_from_slice(&part.dom()[off + lo..off + hi]);
                        let mut class_rep = [0usize; INLINE_KEYS];
                        let mut class_of = [0u8; INLINE_KEYS];
                        let mut num_classes = 0usize;
                        for idx in 0..block_len {
                            let k = dom_keys[idx] as usize;
                            if let Some(c) = (0..num_classes).find(|&c| payload_equiv(k, class_rep[c])) {
                                class_of[idx] = c as u8;
                            } else {
                                class_of[idx] = num_classes as u8;
                                class_rep[num_classes] = k;
                                num_classes += 1;
                            }
                        }
                        let mut chosen = [0u16; INLINE_KEYS];
                        for (c, &rep_k) in class_rep.iter().enumerate().take(num_classes) {
                            let mut m = 0usize;
                            for idx in 0..block_len {
                                if class_of[idx] as usize == c {
                                    chosen[m] = dom_keys[idx];
                                    m += 1;
                                }
                            }
                            let mut next = part.clone();
                            next.bulk_place_first(ctx.fg, ctx.g, lo, &chosen[..m]);
                            step_run(ctx, next, slot_idx, m, rep_k, beat_epoch, cur_words, best, scratch);
                        }
                    } else {
                        let mut classes: Vec<(Vec<u16>, usize)> = Vec::new();
                        for p in lo..hi {
                            let k = part.dom()[off + p];
                            if let Some((keys, _)) = classes.iter_mut().find(|(_, rep_k)| payload_equiv(k as usize, *rep_k)) {
                                keys.push(k);
                            } else {
                                classes.push((vec![k], k as usize));
                            }
                        }
                        for (keys, rep_k) in classes {
                            let mut next = part.clone();
                            next.bulk_place_first(ctx.fg, ctx.g, lo, &keys);
                            step_run(ctx, next, slot_idx, keys.len(), rep_k, beat_epoch, cur_words, best, scratch);
                        }
                    }
                    return;
                }

                let mut keys_inline = [0u16; INLINE_KEYS];
                let heap_keys: Vec<u16> = if block_len <= INLINE_KEYS {
                    keys_inline[..block_len].copy_from_slice(&part.dom()[off + lo..off + hi]);
                    Vec::new()
                } else {
                    part.dom()[off + lo..off + hi].to_vec()
                };
                let cand_keys: &[u16] = if block_len <= INLINE_KEYS { &keys_inline[..block_len] } else { &heap_keys };
                for &k in cand_keys {
                    let mut next = part.clone();
                    next.pin_to_slot(ctx.fg, ctx.g, k as usize, pos);
                    step_run(ctx, next, slot_idx, 1, k as usize, beat_epoch, cur_words, best, scratch);
                }
            }

            let ctx =
                WordsCtx { fg, g, rw, range, range_node, range_wide: range.has_wide_bitset(), payload_raw, payload_canon, dom_slots, mode };
            let total_w = dom_slots.len() * rw;
            let mut cur_inline = [0u64; INLINE_RUN_WORDS];
            let mut cur_heap: Vec<u64> = if total_w > INLINE_RUN_WORDS { vec![0u64; total_w] } else { Vec::new() };
            let cur_words: &mut [u64] = if total_w <= INLINE_RUN_WORDS { &mut cur_inline[..total_w] } else { &mut cur_heap };
            let mut best = None;
            dfs_words(&ctx, part, 0, None, cur_words, &mut best, scratch);
            best.map_or_else(Vec::new, |b| b.parts)
        }
    }
}

/// True iff every adjacent transposition generating the free blocks of `part`
/// touching `active` fixes `item` (so every completion of `part` yields the
/// exact same image of `item`).
fn is_invariant_under_block_swaps_words(
    fg: &FactorGroupSpec,
    part: &Partition,
    item: WorkItem<'_>,
    active: &[(usize, usize)],
    mode: WordOrder,
) -> bool {
    let w = item.plan.words();
    let mut swapped_inline = [0u64; 16];
    let mut swapped_heap: Vec<u64> = if w > 16 { vec![0u64; w] } else { Vec::new() };
    let swapped: &mut [u64] = if w <= 16 { &mut swapped_inline[..w] } else { &mut swapped_heap };
    part.all_active_block_swaps(fg, active, |swap_img| {
        apply_item(mode, fg, swap_img, item, swapped);
        cmp_words_mode(mode, item.plan, item.node, item.wide_bitset, swapped, item.canon) == Ordering::Equal
    })
}

/// Case B: active-atom branch-and-bound for general recursive encodings
/// (`Sorted`, `BitsetRank`, multi-factor `Fcn`/`Map`, `Dyn`, `Ref`).
fn branch_general_words(fg: &FactorGroupSpec, part: Partition, item: WorkItem<'_>, mode: WordOrder) -> Vec<Partition> {
    let mut active = Vec::new();
    collect_unpinned_words(fg, item.plan, item.raw, &part, &mut active);
    if active.is_empty() {
        return vec![part];
    }
    if is_invariant_under_block_swaps_words(fg, &part, item, &active, mode) {
        return vec![part];
    }

    struct GenBest {
        words: Vec<u64>,
        parts: Vec<Partition>,
    }

    let w = item.plan.words();
    let mut best: Option<GenBest> = None;
    let mut cur_img = ImgBuf::default();
    let mut cur_inline = [0u64; 16];
    let mut cur_heap: Vec<u64> = if w > 16 { vec![0u64; w] } else { Vec::new() };
    let cur_words: &mut [u64] = if w <= 16 { &mut cur_inline[..w] } else { &mut cur_heap };
    part.for_each_active_completion(fg, &active, |leaf| {
        leaf.fill_img_buf(fg, &mut cur_img);
        apply_item(mode, fg, cur_img.as_slice(), item, cur_words);
        match &mut best {
            None => best = Some(GenBest { words: cur_words.to_vec(), parts: vec![leaf] }),
            Some(b) => match cmp_words_mode(mode, item.plan, item.node, item.wide_bitset, cur_words, &b.words) {
                Ordering::Greater => {}
                Ordering::Equal => b.parts.push(leaf),
                Ordering::Less => {
                    b.words.clear();
                    b.words.extend_from_slice(cur_words);
                    b.parts.clear();
                    b.parts.push(leaf);
                }
            },
        }
    });
    best.map_or_else(Vec::new, |b| b.parts)
}

/// Core factorized refinement loop across variables in `order`: returns `true`
/// if a non-identity winning permutation was written into `scratch.img`, or
/// `false` when the identity permutation itself achieves the minimum.
fn choose_factorized_words(
    fsym: &FactorSymmetry,
    order: &[usize],
    layout: &Layout,
    raw_words: &[u64],
    sem: Option<&SemFp>,
    mode: WordOrder,
    scratch: &mut FactorScratch,
) -> bool {
    let fg = &fsym.fg;
    let offs = &layout.offsets;
    let mut part = std::mem::take(&mut scratch.part);
    let mut var_canon_buf = std::mem::take(&mut scratch.var_canon_buf);
    part.reset(fg);
    let mut cands: Option<Vec<Partition>> = None;

    for &i in order {
        if fsym.plans[i].is_identity() {
            continue;
        }
        if let Some(cs) = &cands {
            if cs.len() == 1 && cs[0].is_complete() {
                break;
            }
        } else if part.is_complete() {
            break;
        }
        let (lo, hi) = (offs[i], offs.get(i + 1).copied().unwrap_or(raw_words.len()));
        let raw_slice = &raw_words[lo..hi];
        let node = layout.node(i);
        // Canonicalize only variables that actually carry `Dyn`, `Ref` handles,
        // or dynamic witnesses (avoiding copying the whole state into a scratch
        // buffer when an unrelated `Copy` variable triggered `sem`).
        let canon_slice: &[u64] = if mode == WordOrder::Orbit && fsym.has_dyn_var[i] {
            var_canon_buf.resize(raw_slice.len(), 0);
            // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
            unsafe { fsym.plans[i].apply_orbit_unchecked(fg, &fsym.id_img, raw_slice, &mut var_canon_buf) };
            if node.has_dynamic_witness() {
                node.canonicalize_orbit_words(&mut var_canon_buf);
            }
            &var_canon_buf
        } else {
            match sem {
                Some(s) if !s.var_refs[i].is_empty() || node.has_dynamic_witness() => {
                    var_canon_buf.clear();
                    var_canon_buf.extend_from_slice(raw_slice);
                    if let Some(store) = &s.store {
                        let refs = &s.state[s.var_refs[i].clone()];
                        if !refs.is_empty() {
                            let pin = store.pin();
                            for &off in refs {
                                var_canon_buf[off - lo] = pin.digest(var_canon_buf[off - lo]);
                            }
                        }
                    }
                    if node.has_dynamic_witness() {
                        node.canonicalize_words(&mut var_canon_buf);
                    }
                    &var_canon_buf
                }
                _ => raw_slice,
            }
        };
        let item = WorkItem { plan: &fsym.plans[i], node, raw: raw_slice, canon: canon_slice, wide_bitset: fsym.wide_bitset[i] };
        if let Some(cs) = cands.take() {
            let mut next = minimize_across_candidates(fg, cs, PendingItem::Word(item), mode, scratch);
            if next.len() == 1 {
                part = next.pop().unwrap();
            } else {
                cands = Some(next);
            }
            continue;
        }
        match refine_deterministic(fg, &mut part, item, mode, scratch) {
            DetOutcome::Done => {}
            DetOutcome::BranchOne(sub) => {
                let mut cs = branch_single_word(fg, part.clone(), sub, mode, scratch);
                if cs.len() == 1 {
                    part = cs.pop().unwrap();
                } else {
                    cands = Some(cs);
                }
            }
            DetOutcome::NeedBranch(pending) => {
                let mut cs = vec![part.clone()];
                for p in pending {
                    cs = minimize_across_candidates(fg, cs, p, mode, scratch);
                }
                if cs.len() == 1 {
                    part = cs.pop().unwrap();
                } else {
                    cands = Some(cs);
                }
            }
        }
    }

    let non_id = match cands {
        None => {
            if part.contains_identity(fg) {
                false
            } else {
                part.canonicalize_unpinned_blocks(fg);
                part.fill_img_buf(fg, &mut scratch.img);
                true
            }
        }
        Some(mut cs) => {
            if cs.iter().any(|p| p.contains_identity(fg)) {
                false
            } else {
                let win = &mut cs[0];
                win.canonicalize_unpinned_blocks(fg);
                win.fill_img_buf(fg, &mut scratch.img);
                true
            }
        }
    };
    scratch.part = part;
    scratch.var_canon_buf = var_canon_buf;
    non_id
}

// ---------------------------------------------------------------------------
// Public entry points (`orbit_fp`, `least_perm_words_factorized`, `apply_factor_img`)
// ---------------------------------------------------------------------------

thread_local! {
    /// Scratch buffers of explicit `orbit_fp`: the least encoding so far and the
    /// permuted one.
    static ORBIT_BUF: RefCell<(Vec<u64>, Vec<u64>)> = const { RefCell::new((Vec::new(), Vec::new())) };
    /// Scratch buffers of factorized word-level canonicalization.
    static FACTOR_SCRATCH: RefCell<FactorScratch> = RefCell::new(FactorScratch::default());
}

/// Apply factorized flat image table `img` to all variables of `words` into
/// `dst` (exact encoding permutation, preserving handles and dynamic witnesses).
pub(super) fn apply_factor_img(fsym: &FactorSymmetry, layout: &Layout, img: &[u16], words: &[u64], dst: &mut Vec<u64>) {
    dst.resize(words.len(), 0);
    for (i, plan) in fsym.plans.iter().enumerate() {
        let r = layout.var_range(i);
        if plan.is_identity() {
            dst[r.clone()].copy_from_slice(&words[r]);
        } else {
            // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
            unsafe { plan.apply_unchecked(&fsym.fg, img, &words[r.clone()], &mut dst[r]) };
        }
    }
}

/// Select the TLC-least orbit representative directly on encoded words for a
/// factorized group (any order, including `|G| > 720`).
///
/// Returns `Some(false)` when `words` itself is least, `Some(true)` when a
/// non-identity representative was written into `best_buf`, or `None` when
/// any variable cannot be ordered safely on words and must fall back to
/// `InterpModel::least_factor_perm`.
pub(super) fn least_perm_words_factorized(
    fsym: &FactorSymmetry,
    order: &[usize],
    layout: &Layout,
    words: &[u64],
    best_buf: &mut Vec<u64>,
) -> Option<bool> {
    if !fsym.all_orbit_cmp_safe {
        return None;
    }
    FACTOR_SCRATCH.with(|s| {
        let mut scratch = s.borrow_mut();
        let non_id = choose_factorized_words(fsym, order, layout, words, None, WordOrder::Tlc, &mut scratch);
        if !non_id {
            return Some(false);
        }
        apply_factor_img(fsym, layout, scratch.img.as_slice(), words, best_buf);
        Some(true)
    })
}

/// Fingerprint of the canonical representative in the SYMMETRY orbit of `words`.
pub(super) fn orbit_fp(
    engine: &SymmetryEngine,
    order: &[usize],
    layout: &Layout,
    words: &[u64],
    sem: Option<&SemFp>,
    ref_digests: Option<&RefDigests<'_>>,
) -> Result<u64, ModelError> {
    match engine {
        SymmetryEngine::Factorized(fsym) => Ok(orbit_fp_factorized(fsym, layout, words, sem)),
        SymmetryEngine::Explicit(plans) => orbit_fp_explicit(&plans.group, order, layout, words, sem, ref_digests),
    }
}

pub(super) fn orbit_fp_factorized(fsym: &FactorSymmetry, layout: &Layout, words: &[u64], sem: Option<&SemFp>) -> u64 {
    let sem = sem.filter(|s| s.state_needs_canonical(layout));
    FACTOR_SCRATCH.with(|s| {
        let mut scratch = s.borrow_mut();
        let non_id = choose_factorized_words(fsym, &fsym.orbit_order, layout, words, sem, WordOrder::Orbit, &mut scratch);
        if !non_id && !fsym.has_dyn {
            return match sem {
                Some(s) => s.fp_state(layout, words),
                None => fp_words(words),
            };
        }
        let mut out_buf = std::mem::take(&mut scratch.out_buf);
        out_buf.resize(words.len(), 0);
        let img = if non_id { scratch.img.as_slice() } else { &fsym.id_img };
        for (i, plan) in fsym.plans.iter().enumerate() {
            let r = layout.var_range(i);
            let node = layout.node(i);
            if plan.is_identity() {
                out_buf[r.clone()].copy_from_slice(&words[r.clone()]);
                if let Some(s) = sem {
                    if let Some(store) = &s.store {
                        let refs = &s.state[s.var_refs[i].clone()];
                        if !refs.is_empty() {
                            let pin = store.pin();
                            for &off in refs {
                                out_buf[off] = pin.digest(out_buf[off]);
                            }
                        }
                    }
                    if node.has_dynamic_witness() {
                        node.canonicalize_orbit_words(&mut out_buf[r]);
                    }
                }
            } else {
                // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
                unsafe { plan.apply_orbit_unchecked(&fsym.fg, img, &words[r.clone()], &mut out_buf[r.clone()]) };
                if node.has_dynamic_witness() {
                    node.canonicalize_orbit_words(&mut out_buf[r]);
                }
            }
        }
        let fp = fp_words(&out_buf);
        scratch.out_buf = out_buf;
        fp
    })
}

/// Explicit fallback for arbitrary non-full subgroups: scans each `PermPlan`
/// in `group`, pruning at the first variable whose permuted encoding exceeds
/// the best one so far. Under persistent value-store pressure, `ref_digests`
/// supplies the semantic digest of each permuted top-level `Ref` variable
/// directly from decoded values without interning its permuted image.
pub(super) fn orbit_fp_explicit(
    group: &[Vec<PermPlan>],
    order: &[usize],
    layout: &Layout,
    words: &[u64],
    sem: Option<&SemFp>,
    ref_digests: Option<&RefDigests<'_>>,
) -> Result<u64, ModelError> {
    let offs = &layout.offsets;
    ORBIT_BUF.with(|b| {
        let mut b = b.borrow_mut();
        let (best, buf) = &mut *b;
        let mut base = Vec::new();
        let sem = sem.filter(|s| s.state_needs_canonical(layout));
        let start: &[u64] = match sem {
            Some(s) => {
                s.semantic_state(layout, words, &mut base);
                &base
            }
            None => words,
        };
        buf.resize(words.len(), 0);
        best.clear();
        'perm: for (pi, plans) in group.iter().enumerate() {
            let cur: &[u64] = if best.is_empty() { start } else { best };
            let mut less = false;
            for &i in order {
                let (lo, hi) = (offs[i], offs.get(i + 1).copied().unwrap_or(words.len()));
                let ref_digest = ref_digests.filter(|_| sem.is_some_and(|s| s.ref_vars[i]));
                match ref_digest {
                    Some(rd) => {
                        debug_assert_eq!(hi, lo + 1, "a value store slot is one handle");
                        buf[lo] = rd.digest(i, pi)?;
                    }
                    None => {
                        // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
                        unsafe { plans[i].apply_unchecked(&words[lo..hi], &mut buf[lo..hi]) };
                        if let Some(s) = sem {
                            if let Some(store) = &s.store {
                                let refs = &s.state[s.var_refs[i].clone()];
                                if !refs.is_empty() {
                                    let pin = store.pin();
                                    for &off in refs {
                                        buf[off] = pin.digest(buf[off]);
                                    }
                                }
                            }
                        }
                    }
                }
                if sem.is_some() && layout.node(i).has_dynamic_witness() {
                    layout.node(i).canonicalize_words(&mut buf[lo..hi]);
                }
                if !less {
                    match buf[lo..hi].cmp(&cur[lo..hi]) {
                        Ordering::Greater => continue 'perm,
                        Ordering::Less => less = true,
                        Ordering::Equal => {}
                    }
                }
            }
            if less {
                if best.is_empty() {
                    best.resize(words.len(), 0);
                }
                std::mem::swap(best, buf);
            }
        }
        Ok(fp_words(if best.is_empty() { start } else { best }))
    })
}

/// Semantic digests of permuted top-level `Ref` variables computed from
/// decoded values (see `orbit_fp_explicit`), avoiding the store allocation of
/// `PermPlan::Ref`.
pub(super) struct RefDigests<'a> {
    maps: &'a [HashMap<Sym, Value>],
    /// Decoded value of each top-level `Shape::Ref` variable, by variable index.
    vals: Box<[Option<Value>]>,
}

impl<'a> RefDigests<'a> {
    pub(super) fn new(layout: &Layout, words: &[u64], maps: &'a [HashMap<Sym, Value>]) -> Self {
        let vals = layout
            .vars
            .iter()
            .enumerate()
            .map(|(i, s)| match s {
                tlx_layout::Shape::Ref(_) => {
                    // SAFETY: valid words from the matching encoder/program,
                    // with published Dyn handles.
                    Some(unsafe { layout.node(i).decode_unchecked(&words[layout.offsets[i]..]) })
                }
                _ => None,
            })
            .collect();
        Self { maps, vals }
    }

    /// The semantic digest of variable `i`'s value under permutation `p`.
    /// `permute_shared` keeps a value the permutation leaves unchanged (and
    /// preserves its function-domain witness), so unchanged `Ref` values are
    /// not rebuilt for every candidate.
    fn digest(&self, i: usize, p: usize) -> Result<u64, ModelError> {
        let v = self.vals[i].as_ref().expect("ref_digests of a Ref variable");
        let m = &self.maps[p];
        let permuted = tlx_value::ops::permute_shared(v, &|s| m.get(&s).cloned())
            .map_err(|e| ModelError::new(format!("permute Ref variable: {e:?}")))?;
        let value = permuted.as_ref().unwrap_or(v);
        tlx_layout::store::digest_of_value(value).map_err(|e| ModelError::new(format!("value store digest: {e:?}")))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::enc::model::EncModel;
    use crate::settings::Settings;
    use tlx_layout::{FcnWitness, Shape};
    use tlx_testkit::spec::load;
    use tlx_value::Sym;

    fn mv(s: &str) -> Value {
        Value::ModelValue(Sym::new(s))
    }

    fn atom_shape(xs: &[&str]) -> Shape {
        let mut v: Vec<Value> = xs.iter().map(|s| mv(s)).collect();
        v.sort();
        Shape::Atom(v.into())
    }

    fn build_explicit_group(fg: &FactorGroupSpec, layout: &Layout) -> Vec<Vec<PermPlan>> {
        fn lex_perms(n: usize) -> Vec<Vec<u16>> {
            let mut cur: Vec<u16> = (0..n as u16).collect();
            let mut out = Vec::new();
            loop {
                out.push(cur.clone());
                if n < 2 {
                    break;
                }
                let mut i = n - 2;
                while cur[i] >= cur[i + 1] {
                    if i == 0 {
                        return out;
                    }
                    i -= 1;
                }
                let mut j = n - 1;
                while cur[j] <= cur[i] {
                    j -= 1;
                }
                cur.swap(i, j);
                cur[i + 1..].reverse();
            }
            out
        }
        let per_factor: Vec<Vec<Vec<u16>>> = fg.factors.iter().map(|f| lex_perms(f.keys.len())).collect();
        let mut imgs: Vec<Vec<u16>> = vec![vec![0u16; fg.total_keys]];
        for (g, perms) in per_factor.iter().enumerate() {
            let off = fg.factors[g].offset;
            let mut next = Vec::with_capacity(imgs.len() * perms.len());
            for base in &imgs {
                for p in perms {
                    let mut v = base.clone();
                    v[off..off + p.len()].copy_from_slice(p);
                    next.push(v);
                }
            }
            imgs = next;
        }
        let id = fg.identity_img();
        let mut group = Vec::new();
        for img in imgs {
            if img == id {
                continue;
            }
            let fg_c = fg.clone();
            let perm: AtomPerm = Arc::new(move |v: &Value| match v {
                Value::ModelValue(s) => fg_c.map_sym(*s, &img).cloned().unwrap_or_else(|| v.clone()),
                _ => v.clone(),
            });
            let plans: Vec<PermPlan> = layout.vars.iter().map(|s| PermPlan::compile(s, &perm).unwrap()).collect();
            group.push(plans);
        }
        group
    }

    #[test]
    fn factorized_orbit_fp_matches_explicit_across_all_shapes() {
        let mut k1 = vec![Sym::new("a1"), Sym::new("a2"), Sym::new("a3")];
        k1.sort_unstable();
        let mut k2 = vec![Sym::new("b1"), Sym::new("b2")];
        k2.sort_unstable();
        let fg = FactorGroupSpec::new(&[&k1, &k2]);

        let s_a = atom_shape(&["a1", "a2", "a3"]);
        let s_b = atom_shape(&["b1", "b2"]);
        let mut s_a_nil_vals = vec![mv("a1"), mv("a2"), mv("a3"), mv("nil")];
        s_a_nil_vals.sort();
        let s_a_nil = Shape::Atom(s_a_nil_vals.into());

        let mut dom_a: Vec<Value> = k1.iter().copied().map(Value::ModelValue).collect();
        dom_a.sort();

        // 0: packed Record with branching field followed by packed Atom (tests PendingItem::PackedAtom)
        let fcn_a_to_a = Shape::Fcn {
            dom: dom_a.clone().into(),
            range: Box::new(s_a_nil.clone()),
            witness: FcnWitness::Enumerated,
            key_variants: Arc::from([]),
        };
        let mut rec_fields = vec![(Sym::new("aa_fcn"), fcn_a_to_a.clone()), (Sym::new("zz_tail"), s_b.clone())];
        rec_fields.sort_by_key(|f| f.0);
        let rec_shape = Shape::Record(rec_fields.into());

        // 1: Fcn with word-aligned Record payload (Case A + bulk classes)
        let mut inner_fields = vec![(Sym::new("m"), Shape::Int { lo: 0, hi: 2 }), (Sym::new("p"), s_b.clone())];
        inner_fields.sort_by_key(|f| f.0);
        let fcn_words = Shape::Fcn {
            dom: dom_a.clone().into(),
            range: Box::new(Shape::Record(inner_fields.into())),
            witness: FcnWitness::Dynamic,
            key_variants: Arc::from([]),
        };

        // 2: Map keyed by DirectFactor(0) with packed Atom range
        let map_direct = Shape::Map { key: Box::new(s_a.clone()), range: Box::new(s_b.clone()), witness: FcnWitness::Enumerated };

        // 3: Bitset over compound Tuple(Atom, Bool) (BitsetRank -> Case B)
        let pair_shape = Shape::Tuple(vec![s_a.clone(), Shape::Bool].into());
        let bitset_pair = Shape::Set { elem: Box::new(pair_shape), max_card: 4 };

        // 4: SeqBits over K_1
        let seq_bits = Shape::Seq { elem: Box::new(s_a.clone()), max_len: 3 };

        // 5: Nested Ref inside Tuple(Bool, Ref)
        let store = tlx_layout::store::StoreRef::new(usize::MAX);
        let nested_ref = Shape::Tuple(vec![Shape::Bool, Shape::Ref(store.clone())].into());

        let layout = Layout::new(vec![rec_shape, fcn_words, map_direct, bitset_pair, seq_bits, nested_ref]);
        let plans: Vec<FactorPlan> = layout.vars.iter().map(|s| FactorPlan::compile(s, &fg).unwrap()).collect();
        let fsym = FactorSymmetry::new(fg.clone(), plans, &layout);
        let explicit = build_explicit_group(&fg, &layout);
        let sem = SemFp::of(&layout, None);

        let f_rec = |x: i64, p: &str| Value::record(vec![(Sym::new("m"), Value::Int(x)), (Sym::new("p"), mv(p))]);
        let states: Vec<Vec<Value>> = vec![
            vec![
                Value::record(vec![
                    (
                        Sym::new("aa_fcn"),
                        Value::fcn_rcd_from_pairs(vec![(mv("a1"), mv("a2")), (mv("a2"), mv("nil")), (mv("a3"), mv("a1"))]).unwrap(),
                    ),
                    (Sym::new("zz_tail"), mv("b2")),
                ]),
                Value::fcn_rcd_from_pairs(vec![(mv("a1"), f_rec(1, "b2")), (mv("a2"), f_rec(0, "b1")), (mv("a3"), f_rec(0, "b1"))])
                    .unwrap(),
                Value::fcn_rcd_from_pairs(vec![(mv("a2"), mv("b2")), (mv("a3"), mv("b1"))]).unwrap(),
                Value::set_from(vec![Value::tuple(vec![mv("a2"), Value::Bool(true)]), Value::tuple(vec![mv("a3"), Value::Bool(false)])])
                    .unwrap(),
                Value::tuple(vec![mv("a3"), mv("a1")]),
                Value::tuple(vec![Value::Bool(true), Value::set_from(vec![mv("a3"), mv("b2")]).unwrap()]),
            ],
            // Tied bulk identical payloads + self-identity map
            vec![
                Value::record(vec![
                    (
                        Sym::new("aa_fcn"),
                        Value::fcn_rcd_from_pairs(vec![(mv("a1"), mv("a1")), (mv("a2"), mv("a2")), (mv("a3"), mv("a3"))]).unwrap(),
                    ),
                    (Sym::new("zz_tail"), mv("b1")),
                ]),
                Value::fcn_rcd_from_pairs(vec![(mv("a1"), f_rec(0, "b2")), (mv("a2"), f_rec(0, "b2")), (mv("a3"), f_rec(0, "b2"))])
                    .unwrap(),
                Value::fcn_rcd_from_pairs(vec![]).unwrap(),
                Value::set_from(vec![]).unwrap(),
                Value::tuple(vec![]),
                Value::tuple(vec![Value::Bool(false), Value::tuple(vec![mv("a2"), mv("b1")])]),
            ],
        ];

        for st in &states {
            let mut words = vec![0u64; layout.words];
            layout.encode_state(st, &mut words).unwrap();
            let got = orbit_fp_factorized(&fsym, &layout, &words, sem.as_ref());
            let want = orbit_fp_explicit(&explicit, &fsym.orbit_order, &layout, &words, sem.as_ref(), None).unwrap();
            assert_eq!(got, want, "factorized orbit_fp must equal exhaustive explicit orbit_fp");

            // Every group element must produce the identical orbit fingerprint.
            for p_plans in &explicit {
                let mut permuted = vec![0u64; layout.words];
                for (i, plan) in p_plans.iter().enumerate() {
                    let r = layout.var_range(i);
                    plan.apply(&words[r.clone()], &mut permuted[r]);
                }
                let p_fp = orbit_fp_factorized(&fsym, &layout, &permuted, sem.as_ref());
                assert_eq!(p_fp, got, "orbit_fp must be invariant across the entire S_3 x S_2 orbit");
            }
        }
    }

    #[test]
    fn wide_two_word_bitset_is_orbit_invariant() {
        let mut keys: Vec<Sym> = (0..6).map(|i| Sym::new(&format!("m{i}"))).collect();
        keys.sort_unstable();
        let fg = FactorGroupSpec::new(&[&keys]);
        let mut univ: Vec<Value> = (0..64).map(|i| Value::Str(Sym::new(&format!("f{i:02}")))).collect();
        univ.extend(keys.iter().copied().map(Value::ModelValue));
        univ.sort();
        let set_shape = Shape::Set { elem: Box::new(Shape::Atom(univ.into())), max_card: 8 };
        let layout = Layout::new(vec![set_shape]);
        assert!(layout.words >= 2, "must exercise multi-word bitset");
        let plans = vec![FactorPlan::compile(&layout.vars[0], &fg).unwrap()];
        let fsym = FactorSymmetry::new(fg.clone(), plans, &layout);
        assert!(fsym.wide_bitset[0]);

        let st = vec![Value::set_from(vec![
            Value::Str(Sym::new("f00")),
            Value::ModelValue(keys[1]),
            Value::ModelValue(keys[4]),
            Value::ModelValue(keys[5]),
        ])
        .unwrap()];
        let mut words = vec![0u64; layout.words];
        layout.encode_state(&st, &mut words).unwrap();
        let base_fp = orbit_fp_factorized(&fsym, &layout, &words, None);

        let mut img = fg.identity_img();
        let mut swapped = vec![0u64; layout.words];
        for k in 0..keys.len() - 1 {
            img[k] = (k + 1) as u16;
            img[k + 1] = k as u16;
            apply_factor_img(&fsym, &layout, &img, &words, &mut swapped);
            assert_eq!(orbit_fp_factorized(&fsym, &layout, &swapped, None), base_fp);
            img[k] = k as u16;
            img[k + 1] = (k + 1) as u16;
        }
    }

    #[test]
    fn large_groups_above_720_compile_to_factorized_word_engine() {
        let src = r#"---- MODULE LargeFactor ----
EXTENDS Naturals, TLC
CONSTANTS P, Q, R
VARIABLES x, f
Sym == Permutations(P) \cup Permutations(Q) \cup Permutations(R)
V == <<x, f>>
Init == x \in P /\ f = [q \in Q |-> [r \in R |-> 0]]
Next == UNCHANGED <<x, f>>
===="#;
        let cfg_noview = "CONSTANTS P = {p1,p2,p3,p4} Q = {q1,q2,q3,q4} R = {r1,r2,r3}\nINIT Init\nNEXT Next\nSYMMETRY Sym\n";
        let cfg_view = format!("{cfg_noview}VIEW V\n");
        let p_shape = atom_shape(&["p1", "p2", "p3", "p4"]);
        let mut q_dom: Vec<Value> = ["q1", "q2", "q3", "q4"].iter().map(|s| mv(s)).collect();
        q_dom.sort();
        let mut r_dom: Vec<Value> = ["r1", "r2", "r3"].iter().map(|s| mv(s)).collect();
        r_dom.sort();
        let f_shape = Shape::Fcn {
            dom: q_dom.into(),
            range: Box::new(Shape::Fcn {
                dom: r_dom.into(),
                range: Box::new(Shape::Int { lo: 0, hi: 1 }),
                witness: FcnWitness::Enumerated,
                key_variants: Arc::from([]),
            }),
            witness: FcnWitness::Enumerated,
            key_variants: Arc::from([]),
        };
        let settings = Settings::from_lookup(|k| match k {
            "TLX_NO_NATIVE" | "TLX_PARANOID" => Some("1".into()),
            _ => None,
        })
        .unwrap();

        let base_nv = Arc::new(load(src, cfg_noview));
        assert!(base_nv.symmetry_maps().is_empty(), "4!*4!*3! = 3456 > 720 must not materialize symmetry_maps");
        let model_nv = EncModel::new(base_nv, Arc::new(Layout::new(vec![p_shape.clone(), f_shape.clone()])), vec![], &settings);
        assert!(
            matches!(model_nv.fp, super::super::fingerprint::Fingerprint::Symmetry { engine: SymmetryEngine::Factorized(_), .. }),
            "expected factorized Symmetry engine for |G|=3456"
        );

        let base_v = Arc::new(load(src, &cfg_view));
        let view_def = crate::enc::speculate::view_def(&base_v).unwrap();
        let view_shape = Shape::Tuple(vec![p_shape.clone(), f_shape.clone()].into());
        let model_v = EncModel::new(base_v, Arc::new(Layout::new(vec![p_shape, f_shape])), vec![(view_def, view_shape)], &settings);
        assert!(
            matches!(model_v.fp, super::super::fingerprint::Fingerprint::SymView { engine: SymmetryEngine::Factorized(_), .. }),
            "expected factorized SymView engine for |G|=3456"
        );
    }

    #[test]
    fn sym_view_dynamic_witness_ties_preserve_least_representative_inline_and_heap() {
        // Test both inline (`n = 3 <= INLINE_KEYS`) and heap (`n = 18 > INLINE_KEYS`)
        // bulk-class paths in `dfs_words` when payloads compare equal in TLC order
        // (and Orbit order) despite differing dynamic function-domain witness words.
        for n in [3usize, 18usize] {
            let mut k_a: Vec<Sym> = (1..=n).map(|i| Sym::new(&format!("a{i:02}"))).collect();
            k_a.sort_unstable();
            let mut k_b = vec![Sym::new("b1"), Sym::new("b2")];
            k_b.sort_unstable();
            let fg = FactorGroupSpec::new(&[&k_a, &k_b]);

            let dom_a: Vec<Value> = k_a.iter().copied().map(Value::ModelValue).collect();
            let s_a = Shape::Atom(dom_a.clone().into());
            let s_b = atom_shape(&["b1", "b2"]);
            let inner_fcn = Shape::Fcn {
                dom: vec![Value::Int(1), Value::Int(2)].into(),
                range: Box::new(s_b.clone()),
                witness: FcnWitness::Dynamic,
                key_variants: Arc::from([]),
            };
            let x_shape = Shape::Fcn {
                dom: dom_a.clone().into(),
                range: Box::new(inner_fcn),
                witness: FcnWitness::Enumerated,
                key_variants: Arc::from([]),
            };
            let y_shape = Shape::Seq { elem: Box::new(s_a), max_len: n };

            let layout = Layout::new(vec![x_shape, y_shape]);
            let plans: Vec<FactorPlan> = layout.vars.iter().map(|s| FactorPlan::compile(s, &fg).unwrap()).collect();
            let fsym = FactorSymmetry::new(fg.clone(), plans, &layout);
            assert!(fsym.all_orbit_cmp_safe, "dynamic-witness Fcn + Seq must be orbit_cmp_safe");

            // Interval-witness vs enumerated-witness functions over 1..2 -> b2:
            // distinct raw witness words, semantically equal in TLC order.
            let f_interval = Value::fcn_from_pairs(vec![(Value::Int(1), mv("b2")), (Value::Int(2), mv("b2"))]).unwrap();
            let f_enum = Value::fcn_rcd_from_pairs(vec![(Value::Int(1), mv("b2")), (Value::Int(2), mv("b2"))]).unwrap();
            assert_eq!(f_interval, f_enum);

            let x_pairs: Vec<(Value, Value)> =
                dom_a.iter().enumerate().map(|(i, a)| (a.clone(), if i == 1 { f_enum.clone() } else { f_interval.clone() })).collect();
            let x_val = Value::fcn_rcd_from_pairs(x_pairs).unwrap();

            // 1) Already-least `y = <<a01, a02, ..., aN>>` must keep `y` untouched
            //    while minimizing `b2 -> b1` in `x`.
            let y_least = Value::tuple(dom_a.clone());
            let mut words = vec![0u64; layout.words];
            layout.encode_state(&[x_val.clone(), y_least.clone()], &mut words).unwrap();
            let mut best = Vec::new();
            let non_id = least_perm_words_factorized(&fsym, &[0, 1], &layout, &words, &mut best).expect("word-level SymView");
            assert!(non_id, "b2 must be mapped to b1");
            let dec = layout.decode_state(&best);
            assert_eq!(dec[1], y_least, "n={n}: bulk witness-tie grouping must not permute already-least y");

            // 2) Swapping positions 0 and 1 in `y` (moving the enumerated-witness
            //    entry across the tie) must still map back to `y_least`.
            let mut y_swapped_elems = dom_a.clone();
            y_swapped_elems.swap(0, 1);
            let y_swapped = Value::tuple(y_swapped_elems);
            layout.encode_state(&[x_val, y_swapped], &mut words).unwrap();
            let non_id2 = least_perm_words_factorized(&fsym, &[0, 1], &layout, &words, &mut best).expect("word-level SymView");
            assert!(non_id2);
            let dec2 = layout.decode_state(&best);
            assert_eq!(dec2[1], y_least, "n={n}: swapped y must canonicalize to the same least representative");
            assert_eq!(dec2, dec, "n={n}: both states in the orbit must select the identical least state");
        }
    }

    #[test]
    fn orbit_fp_dyn_s8_is_generator_invariant_and_interns_zero_entries() {
        fn has_probe_sym(v: &Value, syms: &[Sym]) -> bool {
            match v {
                Value::ModelValue(m) => syms.contains(m),
                Value::Set(es) | Value::Tuple(es) => es.iter().any(|e| has_probe_sym(e, syms)),
                Value::Record(fs) => fs.iter().any(|(_, e)| has_probe_sym(e, syms)),
                Value::Fcn(ps, _) => ps.iter().any(|(k, e)| has_probe_sym(k, syms) || has_probe_sym(e, syms)),
                _ => false,
            }
        }
        let mut keys: Vec<Sym> = (1..=8).map(|i| Sym::new(&format!("dyn_probe_compile_s8_{i}"))).collect();
        keys.sort_unstable();
        let fg = FactorGroupSpec::new(&[&keys]);
        let layout = Layout::new(vec![Shape::Dyn]);
        let plans = vec![FactorPlan::compile(&Shape::Dyn, &fg).unwrap()];
        let fsym = FactorSymmetry::new(fg.clone(), plans, &layout);
        assert!(fsym.has_dyn);
        let sem = SemFp::of(&layout, None);

        // Pre-intern the base tuple and its 7 adjacent-transposition generator
        // images BEFORE measuring probe-attributed entries in `dynval`.
        let base_tup = Value::tuple(keys.iter().copied().map(Value::ModelValue).collect());
        let mut base_words = vec![0u64; layout.words];
        layout.encode_state(&[base_tup], &mut base_words).unwrap();

        let mut gen_states: Vec<Vec<u64>> = Vec::new();
        let mut img = fg.identity_img();
        for k in 0..keys.len() - 1 {
            img.swap(k, k + 1);
            let mut buf = Vec::new();
            apply_factor_img(&fsym, &layout, &img, &base_words, &mut buf);
            gen_states.push(buf);
            img.swap(k, k + 1);
        }

        let probe_count =
            || -> usize { tlx_layout::dynval::snapshot().iter().flat_map(|s| s.iter()).filter(|v| has_probe_sym(v, &keys)).count() };
        let before = probe_count();
        assert_eq!(before, 8, "expected exactly base + 7 generator tuples before orbit_fp");
        let base_fp = orbit_fp_factorized(&fsym, &layout, &base_words, sem.as_ref());
        assert_eq!(probe_count(), before, "orbit_fp_factorized on Dyn S_8 must intern 0 probe entries (not 8! = 40,320)");
        for (k, swapped) in gen_states.iter().enumerate() {
            let fp = orbit_fp_factorized(&fsym, &layout, swapped, sem.as_ref());
            assert_eq!(fp, base_fp, "orbit_fp_factorized on Dyn S_8 must be invariant under generator swap ({k}, {})", k + 1);
        }
        assert_eq!(probe_count(), before, "all generator checks of orbit_fp_factorized on Dyn S_8 must intern 0 probe entries");
    }

    #[test]
    fn uniform_dyn_fcn_keeps_single_unpinned_block_as_domain_grows() {
        // Verifies that `Fcn(K_a -> Dyn)` where all keys hold the same value
        // (or TLA+-equal values with distinct `intern_exact` handles) keeps the
        // entire `K_a` domain in ONE unpinned block instead of retaining `n!`
        // tied partitions — across both inline (`n = 10`) and heap (`n = 18`)
        // bulk-class paths.
        for n in [10usize, 18usize] {
            let mut k_a: Vec<Sym> = (1..=n).map(|i| Sym::new(&format!("ud_a{i:02}"))).collect();
            k_a.sort_unstable();
            let mut k_b = vec![Sym::new("ud_b1"), Sym::new("ud_b2")];
            k_b.sort_unstable();
            let fg = FactorGroupSpec::new(&[&k_a, &k_b]);

            let dom_a: Vec<Value> = k_a.iter().copied().map(Value::ModelValue).collect();
            let fcn_dyn = Shape::Fcn {
                dom: dom_a.clone().into(),
                range: Box::new(Shape::Dyn),
                witness: FcnWitness::Enumerated,
                key_variants: Arc::from([]),
            };
            let layout = Layout::new(vec![fcn_dyn]);
            let plans = vec![FactorPlan::compile(&layout.vars[0], &fg).unwrap()];
            let fsym = FactorSymmetry::new(fg.clone(), plans, &layout);
            let sem = SemFp::of(&layout, None);

            // Mix identical handles and a semantically-equal `intern_exact`
            // handle (interval vs enumerated function over 1..2 -> ud_b2).
            let v_int = Value::fcn_from_pairs(vec![(Value::Int(1), Value::ModelValue(k_b[1])), (Value::Int(2), Value::ModelValue(k_b[1]))])
                .unwrap();
            let v_enum =
                Value::fcn_rcd_from_pairs(vec![(Value::Int(1), Value::ModelValue(k_b[1])), (Value::Int(2), Value::ModelValue(k_b[1]))])
                    .unwrap();
            assert_eq!(v_int, v_enum);

            let pairs: Vec<(Value, Value)> =
                dom_a.iter().enumerate().map(|(i, a)| (a.clone(), if i == 1 { v_enum.clone() } else { v_int.clone() })).collect();
            let f_val = Value::fcn_rcd_from_pairs(pairs).unwrap();
            let mut words = vec![0u64; layout.words];
            layout.encode_state(&[f_val], &mut words).unwrap();

            // Directly inspect `branch_single_word`: must return 1 partition
            // with `K_a` completely unpinned (`[0..n)`) rather than `n!` partitions.
            let mut scratch = FactorScratch::default();
            let mut part = Partition::default();
            part.reset(&fg);
            let mut canon = vec![0u64; layout.words];
            // SAFETY: valid encoded words from `layout.encode_state`.
            unsafe { fsym.plans[0].apply_orbit_unchecked(&fg, &fsym.id_img, &words, &mut canon) };
            let item = WorkItem { plan: &fsym.plans[0], node: layout.node(0), raw: &words, canon: &canon, wide_bitset: false };
            let cands = branch_single_word(&fg, part, item, WordOrder::Orbit, &mut scratch);
            assert_eq!(cands.len(), 1, "n={n}: uniform Dyn payloads must collapse to 1 candidate, not n!");
            assert_eq!(cands[0].block_lo()[0], 0, "n={n}: domain block must start at 0");
            assert_eq!(cands[0].block_hi()[0] as usize, n, "n={n}: entire domain must stay a single free block [0..n)");

            // Verify `orbit_fp_factorized` is invariant under swaps of both factors.
            let base_fp = orbit_fp_factorized(&fsym, &layout, &words, sem.as_ref());
            let mut img = fg.identity_img();
            let mut swapped = Vec::new();
            img.swap(0, 1);
            apply_factor_img(&fsym, &layout, &img, &words, &mut swapped);
            assert_eq!(orbit_fp_factorized(&fsym, &layout, &swapped, sem.as_ref()), base_fp);
            img.swap(0, 1);
            let boff = fg.factors[1].offset;
            img.swap(boff, boff + 1);
            apply_factor_img(&fsym, &layout, &img, &words, &mut swapped);
            assert_eq!(orbit_fp_factorized(&fsym, &layout, &swapped, sem.as_ref()), base_fp);
        }
    }
}
