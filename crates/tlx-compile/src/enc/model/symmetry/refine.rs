//! Deterministic partition refinement (Rules 1-3) and tied-candidate
//! minimization for `SYMMETRY` on encoded states.

use std::cmp::Ordering;

use tlx_base::partition::{ImgBuf, Partition, INLINE_KEYS};
use tlx_layout::pack::{FieldLoc, SlotLayout};
use tlx_layout::permute::{AtomTable, DomMap, FactorGroupSpec, FactorPlan};

use super::branch::branch_single_word;
use super::order::{apply_item, cmp_words_mode, has_unpinned_words, map_scalar_part, WordOrder, WorkItem};

// ---------------------------------------------------------------------------
// Deterministic refinement (Rules 1-3)
// ---------------------------------------------------------------------------

#[derive(Default)]
pub(super) struct FactorScratch {
    pub(super) part: Partition,
    pub(super) sort: Vec<u16>,
    pub(super) img: ImgBuf,
    pub(super) payload_buf: Vec<u64>,
    /// Reusable comparison scratch for complete-candidate fast path.
    pub(super) cand_cur: Vec<u64>,
    pub(super) cand_best: Vec<u64>,
    /// Output canonicalized state buffer (`orbit_fp`) & per-variable canonicalization scratch.
    pub(super) out_buf: Vec<u64>,
    pub(super) var_canon_buf: Vec<u64>,
}

pub(super) enum DetOutcome<'a> {
    Done,
    /// A single irreducible `WorkItem` needs branching, with no remaining
    /// sibling items (avoids allocating a `Vec<PendingItem>`).
    BranchOne(WorkItem<'a>),
    NeedBranch(Vec<PendingItem<'a>>),
}

#[derive(Clone, Copy)]
pub(super) enum PendingItem<'a> {
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

pub(super) fn refine_deterministic<'a>(
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
pub(super) fn minimize_across_candidates(
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
