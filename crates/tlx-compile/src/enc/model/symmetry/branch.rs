//! Branch-and-bound minimization (Case A packed slots and Case B active
//! atoms) and the factorized refinement loop for `SYMMETRY` on encoded states.

use std::cmp::Ordering;

use tlx_base::partition::{ImgBuf, Partition, INLINE_KEYS};
use tlx_layout::pack::SlotLayout;
use tlx_layout::permute::{AtomTable, DomMap, FactorGroupSpec, FactorPlan};
use tlx_layout::{Layout, LayoutNode};

use super::order::{
    apply_item, cmp_words_mode, collect_unpinned_words, has_unpinned_in_factor_words, map_scalar_part, WordOrder, WorkItem,
};
use super::refine::{minimize_across_candidates, refine_deterministic, DetOutcome, FactorScratch, PendingItem};
use super::FactorSymmetry;
use crate::enc::model::SemFp;

/// Branch-and-bound minimization of a single irreducible `WorkItem`:
/// dispatches direct-factor `Fcn`/`Map` to slot-by-slot Case A, and general
/// recursive encodings to active-atom Case B.
pub(super) fn branch_single_word(
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
pub(super) fn choose_factorized_words(
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
