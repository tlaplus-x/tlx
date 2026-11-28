//! Encoded-word ordering, permutation application and moved-atom scanning
//! for `SYMMETRY` refinement on encoded states.

use std::cmp::Ordering;

use tlx_base::partition::Partition;
use tlx_layout::pack::{FieldLoc, SlotLayout};
use tlx_layout::permute::{AtomTable, FactorGroupSpec, FactorPlan};
use tlx_layout::LayoutNode;
use tlx_value::Value;

// ---------------------------------------------------------------------------
// Word comparison & item application
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum WordOrder {
    /// Canonical orbit order for `Fingerprint::Symmetry` / `ProjectionOrbit`.
    /// Plain unsigned slice `.cmp()`, using little-endian multi-word order on
    /// `>= 2`-word bitsets so Rule 2 is exact at every bitset width.
    Orbit,
    /// Exact TLC value order (`LayoutNode::cmp_tlc_words`) for `SymView`.
    Tlc,
}

#[derive(Clone, Copy)]
pub(super) struct WorkItem<'a> {
    pub(super) plan: &'a FactorPlan,
    pub(super) node: &'a LayoutNode,
    /// Original encoded words (real `Ref` handles for `apply_orbit_unchecked`).
    pub(super) raw: &'a [u64],
    /// Canonicalized words (`Ref` handles replaced by digests, dynamic witness
    /// words zeroed); identical to `raw` when `SemFp` is inactive or in `Tlc` mode.
    pub(super) canon: &'a [u64],
    pub(super) wide_bitset: bool,
}

#[inline]
pub(super) fn cmp_words_mode(mode: WordOrder, plan: &FactorPlan, node: &LayoutNode, wide_bitset: bool, a: &[u64], b: &[u64]) -> Ordering {
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
pub(super) fn apply_item(mode: WordOrder, fg: &FactorGroupSpec, img: &[u16], item: WorkItem<'_>, dst: &mut [u64]) {
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
pub(super) fn map_scalar_part(fg: &FactorGroupSpec, table: &AtomTable, part: &Partition, raw: u64) -> u64 {
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
        Value::ModelValue(_) | Value::Str(_) => {
            if let Some((g, k)) = fg.lookup(tlx_value::SymAtom::from_value(v).unwrap()) {
                f(g, k);
            }
        }
        Value::Bool(_) | Value::Int(_) | Value::Interval(..) => {}
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

pub(super) fn has_unpinned_words(fg: &FactorGroupSpec, plan: &FactorPlan, raw: &[u64], part: &Partition) -> bool {
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

pub(super) fn has_unpinned_in_factor_words(
    fg: &FactorGroupSpec,
    plan: &FactorPlan,
    raw: &[u64],
    part: &Partition,
    target_g: usize,
) -> bool {
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

pub(super) fn collect_unpinned_words(
    fg: &FactorGroupSpec,
    plan: &FactorPlan,
    raw: &[u64],
    part: &Partition,
    out: &mut Vec<(usize, usize)>,
) {
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
