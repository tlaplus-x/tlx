//! Representation-agnostic ordered block partition engine for factorized
//! symmetric-group products `prod_g Sym(K_g)`.
//!
//! Each factor `g` owns a contiguous range `[off, off + len)` inside flat
//! per-key `u16` tables (`dom`, `tgt`, `pos_of`, `block_lo`, `block_hi`).
//! Within a factor, each block `[lo, hi)` maps the domain keys
//! `dom[off + lo .. off + hi]` bijectively onto the target slots
//! `tgt[off + lo .. off + hi]`, which are always kept sorted ascending.
//!
//! Storage stays stack-allocated (`Inline`) whenever `total_keys <= INLINE_KEYS`
//! and spills to a single flat heap `Vec<u16>` for larger groups.

use std::cmp::Ordering;
use std::convert::Infallible;

/// Inline key capacity for stack-allocated [`Partition`] and [`ImgBuf`] tables:
/// covers `S_2..S_16` and products such as `S_4^3`, `S_4 x S_4 x S_3`, or
/// `S_5^3` with zero per-state heap allocation on the hot path.
pub const INLINE_KEYS: usize = 16;

/// Factor layout metadata for a disjoint symmetric-group product
/// `prod_g Sym(K_g)`.
///
/// Implementations must partition `0..self.total_keys()` into `num_factors()`
/// disjoint contiguous ranges `(offset, len)` with every `len <= u16::MAX`.
pub trait FactorLayout {
    /// Total number of keys across all factors.
    fn total_keys(&self) -> usize;

    /// Number of symmetric-group factors.
    fn num_factors(&self) -> usize;

    /// `(offset, len)` of factor `g` inside flat per-key tables.
    fn factor_range(&self, g: usize) -> (usize, usize);
}

#[derive(Clone, Debug)]
enum ImgBufInner {
    Inline { buf: [u16; INLINE_KEYS], len: usize },
    Heap(Vec<u16>),
}

/// Stack-allocated flat permutation image table for `total_keys <= INLINE_KEYS`,
/// spilling to a `Vec<u16>` for larger groups.
#[derive(Clone, Debug)]
pub struct ImgBuf(ImgBufInner);

impl Default for ImgBuf {
    fn default() -> Self {
        Self(ImgBufInner::Inline { buf: [0; INLINE_KEYS], len: 0 })
    }
}

impl ImgBuf {
    /// Resize the buffer to `len` entries.
    ///
    /// Existing inline storage is reused without re-zeroing; callers must
    /// overwrite all `0..len` entries before reading.
    pub fn resize(&mut self, len: usize) {
        if len <= INLINE_KEYS {
            match &mut self.0 {
                ImgBufInner::Inline { len: l, .. } => *l = len,
                ImgBufInner::Heap(_) => self.0 = ImgBufInner::Inline { buf: [0; INLINE_KEYS], len },
            }
        } else {
            match &mut self.0 {
                ImgBufInner::Heap(v) => v.resize(len, 0),
                ImgBufInner::Inline { .. } => self.0 = ImgBufInner::Heap(vec![0; len]),
            }
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        match &self.0 {
            ImgBufInner::Inline { len, .. } => *len,
            ImgBufInner::Heap(v) => v.len(),
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn as_slice(&self) -> &[u16] {
        match &self.0 {
            ImgBufInner::Inline { buf, len } => &buf[..*len],
            ImgBufInner::Heap(v) => v,
        }
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [u16] {
        match &mut self.0 {
            ImgBufInner::Inline { buf, len } => &mut buf[..*len],
            ImgBufInner::Heap(v) => v,
        }
    }
}

/// Backing storage for the 5 flat per-key arrays of [`Partition`]:
/// `dom`, `tgt`, `pos_of`, `block_lo`, `block_hi` laid out contiguously with
/// stride `total_keys`.
#[derive(Clone, Debug)]
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
            match self {
                PartBuf::Inline { stride: s, .. } => *s = stride,
                PartBuf::Heap { .. } => *self = PartBuf::Inline { buf: [0; INLINE_KEYS * 5], stride },
            }
        } else {
            let need = stride.checked_mul(5).expect("partition buffer size overflow");
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
#[derive(Clone, Default, Debug)]
pub struct Partition {
    buf: PartBuf,
    /// Number of slots sitting in blocks of size `>= 2`; `0` means complete.
    unpinned: usize,
}

impl Partition {
    #[inline]
    pub fn dom(&self) -> &[u16] {
        let s = self.buf.stride();
        &self.buf.raw()[..s]
    }

    #[inline]
    pub fn tgt(&self) -> &[u16] {
        let s = self.buf.stride();
        &self.buf.raw()[s..2 * s]
    }

    #[inline]
    pub fn pos_of(&self) -> &[u16] {
        let s = self.buf.stride();
        &self.buf.raw()[2 * s..3 * s]
    }

    #[inline]
    pub fn block_lo(&self) -> &[u16] {
        let s = self.buf.stride();
        &self.buf.raw()[3 * s..4 * s]
    }

    #[inline]
    pub fn block_hi(&self) -> &[u16] {
        let s = self.buf.stride();
        &self.buf.raw()[4 * s..5 * s]
    }

    /// Number of slots sitting in blocks of size `>= 2`.
    #[inline]
    pub fn unpinned(&self) -> usize {
        self.unpinned
    }

    /// Reset to the coarsest partition for `fg` (one full block `[0, len)` per
    /// factor).
    pub fn reset(&mut self, fg: &impl FactorLayout) {
        let total = fg.total_keys();
        self.buf.alloc(total);
        let (dom, tgt, pos_of, block_lo, block_hi) = self.buf.split_mut();
        let mut unpinned = 0usize;
        for g in 0..fg.num_factors() {
            let (off, len) = fg.factor_range(g);
            debug_assert!(len <= usize::from(u16::MAX));
            debug_assert!(off + len <= total);
            let n = len as u16;
            for i in 0..n {
                let idx = off + i as usize;
                dom[idx] = i;
                tgt[idx] = i;
                pos_of[idx] = i;
                block_lo[idx] = 0;
                block_hi[idx] = n;
            }
            if len > 1 {
                unpinned += len;
            }
        }
        self.unpinned = unpinned;
    }

    #[inline]
    pub fn is_complete(&self) -> bool {
        self.unpinned == 0
    }

    #[inline]
    pub fn is_pinned(&self, fg: &impl FactorLayout, g: usize, k: usize) -> bool {
        let (off, _) = fg.factor_range(g);
        let pos = self.pos_of()[off + k] as usize;
        self.block_hi()[off + pos] - self.block_lo()[off + pos] == 1
    }

    #[inline]
    pub fn pinned_target(&self, fg: &impl FactorLayout, g: usize, k: usize) -> Option<u16> {
        let (off, _) = fg.factor_range(g);
        let pos = self.pos_of()[off + k] as usize;
        (self.block_hi()[off + pos] - self.block_lo()[off + pos] == 1).then(|| self.tgt()[off + pos])
    }

    /// Pin domain key `(g, k)` to the target slot at position `slot_pos` within
    /// its current block `[lo, hi)`, keeping remaining target slots sorted.
    pub fn pin_to_slot(&mut self, fg: &impl FactorLayout, g: usize, k: usize, slot_pos: usize) {
        let (off, _) = fg.factor_range(g);
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
    pub fn pin_smallest(&mut self, fg: &impl FactorLayout, g: usize, k: usize) {
        let (off, _) = fg.factor_range(g);
        let p = self.pos_of()[off + k] as usize;
        let lo = self.block_lo()[off + p] as usize;
        self.pin_to_slot(fg, g, k, lo);
    }

    /// Rule 2: refine every block `B` of factor `g` into `(B \cap S)` followed
    /// by `(B \setminus S)`, mapping members onto the smallest target slots.
    pub fn split_by_pred(&mut self, fg: &impl FactorLayout, g: usize, mut in_set: impl FnMut(usize) -> bool, scratch: &mut Vec<u16>) {
        let (off, n) = fg.factor_range(g);
        let (dom, _, pos_of, block_lo, block_hi) = self.buf.split_mut();
        let mut lo = 0usize;
        while lo < n {
            let hi = block_hi[off + lo] as usize;
            if hi - lo > 1 {
                scratch.clear();
                let mut write = lo;
                for pos in lo..hi {
                    let k = dom[off + pos];
                    if in_set(k as usize) {
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
    pub fn bulk_place_first(&mut self, fg: &impl FactorLayout, g: usize, lo: usize, chosen: &[u16]) {
        let (off, _) = fg.factor_range(g);
        let (dom, _, pos_of, block_lo, block_hi) = self.buf.split_mut();
        let hi = block_hi[off + lo] as usize;
        let m = chosen.len();
        debug_assert_eq!(block_lo[off + lo] as usize, lo);
        debug_assert!(m > 0 && lo + m <= hi);
        if lo + m == hi {
            return;
        }
        let rem = hi - lo - m;
        let mut rest_inline = [0u16; INLINE_KEYS];
        let mut rest_heap: Vec<u16> = Vec::new();
        let mut rlen = 0usize;
        if rem <= INLINE_KEYS {
            for pos in lo..hi {
                let k = dom[off + pos];
                if !chosen.contains(&k) {
                    rest_inline[rlen] = k;
                    rlen += 1;
                }
            }
            debug_assert_eq!(rlen, rem);
        } else {
            rest_heap.reserve(rem);
            for pos in lo..hi {
                let k = dom[off + pos];
                if !chosen.contains(&k) {
                    rest_heap.push(k);
                }
            }
            debug_assert_eq!(rest_heap.len(), rem);
        }
        let mid = lo + m;
        dom[off + lo..off + mid].copy_from_slice(chosen);
        if rem <= INLINE_KEYS {
            dom[off + mid..off + hi].copy_from_slice(&rest_inline[..rlen]);
        } else {
            dom[off + mid..off + hi].copy_from_slice(&rest_heap);
        }
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

    /// Rule 3 (fallible): for every block `B \subseteq D` of factor `g` with
    /// `|B| >= 2`, stably sort `B` by `cmp` and split into tied sub-blocks.
    ///
    /// Callers must ensure every block of factor `g` is either entirely inside
    /// or entirely outside `in_dom` (for example by calling
    /// [`Self::split_by_pred`] first), as only each block's first element is
    /// tested. If `cmp` returns `Err(e)`, the error is propagated immediately
    /// and the partition may be left partially refined (callers must discard
    /// or `reset` it before reuse).
    pub fn try_refine_by_cmp<E>(
        &mut self,
        fg: &impl FactorLayout,
        g: usize,
        mut in_dom: impl FnMut(usize) -> bool,
        mut cmp: impl FnMut(u16, u16) -> Result<Ordering, E>,
        scratch: &mut Vec<u16>,
    ) -> Result<(), E> {
        let (off, n) = fg.factor_range(g);
        let (dom, _, pos_of, block_lo, block_hi) = self.buf.split_mut();
        let mut lo = 0usize;
        while lo < n {
            let hi = block_hi[off + lo] as usize;
            if hi - lo > 1 && in_dom(dom[off + lo] as usize) {
                try_stable_sort_u16(&mut dom[off + lo..off + hi], &mut cmp, scratch)?;
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

    /// Rule 3 (infallible): stably sort every multi-element block `B \subseteq D`
    /// of factor `g` by `cmp` and split into tied sub-blocks.
    #[inline]
    pub fn refine_by_cmp(
        &mut self,
        fg: &impl FactorLayout,
        g: usize,
        in_dom: impl FnMut(usize) -> bool,
        mut cmp: impl FnMut(u16, u16) -> Ordering,
        scratch: &mut Vec<u16>,
    ) {
        let Ok(()) = self.try_refine_by_cmp::<Infallible>(fg, g, in_dom, |a, b| Ok(cmp(a, b)), scratch);
    }

    /// Fill `dst` (`dst.len() >= fg.total_keys()`) with `dst[off + k] = target(k)`
    /// for this partition's current representative bijection `dom[pos] -> tgt[pos]`.
    pub fn fill_img_slice(&self, fg: &impl FactorLayout, dst: &mut [u16]) {
        let dom = self.dom();
        let tgt = self.tgt();
        for g in 0..fg.num_factors() {
            let (off, len) = fg.factor_range(g);
            for pos in 0..len {
                let k = dom[off + pos] as usize;
                dst[off + k] = tgt[off + pos];
            }
        }
    }

    /// Fill `img` (resized to `fg.total_keys()`) with `img[off + k] = target(k)`.
    pub fn fill_img_vec(&self, fg: &impl FactorLayout, img: &mut Vec<u16>) {
        img.resize(fg.total_keys(), 0);
        self.fill_img_slice(fg, img);
    }

    /// Fill `dst` (resized to `fg.total_keys()`) with `dst[off + k] = target(k)`.
    pub fn fill_img_buf(&self, fg: &impl FactorLayout, dst: &mut ImgBuf) {
        dst.resize(fg.total_keys());
        self.fill_img_slice(fg, dst.as_mut_slice());
    }

    /// True iff the identity permutation is consistent with this partition
    /// (every domain key `k` lies in a block whose target set contains `k`).
    pub fn contains_identity(&self, fg: &impl FactorLayout) -> bool {
        let dom = self.dom();
        let tgt = self.tgt();
        let block_lo = self.block_lo();
        let block_hi = self.block_hi();
        for g in 0..fg.num_factors() {
            let (off, len) = fg.factor_range(g);
            for pos in 0..len {
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
    pub fn canonicalize_unpinned_blocks(&mut self, fg: &impl FactorLayout) {
        let (dom, _, pos_of, _, block_hi) = self.buf.split_mut();
        for g in 0..fg.num_factors() {
            let (off, n) = fg.factor_range(g);
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

    /// Check `pred(&swap_img)` on every adjacent transposition generating the
    /// free blocks of `self` that intersect `active`.
    ///
    /// Returns `Ok(true)` iff every such transposition satisfies `pred`
    /// (short-circuiting on the first `Ok(false)` or `Err`). Since adjacent
    /// swaps generate `prod_B Sym(B)`, invariance under them proves every
    /// completion of `self` acts identically on the tested value.
    pub fn try_all_active_block_swaps<E>(
        &self,
        fg: &impl FactorLayout,
        active: &[(usize, usize)],
        mut pred: impl FnMut(&[u16]) -> Result<bool, E>,
    ) -> Result<bool, E> {
        let mut swap_img = ImgBuf::default();
        swap_img.resize(fg.total_keys());
        fill_identity_img(fg, swap_img.as_mut_slice());
        let dom = self.dom();
        let block_hi = self.block_hi();
        for g in 0..fg.num_factors() {
            if !active.iter().any(|&(ag, _)| ag == g) {
                continue;
            }
            let (off, n) = fg.factor_range(g);
            let mut lo = 0usize;
            while lo < n {
                let hi = block_hi[off + lo] as usize;
                if hi - lo > 1 && (lo..hi).any(|pos| active.contains(&(g, dom[off + pos] as usize))) {
                    for pos in lo..(hi - 1) {
                        let ka = dom[off + pos];
                        let kb = dom[off + pos + 1];
                        let s = swap_img.as_mut_slice();
                        s[off + ka as usize] = kb;
                        s[off + kb as usize] = ka;
                        let keep = pred(swap_img.as_slice());
                        let s = swap_img.as_mut_slice();
                        s[off + ka as usize] = ka;
                        s[off + kb as usize] = kb;
                        if !keep? {
                            return Ok(false);
                        }
                    }
                }
                lo = hi;
            }
        }
        Ok(true)
    }

    /// Infallible wrapper around [`Self::try_all_active_block_swaps`].
    #[inline]
    pub fn all_active_block_swaps(&self, fg: &impl FactorLayout, active: &[(usize, usize)], mut pred: impl FnMut(&[u16]) -> bool) -> bool {
        let Ok(ok) = self.try_all_active_block_swaps::<Infallible>(fg, active, |swap_img| Ok(pred(swap_img)));
        ok
    }

    /// Visit every partition obtained by pinning each `(g, k)` in `active`
    /// across every available slot in its current block (in ascending slot
    /// order), leaving all inactive blocks intact.
    pub fn try_for_each_active_completion<E>(
        self,
        fg: &impl FactorLayout,
        active: &[(usize, usize)],
        mut visit: impl FnMut(Partition) -> Result<(), E>,
    ) -> Result<(), E> {
        fn dfs<L: FactorLayout, E>(
            fg: &L,
            active: &[(usize, usize)],
            part: Partition,
            idx: usize,
            visit: &mut impl FnMut(Partition) -> Result<(), E>,
        ) -> Result<(), E> {
            if idx == active.len() {
                return visit(part);
            }
            let (g, k) = active[idx];
            let (off, _) = fg.factor_range(g);
            let p = part.pos_of()[off + k] as usize;
            let lo = part.block_lo()[off + p] as usize;
            let hi = part.block_hi()[off + p] as usize;
            if hi - lo == 1 {
                return dfs(fg, active, part, idx + 1, visit);
            }
            for slot_pos in lo..hi {
                let mut next = part.clone();
                next.pin_to_slot(fg, g, k, slot_pos);
                dfs(fg, active, next, idx + 1, visit)?;
            }
            Ok(())
        }
        dfs(fg, active, self, 0, &mut visit)
    }

    /// Infallible wrapper around [`Self::try_for_each_active_completion`].
    #[inline]
    pub fn for_each_active_completion(self, fg: &impl FactorLayout, active: &[(usize, usize)], mut visit: impl FnMut(Partition)) {
        let Ok(()) = self.try_for_each_active_completion::<Infallible>(fg, active, |leaf| {
            visit(leaf);
            Ok(())
        });
    }

    /// Approximate heap bytes owned by this partition (0 when inline).
    pub fn heap_bytes(&self) -> usize {
        self.buf.heap_bytes()
    }
}

fn fill_identity_img(fg: &impl FactorLayout, dst: &mut [u16]) {
    for g in 0..fg.num_factors() {
        let (off, len) = fg.factor_range(g);
        for i in 0..len {
            dst[off + i] = i as u16;
        }
    }
}

/// Fallible stable sort: insertion sort for small slices (`<= 16`), bottom-up
/// merge sort using `scratch` for larger blocks.
fn try_stable_sort_u16<E>(
    slice: &mut [u16],
    cmp: &mut impl FnMut(u16, u16) -> Result<Ordering, E>,
    scratch: &mut Vec<u16>,
) -> Result<(), E> {
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

#[cfg(test)]
mod tests {
    use super::*;

    struct TestLayout {
        ranges: Vec<(usize, usize)>,
        total: usize,
    }

    impl TestLayout {
        fn new(lens: &[usize]) -> Self {
            let mut ranges = Vec::with_capacity(lens.len());
            let mut off = 0usize;
            for &len in lens {
                ranges.push((off, len));
                off += len;
            }
            Self { ranges, total: off }
        }
    }

    impl FactorLayout for TestLayout {
        fn total_keys(&self) -> usize {
            self.total
        }

        fn num_factors(&self) -> usize {
            self.ranges.len()
        }

        fn factor_range(&self, g: usize) -> (usize, usize) {
            self.ranges[g]
        }
    }

    fn assert_invariants(fg: &TestLayout, part: &Partition) {
        let dom = part.dom();
        let tgt = part.tgt();
        let pos_of = part.pos_of();
        let blo = part.block_lo();
        let bhi = part.block_hi();
        let mut expected_unpinned = 0usize;
        for g in 0..fg.num_factors() {
            let (off, n) = fg.factor_range(g);
            let mut seen_dom = vec![false; n];
            let mut seen_tgt = vec![false; n];
            let mut lo = 0usize;
            while lo < n {
                let hi = bhi[off + lo] as usize;
                assert!(hi > lo && hi <= n, "invalid block [{lo}, {hi})");
                if hi - lo > 1 {
                    expected_unpinned += hi - lo;
                }
                for pos in lo..hi {
                    assert_eq!(blo[off + pos] as usize, lo);
                    assert_eq!(bhi[off + pos] as usize, hi);
                    let k = dom[off + pos] as usize;
                    let t = tgt[off + pos] as usize;
                    assert!(!seen_dom[k], "duplicate dom key {k}");
                    assert!(!seen_tgt[t], "duplicate tgt slot {t}");
                    seen_dom[k] = true;
                    seen_tgt[t] = true;
                    assert_eq!(pos_of[off + k] as usize, pos);
                    if pos > lo {
                        assert!(tgt[off + pos - 1] < tgt[off + pos], "tgt not sorted ascending");
                    }
                }
                lo = hi;
            }
        }
        assert_eq!(part.unpinned(), expected_unpinned);
        assert_eq!(part.is_complete(), expected_unpinned == 0);
    }

    #[test]
    fn inline_heap_transitions_for_partition_and_img_buf() {
        let small = TestLayout::new(&[4, 3]); // 7 <= INLINE_KEYS
        let exact = TestLayout::new(&[16]); // 16 == INLINE_KEYS
        let large = TestLayout::new(&[10, 10]); // 20 > INLINE_KEYS

        let mut part = Partition::default();
        part.reset(&small);
        assert_eq!(part.heap_bytes(), 0);
        assert_invariants(&small, &part);

        // Inline -> Inline reuse (grows to exact INLINE_KEYS without heap).
        part.reset(&exact);
        assert_eq!(part.heap_bytes(), 0);
        assert_invariants(&exact, &part);

        // Inline -> Heap transition.
        part.reset(&large);
        assert!(part.heap_bytes() >= 20 * 5 * std::mem::size_of::<u16>());
        assert_invariants(&large, &part);

        // Heap -> Inline transition.
        part.reset(&small);
        assert_eq!(part.heap_bytes(), 0);
        assert_invariants(&small, &part);

        // ImgBuf transitions across inline/heap boundaries.
        let mut img = ImgBuf::default();
        assert!(img.is_empty());
        part.fill_img_buf(&small, &mut img);
        assert_eq!(img.as_slice(), &[0, 1, 2, 3, 0, 1, 2]);
        part.reset(&large);
        part.fill_img_buf(&large, &mut img);
        assert_eq!(img.len(), 20);
        assert_eq!(&img.as_slice()[..10], &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
        assert_eq!(&img.as_slice()[10..], &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]);
        part.reset(&small);
        part.fill_img_buf(&small, &mut img);
        assert_eq!(img.as_slice(), &[0, 1, 2, 3, 0, 1, 2]);
    }

    #[test]
    fn pin_to_slot_and_pin_smallest_keep_targets_sorted() {
        let fg = TestLayout::new(&[4, 2]);
        let mut part = Partition::default();
        part.reset(&fg);
        assert!(!part.is_pinned(&fg, 0, 2));
        assert_eq!(part.pinned_target(&fg, 0, 2), None);

        // Pin key 2 to target slot at pos 2 (target value 2).
        part.pin_to_slot(&fg, 0, 2, 2);
        assert_invariants(&fg, &part);
        assert!(part.is_pinned(&fg, 0, 2));
        assert_eq!(part.pinned_target(&fg, 0, 2), Some(2));
        // Remaining block [1, 4) holds target slots [0, 1, 3] sorted ascending.
        assert_eq!(&part.tgt()[1..4], &[0, 1, 3]);
        assert!(part.contains_identity(&fg));

        // Pin key 3 to smallest remaining target slot (target 0) -> no longer contains identity.
        part.pin_smallest(&fg, 0, 3);
        assert_invariants(&fg, &part);
        assert_eq!(part.pinned_target(&fg, 0, 3), Some(0));
        assert!(!part.contains_identity(&fg));

        // Pinning an already-pinned key is a no-op.
        let unpinned_before = part.unpinned();
        part.pin_smallest(&fg, 0, 3);
        assert_eq!(part.unpinned(), unpinned_before);

        // Pinning one key of a 2-element block pins both and updates unpinned by 2.
        part.pin_to_slot(&fg, 1, 1, 0);
        assert_invariants(&fg, &part);
        assert_eq!(part.pinned_target(&fg, 1, 1), Some(0));
        assert_eq!(part.pinned_target(&fg, 1, 0), Some(1));
    }

    #[test]
    fn split_by_pred_splits_multi_blocks_and_tracks_unpinned() {
        let fg = TestLayout::new(&[6]);
        let mut part = Partition::default();
        let mut scratch = Vec::new();
        part.reset(&fg);

        // Split into even {0, 2, 4} and odd {1, 3, 5}.
        part.split_by_pred(&fg, 0, |k| k % 2 == 0, &mut scratch);
        assert_invariants(&fg, &part);
        assert_eq!(&part.dom()[0..3], &[0, 2, 4]);
        assert_eq!(&part.dom()[3..6], &[1, 3, 5]);
        assert_eq!(part.unpinned(), 6);
        assert!(!part.contains_identity(&fg)); // key 4 sits in target set {0, 1, 2}

        // Split again by `k < 3`: {0, 2} | {4} | {1} | {3, 5}.
        part.split_by_pred(&fg, 0, |k| k < 3, &mut scratch);
        assert_invariants(&fg, &part);
        assert_eq!(part.unpinned(), 4);
        assert!(part.is_pinned(&fg, 0, 4));
        assert!(part.is_pinned(&fg, 0, 1));
    }

    #[test]
    fn bulk_place_first_handles_inline_and_heap_remainders() {
        // Inline remainder (rem <= INLINE_KEYS).
        let fg_small = TestLayout::new(&[5]);
        let mut part = Partition::default();
        part.reset(&fg_small);
        part.bulk_place_first(&fg_small, 0, 0, &[4, 1]);
        assert_invariants(&fg_small, &part);
        assert_eq!(&part.dom()[0..2], &[4, 1]);
        assert_eq!(&part.dom()[2..5], &[0, 2, 3]);
        assert_eq!(part.unpinned(), 5);

        // Placing the entire block is a no-op.
        part.bulk_place_first(&fg_small, 0, 0, &[4, 1]);
        assert_invariants(&fg_small, &part);

        // Heap remainder (rem > INLINE_KEYS): 20 keys, place 2 -> rem = 18 > 16.
        let fg_large = TestLayout::new(&[20]);
        part.reset(&fg_large);
        part.bulk_place_first(&fg_large, 0, 0, &[19, 0]);
        assert_invariants(&fg_large, &part);
        assert_eq!(&part.dom()[0..2], &[19, 0]);
        assert_eq!(part.block_hi()[0], 2);
        assert_eq!(part.block_lo()[2], 2);
        assert_eq!(part.block_hi()[2], 20);
        assert_eq!(part.unpinned(), 20);
    }

    #[test]
    fn try_refine_by_cmp_stability_and_error_propagation() {
        // Insertion-sort path (n = 6 <= 16) + error propagation.
        let fg6 = TestLayout::new(&[6]);
        let mut part = Partition::default();
        let mut scratch = Vec::new();
        part.reset(&fg6);
        let err = part.try_refine_by_cmp(
            &fg6,
            0,
            |_| true,
            |a, b| {
                if a == 3 || b == 3 {
                    Err("incomparable")
                } else {
                    Ok((a % 2).cmp(&(b % 2)))
                }
            },
            &mut scratch,
        );
        assert_eq!(err, Err("incomparable"));

        // Merge-sort path (n = 20 > 16): group by `k % 4`, preserving original
        // ascending key order within every tied sub-block (stability check).
        let fg20 = TestLayout::new(&[20]);
        part.reset(&fg20);
        part.refine_by_cmp(&fg20, 0, |_| true, |a, b| (a % 4).cmp(&(b % 4)), &mut scratch);
        assert_invariants(&fg20, &part);
        for bucket in 0..4usize {
            let lo = bucket * 5;
            let hi = lo + 5;
            let expected: Vec<u16> = (0..20u16).filter(|&k| k as usize % 4 == bucket).collect();
            assert_eq!(&part.dom()[lo..hi], &expected[..]);
            assert_eq!(part.block_lo()[lo] as usize, lo);
            assert_eq!(part.block_hi()[lo] as usize, hi);
        }

        // Error propagation on the merge-sort path (n = 20 > 16).
        part.reset(&fg20);
        let err =
            part.try_refine_by_cmp(&fg20, 0, |_| true, |a, b| if a == 17 || b == 17 { Err(42u32) } else { Ok(a.cmp(&b)) }, &mut scratch);
        assert_eq!(err, Err(42));
    }

    #[test]
    fn contains_identity_and_canonicalize_unpinned_blocks() {
        let fg = TestLayout::new(&[4, 3]);
        let mut part = Partition::default();
        part.reset(&fg);
        assert!(part.contains_identity(&fg));

        // Pin key 0 -> target 0 (still contains identity), then scramble unpinned block [1, 4).
        part.pin_to_slot(&fg, 0, 0, 0);
        part.bulk_place_first(&fg, 0, 1, &[3, 2]);
        assert_invariants(&fg, &part);
        // Block [1, 3) has dom {3, 2} and tgt {1, 2} -> key 3 not in {1, 2}.
        assert!(!part.contains_identity(&fg));

        // Canonicalizing sorts dom ascending inside each unpinned block.
        part.canonicalize_unpinned_blocks(&fg);
        assert_invariants(&fg, &part);
        assert_eq!(&part.dom()[1..3], &[2, 3]);

        // Verify fill_img_vec / fill_img_buf / fill_img_slice agree.
        let mut img_vec = Vec::new();
        let mut img_buf = ImgBuf::default();
        let mut img_arr = [0u16; 7];
        part.fill_img_vec(&fg, &mut img_vec);
        part.fill_img_buf(&fg, &mut img_buf);
        part.fill_img_slice(&fg, &mut img_arr);
        assert_eq!(img_vec.as_slice(), img_buf.as_slice());
        assert_eq!(img_vec.as_slice(), &img_arr[..]);
        // Factor 0: 0->0, 2->1, 3->2, 1->3; factor 1: identity 0->0, 1->1, 2->2.
        assert_eq!(img_vec, vec![0, 3, 1, 2, 0, 1, 2]);
    }

    #[test]
    fn active_block_swaps_and_completions() {
        let fg = TestLayout::new(&[3, 2]);
        let mut part = Partition::default();
        part.reset(&fg);

        // Only factor 0 has active atoms; factor 1 must not be swapped.
        let active = [(0, 0), (0, 2)];
        let mut seen_swaps = Vec::new();
        let all_ok = part.all_active_block_swaps(&fg, &active, |img| {
            seen_swaps.push(img.to_vec());
            true
        });
        assert!(all_ok);
        // Adjacent swaps of [0, 1, 2] are (0,1) and (1,2), with factor 1 fixed.
        assert_eq!(seen_swaps, vec![vec![1, 0, 2, 0, 1], vec![0, 2, 1, 0, 1]]);

        // Short-circuit on false.
        let mut calls = 0usize;
        let ok = part.all_active_block_swaps(&fg, &active, |_| {
            calls += 1;
            false
        });
        assert!(!ok);
        assert_eq!(calls, 1);

        // Active completions over 2 keys in S_3: 3 * 2 = 6 leaves, factor 1 untouched.
        let mut leaves = Vec::new();
        part.for_each_active_completion(&fg, &active, |leaf| {
            assert_invariants(&fg, &leaf);
            assert!(leaf.is_pinned(&fg, 0, 0));
            assert!(leaf.is_pinned(&fg, 0, 2));
            assert!(!leaf.is_pinned(&fg, 1, 0));
            let mut img = Vec::new();
            leaf.fill_img_vec(&fg, &mut img);
            leaves.push(img);
        });
        assert_eq!(leaves.len(), 6);
    }
}
