//! Lock-free open-addressing fingerprint tables, cache-line quotiented slots
//! and page-wise physical reclamation during growth (docs/scale.md §4.1).
//!
//! Fingerprints are placed monotonically by `home = (fp * n) >> 64`
//! (`fastrange`). Because every bucket spans at most `u64::MAX / n + 1 <= 2^k`
//! consecutive values where `k = bit_width(u64::MAX / n)`, the low `k` bits
//! `low = fp & ((1 << k) - 1)` uniquely identify every member of `home`, and
//! `base + (low.wrapping_sub(base) & mask)` with `base = ceil(home * 2^64 / n)`
//! recovers the exact 64-bit `fp` without division on insert or lookup.
//!
//! Two slot tiers share one `Table` interface:
//! - `n < 2^21`: `AtomicU64` slots (`8.0 B/slot`), storing normalized `fp`
//!   directly (`0` = empty).
//! - `n >= 2^21`: `Line` (`64 B` per 10 slots = `6.4 B/slot`), packing each
//!   slot's `AtomicU16` `(tag, low_hi)` header and `AtomicU32` `low_lo`
//!   payload into the same 64-byte hardware cache line.
//!
//! Compact slot publication is lock-free via wait-free helping: before claiming
//! an empty slot's header with its per-thread `claim_id` (`1..=4095`), a writer
//! publishes `(want_hi, want_lo)` into its cache-line-padded entry in `CLAIMS`.
//! Any thread probing a claimed slot completes the write of `lo` and `hi`
//! directly in O(1) without waiting for the claiming thread to resume.
//!
//! Rare probe displacements `d >= d_inline_max` store the overflow tag in `hi`
//! and an index into `Overflow` (a lock-free segmented `u64` array, empty until
//! needed, charged directly to the set's memory gauge and optionally capped).

use std::alloc::{alloc_zeroed, dealloc, handle_alloc_error, Layout};
use std::ptr::NonNull;
use std::sync::atomic::{fence, AtomicBool, AtomicU16, AtomicU32, AtomicU64, Ordering};
use std::sync::Arc;

use tlx_base::padded::Padded;

use super::count::SLACK;
use super::overflow::{page_size, Overflow};
use super::{HARD_DEN, HARD_NUM, HIGH_DEN, HIGH_NUM, OVERFLOW};
use crate::io::IoError;
use crate::mem::Gauge;

/// Tables of at least this many bytes are mapped from the OS directly so
/// untouched pages stay non-resident and completed chunks can be released
/// physically during parallel rehash.
const MAP_BYTES: usize = 1 << 20;

/// Home-slot threshold from which 48-bit cache-line quotiented slots
/// (`6.4 B/slot`, 10 per 64 B line) apply: `low_bits <= 43` fits `low_hi` in
/// at most 11 bits, leaving `4095` lock-free claim IDs (`1..=4095`) plus at
/// least `29` inline probe displacements (`d = 0..=28`) and an overflow tag.
pub(super) const COMPACT48_MIN_SLOTS: usize = 1 << 21;

/// Slots per 64-byte cache line in the compact tier.
const SLOTS_48: usize = 10;

/// Slots per `AtomicU64` probe group in the `< 2^21` tier.
const RAW_GROUP: usize = 4;

/// Maximum byte granularity of one parallel rehash work unit with physical
/// reclamation (`2 MiB`: aligns to 2 MiB transparent huge pages, 4/16/64 KiB
/// base pages, and 64-byte cache lines while avoiding THP splits and excess
/// `madvise` TLB shootdowns).
pub(super) const REHASH_CHUNK_BYTES: usize = 2 << 20;

/// Header encoding in `Compact` (`AtomicU16`):
/// - `0`: empty slot (`EMPTY_HI`).
/// - `1..=MAX_CLAIMS` (`1..=4095`): in-flight claim owned by `claim_id`;
///   `CLAIMS[claim_id - 1]` holds `(want_hi << 32) | want_lo` for O(1) helping.
/// - `>= PUBLISHED_BASE` (`4096`): published slot (`(tag << q_hi_bits) | q_hi`).
const EMPTY_HI: u16 = 0;
const MAX_CLAIMS: usize = 4095;
const PUBLISHED_BASE: u16 = 4096;
/// Claim sentinel used only by exclusive `place` during `grow_to` (no readers).
const PLACE_CLAIM_HI: u16 = 1;

const CLAIM_WORDS: usize = MAX_CLAIMS.div_ceil(64);

/// Per-thread publication descriptors for wait-free helping on `Compact`.
/// Only the first `N` entries (for `N` active threads) are ever touched.
static CLAIMS: [Padded<AtomicU64>; MAX_CLAIMS] = [const { Padded(AtomicU64::new(0)) }; MAX_CLAIMS];

/// Lock-free bitmap of currently assigned thread claim IDs (`0..MAX_CLAIMS`).
static CLAIM_BITS: [AtomicU64; CLAIM_WORDS] = [const { AtomicU64::new(0) }; CLAIM_WORDS];

struct ClaimGuard(u16);

impl ClaimGuard {
    fn acquire() -> ClaimGuard {
        for (w, word) in CLAIM_BITS.iter().enumerate() {
            let mut cur = word.load(Ordering::Relaxed);
            while cur != u64::MAX {
                let bit = (!cur).trailing_zeros() as usize;
                let idx = w * 64 + bit;
                if idx >= MAX_CLAIMS {
                    break;
                }
                let mask = 1u64 << bit;
                match word.compare_exchange_weak(cur, cur | mask, Ordering::Acquire, Ordering::Relaxed) {
                    Ok(_) => return ClaimGuard((idx + 1) as u16),
                    Err(v) => cur = v,
                }
            }
        }
        panic!("fingerprint set: more than {MAX_CLAIMS} concurrent inserting threads");
    }
}

impl Drop for ClaimGuard {
    fn drop(&mut self) {
        let idx = (self.0 - 1) as usize;
        CLAIM_BITS[idx / 64].fetch_and(!(1u64 << (idx % 64)), Ordering::Release);
    }
}

thread_local! {
    /// Zero-cost `const`-initialized TLS cache for the thread's claim ID so the
    /// hot insert path avoids destructor-bearing TLS lookup overhead.
    static CLAIM_ID_FAST: std::cell::Cell<u16> = const { std::cell::Cell::new(0) };
    static CLAIM_GUARD: std::cell::OnceCell<ClaimGuard> = const { std::cell::OnceCell::new() };
}

#[cold]
#[inline(never)]
fn init_claim_id() -> u16 {
    CLAIM_GUARD.with(|cell| {
        let id = cell.get_or_init(ClaimGuard::acquire).0;
        CLAIM_ID_FAST.set(id);
        id
    })
}

#[inline(always)]
fn this_claim_id() -> u16 {
    let id = CLAIM_ID_FAST.get();
    if id != 0 {
        id
    } else {
        init_claim_id()
    }
}

#[inline(always)]
fn pack_claim(want_hi: u16, want_lo: u32) -> u64 {
    ((want_hi as u64) << 32) | (want_lo as u64)
}

#[cfg(test)]
type PauseHook = Box<dyn Fn() + Send + Sync>;

/// Raw zeroed memory backing a slot array, either anonymous `mmap` (for
/// `>= MAP_BYTES`) or `alloc_zeroed`.
struct MappedBuf {
    ptr: NonNull<u8>,
    layout: Layout,
    mapped: bool,
}

// SAFETY: `MappedBuf` uniquely owns its allocation and exposes shared access
// only through atomic types.
unsafe impl Send for MappedBuf {}
// SAFETY: Shared references only read metadata or atomic elements.
unsafe impl Sync for MappedBuf {}

impl MappedBuf {
    fn zeroed(size: usize, align: usize) -> MappedBuf {
        assert!(size > 0, "empty fingerprint table buffer");
        let layout = Layout::from_size_align(size, align).expect("fingerprint set too large");
        #[cfg(unix)]
        if layout.size() >= MAP_BYTES {
            // SAFETY: requests a fresh private anonymous mapping of `layout.size()`
            // bytes at an OS-chosen page-aligned address (`>= 4096 >= align`),
            // touching no existing mapping.
            let p = unsafe {
                libc::mmap(
                    std::ptr::null_mut(),
                    layout.size(),
                    libc::PROT_READ | libc::PROT_WRITE,
                    libc::MAP_PRIVATE | libc::MAP_ANON,
                    -1,
                    0,
                )
            };
            if p != libc::MAP_FAILED {
                #[cfg(target_os = "linux")]
                // SAFETY: `p` and `layout.size()` name the anonymous mapping
                // just created above.
                unsafe {
                    libc::madvise(p, layout.size(), libc::MADV_HUGEPAGE);
                }
                return MappedBuf { ptr: NonNull::new(p.cast()).expect("mapped non-null"), layout, mapped: true };
            }
        }
        // SAFETY: `layout` has non-zero size (`size > 0`) and valid power-of-two alignment.
        let raw = unsafe { alloc_zeroed(layout) };
        let Some(ptr) = NonNull::new(raw) else { handle_alloc_error(layout) };
        MappedBuf { ptr, layout, mapped: false }
    }

    /// Advise the OS kernel that physical pages wholly inside `byte_lo..byte_hi`
    /// will not be read again and may be reclaimed immediately.
    ///
    /// # Safety
    /// No thread may read or write `byte_lo..byte_hi` concurrently or after
    /// this call, and `byte_lo <= byte_hi <= self.layout.size()`.
    unsafe fn discard_bytes(&self, byte_lo: usize, byte_hi: usize) {
        debug_assert!(byte_lo <= byte_hi && byte_hi <= self.layout.size());
        #[cfg(unix)]
        if self.mapped {
            let page = page_size();
            let lo = byte_lo.next_multiple_of(page);
            let hi = byte_hi & !(page - 1);
            if lo < hi {
                #[cfg(target_os = "macos")]
                const ADVICE: libc::c_int = libc::MADV_FREE_REUSABLE;
                #[cfg(not(target_os = "macos"))]
                const ADVICE: libc::c_int = libc::MADV_DONTNEED;
                // SAFETY: `self.mapped` came from `mmap` (hence page-aligned);
                // `lo` and `hi - lo` are page-aligned within `0..layout.size()`,
                // and the caller guarantees no further accesses to this range.
                unsafe {
                    libc::madvise(self.ptr.as_ptr().add(lo).cast(), hi - lo, ADVICE);
                }
            }
        }
    }
}

impl Drop for MappedBuf {
    fn drop(&mut self) {
        if self.mapped {
            #[cfg(unix)]
            // SAFETY: `ptr` and `layout.size()` match the `mmap` in `zeroed`,
            // and `&mut self` guarantees exclusive teardown.
            unsafe {
                libc::munmap(self.ptr.as_ptr().cast(), self.layout.size());
            }
        } else {
            // SAFETY: `ptr` was allocated by `alloc_zeroed(self.layout)`.
            unsafe {
                dealloc(self.ptr.as_ptr(), self.layout);
            }
        }
    }
}

/// Precomputed constants for division-free low-bit `fastrange` quotienting and
/// exact 64-bit reconstruction over `n` home slots.
#[derive(Clone, Copy, Debug)]
pub(super) struct Quotient {
    n: u64,
    /// `bit_width(u64::MAX / n)`: low bits of `fp` that uniquely distinguish
    /// every member of a home bucket.
    pub(super) low_bits: u32,
    low_mask: u64,
    /// When `n` is a power of two (`2^s`), `base(home) = home << (64 - s)`;
    /// otherwise `0` (use `base_q` / `base_r` recurrence or `div_ceil`).
    pow2_shift: u32,
    /// `floor(2^64 / n)` and `2^64 mod n` for division-free sequential
    /// `base(home)` stepping during `rehash_range`.
    base_q: u64,
    base_r: u64,
}

impl Quotient {
    pub(super) fn new(n: usize) -> Quotient {
        assert!(n >= 2 && (n as u64) <= (1u64 << 60), "invalid fingerprint slot count {n}");
        let d = n as u64;
        let q_max = u64::MAX / d;
        let low_bits = (64 - q_max.leading_zeros()).max(1);
        let low_mask = (1u64 << low_bits) - 1;
        let pow2_shift = if d.is_power_of_two() { 64 - d.trailing_zeros() } else { 0 };
        let base_q = ((1u128 << 64) / d as u128) as u64;
        let base_r = ((1u128 << 64) % d as u128) as u64;
        Quotient { n: d, low_bits, low_mask, pow2_shift, base_q, base_r }
    }

    /// Map `fp` to `(home, low)` with `0 <= home < n` and
    /// `fp == reconstruct(home, low)`.
    #[inline(always)]
    pub(super) fn split(&self, fp: u64) -> (usize, u64) {
        let home = ((fp as u128 * self.n as u128) >> 64) as usize;
        (home, fp & self.low_mask)
    }

    #[inline(always)]
    fn reconstruct_with_base(&self, base: u64, low: u64) -> u64 {
        base.wrapping_add(low.wrapping_sub(base) & self.low_mask)
    }

    /// Recover the exact 64-bit `fp` from `(home, low)`.
    #[inline]
    pub(super) fn reconstruct(&self, home: usize, low: u64) -> u64 {
        debug_assert!((home as u64) < self.n);
        let h = home as u64;
        let base = if h == 0 {
            0
        } else if self.pow2_shift != 0 {
            h << self.pow2_shift
        } else {
            (((h as u128) << 64).div_ceil(self.n as u128)) as u64
        };
        let fp = self.reconstruct_with_base(base, low);
        debug_assert_eq!(self.split(fp), (home, low));
        fp
    }
}

/// Division-free incremental cursor for `base(home) = ceil(home * 2^64 / n)`
/// during sequential table scans (`rehash_range`) on non-power-of-two `n`.
struct BaseCursor {
    quot: Quotient,
    h: u64,
    q: u64,
    rem: u64,
}

impl BaseCursor {
    fn new(quot: Quotient, start_h: usize) -> BaseCursor {
        let h = start_h as u64;
        let (q, rem) = if h == 0 || quot.pow2_shift != 0 {
            (0, 0)
        } else {
            let num = (h as u128) << 64;
            let d = quot.n as u128;
            ((num / d) as u64, (num % d) as u64)
        };
        BaseCursor { quot, h, q, rem }
    }

    #[inline(always)]
    fn base(&mut self, home: usize) -> u64 {
        let target = home as u64;
        if target == 0 {
            return 0;
        }
        if self.quot.pow2_shift != 0 {
            return target << self.quot.pow2_shift;
        }
        if target >= self.h && target - self.h <= 16 {
            while self.h < target {
                self.q = self.q.wrapping_add(self.quot.base_q);
                self.rem += self.quot.base_r;
                if self.rem >= self.quot.n {
                    self.rem -= self.quot.n;
                    self.q = self.q.wrapping_add(1);
                }
                self.h += 1;
            }
        } else if target < self.h && self.h - target <= 16 {
            while self.h > target {
                if self.rem < self.quot.base_r {
                    self.rem += self.quot.n;
                    self.q = self.q.wrapping_sub(1);
                }
                self.rem -= self.quot.base_r;
                self.q = self.q.wrapping_sub(self.quot.base_q);
                self.h -= 1;
            }
        } else {
            let num = (target as u128) << 64;
            let d = self.quot.n as u128;
            self.h = target;
            self.q = (num / d) as u64;
            self.rem = (num % d) as u64;
        }
        self.q.wrapping_add((self.rem != 0) as u64)
    }

    #[inline(always)]
    fn reconstruct(&mut self, home: usize, low: u64) -> u64 {
        let base = self.base(home);
        let fp = self.quot.reconstruct_with_base(base, low);
        debug_assert_eq!(self.quot.split(fp), (home, low));
        fp
    }
}

/// One 64-byte cache line holding `SLOTS_48` (10) quotiented slots: both `hi`
/// and `lo` of every slot in the line reside in the same hardware cache line.
#[repr(C, align(64))]
struct Line {
    hi: [AtomicU16; SLOTS_48],
    _pad: [u8; 4],
    lo: [AtomicU32; SLOTS_48],
}

const _: () = assert!(std::mem::size_of::<Line>() == 64);

/// Quotiented compact slot array of `len = n + OVERFLOW` slots packed in
/// 64-byte cache-line `Line` blocks (`6.4 B/slot`).
struct Compact {
    buf: MappedBuf,
    lines: usize,
    len: usize,
    quot: Quotient,
    q_hi_bits: u32,
    q_hi_mask: u16,
    tag_base: u16,
    d_max_tag: u16,
    d_inline_max: usize,
    overflow: Box<Overflow>,
    #[cfg(test)]
    pause_active: AtomicBool,
    #[cfg(test)]
    pause_hook: std::sync::Mutex<Option<PauseHook>>,
}

impl Compact {
    fn tag_params(low_bits: u32) -> (u32, u16, u16, u16, usize) {
        let q_hi_bits = low_bits.saturating_sub(32);
        assert!(q_hi_bits <= 11, "compact tier requires low_bits <= 43 (got {low_bits})");
        let q_hi_mask = if q_hi_bits == 0 { 0 } else { ((1u32 << q_hi_bits) - 1) as u16 };
        let tag_base = PUBLISHED_BASE >> q_hi_bits;
        let d_max_tag = ((1u32 << (16 - q_hi_bits)) - 1) as u16;
        let d_inline_max = (d_max_tag - tag_base) as usize;
        (q_hi_bits, q_hi_mask, tag_base, d_max_tag, d_inline_max)
    }

    pub(super) fn d_inline_max_for(n: usize) -> usize {
        let quot = Quotient::new(n);
        Self::tag_params(quot.low_bits).4
    }

    fn new(n: usize, len: usize, mem: Arc<Gauge>, max_overflow_bytes: usize) -> Compact {
        let quot = Quotient::new(n);
        let (q_hi_bits, q_hi_mask, tag_base, d_max_tag, d_inline_max) = Self::tag_params(quot.low_bits);
        let lines = len.div_ceil(SLOTS_48);
        let bytes = lines.checked_mul(64).expect("fingerprint set too large");
        let buf = MappedBuf::zeroed(bytes, 64);
        Compact {
            buf,
            lines,
            len,
            quot,
            q_hi_bits,
            q_hi_mask,
            tag_base,
            d_max_tag,
            d_inline_max,
            overflow: Box::new(Overflow::new(mem, max_overflow_bytes)),
            #[cfg(test)]
            pause_active: AtomicBool::new(false),
            #[cfg(test)]
            pause_hook: std::sync::Mutex::new(None),
        }
    }

    #[inline(always)]
    fn line(&self, g: usize) -> &Line {
        debug_assert!(g < self.lines);
        // SAFETY: `buf` holds `self.lines` zero-initialized 64-byte `Line`
        // values aligned to 64 bytes, and callers keep `g < self.lines`.
        unsafe { &*self.buf.ptr.as_ptr().cast::<Line>().add(g) }
    }

    #[inline(always)]
    fn want_hi(&self, d: usize, q_hi: u16) -> u16 {
        let tag = if d < self.d_inline_max { self.tag_base + d as u16 } else { self.d_max_tag };
        (tag << self.q_hi_bits) | q_hi
    }

    /// Scan all 10 headers in `ln`, returning `(mask, values)` where bit `pos`
    /// is set for `pos >= k` whenever `hi[pos]` matches `want(pos)`, is empty,
    /// or is an in-flight claim (`< PUBLISHED_BASE`).
    #[inline(always)]
    fn line_mask(&self, ln: &Line, k: usize, want0: u16, step: u16) -> (u32, [u16; SLOTS_48]) {
        let mut vals = [0u16; SLOTS_48];
        let mut m = 0u32;
        for (pos, slot) in vals.iter_mut().enumerate() {
            let x = ln.hi[pos].load(Ordering::Relaxed);
            *slot = x;
            let want = want0.wrapping_add((pos as u16).wrapping_mul(step));
            m |= ((x == want) as u32 | (x < PUBLISHED_BASE) as u32) << pos;
        }
        (m & (u32::MAX << k), vals)
    }

    /// Wait-free O(1) helper for an in-flight claim (`1..=MAX_CLAIMS`): reads
    /// the claiming thread's published `(want_hi, want_lo)` from `CLAIMS`,
    /// verifies the claim is still active on `ln.hi[pos]`, writes `lo` and
    /// publishes `hi` without waiting for the claiming thread to resume.
    #[cold]
    #[inline(never)]
    fn help_claim(&self, ln: &Line, pos: usize) -> u16 {
        let cur = ln.hi[pos].load(Ordering::Acquire);
        if cur == EMPTY_HI || cur >= PUBLISHED_BASE {
            return cur;
        }
        // `cur` is `cid` in `1..=MAX_CLAIMS`. The Acquire load above pairs with
        // the writer's `CAS(0 -> cid, Release)` (after it wrote `CLAIMS[cid-1]`).
        // The Acquire load of `CLAIMS[cid-1]` below pairs with any subsequent
        // `Release` write by the same thread to `CLAIMS[cid-1]` (which only
        // occurs after `ln.hi[pos].store(want_hi, Release)`), so if `now == cur`
        // below, `p` is guaranteed to be this slot's exact payload.
        let p = CLAIMS[(cur - 1) as usize].0.load(Ordering::Acquire);
        let now = ln.hi[pos].load(Ordering::Acquire);
        if now != cur {
            return now;
        }
        let want_hi = (p >> 32) as u16;
        let want_lo = p as u32;
        ln.lo[pos].store(want_lo, Ordering::Relaxed);
        match ln.hi[pos].compare_exchange(cur, want_hi, Ordering::Release, Ordering::Acquire) {
            Ok(_) => want_hi,
            Err(actual) => actual,
        }
    }

    #[inline(always)]
    fn payload_matches<const INLINE: bool>(&self, ln: &Line, pos: usize, fp: u64, q_lo: u32) -> bool {
        if INLINE {
            ln.lo[pos].load(Ordering::Relaxed) == q_lo
        } else {
            self.overflow.get(ln.lo[pos].load(Ordering::Relaxed)) == fp
        }
    }

    /// Single lock-free slot resolver shared by inline (`INLINE = true`) and
    /// displacement-overflow (`INLINE = false`) probe paths.
    #[inline(always)]
    #[allow(clippy::too_many_arguments)] // private inlined helper specialized by const INLINE
    fn resolve_slot<const INLINE: bool>(
        &self,
        ln: &Line,
        pos: usize,
        mut cur: u16,
        want: u16,
        fp: u64,
        q_lo: u32,
        ovf_idx: &mut Option<u32>,
        before_claim: &mut impl FnMut() -> Result<Option<bool>, super::Full>,
    ) -> Result<Option<bool>, super::Full> {
        if cur != EMPTY_HI && cur < PUBLISHED_BASE {
            cur = self.help_claim(ln, pos);
        }
        if cur == want {
            fence(Ordering::Acquire);
            if self.payload_matches::<INLINE>(ln, pos, fp, q_lo) {
                return Ok(Some(false));
            }
            return Ok(None);
        }
        if cur != EMPTY_HI {
            return Ok(None);
        }
        if let Some(done) = before_claim()? {
            return Ok(Some(done));
        }
        let lo_val = if INLINE {
            q_lo
        } else if let Some(idx) = *ovf_idx {
            idx
        } else {
            let idx = self.overflow.try_push(fp)?;
            *ovf_idx = Some(idx);
            idx
        };
        let cid = this_claim_id();
        CLAIMS[(cid - 1) as usize].0.store(pack_claim(want, lo_val), Ordering::Release);
        match ln.hi[pos].compare_exchange(EMPTY_HI, cid, Ordering::Release, Ordering::Acquire) {
            Ok(_) => {
                #[cfg(test)]
                if self.pause_active.load(Ordering::Acquire) {
                    let hook = self.pause_hook.lock().expect("pause hook lock").take();
                    self.pause_active.store(false, Ordering::Release);
                    if let Some(h) = hook {
                        h();
                    }
                }
                ln.lo[pos].store(lo_val, Ordering::Relaxed);
                ln.hi[pos].store(want, Ordering::Release);
                Ok(Some(true))
            }
            Err(mut other) => {
                if other < PUBLISHED_BASE && other != EMPTY_HI {
                    other = self.help_claim(ln, pos);
                }
                if other == want && self.payload_matches::<INLINE>(ln, pos, fp, q_lo) {
                    return Ok(Some(false));
                }
                Ok(None)
            }
        }
    }

    /// Lock-free lookup/insert of normalized `fp`; calls `before_claim()` once
    /// at the first empty slot (hard-limit check and disk-tier lookup) before
    /// claiming a slot.
    #[inline(always)]
    fn insert_with(
        &self,
        fp: u64,
        probes: &mut u64,
        mut before_claim: impl FnMut() -> Result<Option<bool>, super::Full>,
    ) -> Result<bool, super::Full> {
        let (home, low) = self.quot.split(fp);
        let q_lo = low as u32;
        let q_hi = ((low >> 32) as u16) & self.q_hi_mask;
        let step = 1u16 << self.q_hi_bits;
        let mut g = home / SLOTS_48;
        let mut k = home % SLOTS_48;
        let mut base = g * SLOTS_48;
        let mut ovf_idx = None;

        // Fast check on the home slot itself (d = 0): resolves most inserts
        // and duplicate hits without scanning all 10 headers in the line.
        let ln0 = self.line(g);
        let cur0 = ln0.hi[k].load(Ordering::Relaxed);
        let want_d0 = PUBLISHED_BASE | q_hi;
        if cur0 == want_d0 || cur0 < PUBLISHED_BASE {
            if let Some(done) = self.resolve_slot::<true>(ln0, k, cur0, want_d0, fp, q_lo, &mut ovf_idx, &mut before_claim)? {
                return Ok(done);
            }
        }
        k += 1;
        *probes += 1;
        if k == SLOTS_48 {
            g += 1;
            base += SLOTS_48;
            k = 0;
        }
        if base + k >= self.len {
            return Err(super::Full);
        }

        loop {
            let ln = self.line(g);
            // Fast whole-line inline path when all slots in `ln` stay within
            // `d_inline_max` (always true on the first cache line because
            // `SLOTS_48 == 10 < 29 <= d_inline_max`).
            if base + SLOTS_48 - home <= self.d_inline_max {
                let want0 = q_hi | (self.tag_base.wrapping_add(base.wrapping_sub(home) as u16) << self.q_hi_bits);
                let (mut m, vals) = self.line_mask(ln, k, want0, step);
                while m != 0 {
                    let pos = m.trailing_zeros() as usize;
                    *probes += (pos - k) as u64;
                    if base + pos >= self.len {
                        return Err(super::Full);
                    }
                    let want = want0.wrapping_add((pos as u16).wrapping_mul(step));
                    if let Some(done) = self.resolve_slot::<true>(ln, pos, vals[pos], want, fp, q_lo, &mut ovf_idx, &mut before_claim)? {
                        return Ok(done);
                    }
                    k = pos + 1;
                    *probes += 1;
                    if base + k >= self.len {
                        return Err(super::Full);
                    }
                    m &= m - 1;
                }
                *probes += (SLOTS_48 - k) as u64;
                g += 1;
                base += SLOTS_48;
                k = 0;
                if base >= self.len {
                    return Err(super::Full);
                }
                continue;
            }

            let i = base + k;
            if i >= self.len {
                return Err(super::Full);
            }
            let d = i - home;
            let want = self.want_hi(d, q_hi);
            let cur = ln.hi[k].load(Ordering::Relaxed);
            let done = if d < self.d_inline_max {
                self.resolve_slot::<true>(ln, k, cur, want, fp, q_lo, &mut ovf_idx, &mut before_claim)?
            } else {
                self.resolve_slot::<false>(ln, k, cur, want, fp, q_lo, &mut ovf_idx, &mut before_claim)?
            };
            if let Some(res) = done {
                return Ok(res);
            }
            k += 1;
            *probes += 1;
            if k == SLOTS_48 {
                g += 1;
                base += SLOTS_48;
                k = 0;
            }
            if base + k >= self.len {
                return Err(super::Full);
            }
        }
    }

    #[inline(always)]
    fn contains(&self, fp: u64) -> bool {
        let (home, low) = self.quot.split(fp);
        let q_lo = low as u32;
        let q_hi = ((low >> 32) as u16) & self.q_hi_mask;
        let g = home / SLOTS_48;
        let k = home % SLOTS_48;
        let ln0 = self.line(g);
        let cur0 = ln0.hi[k].load(Ordering::Acquire);
        if cur0 == (PUBLISHED_BASE | q_hi) && ln0.lo[k].load(Ordering::Relaxed) == q_lo {
            return true;
        }
        if cur0 == EMPTY_HI {
            return false;
        }
        self.contains_probe(fp, home, low, g, k, cur0)
    }

    #[inline(never)]
    fn contains_probe(&self, fp: u64, home: usize, low: u64, mut g: usize, mut k: usize, cur0: u16) -> bool {
        let q_lo = low as u32;
        let q_hi = ((low >> 32) as u16) & self.q_hi_mask;
        let mut base = g * SLOTS_48;
        if cur0 < PUBLISHED_BASE {
            let ln0 = self.line(g);
            let cur = self.help_claim(ln0, k);
            if cur == EMPTY_HI {
                return false;
            }
            if cur == (PUBLISHED_BASE | q_hi) {
                fence(Ordering::Acquire);
                if ln0.lo[k].load(Ordering::Relaxed) == q_lo {
                    return true;
                }
            }
        }
        k += 1;
        if k == SLOTS_48 {
            g += 1;
            base += SLOTS_48;
            k = 0;
        }
        let step = 1u16 << self.q_hi_bits;

        while base + k < self.len {
            let ln = self.line(g);
            if base + SLOTS_48 - home <= self.d_inline_max {
                let want0 = q_hi | (self.tag_base.wrapping_add(base.wrapping_sub(home) as u16) << self.q_hi_bits);
                let (mut m, vals) = self.line_mask(ln, k, want0, step);
                while m != 0 {
                    let pos = m.trailing_zeros() as usize;
                    if base + pos >= self.len {
                        return false;
                    }
                    let want = want0.wrapping_add((pos as u16).wrapping_mul(step));
                    let mut cur = vals[pos];
                    if cur != EMPTY_HI && cur < PUBLISHED_BASE {
                        cur = self.help_claim(ln, pos);
                    }
                    if cur == EMPTY_HI {
                        return false;
                    }
                    if cur == want {
                        fence(Ordering::Acquire);
                        if ln.lo[pos].load(Ordering::Relaxed) == q_lo {
                            return true;
                        }
                    }
                    m &= m - 1;
                }
                g += 1;
                base += SLOTS_48;
                k = 0;
                continue;
            }
            let i = base + k;
            let d = i - home;
            let want = self.want_hi(d, q_hi);
            let mut cur = ln.hi[k].load(Ordering::Acquire);
            if cur != EMPTY_HI && cur < PUBLISHED_BASE {
                cur = self.help_claim(ln, k);
            }
            if cur == EMPTY_HI {
                return false;
            }
            if cur == want {
                let matched = if d < self.d_inline_max {
                    self.payload_matches::<true>(ln, k, fp, q_lo)
                } else {
                    self.payload_matches::<false>(ln, k, fp, q_lo)
                };
                if matched {
                    return true;
                }
            }
            k += 1;
            if k == SLOTS_48 {
                g += 1;
                base += SLOTS_48;
                k = 0;
            }
        }
        false
    }

    /// Insert distinct `fp` during parallel `grow_to` (exclusive set access:
    /// no concurrent readers).
    #[inline(always)]
    fn place(&self, fp: u64) {
        let (home, low) = self.quot.split(fp);
        let q_lo = low as u32;
        let q_hi = ((low >> 32) as u16) & self.q_hi_mask;
        let mut g = home / SLOTS_48;
        let mut k = home % SLOTS_48;
        let mut base = g * SLOTS_48;

        // Fast home-slot claim (`d = 0`): handles most rehashed entries without
        // scanning all 10 headers in `ln`.
        let ln0 = self.line(g);
        if ln0.hi[k].load(Ordering::Relaxed) == EMPTY_HI
            && ln0.hi[k].compare_exchange(EMPTY_HI, PLACE_CLAIM_HI, Ordering::Relaxed, Ordering::Relaxed).is_ok()
        {
            ln0.lo[k].store(q_lo, Ordering::Relaxed);
            ln0.hi[k].store(PUBLISHED_BASE | q_hi, Ordering::Relaxed);
            return;
        }
        k += 1;
        if k == SLOTS_48 {
            g += 1;
            base += SLOTS_48;
            k = 0;
        }

        while base + k < self.len {
            let ln = self.line(g);
            let mut m = 0u32;
            for pos in 0..SLOTS_48 {
                m |= ((ln.hi[pos].load(Ordering::Relaxed) == EMPTY_HI) as u32) << pos;
            }
            m &= u32::MAX << k;
            while m != 0 {
                let pos = m.trailing_zeros() as usize;
                let i = base + pos;
                if i >= self.len {
                    panic!("fingerprint set: the overflow area is full while growing");
                }
                if ln.hi[pos].compare_exchange(EMPTY_HI, PLACE_CLAIM_HI, Ordering::Relaxed, Ordering::Relaxed).is_ok() {
                    let d = i - home;
                    let lo_val = if d < self.d_inline_max {
                        q_lo
                    } else {
                        self.overflow.try_push(fp).expect("fingerprint set: overflow table full while growing")
                    };
                    ln.lo[pos].store(lo_val, Ordering::Relaxed);
                    ln.hi[pos].store(self.want_hi(d, q_hi), Ordering::Relaxed);
                    return;
                }
                m &= m - 1;
            }
            g += 1;
            base += SLOTS_48;
            k = 0;
        }
        panic!("fingerprint set: the overflow area is full while growing");
    }

    #[inline]
    fn decode_exclusive(&self, i: usize) -> Option<u64> {
        let ln = self.line(i / SLOTS_48);
        let pos = i % SLOTS_48;
        let h = ln.hi[pos].load(Ordering::Relaxed);
        if h == EMPTY_HI {
            return None;
        }
        debug_assert!(h >= PUBLISHED_BASE);
        let lo = ln.lo[pos].load(Ordering::Relaxed);
        let tag = h >> self.q_hi_bits;
        if tag == self.d_max_tag {
            Some(self.overflow.get(lo))
        } else {
            let d = (tag - self.tag_base) as usize;
            let low = (((h & self.q_hi_mask) as u64) << 32) | (lo as u64);
            Some(self.quot.reconstruct(i - d, low))
        }
    }

    #[inline]
    fn is_occupied_exclusive(&self, i: usize) -> bool {
        self.line(i / SLOTS_48).hi[i % SLOTS_48].load(Ordering::Relaxed) != EMPTY_HI
    }

    fn rehash_range(&self, lo: usize, hi: usize, dst: &Table) {
        let end = hi.min(self.len);
        if lo >= end {
            return;
        }
        let mut cursor = BaseCursor::new(self.quot, lo);
        let mut g = lo / SLOTS_48;
        let mut start_pos = lo % SLOTS_48;
        let mut base = g * SLOTS_48;
        while base < end {
            let ln = self.line(g);
            let stop_pos = SLOTS_48.min(end - base);
            for pos in start_pos..stop_pos {
                let h = ln.hi[pos].load(Ordering::Relaxed);
                if h == EMPTY_HI {
                    continue;
                }
                debug_assert!(h >= PUBLISHED_BASE);
                let lo_val = ln.lo[pos].load(Ordering::Relaxed);
                let tag = h >> self.q_hi_bits;
                let fp = if tag == self.d_max_tag {
                    self.overflow.get(lo_val)
                } else {
                    let d = (tag - self.tag_base) as usize;
                    let low = (((h & self.q_hi_mask) as u64) << 32) | (lo_val as u64);
                    cursor.reconstruct(base + pos - d, low)
                };
                dst.place(fp);
            }
            g += 1;
            base += SLOTS_48;
            start_pos = 0;
        }
    }

    fn count_cluster_excess(&self, d_max: usize) -> usize {
        let mut excess = 0usize;
        let mut run = 0usize;
        let mut base = 0usize;
        for g in 0..self.lines {
            let ln = self.line(g);
            let limit = SLOTS_48.min(self.len - base);
            for pos in 0..limit {
                if ln.hi[pos].load(Ordering::Relaxed) != EMPTY_HI {
                    run += 1;
                } else {
                    excess += run.saturating_sub(d_max);
                    run = 0;
                }
            }
            base += SLOTS_48;
        }
        excess + run.saturating_sub(d_max)
    }

    /// # Safety
    /// No thread accesses slots `lo..hi` concurrently or afterwards, and `lo`
    /// (and `hi`, unless `hi >= self.len`) is a multiple of `SLOTS_48`.
    unsafe fn discard_slot_range(&self, lo: usize, hi: usize) {
        debug_assert_eq!(lo % SLOTS_48, 0);
        let byte_lo = (lo / SLOTS_48) * 64;
        let byte_hi = if hi >= self.len {
            self.buf.layout.size()
        } else {
            debug_assert_eq!(hi % SLOTS_48, 0);
            (hi / SLOTS_48) * 64
        };
        // SAFETY: caller guarantees exclusive deadness of `lo..hi`.
        unsafe { self.buf.discard_bytes(byte_lo, byte_hi) };
    }
}

/// Raw 64-bit `AtomicU64` slot array for tables with `< 2^21` home slots.
struct Raw64 {
    buf: MappedBuf,
    len: usize,
    n: usize,
}

impl Raw64 {
    fn new(n: usize, len: usize) -> Raw64 {
        let bytes = len.checked_mul(8).expect("fingerprint set too large");
        Raw64 { buf: MappedBuf::zeroed(bytes, 8), len, n }
    }

    #[inline(always)]
    fn home(&self, fp: u64) -> usize {
        ((fp as u128 * self.n as u128) >> 64) as usize
    }

    #[inline(always)]
    fn slot(&self, i: usize) -> &AtomicU64 {
        debug_assert!(i < self.len);
        // SAFETY: `buf` holds `self.len` zero-initialized `AtomicU64`s aligned
        // to 8 bytes, and callers keep `i < self.len`.
        unsafe { &*self.buf.ptr.as_ptr().cast::<AtomicU64>().add(i) }
    }

    #[inline(always)]
    fn insert_with(
        &self,
        fp: u64,
        probes: &mut u64,
        mut before_claim: impl FnMut() -> Result<Option<bool>, super::Full>,
    ) -> Result<bool, super::Full> {
        let end = self.len;
        let mut i = self.home(fp);
        loop {
            let g = i & !(RAW_GROUP - 1);
            if g + RAW_GROUP <= end {
                let mut m = 0u32;
                for k in 0..RAW_GROUP {
                    let x = self.slot(g + k).load(Ordering::Relaxed);
                    m |= ((x == fp) as u32 | (x == 0) as u32) << k;
                }
                m &= u32::MAX << (i - g);
                if m == 0 {
                    *probes += (g + RAW_GROUP - i) as u64;
                    i = g + RAW_GROUP;
                    if i >= end {
                        return Err(super::Full);
                    }
                    continue;
                }
                let j = g + m.trailing_zeros() as usize;
                *probes += (j - i) as u64;
                i = j;
            }
            let cur = self.slot(i).load(Ordering::Relaxed);
            if cur == fp {
                return Ok(false);
            }
            if cur == 0 {
                if let Some(done) = before_claim()? {
                    return Ok(done);
                }
                match self.slot(i).compare_exchange(0, fp, Ordering::AcqRel, Ordering::Acquire) {
                    Ok(_) => return Ok(true),
                    Err(other) if other == fp => return Ok(false),
                    Err(_) => {}
                }
            }
            i += 1;
            *probes += 1;
            if i == end {
                return Err(super::Full);
            }
        }
    }

    #[inline(always)]
    fn contains(&self, fp: u64) -> bool {
        (self.home(fp)..self.len).map(|i| self.slot(i).load(Ordering::Acquire)).take_while(|&c| c != 0).any(|c| c == fp)
    }

    fn place(&self, fp: u64) {
        let mut i = self.home(fp);
        while i < self.len {
            if self.slot(i).compare_exchange(0, fp, Ordering::Relaxed, Ordering::Relaxed).is_ok() {
                return;
            }
            i += 1;
        }
        panic!("fingerprint set: the overflow area is full while growing");
    }

    fn rehash_range(&self, lo: usize, hi: usize, dst: &Table) {
        for i in lo..hi.min(self.len) {
            let fp = self.slot(i).load(Ordering::Relaxed);
            if fp != 0 {
                dst.place(fp);
            }
        }
    }

    fn count_cluster_excess(&self, d_max: usize) -> usize {
        let mut excess = 0usize;
        let mut run = 0usize;
        for i in 0..self.len {
            if self.slot(i).load(Ordering::Relaxed) != 0 {
                run += 1;
            } else {
                excess += run.saturating_sub(d_max);
                run = 0;
            }
        }
        excess + run.saturating_sub(d_max)
    }

    /// # Safety
    /// No thread accesses slots `lo..hi` concurrently or afterwards.
    unsafe fn discard_slot_range(&self, lo: usize, hi: usize) {
        let byte_lo = lo * 8;
        let byte_hi = hi.min(self.len) * 8;
        // SAFETY: caller guarantees exclusive deadness of `lo..hi`.
        unsafe { self.buf.discard_bytes(byte_lo, byte_hi) };
    }
}

enum Storage {
    Raw64(Raw64),
    Compact48(Compact),
}

/// A fingerprint table: `n` home slots plus `OVERFLOW` probe slots.
pub(super) struct Table {
    storage: Storage,
    pub(super) n: usize,
    len: usize,
    pub(super) high: usize,
    pub(super) hard: usize,
    pub(super) base: usize,
    pub(super) high_at: usize,
    pub(super) hard_at: usize,
    pub(super) direct_at: usize,
    pub(super) drained: AtomicBool,
    pub(super) high_reached: AtomicBool,
}

impl Table {
    pub(super) fn new(n: usize, base: usize, mem: Arc<Gauge>, max_overflow_bytes: usize) -> Table {
        let len = n.checked_add(OVERFLOW).expect("fingerprint set too large");
        let storage = if n >= COMPACT48_MIN_SLOTS {
            Storage::Compact48(Compact::new(n, len, mem, max_overflow_bytes))
        } else {
            Storage::Raw64(Raw64::new(n, len))
        };
        let high = Table::high_of(n);
        let hard = n / HARD_DEN * HARD_NUM + (n % HARD_DEN * HARD_NUM).div_ceil(HARD_DEN);
        let high_at = base + high;
        Table {
            storage,
            n,
            len,
            high,
            hard,
            base,
            high_at,
            hard_at: base + hard,
            direct_at: high_at.saturating_sub(SLACK),
            drained: AtomicBool::new(false),
            high_reached: AtomicBool::new(false),
        }
    }

    pub(super) fn high_of(n: usize) -> usize {
        n / HIGH_DEN * HIGH_NUM + n % HIGH_DEN * HIGH_NUM / HIGH_DEN
    }

    /// Bytes of the slot array for `slots` home slots (excluding any rare
    /// overflow segment allocation).
    pub(super) fn array_bytes(slots: usize) -> usize {
        let len = slots.saturating_add(OVERFLOW);
        if slots >= COMPACT48_MIN_SLOTS {
            len.div_ceil(SLOTS_48).saturating_mul(64)
        } else {
            len.saturating_mul(8)
        }
    }

    /// Bytes of `slots` home slots without the fixed `OVERFLOW` tail.
    pub(super) fn home_bytes(slots: usize) -> usize {
        if slots >= COMPACT48_MIN_SLOTS {
            slots.div_ceil(SLOTS_48).saturating_mul(64)
        } else {
            slots.saturating_mul(8)
        }
    }

    /// Fixed probe-tail bytes added on top of home slots for `slots`.
    pub(super) fn probe_tail_bytes(slots: usize) -> usize {
        Self::array_bytes(slots).saturating_sub(Self::home_bytes(slots))
    }

    /// Most home slots whose `home_bytes(slots)` fits in `bytes`.
    pub(super) fn home_slots_for_bytes(bytes: usize) -> usize {
        if bytes >= Self::home_bytes(COMPACT48_MIN_SLOTS) {
            (bytes / 64).saturating_mul(SLOTS_48)
        } else {
            bytes / 8
        }
    }

    /// Most home slots whose `array_bytes(slots)` fits in `bytes`.
    pub(super) fn slots_for_bytes(bytes: usize) -> usize {
        if bytes >= Self::array_bytes(COMPACT48_MIN_SLOTS) {
            (bytes / 64).saturating_mul(SLOTS_48).saturating_sub(OVERFLOW)
        } else {
            (bytes / 8).saturating_sub(OVERFLOW)
        }
    }

    #[inline]
    pub(super) fn slot_len(&self) -> usize {
        self.len
    }

    #[cfg(test)]
    #[inline]
    pub(super) fn home(&self, fp: u64) -> usize {
        ((fp as u128 * self.n as u128) >> 64) as usize
    }

    fn buf(&self) -> &MappedBuf {
        match &self.storage {
            Storage::Raw64(t) => &t.buf,
            Storage::Compact48(t) => &t.buf,
        }
    }

    /// Bytes of the slot array alone (excluding `Overflow`, which charges the
    /// set's gauge directly).
    pub(super) fn array_bytes_now(&self) -> usize {
        self.buf().layout.size()
    }

    pub(super) fn bytes(&self) -> usize {
        self.array_bytes_now() + self.overflow_bytes()
    }

    pub(super) fn overflow_bytes(&self) -> usize {
        match &self.storage {
            Storage::Raw64(_) => 0,
            Storage::Compact48(t) => t.overflow.bytes(),
        }
    }

    pub(super) fn is_mapped(&self) -> bool {
        self.buf().mapped
    }

    /// Smallest slot quantum aligned to both cache-line blocks and OS pages.
    fn page_align_slots(&self) -> usize {
        let page = page_size().max(64);
        match &self.storage {
            Storage::Raw64(_) => page / 8,
            Storage::Compact48(_) => (page / 64) * SLOTS_48,
        }
    }

    /// Maximum slot granularity of one `REHASH_CHUNK_BYTES` (`2 MiB`) chunk.
    pub(super) fn rehash_chunk_slots(&self) -> usize {
        let bytes = REHASH_CHUNK_BYTES.max(page_size());
        match &self.storage {
            Storage::Raw64(_) => bytes / 8,
            Storage::Compact48(_) => (bytes / 64) * SLOTS_48,
        }
    }

    /// Page- and line-aligned slot granularity of one rehash work unit,
    /// honoring `-fpbits` (`shards`) down to a single OS page while capping
    /// each unit at `rehash_chunk_slots()` (`2 MiB`).
    pub(super) fn rehash_unit_slots(&self, shards: usize) -> usize {
        let align = self.page_align_slots();
        let max_unit = self.rehash_chunk_slots();
        let shard_slots = self.len.div_ceil(shards.max(1));
        shard_slots.next_multiple_of(align).clamp(align, max_unit)
    }

    /// Byte size of `unit_slots` slots in this table.
    pub(super) fn unit_bytes(&self, unit_slots: usize) -> usize {
        match &self.storage {
            Storage::Raw64(_) => unit_slots.saturating_mul(8),
            Storage::Compact48(_) => unit_slots.div_ceil(SLOTS_48).saturating_mul(64),
        }
    }

    /// Sound upper bound on destination `Overflow` bytes when rehashing this
    /// table (`entries` occupied entries) into `dst_slots > self.n` home slots.
    ///
    /// Because `fastrange` is monotonic and `dst_slots > self.n`, separate
    /// probe clusters in `self` cannot merge in the destination, so each
    /// cluster of length `L` can contribute at most `L.saturating_sub(d_max)`
    /// overflow entries. Interior probe clusters can exceed `OVERFLOW`, so the
    /// only valid zero fast path is `entries <= d_max`.
    pub(super) fn max_grow_overflow_bytes(&self, dst_slots: usize, entries: usize) -> usize {
        if dst_slots < COMPACT48_MIN_SLOTS || dst_slots <= self.n {
            return 0;
        }
        let d_max = Compact::d_inline_max_for(dst_slots);
        if entries <= d_max {
            return 0;
        }
        let excess = match &self.storage {
            Storage::Raw64(t) => t.count_cluster_excess(d_max),
            Storage::Compact48(t) => t.count_cluster_excess(d_max),
        };
        Overflow::bytes_for_entries(excess)
    }

    #[inline(always)]
    pub(super) fn insert_with(
        &self,
        fp: u64,
        probes: &mut u64,
        before_claim: impl FnMut() -> Result<Option<bool>, super::Full>,
    ) -> Result<bool, super::Full> {
        match &self.storage {
            Storage::Raw64(t) => t.insert_with(fp, probes, before_claim),
            Storage::Compact48(t) => t.insert_with(fp, probes, before_claim),
        }
    }

    #[inline(always)]
    pub(super) fn contains(&self, fp: u64) -> bool {
        match &self.storage {
            Storage::Raw64(t) => t.contains(fp),
            Storage::Compact48(t) => t.contains(fp),
        }
    }

    #[inline(always)]
    pub(super) fn place(&self, fp: u64) {
        match &self.storage {
            Storage::Raw64(t) => t.place(fp),
            Storage::Compact48(t) => t.place(fp),
        }
    }

    #[inline]
    fn decode_exclusive(&self, i: usize) -> Option<u64> {
        match &self.storage {
            Storage::Raw64(t) => {
                let x = t.slot(i).load(Ordering::Relaxed);
                (x != 0).then_some(x)
            }
            Storage::Compact48(t) => t.decode_exclusive(i),
        }
    }

    #[inline]
    fn is_occupied_exclusive(&self, i: usize) -> bool {
        match &self.storage {
            Storage::Raw64(t) => t.slot(i).load(Ordering::Relaxed) != 0,
            Storage::Compact48(t) => t.is_occupied_exclusive(i),
        }
    }

    /// Read-only sorted emission of all probe clusters starting in `lo..hi`:
    /// decodes each cluster into a reusable scratch `Vec<u64>`, sorts it, and
    /// yields its fingerprints in ascending order without mutating the table.
    pub(super) fn sorted_clusters(&self, lo: usize, hi: usize, mut f: impl FnMut(u64) -> Result<(), IoError>) -> Result<(), IoError> {
        let end = self.len;
        let mut i = lo;
        if i > 0 && self.is_occupied_exclusive(i - 1) {
            while i < end && self.is_occupied_exclusive(i) {
                i += 1;
            }
        }
        let mut cluster: Vec<u64> = Vec::new();
        while i < hi.min(end) {
            let Some(first) = self.decode_exclusive(i) else {
                i += 1;
                continue;
            };
            cluster.clear();
            cluster.push(first);
            i += 1;
            while i < end {
                let Some(fp) = self.decode_exclusive(i) else { break };
                cluster.push(fp);
                i += 1;
            }
            cluster.sort_unstable();
            for &fp in &cluster {
                f(fp)?;
            }
        }
        Ok(())
    }

    pub(super) fn rehash_range(&self, lo: usize, hi: usize, dst: &Table) {
        match &self.storage {
            Storage::Raw64(t) => t.rehash_range(lo, hi, dst),
            Storage::Compact48(t) => t.rehash_range(lo, hi, dst),
        }
    }

    /// Release physical pages of completed rehash unit `lo..hi`.
    ///
    /// # Safety
    /// No thread reads or writes slots `lo..hi` concurrently or afterwards,
    /// and `lo` / `hi` (unless `hi >= slot_len()`) are aligned to
    /// `rehash_unit_slots()`.
    pub(super) unsafe fn discard_slot_range(&self, lo: usize, hi: usize) {
        // SAFETY: caller upholds exclusive deadness and alignment of `lo..hi`.
        unsafe {
            match &self.storage {
                Storage::Raw64(t) => t.discard_slot_range(lo, hi),
                Storage::Compact48(t) => t.discard_slot_range(lo, hi),
            }
        }
    }

    #[cfg(test)]
    pub(super) fn set_pause_after_claim(&self, hook: impl Fn() + Send + Sync + 'static) {
        if let Storage::Compact48(t) = &self.storage {
            *t.pause_hook.lock().expect("pause hook lock") = Some(Box::new(hook));
            t.pause_active.store(true, Ordering::Release);
        } else {
            panic!("set_pause_after_claim requires Compact48");
        }
    }

    #[cfg(test)]
    pub(super) fn is_occupied(&self, i: usize) -> bool {
        self.is_occupied_exclusive(i)
    }

    #[cfg(test)]
    pub(super) fn entries_vec(&self) -> Vec<u64> {
        (0..self.len).filter_map(|i| self.decode_exclusive(i)).collect()
    }

    #[cfg(test)]
    pub(super) fn fault_pages(&self) {
        let buf = self.buf();
        for off in (0..buf.layout.size()).step_by(4096) {
            // SAFETY: `off < layout.size()` inside an exclusively owned zeroed table buffer.
            unsafe { std::ptr::write_volatile(buf.ptr.as_ptr().add(off), 0) };
        }
    }

    #[cfg(all(test, target_os = "linux"))]
    pub(super) fn overflow_fixed_resident_bytes(&self) -> usize {
        match &self.storage {
            Storage::Raw64(_) => 0,
            Storage::Compact48(t) => t.overflow.fixed_resident_bytes(),
        }
    }

    #[cfg(all(test, target_os = "linux"))]
    pub(super) fn resident_bytes(&self) -> usize {
        let buf = self.buf();
        if !buf.mapped {
            return buf.layout.size();
        }
        let page = page_size();
        let len = buf.layout.size() & !(page - 1);
        if len == 0 {
            return 0;
        }
        let pages = len / page;
        let mut vec = vec![0u8; pages];
        // SAFETY: `buf.mapped` is a page-aligned `mmap` of at least `len`
        // page-aligned bytes, and `vec` holds `pages = len / page` bytes.
        let rc = unsafe { libc::mincore(buf.ptr.as_ptr().cast(), len, vec.as_mut_ptr()) };
        assert_eq!(rc, 0, "mincore failed");
        vec.iter().filter(|&&b| b & 1 != 0).count() * page + self.overflow_bytes()
    }
}
