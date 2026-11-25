//! Lock-free displacement-overflow storage for compact fingerprint tables.
//!
//! Entries whose linear-probe displacement reaches `d_inline_max` store their
//! exact 64-bit fingerprint here and keep the 32-bit index in the slot's `lo`
//! word. All allocations are demand-zero and charged directly to the owning
//! `FpSet`'s `Gauge`:
//!
//! - Fixed-cap tables (`max_bytes < usize::MAX`, `-fpmem`): reserve a single
//!   demand-zero mapping of `max_bytes` bytes up front and bound pushes by an
//!   atomic index check (`idx < cap`), charging the gauge in `CHARGE_STEP`
//!   increments as slots are claimed. Racing writers never allocate candidate
//!   buffers.
//! - Growing tables (`max_bytes == usize::MAX`): grow geometrically in
//!   segments (`8 KiB, 8 KiB, 16 KiB, ...`) backed by demand-zero anonymous
//!   `mmap` so losing CAS contenders unmap without touching or materializing
//!   any physical pages.

use std::alloc::{alloc_zeroed, dealloc, handle_alloc_error, Layout};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicU64, AtomicUsize, Ordering};
use std::sync::Arc;

use crate::mem::Gauge;

/// First segment size (`1024` `u64`s = `8 KiB`) and segment count (`4G`
/// capacity) of the segmented overflow store.
const OVF_FIRST_SHIFT: u32 = 10;
const OVF_SEGS: usize = 23;

/// Gauge accounting step (`8 KiB`) for fixed-cap demand-zero overflow storage.
const CHARGE_STEP: usize = 8 << 10;

pub(super) fn page_size() -> usize {
    #[cfg(unix)]
    {
        static PAGE: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
        *PAGE.get_or_init(|| {
            // SAFETY: `sysconf(_SC_PAGESIZE)` has no preconditions.
            let p = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
            if p > 0 && (p as usize).is_power_of_two() {
                p as usize
            } else {
                4096
            }
        })
    }
    #[cfg(not(unix))]
    {
        4096
    }
}

/// Reserve a zero-initialized buffer of at least `byte_len` bytes, preferring
/// demand-zero anonymous `mmap` on Unix so untouched pages stay non-resident.
/// Returns `(ptr, alloc_len, is_mapped)`.
fn alloc_demand_zero(byte_len: usize) -> (NonNull<AtomicU64>, usize, bool) {
    assert!(byte_len > 0 && byte_len.is_multiple_of(8));
    #[cfg(unix)]
    {
        let map_len = byte_len.next_multiple_of(page_size());
        // SAFETY: requests a fresh private anonymous mapping of `map_len`
        // page-aligned bytes at an OS-chosen page-aligned address (`>= 8`),
        // touching no existing mapping; kernel guarantees zero-filled pages.
        let p = unsafe {
            libc::mmap(std::ptr::null_mut(), map_len, libc::PROT_READ | libc::PROT_WRITE, libc::MAP_PRIVATE | libc::MAP_ANON, -1, 0)
        };
        if p != libc::MAP_FAILED {
            return (NonNull::new(p.cast::<AtomicU64>()).expect("mapped non-null"), map_len, true);
        }
    }
    let layout = Layout::from_size_align(byte_len, 8).expect("overflow segment too large");
    // SAFETY: `byte_len > 0` and alignment 8 is a valid power of two.
    let raw = unsafe { alloc_zeroed(layout) };
    let Some(ptr) = NonNull::new(raw.cast::<AtomicU64>()) else { handle_alloc_error(layout) };
    (ptr, byte_len, false)
}

/// Release a buffer returned by `alloc_demand_zero`.
///
/// # Safety
/// `ptr`, `alloc_len`, and `mapped` must match a live allocation from
/// `alloc_demand_zero`, and no thread may access the memory afterwards.
unsafe fn free_demand_zero(ptr: NonNull<AtomicU64>, alloc_len: usize, mapped: bool) {
    if mapped {
        #[cfg(unix)]
        // SAFETY: caller guarantees `ptr` and `alloc_len` came from `mmap` in
        // `alloc_demand_zero` and are no longer accessed.
        unsafe {
            libc::munmap(ptr.as_ptr().cast(), alloc_len);
        }
    } else {
        let layout = Layout::from_size_align(alloc_len, 8).expect("valid overflow layout");
        // SAFETY: caller guarantees `ptr` came from `alloc_zeroed(layout)` and
        // is no longer accessed.
        unsafe {
            dealloc(ptr.as_ptr().cast(), layout);
        }
    }
}

enum Backing {
    Fixed { ptr: NonNull<AtomicU64>, cap: usize, alloc_len: usize, mapped: bool, charged_bytes: AtomicUsize },
    Segmented { alloc_bytes: AtomicUsize, segs: [AtomicPtr<AtomicU64>; OVF_SEGS], seg_mapped: [AtomicBool; OVF_SEGS] },
}

/// Lock-free append-only store of full 64-bit overflow fingerprints.
pub(super) struct Overflow {
    len: AtomicUsize,
    mem: Arc<Gauge>,
    backing: Backing,
}

// SAFETY: `Overflow` uniquely owns its demand-zero backing memory and exposes
// shared access only through `AtomicU64` elements published via synchronization.
unsafe impl Send for Overflow {}
// SAFETY: Shared references only access atomic metadata and `AtomicU64` slots.
unsafe impl Sync for Overflow {}

impl Overflow {
    pub(super) fn new(mem: Arc<Gauge>, max_bytes: usize) -> Overflow {
        let backing = if max_bytes < usize::MAX {
            let cap = (max_bytes / 8).min(u32::MAX as usize);
            if cap == 0 {
                Backing::Fixed { ptr: NonNull::dangling(), cap: 0, alloc_len: 0, mapped: false, charged_bytes: AtomicUsize::new(0) }
            } else {
                let (ptr, alloc_len, mapped) = alloc_demand_zero(cap * 8);
                Backing::Fixed { ptr, cap, alloc_len, mapped, charged_bytes: AtomicUsize::new(0) }
            }
        } else {
            Backing::Segmented {
                alloc_bytes: AtomicUsize::new(0),
                segs: std::array::from_fn(|_| AtomicPtr::new(std::ptr::null_mut())),
                seg_mapped: std::array::from_fn(|_| AtomicBool::new(false)),
            }
        };
        Overflow { len: AtomicUsize::new(0), mem, backing }
    }

    #[inline]
    fn seg_len(s: usize) -> usize {
        1usize << (OVF_FIRST_SHIFT as usize + s.saturating_sub(1))
    }

    #[inline]
    fn seg_bytes(s: usize) -> usize {
        Self::seg_len(s) * 8
    }

    /// Cumulative bytes allocated in segmented mode once segments `0..=s` exist.
    #[inline]
    fn total_bytes_through(s: usize) -> usize {
        (1usize << (OVF_FIRST_SHIFT as usize + s)).saturating_mul(8)
    }

    /// Upper-bound bytes required to hold `entries` overflow fingerprints in a
    /// growing (segmented) table.
    pub(super) fn bytes_for_entries(entries: usize) -> usize {
        if entries == 0 {
            return 0;
        }
        let (s, _) = Self::locate((entries - 1).min(u32::MAX as usize) as u32);
        Self::total_bytes_through(s)
    }

    #[inline]
    fn locate(idx: u32) -> (usize, usize) {
        let top = idx >> OVF_FIRST_SHIFT;
        if top == 0 {
            (0, idx as usize)
        } else {
            let s = (32 - top.leading_zeros()) as usize;
            let base = 1usize << (OVF_FIRST_SHIFT as usize + s - 1);
            (s, idx as usize - base)
        }
    }

    #[cold]
    #[inline(never)]
    fn ensure_seg(
        &self,
        s: usize,
        alloc_bytes: &AtomicUsize,
        segs: &[AtomicPtr<AtomicU64>; OVF_SEGS],
        seg_mapped: &[AtomicBool; OVF_SEGS],
    ) -> *mut AtomicU64 {
        let p = segs[s].load(Ordering::Acquire);
        if !p.is_null() {
            return p;
        }
        let seg_bytes = Self::seg_bytes(s);
        let (ptr, alloc_len, mapped) = alloc_demand_zero(seg_bytes);
        let raw = ptr.as_ptr();
        match segs[s].compare_exchange(std::ptr::null_mut(), raw, Ordering::AcqRel, Ordering::Acquire) {
            Ok(_) => {
                seg_mapped[s].store(mapped, Ordering::Relaxed);
                alloc_bytes.fetch_add(seg_bytes, Ordering::Relaxed);
                self.mem.add(seg_bytes);
                raw
            }
            Err(existing) => {
                // SAFETY: `ptr` was just allocated by `alloc_demand_zero` and
                // was never published (nor touched), so freeing it is exclusive.
                unsafe { free_demand_zero(ptr, alloc_len, mapped) };
                existing
            }
        }
    }

    #[cold]
    #[inline(never)]
    pub(super) fn try_push(&self, fp: u64) -> Result<u32, super::Full> {
        match &self.backing {
            Backing::Fixed { ptr, cap, charged_bytes, .. } => {
                let mut idx = self.len.load(Ordering::Relaxed);
                loop {
                    if idx >= *cap {
                        return Err(super::Full);
                    }
                    match self.len.compare_exchange_weak(idx, idx + 1, Ordering::Relaxed, Ordering::Relaxed) {
                        Ok(_) => break,
                        Err(v) => idx = v,
                    }
                }
                let need = ((idx + 1) * 8).next_multiple_of(CHARGE_STEP).min(*cap * 8);
                let mut cur = charged_bytes.load(Ordering::Relaxed);
                while cur < need {
                    match charged_bytes.compare_exchange_weak(cur, need, Ordering::Relaxed, Ordering::Relaxed) {
                        Ok(_) => {
                            self.mem.add(need - cur);
                            break;
                        }
                        Err(v) => cur = v,
                    }
                }
                // SAFETY: `idx < *cap`, and `ptr` backs `*cap` zero-initialized
                // `AtomicU64` entries for the lifetime of `self`.
                unsafe {
                    (*ptr.as_ptr().add(idx)).store(fp, Ordering::Release);
                }
                Ok(idx as u32)
            }
            Backing::Segmented { alloc_bytes, segs, seg_mapped } => {
                let idx = self.len.fetch_add(1, Ordering::Relaxed);
                if idx >= u32::MAX as usize {
                    return Err(super::Full);
                }
                let (s, off) = Self::locate(idx as u32);
                let base = self.ensure_seg(s, alloc_bytes, segs, seg_mapped);
                // SAFETY: `base` points to a live segment of `seg_len(s)`
                // `AtomicU64`s, and `off < seg_len(s)`.
                unsafe {
                    (*base.add(off)).store(fp, Ordering::Release);
                }
                Ok(idx as u32)
            }
        }
    }

    #[cold]
    #[inline(never)]
    pub(super) fn get(&self, idx: u32) -> u64 {
        match &self.backing {
            Backing::Fixed { ptr, cap, .. } => {
                let i = idx as usize;
                debug_assert!(i < *cap);
                // SAFETY: `idx` was returned by `try_push` (`i < *cap`) and
                // stored with `Release` before the slot header published `idx`.
                unsafe { (*ptr.as_ptr().add(i)).load(Ordering::Acquire) }
            }
            Backing::Segmented { segs, .. } => {
                let (s, off) = Self::locate(idx);
                let base = segs[s].load(Ordering::Acquire);
                debug_assert!(!base.is_null());
                // SAFETY: `idx` was returned by `try_push`, which initialized
                // segment `s` (`Acquire` pairs with `ensure_seg`'s `AcqRel`)
                // and wrote `off < seg_len(s)` before slot publication.
                unsafe { (*base.add(off)).load(Ordering::Acquire) }
            }
        }
    }

    pub(super) fn bytes(&self) -> usize {
        match &self.backing {
            Backing::Fixed { charged_bytes, .. } => charged_bytes.load(Ordering::Relaxed),
            Backing::Segmented { alloc_bytes, .. } => alloc_bytes.load(Ordering::Relaxed),
        }
    }

    #[cfg(all(test, target_os = "linux"))]
    pub(super) fn fixed_resident_bytes(&self) -> usize {
        let Backing::Fixed { ptr, alloc_len, mapped, .. } = &self.backing else {
            return self.bytes();
        };
        if !*mapped || *alloc_len == 0 {
            return *alloc_len;
        }
        let page = page_size();
        let len = *alloc_len & !(page - 1);
        let pages = len / page;
        let mut vec = vec![0u8; pages];
        // SAFETY: `ptr` is a page-aligned `mmap` of `len` bytes and `vec` has
        // `pages = len / page` elements.
        let rc = unsafe { libc::mincore(ptr.as_ptr().cast(), len, vec.as_mut_ptr()) };
        assert_eq!(rc, 0, "mincore failed on fixed overflow");
        vec.iter().filter(|&&b| b & 1 != 0).count() * page
    }
}

impl Drop for Overflow {
    fn drop(&mut self) {
        match &mut self.backing {
            Backing::Fixed { ptr, alloc_len, mapped, charged_bytes, .. } => {
                let charged = *charged_bytes.get_mut();
                if charged > 0 {
                    self.mem.sub(charged);
                }
                if *alloc_len > 0 {
                    // SAFETY: `&mut self` guarantees exclusive drop of the
                    // allocation from `alloc_demand_zero`.
                    unsafe { free_demand_zero(*ptr, *alloc_len, *mapped) };
                }
            }
            Backing::Segmented { alloc_bytes, segs, seg_mapped } => {
                let bytes = *alloc_bytes.get_mut();
                if bytes > 0 {
                    self.mem.sub(bytes);
                }
                for s in 0..OVF_SEGS {
                    let p = *segs[s].get_mut();
                    if let Some(ptr) = NonNull::new(p) {
                        let mapped = *seg_mapped[s].get_mut();
                        let seg_bytes = Self::seg_bytes(s);
                        let alloc_len = if mapped { seg_bytes.next_multiple_of(page_size()) } else { seg_bytes };
                        // SAFETY: `&mut self` guarantees exclusive drop of the
                        // published segment from `alloc_demand_zero`.
                        unsafe { free_demand_zero(ptr, alloc_len, mapped) };
                    }
                }
            }
        }
    }
}
