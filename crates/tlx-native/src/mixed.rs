//! Mixed mode, host side (docs/mixed-mode.md §2–6): generated code
//! calls `host->eval` for the boxed *regions* it cannot compile, and passes
//! boxed values around as opaque handles.
//!
//! - [`Regions`] is the host's region table for one generated library (rid
//!   -> signature and evaluator). tlx-native only moves values across the
//!   ABI; what a region means is up to the implementation (tlx-compile
//!   evaluates IR subtrees in its IR executor).
//! - [`MixedCx`] is the per-worker state of mixed calls: the value arena
//!   behind the handles, the decoded-state cache, the panic of a callback
//!   and counters. It outlives calls (one per worker thread); the arena is
//!   emptied after every call.
//!
//! Handles: `epoch << 32 | (index + 1)`. Each arena slot records the epoch
//! it was made in; the epoch advances after every call and every
//! `release`, so a handle used after its call ended or after it was
//! released no longer matches its slot (index reused or gone) and is
//! refused with a panic: it is a bug in the generated code, not a TLA+
//! error.

use std::any::Any;
use std::sync::Arc;

use tlx_value::{ops, Value};

/// How a region input or result crosses the ABI.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Kind {
    /// A Bool or Int: `int64_t` (`tlx_arg.i`, `out[0]`).
    Scalar,
    /// An encoding of this many words (`tlx_arg.w` points to them; a
    /// result is written to `out[0..n]`).
    Words(u32),
    /// A boxed value, as a handle (`tlx_arg.h`, `out[0]`).
    Handle,
}

/// Inputs (in `args` order) and result of a region.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RegionSig {
    pub inputs: Vec<Kind>,
    pub result: Kind,
}

/// A region input.
#[derive(Clone, Copy, Debug)]
pub enum In<'a> {
    Int(i64),
    Words(&'a [u64]),
    Val(&'a Value),
}

/// A region result; must match the region's result kind (`Bool`/`Int` for
/// `Scalar`, words of the right length for `Words`, `Val` for `Handle`).
#[derive(Clone, Debug)]
pub enum Out {
    Bool(bool),
    Int(i64),
    Words(Box<[u64]>),
    Val(Value),
}

/// A region failed (a TLA+ evaluation error, a value outside a layout...):
/// the generated function returns `TLX_ERR` and the host re-runs the call
/// in the interpreter, which reports the error. The message is only kept
/// for statistics and debugging.
#[derive(Clone, Debug)]
pub struct RegionError(pub String);

/// The host's region table of one generated library.
pub trait Regions {
    /// Number of regions (rids are `0..len`).
    fn len(&self) -> u32;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    /// Hash of the table, compared with the library's `regions_hash` when
    /// it is loaded and on every call.
    fn hash(&self) -> u64;
    fn sig(&self, rid: u32) -> &RegionSig;
    /// Evaluate region `rid` (inputs as in `sig(rid)`).
    fn eval(&self, rid: u32, args: &Args<'_>, env: &mut RegionEnv<'_>) -> Result<Out, RegionError>;
}

/// The value store operations a library calls (`host->ref_op` and
/// `host->ref_elems`, ABI v5), implemented by the compiled tier for one
/// model: the table the code was generated for (its size and hash are
/// checked when the library is loaded).
pub trait RefOps: Send + Sync {
    /// Number of operations (ids are `0..len`).
    fn len(&self) -> u32;
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
    fn hash(&self) -> u64;
    /// Run operation `op`; false: an error (the interpreter decides).
    ///
    /// # Safety
    /// `op` must identify an operation in this table. `args` must point to
    /// its initialized argument words; encoding arguments must in turn point
    /// to initialized encodings of the required types and widths. Each input
    /// span must be readable within one allocation, remain live and immutable
    /// for the call, and have a byte length no greater than `isize::MAX`.
    ///
    /// `out` must provide exclusive writable storage for the operation's
    /// result, within one allocation and with a byte length no greater than
    /// `isize::MAX`; its contents may initially be uninitialized. Its span
    /// must not overlap the argument words or any referenced encoding.
    /// All pointers must be non-null and aligned for `u64`, even for empty
    /// spans, and all storage must remain live for the call.
    unsafe fn run(&self, op: u32, args: *const u64, out: *mut u64) -> bool;
    /// The handles of the elements of stored set `set` (None: not a set).
    fn elems(&self, set: u64) -> Option<&[u64]>;
}

/// `tlx_arg` in tlx_abi.h.
#[repr(C)]
#[derive(Clone, Copy)]
pub union Arg {
    pub i: i64,
    pub w: *const u64,
    pub h: u64,
}

/// The inputs of one region call.
pub struct Args<'a> {
    sig: &'a [Kind],
    raw: *const Arg,
    arena: &'a Arena,
}

impl<'a> Args<'a> {
    /// # Safety
    /// `raw` must point to `sig.len()` slots as `sig` describes them (an
    /// encoding slot pointing to its words), valid for `'a`.
    pub(crate) unsafe fn new(sig: &'a [Kind], raw: *const Arg, arena: &'a Arena) -> Args<'a> {
        Args { sig, raw, arena }
    }

    pub fn len(&self) -> usize {
        self.sig.len()
    }

    pub fn is_empty(&self) -> bool {
        self.sig.is_empty()
    }

    /// Input `i`. Panics on an invalid or stale handle.
    pub fn get(&self, i: usize) -> In<'a> {
        let kind = self.sig[i];
        // SAFETY: `new`'s contract: slot i exists and holds the kind of
        // `sig[i]`; an encoding points to its `n` words.
        unsafe {
            let a = *self.raw.add(i);
            match kind {
                Kind::Scalar => In::Int(a.i),
                Kind::Words(n) => In::Words(std::slice::from_raw_parts(a.w, n as usize)),
                Kind::Handle => In::Val(self.arena.get(a.h)),
            }
        }
    }
}

/// What a region sees besides its inputs.
pub struct RegionEnv<'a> {
    /// The current state (None in Init).
    pub s0: Option<&'a [u64]>,
    /// The next-state buffer in scope (None in state predicates).
    pub s1: Option<&'a [u64]>,
    /// `TLCGet("level")` of the call.
    pub level: u32,
    /// Decoded current state, shared by the calls on the same state.
    pub cache: &'a mut StateCache,
}

// Retain small buffers for reuse without pinning a rare call/state peak per worker.
const RETAINED_ARENA_SLOTS: usize = 2048;
const RETAINED_CACHE_WORDS: usize = 2048;

/// The decoding of the most recent current state. A hit compares all the
/// state's words (cheap next to decoding; buffers are reused and
/// fingerprints may collide).
#[derive(Default)]
pub struct StateCache {
    words: Vec<u64>,
    vals: Option<Arc<[Value]>>,
    /// Number of decodings (misses).
    pub decodes: u64,
}

impl StateCache {
    /// The values of state `s`, decoded with `decode` unless `s` is the
    /// cached state.
    pub fn get(&mut self, s: &[u64], decode: impl FnOnce(&[u64]) -> Vec<Value>) -> Arc<[Value]> {
        match &self.vals {
            Some(v) if self.words == s => v.clone(),
            _ => {
                let v: Arc<[Value]> = decode(s).into();
                self.words.clear();
                self.words.extend_from_slice(s);
                self.vals = Some(v.clone());
                self.decodes += 1;
                v
            }
        }
    }

    pub fn clear(&mut self) {
        self.words.clear();
        if self.words.capacity() > RETAINED_CACHE_WORDS {
            self.words.shrink_to(RETAINED_CACHE_WORDS);
        }
        self.vals = None;
    }
}

/// The values behind the handles of a call.
#[derive(Default)]
pub(crate) struct Arena {
    /// Value and the epoch it was made in.
    slots: Vec<(Value, u32)>,
    epoch: u32,
}

impl Arena {
    fn push(&mut self, v: Value) -> u64 {
        let idx = self.slots.len();
        assert!(idx < u32::MAX as usize, "value arena overflow");
        self.slots.push((v, self.epoch));
        (self.epoch as u64) << 32 | (idx as u64 + 1)
    }

    /// The value of handle `h`; panics if `h` is invalid or stale.
    fn get(&self, h: u64) -> &Value {
        let idx = (h & 0xffff_ffff) as usize;
        match idx.checked_sub(1).and_then(|i| self.slots.get(i)) {
            Some((v, e)) if *e == (h >> 32) as u32 => v,
            _ => panic!("stale or invalid value handle {h:#x} (epoch {}, {} live values)", self.epoch, self.slots.len()),
        }
    }

    fn mark(&self) -> u64 {
        self.slots.len() as u64
    }

    fn release(&mut self, mark: u64) {
        assert!(mark <= self.slots.len() as u64, "release to mark {mark} above the arena top {}", self.slots.len());
        self.slots.truncate(mark as usize);
        self.epoch = self.epoch.wrapping_add(1);
    }

    /// Free all values (end of a call).
    fn reset(&mut self) {
        self.slots.clear();
        if self.slots.capacity() > RETAINED_ARENA_SLOTS {
            self.slots.shrink_to(RETAINED_ARENA_SLOTS);
        }
        self.epoch = self.epoch.wrapping_add(1);
    }
}

/// Per-worker state of mixed calls (see the module documentation).
#[derive(Default)]
pub struct MixedCx {
    pub(crate) arena: Arena,
    pub cache: StateCache,
    /// A panic of a host callback, resumed when the generated function has
    /// returned (unwinding through C frames is not allowed).
    pub(crate) panic: Option<Box<dyn Any + Send>>,
    /// Region evaluations, and how many of them failed.
    pub evals: u64,
    pub errors: u64,
    /// The message of the last failed region evaluation or enumeration.
    pub last_error: Option<String>,
}

impl MixedCx {
    pub fn new() -> MixedCx {
        MixedCx::default()
    }

    /// Number of live values (0 between calls).
    pub fn live_values(&self) -> usize {
        self.arena.slots.len()
    }

    /// End of a call: free its values, invalidate its handles.
    pub(crate) fn end_call(&mut self) {
        self.arena.reset();
    }

    pub(crate) fn push(&mut self, v: Value) -> u64 {
        self.arena.push(v)
    }

    pub(crate) fn mark(&self) -> u64 {
        self.arena.mark()
    }

    pub(crate) fn release(&mut self, mark: u64) {
        self.arena.release(mark)
    }

    /// `host->elems`: push the elements of set handle `set`; returns the
    /// handle of the first one and their number.
    pub(crate) fn elems(&mut self, set: u64, sorted: bool) -> Result<(u64, u64), RegionError> {
        let s = self.arena.get(set);
        let xs = if sorted { ops::enumerate_normalized(s) } else { ops::enumerate(s) }.map_err(|e| RegionError(e.into_message()))?;
        let n = xs.len() as u64;
        let mut first = (self.arena.epoch as u64) << 32 | (self.arena.slots.len() as u64 + 1);
        for (i, x) in xs.into_iter().enumerate() {
            let h = self.arena.push(x);
            if i == 0 {
                first = h;
            }
        }
        Ok((first, n))
    }

    pub(crate) fn failed(&mut self, e: RegionError) {
        self.errors += 1;
        self.last_error = Some(e.0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn handles_and_epochs() {
        let mut a = Arena::default();
        let h1 = a.push(Value::Int(1));
        let m = a.mark();
        let h2 = a.push(Value::Int(2));
        assert_eq!(a.get(h2), &Value::Int(2));
        a.release(m);
        let h3 = a.push(Value::Int(3));
        assert_eq!(h3 & 0xffff_ffff, h2 & 0xffff_ffff, "index reused");
        assert_ne!(h3, h2);
        assert_eq!(a.get(h1), &Value::Int(1));
        assert_eq!(a.get(h3), &Value::Int(3));
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| a.get(h2).clone()));
        assert!(r.is_err(), "a released handle must be refused");
        a.reset();
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| a.get(h1).clone()));
        assert!(r.is_err(), "a handle of an ended call must be refused");
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| a.get(0).clone()));
        assert!(r.is_err(), "handle 0 is invalid");
    }

    #[test]
    fn end_call_bounds_arena_capacity_and_invalidates_handles() {
        let mut cx = MixedCx::new();
        let stale = cx.push(Value::Int(7));
        for _ in 0..RETAINED_ARENA_SLOTS * 16 {
            cx.push(Value::Int(1));
        }
        assert!(cx.arena.slots.capacity() > RETAINED_ARENA_SLOTS);
        cx.end_call();
        assert_eq!(cx.live_values(), 0);
        assert_eq!(cx.arena.slots.capacity(), RETAINED_ARENA_SLOTS);

        let fresh = cx.push(Value::Int(9));
        assert_eq!(fresh as u32, stale as u32, "index reused");
        assert_eq!(cx.arena.get(fresh), &Value::Int(9));
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| cx.arena.get(stale).clone()));
        assert!(r.is_err(), "shrinking must not revive a stale handle");
    }

    #[test]
    fn small_calls_reuse_arena_buffer() {
        let mut cx = MixedCx::new();
        cx.end_call();
        assert_eq!(cx.arena.slots.capacity(), 0);
        for _ in 0..32 {
            cx.push(Value::Int(1));
        }
        let capacity = cx.arena.slots.capacity();
        let ptr = cx.arena.slots.as_ptr();
        for _ in 0..3 {
            cx.end_call();
            for _ in 0..32 {
                cx.push(Value::Int(2));
            }
            assert_eq!(cx.arena.slots.capacity(), capacity);
            assert_eq!(cx.arena.slots.as_ptr(), ptr);
        }
    }

    #[test]
    fn clear_bounds_cache_capacity_and_forces_decode() {
        let mut c = StateCache::default();
        c.clear();
        assert_eq!(c.words.capacity(), 0);
        let words = vec![1; RETAINED_CACHE_WORDS * 16];
        let old = c.get(&words, |_| vec![Value::Int(1)]);
        assert!(c.words.capacity() > RETAINED_CACHE_WORDS);
        c.clear();
        assert!(c.words.is_empty());
        assert!(c.vals.is_none());
        assert_eq!(c.words.capacity(), RETAINED_CACHE_WORDS);
        assert_eq!(&*old, &[Value::Int(1)]);

        let fresh = c.get(&[], |_| vec![Value::Int(2)]);
        assert_eq!(&*fresh, &[Value::Int(2)]);
        assert_eq!(c.decodes, 2);
        let hit = c.get(&[], |_| panic!("cached state must not decode again"));
        assert!(Arc::ptr_eq(&fresh, &hit));
    }

    #[test]
    fn clear_reuses_small_cache_buffer() {
        let mut c = StateCache::default();
        c.get(&[1, 2], |_| vec![Value::Int(1)]);
        let capacity = c.words.capacity();
        let ptr = c.words.as_ptr();
        c.clear();
        c.get(&[1, 2], |_| vec![Value::Int(2)]);
        assert_eq!(c.words.capacity(), capacity);
        assert_eq!(c.words.as_ptr(), ptr);
        assert_eq!(c.decodes, 2);
    }

    #[test]
    fn state_cache_compares_words() {
        let mut c = StateCache::default();
        let dec = |s: &[u64]| s.iter().map(|w| Value::Int(*w as i64)).collect();
        let a = c.get(&[1, 2], dec);
        let b = c.get(&[1, 2], dec);
        assert!(Arc::ptr_eq(&a, &b));
        let d = c.get(&[1, 3], dec);
        assert_eq!(&*d, &[Value::Int(1), Value::Int(3)]);
        assert_eq!(c.decodes, 2);
    }
}
