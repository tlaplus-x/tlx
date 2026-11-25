//! Loading a generated model library and calling it through the C ABI.
//!
//! Safety contract with the generated code (see `docs/unsafe-audit.md`):
//! - unsafe construction establishes that the library implements this ABI;
//!   neither successful compilation of arbitrary C nor a matching version
//!   or table hash proves that its pointers and functions are safe;
//! - every state argument points to `words` readable `u64`s (checked here
//!   with `assert!`, so safe callers cannot cause out-of-bounds reads), and
//!   the generated functions read at most `words` words through it;
//! - the generated code has no mutable global state (only `static const`
//!   tables and automatic buffers), so its functions may run concurrently;
//! - the `cx` pointer passed back to the host callbacks is the `CallCtx`
//!   given to that same call, used only during it;
//! - mixed mode (ABI v3): the library was generated for the region table
//!   whose hash it reports (`regions_hash`, checked at load and on every
//!   call), so the `args` of `host->eval` hold the inputs its signature
//!   describes, `out` has room for its result, and `s0`/`s1` are NULL or
//!   point to `words` words.

use std::ffi::{c_char, c_int, c_void, CStr};
use std::path::Path;
use std::sync::Arc;

use libloading::Library;

use crate::mixed::{Arg, Args, Kind, MixedCx, Out, RefOps, RefOpsScope, RegionEnv, Regions};

/// Host callbacks (`tlx_host` in tlx_abi.h).
#[repr(C)]
pub struct Host {
    pub emit: unsafe extern "C" fn(cx: *mut c_void, state: *const u64, action: u32) -> c_int,
    pub error: unsafe extern "C" fn(cx: *mut c_void, err_id: u32),
    pub miss: unsafe extern "C" fn(cx: *mut c_void, var: u32),
    pub eval: unsafe extern "C" fn(cx: *mut c_void, rid: u32, s0: *const u64, s1: *const u64, args: *const Arg, out: *mut u64) -> c_int,
    pub elems: unsafe extern "C" fn(cx: *mut c_void, set: u64, sorted: u32, first: *mut u64, n: *mut u64) -> c_int,
    pub mark: unsafe extern "C" fn(cx: *mut c_void) -> u64,
    pub release: unsafe extern "C" fn(cx: *mut c_void, mark: u64),
    pub ref_op: unsafe extern "C" fn(cx: *mut c_void, op: u32, args: *const u64, out: *mut u64) -> c_int,
    pub ref_elems: unsafe extern "C" fn(cx: *mut c_void, set: u64, first: *mut *const u64, n: *mut u64) -> c_int,
}

/// One callback of [`Host`] (`tlx_host` in `tlx_abi.h`), in field order.
///
/// The C header owns the ABI, [`Host`] mirrors its layout and this enum names
/// its fields: [`HostFn::offset`] and [`HostFn::abi`] are the facts the JIT
/// backend loads the callback pointers and builds their call signatures with.
/// `tlx_abi.h` pins the layout it declares, and `tests/native.rs` compiles it
/// and compares every C offset/size/alignment and prototype against these
/// facts, so the Rust, C and JIT views cannot drift apart.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum HostFn {
    Emit,
    Error,
    Miss,
    Eval,
    Elems,
    Mark,
    Release,
    RefOp,
    RefElems,
}

/// Kind of one host-callback parameter or result, named by its C type in
/// `tlx_abi.h`. The Cranelift backend maps everything but the 32-bit kinds
/// to `i64`, and [`HostArg::bits`] is the width the C ABI gives it, so a
/// consumer can derive either without a second type table.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum HostArg {
    /// `tlx_ctx *`: the per-call host context, first in every callback.
    Ctx,
    /// `const uint64_t *`: a state.
    State,
    /// `uint64_t *`: a word out-parameter.
    WordOut,
    /// `const tlx_arg *`: the region arguments.
    Args,
    /// `const uint64_t **`: the element-handles out-parameter.
    ElemsOut,
    /// `uint64_t`: a handle, a mark or an element count.
    U64,
    /// `uint32_t`: an id, an action or a flag.
    U32,
    /// `int`: a return code.
    I32,
}

impl HostArg {
    /// Its width in the C ABI: 32 bits for the 32-bit kinds, 64 otherwise.
    pub const fn bits(self) -> u32 {
        match self {
            HostArg::U32 | HostArg::I32 => 32,
            HostArg::Ctx | HostArg::State | HostArg::WordOut | HostArg::Args | HostArg::ElemsOut | HostArg::U64 => 64,
        }
    }
}

/// Machine-independent signature of one host callback, as `tlx_abi.h`
/// declares it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct HostSignature {
    /// Parameters in call order, the `tlx_ctx *` first.
    pub params: &'static [HostArg],
    /// `None` for `void`.
    pub ret: Option<HostArg>,
}

impl HostFn {
    /// Every callback, in `tlx_host` field order.
    pub const ALL: [HostFn; 9] = [
        HostFn::Emit,
        HostFn::Error,
        HostFn::Miss,
        HostFn::Eval,
        HostFn::Elems,
        HostFn::Mark,
        HostFn::Release,
        HostFn::RefOp,
        HostFn::RefElems,
    ];

    /// Offset of the function pointer in `tlx_host` ([`Host`]).
    pub const fn offset(self) -> usize {
        match self {
            HostFn::Emit => std::mem::offset_of!(Host, emit),
            HostFn::Error => std::mem::offset_of!(Host, error),
            HostFn::Miss => std::mem::offset_of!(Host, miss),
            HostFn::Eval => std::mem::offset_of!(Host, eval),
            HostFn::Elems => std::mem::offset_of!(Host, elems),
            HostFn::Mark => std::mem::offset_of!(Host, mark),
            HostFn::Release => std::mem::offset_of!(Host, release),
            HostFn::RefOp => std::mem::offset_of!(Host, ref_op),
            HostFn::RefElems => std::mem::offset_of!(Host, ref_elems),
        }
    }

    /// The callback's declared C signature (`tlx_abi.h`).
    pub const fn abi(self) -> HostSignature {
        use HostArg::*;
        match self {
            HostFn::Emit => HostSignature { params: &[Ctx, State, U32], ret: Some(I32) },
            HostFn::Error => HostSignature { params: &[Ctx, U32], ret: None },
            HostFn::Miss => HostSignature { params: &[Ctx, U32], ret: None },
            HostFn::Eval => HostSignature { params: &[Ctx, U32, State, State, Args, WordOut], ret: Some(I32) },
            HostFn::Elems => HostSignature { params: &[Ctx, U64, U32, WordOut, WordOut], ret: Some(I32) },
            HostFn::Mark => HostSignature { params: &[Ctx], ret: Some(U64) },
            HostFn::Release => HostSignature { params: &[Ctx, U64], ret: None },
            HostFn::RefOp => HostSignature { params: &[Ctx, U32, State, WordOut], ret: Some(I32) },
            HostFn::RefElems => HostSignature { params: &[Ctx, U64, ElemsOut, WordOut], ret: Some(I32) },
        }
    }
}

/// `sizeof(tlx_host)`.
pub const HOST_SIZE: usize = std::mem::size_of::<Host>();
/// `_Alignof(tlx_host)`.
pub const HOST_ALIGN: usize = std::mem::align_of::<Host>();

// Compile-time check of [`Host`] against [`HostFn`]: the callbacks are exactly
// the struct, in field order, with no gap, extra field or padding (`tlx_abi.h`
// holds the same fact in C and `tests/native.rs` compares both with the
// compiled header).
const _: () = {
    type Cb = unsafe extern "C" fn();
    let stride = std::mem::size_of::<Cb>();
    let mut off = 0;
    let mut i = 0;
    while i < HostFn::ALL.len() {
        assert!(HostFn::ALL[i].offset() == off, "Host holds its callbacks in HostFn order, back to back");
        off += stride;
        i += 1;
    }
    assert!(HOST_SIZE == off, "Host holds only its callbacks");
    assert!(HOST_ALIGN == std::mem::align_of::<Cb>(), "Host is aligned like the function pointers it holds");
};

/// `tlx_spec_info` in tlx_abi.h.
#[repr(C)]
struct SpecInfo {
    abi_version: u32,
    words: u32,
    n_actions: u32,
    n_invariants: u32,
    action_names: *const *const c_char,
    invariant_names: *const *const c_char,
    n_errors: u32,
    error_msgs: *const *const c_char,
    n_regions: u32,
    regions_hash: u64,
    n_refops: u32,
    refops_hash: u64,
}

// Return codes of generated functions (tlx_abi.h).
pub const OK: c_int = 0;
pub const STOP: c_int = 1;
pub const ERR: c_int = -1;
pub const MISS: c_int = -2;
/// Returned by generated code for actions/predicates it does not implement
/// (`TLX_UNSUPPORTED`, defined by the code generator), and by
/// `action_property_raw` when the library has no action properties.
pub const UNSUPPORTED: c_int = -3;

pub type InitFn = unsafe extern "C" fn(*const Host, *mut c_void) -> c_int;
pub type NextFn = unsafe extern "C" fn(*const Host, *mut c_void, *const u64, u32) -> c_int;
pub type InvFn = unsafe extern "C" fn(*const Host, *mut c_void, *const u64, u32) -> c_int;
pub type APropFn = unsafe extern "C" fn(*const Host, *mut c_void, *const u64, *const u64, u32) -> c_int;

/// The entry points of an in-process implementation of the ABI (the
/// Cranelift JIT, `TLX_JIT`), with the same contract as the symbols of a
/// generated library, and the size and hash of the region table it calls
/// (`tlx_spec_info`).
pub struct EntryPoints {
    pub init: InitFn,
    pub next: NextFn,
    pub inv: InvFn,
    pub aprop: Option<APropFn>,
    pub n_regions: u32,
    pub regions_hash: u64,
    /// The value store operation table the code calls (None: none).
    pub refops: Option<Arc<dyn RefOps>>,
}

/// A loaded generated model.
pub struct NativeLib {
    /// What keeps the code alive (the loaded library, or JIT memory).
    _lib: Box<dyn std::any::Any + Send + Sync>,
    words: usize,
    action_names: Vec<String>,
    invariant_names: Vec<String>,
    error_msgs: Vec<String>,
    /// Number of host regions the code calls (0: no mixed mode).
    n_regions: u32,
    /// Hash of the region table the code was generated for.
    regions_hash: u64,
    /// The value store operations the code calls (`host->ref_op`).
    refops: Option<Arc<dyn RefOps>>,
    init: InitFn,
    next: NextFn,
    inv: InvFn,
    aprop: Option<APropFn>,
}

// `NativeLib` is `Send + Sync` (its fields are): calling its functions from
// several threads at once relies on the generated code having no mutable
// global state (see the module documentation).

/// # Safety
/// `p` must point to `n` pointers to NUL-terminated strings.
unsafe fn strings(p: *const *const c_char, n: u32) -> Vec<String> {
    // SAFETY: the caller's contract.
    (0..n as usize).map(|i| unsafe { CStr::from_ptr(*p.add(i)) }.to_string_lossy().into_owned()).collect()
}

/// The mixed-mode side of a call: the worker's `MixedCx`, the library's
/// region table and the level of the state(s) the call is about.
pub struct Mixed<'a> {
    pub cx: &'a mut MixedCx,
    pub regions: &'a dyn Regions,
    pub level: u32,
}

/// Outcome of one call into generated code.
struct Call {
    rc: c_int,
    /// Error id reported through `host->error`.
    error: Option<u32>,
    /// Variable reported through `host->miss`.
    miss: Option<u32>,
}

/// Panic unless `s` has the `words` words generated code reads through it.
#[inline]
#[track_caller]
fn check_len(s: &[u64], words: usize) {
    assert_eq!(s.len(), words, "state of {} words passed to a native library of {words}-word states", s.len());
}

impl NativeLib {
    /// Read-only metadata of the loaded generated model.
    pub fn words(&self) -> usize {
        self.words
    }

    /// Read-only metadata of the loaded generated model.
    pub fn action_names(&self) -> &[String] {
        &self.action_names
    }

    /// Read-only metadata of the loaded generated model.
    pub fn invariant_names(&self) -> &[String] {
        &self.invariant_names
    }

    /// Read-only metadata of the loaded generated model.
    pub fn error_msgs(&self) -> &[String] {
        &self.error_msgs
    }

    /// Read-only metadata of the loaded generated model.
    pub fn n_regions(&self) -> u32 {
        self.n_regions
    }

    /// Read-only metadata of the loaded generated model.
    pub fn regions_hash(&self) -> u64 {
        self.regions_hash
    }

    /// Load a library without host regions.
    ///
    /// # Safety
    /// The caller must satisfy the code, metadata and environment trust
    /// requirements of [`Self::load_with`]. No region or refop table is supplied.
    ///
    /// ```compile_fail,E0133
    /// use tlx_native::native::NativeLib;
    /// let _ = NativeLib::load(std::path::Path::new("model.so"));
    /// ```
    pub unsafe fn load(path: &Path) -> Result<NativeLib, String> {
        // SAFETY: the caller supplies the same trust proof as load_with.
        unsafe { Self::load_with(path, None, None) }
    }

    /// Load a library generated for the region table `regions` and the
    /// value store operation table `refops` (None: one without). A library
    /// of another ABI version, region table or operation table is refused.
    ///
    /// # Safety
    /// The caller must trust the library, its dependencies and their load/unload
    /// initializers, as well as the compiler, cache and path resolution (including
    /// replacement between build and load). A content hash is a cache key, not
    /// authentication; `build::build` accepts arbitrary C and proves no ABI contract.
    ///
    /// `tlx_info` must have the declared C signature and return a non-null,
    /// aligned pointer to a readable ABI-version `u32`. If that version matches,
    /// it must point to a fully initialized `tlx_spec_info` of our ABI, with valid
    /// counts and readable arrays of pointers to NUL-terminated strings, all
    /// immutable and live while the library is loaded. If the table checks pass,
    /// every entry point must implement the module's state, callback, lifetime
    /// and concurrency contract, with the declared signatures. Callback buffers
    /// must match the actual region/refop signatures, not merely their hashes.
    /// Metadata checks detect incompatibility; they do not establish this proof.
    ///
    /// ```compile_fail,E0133
    /// use tlx_native::native::NativeLib;
    /// let _ = NativeLib::load_with(std::path::Path::new("model.so"), None, None);
    /// ```
    pub unsafe fn load_with(path: &Path, regions: Option<&dyn Regions>, refops: Option<Arc<dyn RefOps>>) -> Result<NativeLib, String> {
        // SAFETY: the caller establishes load/unload safety, the tlx_info
        // signature and readable metadata, and (if checks pass) every symbol's
        // ABI and callback contract. The Library is retained with the function
        // pointers, so neither code nor its static data is unloaded early.
        unsafe {
            let lib = Library::new(path).map_err(|e| format!("cannot load {}: {e}", path.display()))?;
            let info: libloading::Symbol<unsafe extern "C" fn() -> *const SpecInfo> = lib.get(b"tlx_info").map_err(|e| e.to_string())?;
            let info = info();
            // Read only the version prefix until we know the metadata layout.
            let version = info.cast::<u32>().read();
            if version != crate::ABI_VERSION {
                return Err(format!("ABI version mismatch: library {} vs host {}", version, crate::ABI_VERSION));
            }
            let info = &*info;
            match regions {
                None if info.n_regions != 0 => {
                    return Err(format!("the library calls {} host regions but no region table was given", info.n_regions))
                }
                Some(r) if (r.len(), r.hash()) != (info.n_regions, info.regions_hash) => {
                    return Err(format!(
                        "region table mismatch: library {} regions (hash {:016x}), host {} regions (hash {:016x})",
                        info.n_regions,
                        info.regions_hash,
                        r.len(),
                        r.hash()
                    ))
                }
                _ => {}
            }
            let (n, h) = refops.as_ref().map_or((0, 0), |r| (r.len(), r.hash()));
            if (n, h) != (info.n_refops, info.refops_hash) {
                return Err(format!(
                    "value store operation table mismatch: library {} operations (hash {:016x}), host {n} (hash {h:016x})",
                    info.n_refops, info.refops_hash
                ));
            }
            let init: InitFn = *lib.get::<InitFn>(b"tlx_init").map_err(|e| e.to_string())?;
            let next: NextFn = *lib.get::<NextFn>(b"tlx_next").map_err(|e| e.to_string())?;
            let inv: InvFn = *lib.get::<InvFn>(b"tlx_invariant").map_err(|e| e.to_string())?;
            let aprop: Option<APropFn> = lib.get::<APropFn>(b"tlx_action_property").ok().map(|f| *f);
            Ok(NativeLib {
                words: info.words as usize,
                action_names: strings(info.action_names, info.n_actions),
                invariant_names: strings(info.invariant_names, info.n_invariants),
                error_msgs: strings(info.error_msgs, info.n_errors),
                n_regions: info.n_regions,
                regions_hash: info.regions_hash,
                refops: refops.filter(|r| !r.is_empty()),
                init,
                next,
                inv,
                aprop,
                _lib: Box::new(lib),
            })
        }
    }

    /// A library whose code was generated in-process.
    ///
    /// # Safety
    /// The entry points must implement the ABI of a generated library for
    /// states of `words` words, `action_names.len()` actions and
    /// `invariant_names.len()` invariants, and stay valid while `keep` lives.
    pub unsafe fn from_entry_points(
        keep: Box<dyn std::any::Any + Send + Sync>,
        words: usize,
        action_names: Vec<String>,
        invariant_names: Vec<String>,
        e: EntryPoints,
    ) -> NativeLib {
        NativeLib {
            _lib: keep,
            words,
            action_names,
            invariant_names,
            error_msgs: vec!["runtime error".into()],
            n_regions: e.n_regions,
            regions_hash: e.regions_hash,
            refops: e.refops,
            init: e.init,
            next: e.next,
            inv: e.inv,
            aprop: e.aprop,
        }
    }

    /// Call `f` with `HOST` and a fresh `CallCtx` that sends emitted states
    /// to `out`, without host regions.
    ///
    /// # Safety
    /// As `call_mixed`.
    #[inline]
    unsafe fn call(&self, out: &mut dyn FnMut(Box<[u64]>, u32) -> bool, f: impl FnOnce(*const Host, *mut c_void) -> c_int) -> Call {
        let mut mx = MixedCx::new();
        // SAFETY: the caller's contract.
        unsafe { self.call_mixed(&mut mx, None, 0, out, f) }
    }

    /// Call `f` with `HOST` and a fresh `CallCtx` that sends emitted states
    /// to `out` and evaluates regions with `regions` in `mx`.
    ///
    /// # Safety
    /// `f` must call a generated function of this library, passing the host
    /// and context it receives; any state pointers it passes must point to
    /// `words` u64s.
    ///
    /// A panic of a callback (`out`, a region evaluation, a stale handle) is
    /// caught there (unwinding through C frames is not allowed), the call is
    /// told to stop (`emit`) or fails (`eval`, `elems`), and the panic is
    /// resumed here once the generated function has returned. The values
    /// made during the call are freed when it returns.
    #[inline]
    unsafe fn call_mixed(
        &self,
        mx: &mut MixedCx,
        regions: Option<&dyn Regions>,
        level: u32,
        out: &mut dyn FnMut(Box<[u64]>, u32) -> bool,
        f: impl FnOnce(*const Host, *mut c_void) -> c_int,
    ) -> Call {
        if let Some(r) = regions {
            assert!(
                (r.len(), r.hash()) == (self.n_regions, self.regions_hash),
                "region table (hash {:016x}) is not the one the library was loaded for ({:016x})",
                r.hash(),
                self.regions_hash
            );
        }
        if let Some(ops) = self.refops.as_deref() {
            return self.call_mixed_pinned(ops, regions, mx, out, level, f);
        }
        let mut cx = CallCtx { words: self.words, out, error: None, miss: None, mx, regions, refops: None, level };
        let rc = f(&HOST, &mut cx as *mut CallCtx as *mut c_void);
        let (error, miss) = (cx.error, cx.miss);
        cx.mx.end_call();
        if let Some(p) = cx.mx.panic.take() {
            std::panic::resume_unwind(p);
        }
        Call { rc, error, miss }
    }

    #[inline(never)]
    fn call_mixed_pinned<F>(
        &self,
        ops: &dyn RefOps,
        regions: Option<&dyn Regions>,
        mx: &mut MixedCx,
        out: &mut dyn FnMut(Box<[u64]>, u32) -> bool,
        level: u32,
        f: F,
    ) -> Call
    where
        F: FnOnce(*const Host, *mut c_void) -> i32,
    {
        let mut f = Some(f);
        let mut out = Some(out);
        let mut mx = Some(mx);
        let mut result = None;
        ops.with_scope(&mut |scope| {
            let f = f.take().expect("RefOps::with_scope invoked callback more than once");
            let out = out.take().unwrap();
            let mx = mx.take().unwrap();
            let mut cx = CallCtx { words: self.words, out, error: None, miss: None, mx, regions, refops: Some(scope), level };
            let rc = f(&HOST, &mut cx as *mut CallCtx as *mut c_void);
            let (error, miss) = (cx.error, cx.miss);
            cx.mx.end_call();
            if let Some(p) = cx.mx.panic.take() {
                std::panic::resume_unwind(p);
            }
            result = Some(Call { rc, error, miss });
        });
        result.expect("RefOps::with_scope did not invoke callback")
    }

    /// Run Init, appending initial states to `out` (ABI return code).
    pub fn init_into(&self, out: &mut Vec<Box<[u64]>>) -> c_int {
        // SAFETY: calls a generated function with the given host and context.
        unsafe { self.call(&mut push_to(out), |h, cx| (self.init)(h, cx)).rc }
    }

    /// Run action `action` on state `s`, appending generated states to `out`.
    /// Returns the ABI return code (OK, STOP, ERR, MISS or a negative
    /// "unsupported" code).
    pub fn next_into(&self, s: &[u64], action: u32, out: &mut Vec<Box<[u64]>>) -> c_int {
        check_len(s, self.words);
        // SAFETY: as above; s has `words` elements.
        unsafe { self.call(&mut push_to(out), |h, cx| (self.next)(h, cx, s.as_ptr(), action)).rc }
    }

    /// Evaluate invariant `i` (1 = holds, 0 = violated, negative = error/unsupported).
    pub fn invariant_raw(&self, s: &[u64], i: u32) -> c_int {
        self.invariant_call(s, i).rc
    }

    fn invariant_call(&self, s: &[u64], i: u32) -> Call {
        check_len(s, self.words);
        // SAFETY: as above; s has `words` elements.
        unsafe { self.call(&mut discard, |h, cx| (self.inv)(h, cx, s.as_ptr(), i)) }
    }

    /// Evaluate action property `i` on the transition `s -> t` (1 = holds,
    /// 0 = violated, negative = error/unsupported or not provided).
    pub fn action_property_raw(&self, s: &[u64], t: &[u64], i: u32) -> c_int {
        let Some(f) = self.aprop else { return UNSUPPORTED };
        check_len(s, self.words);
        check_len(t, self.words);
        // SAFETY: as above; s and t have `words` elements.
        unsafe { self.call(&mut discard, |h, cx| f(h, cx, s.as_ptr(), t.as_ptr(), i)).rc }
    }

    /// `init_into` with host regions.
    pub fn init_mixed(&self, m: Mixed<'_>, out: &mut Vec<Box<[u64]>>) -> c_int {
        // SAFETY: calls a generated function with the given host and context.
        unsafe { self.call_mixed(m.cx, Some(m.regions), m.level, &mut push_to(out), |h, cx| (self.init)(h, cx)).rc }
    }

    /// `next_into` with host regions.
    pub fn next_mixed(&self, m: Mixed<'_>, s: &[u64], action: u32, out: &mut Vec<Box<[u64]>>) -> c_int {
        check_len(s, self.words);
        // SAFETY: as above; s has `words` elements.
        unsafe { self.call_mixed(m.cx, Some(m.regions), m.level, &mut push_to(out), |h, cx| (self.next)(h, cx, s.as_ptr(), action)).rc }
    }

    /// `invariant_raw` with host regions.
    pub fn invariant_mixed(&self, m: Mixed<'_>, s: &[u64], i: u32) -> c_int {
        check_len(s, self.words);
        // SAFETY: as above; s has `words` elements.
        unsafe { self.call_mixed(m.cx, Some(m.regions), m.level, &mut discard, |h, cx| (self.inv)(h, cx, s.as_ptr(), i)).rc }
    }

    /// `action_property_raw` with host regions.
    pub fn action_property_mixed(&self, m: Mixed<'_>, s: &[u64], t: &[u64], i: u32) -> c_int {
        let Some(f) = self.aprop else { return UNSUPPORTED };
        check_len(s, self.words);
        check_len(t, self.words);
        // SAFETY: as above; s and t have `words` elements.
        unsafe { self.call_mixed(m.cx, Some(m.regions), m.level, &mut discard, |h, cx| f(h, cx, s.as_ptr(), t.as_ptr(), i)).rc }
    }

    // The `Model`-shaped view of the library (states are raw word arrays).
    // tlx-runtime's `Model` impl lives in the crate's tests (`tests/common`),
    // which keeps tlx-native independent of tlx-runtime; these are the
    // runtime-free entry points it needs.

    /// Run Init, calling `out` for each emitted state (returning `false` to
    /// stop); `Err` is the failure message.
    pub fn init_states(&self, out: &mut dyn FnMut(Box<[u64]>, u32) -> bool) -> Result<(), String> {
        // SAFETY: calls a generated function with the given host and context.
        let c = unsafe { self.call(out, |h, cx| (self.init)(h, cx)) };
        self.check(&c)
    }

    /// Run each action of the library on `s`, calling `out` for each state.
    pub fn successors(&self, s: &[u64], out: &mut dyn FnMut(Box<[u64]>, u32) -> bool) -> Result<(), String> {
        for a in 0..self.action_names.len() as u32 {
            let mut stopped = false;
            let mut o = |t: Box<[u64]>, act: u32| {
                let go = out(t, act);
                stopped |= !go;
                go
            };
            check_len(s, self.words);
            // SAFETY: as above; s has `words` elements (checked).
            let c = unsafe { self.call(&mut o, |h, cx| (self.next)(h, cx, s.as_ptr(), a)) };
            self.check(&c)?;
            if stopped {
                break;
            }
        }
        Ok(())
    }

    /// The index of the first violated invariant of `s` (checked in order).
    pub fn check_invariants(&self, s: &[u64]) -> Result<Option<usize>, String> {
        for i in 0..self.invariant_names.len() {
            let c = self.invariant_call(s, i as u32);
            match c.rc {
                ERR => return Err(self.error_message(&c)),
                0 => return Ok(Some(i)),
                _ => {}
            }
        }
        Ok(None)
    }

    fn check(&self, c: &Call) -> Result<(), String> {
        match c.rc {
            OK | STOP => Ok(()),
            _ => Err(self.error_message(c)),
        }
    }

    /// The message for a failed call (`rc` is neither OK nor STOP).
    fn error_message(&self, c: &Call) -> String {
        match c.rc {
            ERR => c.error.and_then(|i| self.error_msgs.get(i as usize).cloned()).unwrap_or_else(|| "runtime error".into()),
            MISS => format!("layout miss on variable {}", c.miss.unwrap_or(u32::MAX)),
            other => format!("generated code returned {other}"),
        }
    }
}

/// An emit callback appending states to `out` (and never stopping).
fn push_to(out: &mut Vec<Box<[u64]>>) -> impl FnMut(Box<[u64]>, u32) -> bool + '_ {
    |t, _| {
        out.push(t);
        true
    }
}

/// An emit callback for predicates (which never emit).
fn discard(_: Box<[u64]>, _: u32) -> bool {
    true
}

// ---------------------------------------------------------------------------
// Host callbacks

/// Per-call context passed through the C ABI.
struct CallCtx<'a> {
    words: usize,
    out: &'a mut dyn FnMut(Box<[u64]>, u32) -> bool,
    error: Option<u32>,
    miss: Option<u32>,
    /// Value arena, state cache and the panic of a callback (resumed after
    /// the call returns).
    mx: &'a mut MixedCx,
    regions: Option<&'a dyn Regions>,
    refops: Option<&'a dyn RefOpsScope>,
    level: u32,
}

// SAFETY: the callbacks are only called by generated code during a
// `NativeLib::call_mixed`, with the `CallCtx` of that call (exclusively
// borrowed by it for the whole call) and, for `emit`, a pointer to a state
// of `words` words; for `eval`, see the module documentation.

unsafe extern "C" fn emit_cb(cx: *mut c_void, state: *const u64, action: u32) -> c_int {
    // SAFETY: see above.
    let cx = unsafe { &mut *(cx as *mut CallCtx) };
    if cx.mx.panic.is_some() {
        return STOP;
    }
    // SAFETY: see above (the state is copied before the callback returns).
    let s: Box<[u64]> = unsafe { std::slice::from_raw_parts(state, cx.words) }.into();
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| (cx.out)(s, action))) {
        Ok(true) => OK,
        Ok(false) => STOP,
        Err(p) => {
            cx.mx.panic = Some(p);
            STOP
        }
    }
}

/// Run a mixed-mode callback body, catching a panic (kept in the
/// `MixedCx`, resumed after the call; the callback then returns `failed`).
/// After a panic, callbacks do nothing and return `failed`.
fn guarded<R>(cx: &mut CallCtx, failed: R, f: impl FnOnce(&mut CallCtx) -> R) -> R {
    if cx.mx.panic.is_some() {
        return failed;
    }
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| f(&mut *cx))) {
        Ok(r) => r,
        Err(p) => {
            cx.mx.panic = Some(p);
            failed
        }
    }
}

// SAFETY: called only by generated code with the `CallCtx` of the current
// `NativeLib::call_mixed` (see the contract on `emit_cb`).
unsafe extern "C" fn eval_cb(cx: *mut c_void, rid: u32, s0: *const u64, s1: *const u64, args: *const Arg, out: *mut u64) -> c_int {
    // SAFETY: see above.
    let cx = unsafe { &mut *(cx as *mut CallCtx) };
    guarded(cx, ERR, |cx| {
        let regions = cx.regions.expect("generated code called host->eval without a region table");
        assert!(rid < regions.len(), "region {rid} out of range ({} regions)", regions.len());
        let sig = regions.sig(rid);
        let words = cx.words;
        // SAFETY: see above: state pointers are NULL or point to `words`
        // words.
        let state = |p: *const u64| (!p.is_null()).then(|| unsafe { std::slice::from_raw_parts(p, words) });
        let mx = &mut *cx.mx;
        mx.evals += 1;
        let r = {
            // SAFETY: see above: `args` holds the region's inputs.
            let args = unsafe { Args::new(&sig.inputs, args, &mx.arena) };
            let mut env = RegionEnv { s0: state(s0), s1: state(s1), level: cx.level, cache: &mut mx.cache };
            regions.eval(rid, &args, &mut env)
        };
        let v = match r {
            Ok(v) => v,
            Err(e) => {
                mx.failed(e);
                return ERR;
            }
        };
        // SAFETY: see above: `out` has room for the region's result.
        unsafe {
            match (sig.result, v) {
                (Kind::Scalar, Out::Int(i)) => *out = i as u64,
                (Kind::Scalar, Out::Bool(b)) => *out = b as u64,
                (Kind::Words(n), Out::Words(w)) => {
                    assert_eq!(w.len(), n as usize, "region {rid}: result of {} words, expected {n}", w.len());
                    std::ptr::copy_nonoverlapping(w.as_ptr(), out, w.len());
                }
                (Kind::Handle, Out::Val(v)) => *out = mx.push(v),
                (k, v) => panic!("region {rid}: result {v:?} does not match its kind {k:?}"),
            }
        }
        OK
    })
}

// SAFETY: called only by generated code with the `CallCtx` of the current
// `NativeLib::call_mixed` (see the contract on `emit_cb`).
unsafe extern "C" fn elems_cb(cx: *mut c_void, set: u64, sorted: u32, first: *mut u64, n: *mut u64) -> c_int {
    // SAFETY: see above.
    let cx = unsafe { &mut *(cx as *mut CallCtx) };
    guarded(cx, ERR, |cx| match cx.mx.elems(set, sorted != 0) {
        Ok((f, k)) => {
            // SAFETY: the generated code passes pointers to two variables.
            unsafe {
                *first = f;
                *n = k;
            }
            OK
        }
        Err(e) => {
            cx.mx.failed(e);
            ERR
        }
    })
}

// SAFETY: called only by generated code with the `CallCtx` of the current
// `NativeLib::call_mixed` (see the contract on `emit_cb`).
unsafe extern "C" fn mark_cb(cx: *mut c_void) -> u64 {
    // SAFETY: see above.
    let cx = unsafe { &mut *(cx as *mut CallCtx) };
    cx.mx.mark()
}

// SAFETY: called only by generated code with the `CallCtx` of the current
// `NativeLib::call_mixed` (see the contract on `emit_cb`).
unsafe extern "C" fn release_cb(cx: *mut c_void, mark: u64) {
    // SAFETY: see above.
    let cx = unsafe { &mut *(cx as *mut CallCtx) };
    guarded(cx, (), |cx| cx.mx.release(mark))
}

// SAFETY: called only by generated code with the `CallCtx` of the current
// `NativeLib::call_mixed` (see the contract on `emit_cb`).
unsafe extern "C" fn error_cb(cx: *mut c_void, err_id: u32) {
    // SAFETY: see above.
    unsafe { (*(cx as *mut CallCtx)).error = Some(err_id) };
}

// SAFETY: called only by generated code with the `CallCtx` of the current
// `NativeLib::call_mixed` (see the contract on `emit_cb`).
unsafe extern "C" fn miss_cb(cx: *mut c_void, var: u32) {
    // SAFETY: see above.
    unsafe { (*(cx as *mut CallCtx)).miss = Some(var) };
}

// SAFETY: called only by generated code with the `CallCtx` of the current
// `NativeLib::call_mixed` (see the contract on `emit_cb`); `args` and `out`
// as `RefOps::run` requires (the library was generated for this table).
unsafe extern "C" fn ref_op_cb(cx: *mut c_void, op: u32, args: *const u64, out: *mut u64) -> c_int {
    // SAFETY: see above.
    let cx = unsafe { &mut *(cx as *mut CallCtx) };
    guarded(cx, ERR, |cx| {
        let ops = cx.refops.expect("generated code called host->ref_op without an operation table");
        assert!(op < ops.len(), "value store operation {op} out of range ({} operations)", ops.len());
        // SAFETY: see above.
        if unsafe { ops.run(op, args, out) } {
            OK
        } else {
            ERR
        }
    })
}

// SAFETY: called only by generated code with the `CallCtx` of the current
// `NativeLib::call_mixed` (see the contract on `emit_cb`).
unsafe extern "C" fn ref_elems_cb(cx: *mut c_void, set: u64, first: *mut *const u64, n: *mut u64) -> c_int {
    // SAFETY: see above.
    let cx = unsafe { &mut *(cx as *mut CallCtx) };
    guarded(cx, ERR, |cx| {
        let ops = cx.refops.expect("generated code called host->ref_elems without an operation table");
        match ops.elems(set) {
            Some(es) => {
                // SAFETY: the generated code passes pointers to two variables;
                // `RefOpsScope` pins the value store for the entire native call.
                unsafe {
                    *first = es.as_ptr();
                    *n = es.len() as u64;
                }
                OK
            }
            None => ERR,
        }
    })
}

/// Host callbacks; they expect a `CallCtx` as context.
static HOST: Host = Host {
    emit: emit_cb,
    error: error_cb,
    miss: miss_cb,
    eval: eval_cb,
    elems: elems_cb,
    mark: mark_cb,
    release: release_cb,
    ref_op: ref_op_cb,
    ref_elems: ref_elems_cb,
};
