//! Cranelift backend of the compiled tier (`TLX_JIT`, cargo feature `jit`,
//! on by default; docs/design.md §6.6).
//!
//! A port of `cgen` that emits Cranelift IR instead of C and compiles it
//! in-process. It implements the same ABI entry points as a generated C
//! library (`tlx_init`, `tlx_next`, `tlx_invariant`, `tlx_action_property`),
//! so the result plugs in as a `NativeLib`. It covers
//! the same IR as `cgen`; anything it does not translate becomes a stub
//! returning `UNSUPPORTED`, exactly like a C stub.
//!
//! Mixed mode (docs/mixed-mode.md §4): the JIT does not decide region
//! boundaries itself. It follows the model's native plan (`native_plan`):
//! it calls the plan's regions where the C code calls them (`RegionPlan`:
//! the IR node of each region), with the same host callbacks (`eval`,
//! `elems`, `mark`/`release`), so that the JIT and C libraries of a model
//! share one region table and are interchangeable. A region the JIT does
//! not reach makes the whole library fail (the caller then uses C).
//!
//! Representation (as in C): Bool/Int are `i64`; encodings are pointers
//! (`i64`) into the states, static constants (owned by the library) or
//! stack slots of the function; boxed values (mixed mode) are `i64`
//! handles. A runtime error jumps to the function's error block
//! (`return TLX_ERR`).

mod expr;
mod gen;
mod rt;
mod stmt;

use std::collections::hash_map::DefaultHasher;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use cranelift_codegen::ir::function::FunctionStencil;
use cranelift_codegen::ir::{types, AbiParam, InstBuilder, Signature, StackSlotData, StackSlotKind, UserFuncName};
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::{Context, FinalizedMachReloc};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Switch};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{default_libcall_names, DataDescription, DataId, FuncId, Linkage, Module, ModuleReloc};
use tlx_base::diag::{self, Topic};
use tlx_native::native::{EntryPoints, NativeLib, UNSUPPORTED};

use crate::ir::*;
use crate::native_plan::{NativeSet, RegionCursor, RegionPlan};
use crate::types::Typing;

use gen::{Gen, Kind};

/// Why an IR construct has no translation.
pub(crate) struct Unsupported(pub String);

type R<T> = Result<T, Unsupported>;

fn no<T>(msg: impl Into<String>) -> R<T> {
    Err(Unsupported(msg.into()))
}

/// At most this many threads compile the functions of a library.
const JIT_THREADS: usize = 8;

const I64: types::Type = types::I64;
const I32: types::Type = types::I32;

/// A JIT-compiled model library.
pub struct JitLibrary {
    pub lib: NativeLib,
    pub native: NativeSet,
    /// Time spent translating to Cranelift IR and compiling.
    pub compile_time: Duration,
    /// Machine code bytes.
    pub code_bytes: usize,
}

/// What keeps JIT code and its constants alive.
struct Keep {
    module: Option<JITModule>,
    _statics: SharedStatics,
}

// SAFETY: after `finalize_definitions` the module is never used again
// except to free its memory on drop; the code and constants are immutable.
unsafe impl Send for Keep {}
unsafe impl Sync for Keep {}

impl Drop for Keep {
    fn drop(&mut self) {
        if let Some(m) = self.module.take() {
            // SAFETY: the library holding the function pointers is being
            // dropped with this.
            unsafe { m.free_memory() };
        }
    }
}

/// Constant tables referenced by address from JIT code.
#[derive(Default)]
struct Statics {
    words: Vec<Box<[u64]>>,
    words_map: HashMap<Vec<u64>, i64>,
    i32s: Vec<Box<[i32]>>,
    i32s_map: HashMap<Vec<i32>, i64>,
    i64s: Vec<Box<[i64]>>,
    i64s_map: HashMap<Vec<i64>, i64>,
}

/// Append-only shared constant pool so identical constant tables keep stable
/// addresses across layout-miss restarts and outlive the `JitCache` via `Keep`.
#[derive(Clone, Default)]
pub(crate) struct SharedStatics(Arc<Mutex<Statics>>);

impl SharedStatics {
    pub(crate) fn words(&self, w: &[u64]) -> i64 {
        let mut s = self.0.lock().unwrap();
        let key: &[u64] = if w.is_empty() { &[0] } else { w };
        if let Some(&p) = s.words_map.get(key) {
            return p;
        }
        let b: Box<[u64]> = key.into();
        let p = b.as_ptr() as i64;
        s.words.push(b);
        s.words_map.insert(key.to_vec(), p);
        p
    }
    pub(crate) fn i32s(&self, w: &[i32]) -> i64 {
        let mut s = self.0.lock().unwrap();
        let key: &[i32] = if w.is_empty() { &[-1] } else { w };
        if let Some(&p) = s.i32s_map.get(key) {
            return p;
        }
        let b: Box<[i32]> = key.into();
        let p = b.as_ptr() as i64;
        s.i32s.push(b);
        s.i32s_map.insert(key.to_vec(), p);
        p
    }
    pub(crate) fn i64s(&self, w: &[i64]) -> i64 {
        let mut s = self.0.lock().unwrap();
        let key: &[i64] = if w.is_empty() { &[0] } else { w };
        if let Some(&p) = s.i64s_map.get(key) {
            return p;
        }
        let b: Box<[i64]> = key.into();
        let p = b.as_ptr() as i64;
        s.i64s.push(b);
        s.i64s_map.insert(key.to_vec(), p);
        p
    }
}

/// Cross-attempt cache of compiled Cranelift machine code keyed by exact
/// `(isa_key, user_namespaces, FunctionStencil)` structural equality (no
/// hash-only reuse).
#[derive(Default)]
pub(crate) struct JitCache {
    statics: SharedStatics,
    entries: HashMap<u64, Vec<CachedFn>>,
    #[cfg(test)]
    hits: usize,
}

#[cfg(test)]
impl JitCache {
    pub(crate) fn entry_count(&self) -> usize {
        self.entries.values().map(Vec::len).sum()
    }
    pub(crate) fn hits(&self) -> usize {
        self.hits
    }
}

struct CachedFn {
    isa_key: String,
    namespaces: Vec<u32>,
    stencil: FunctionStencil,
    align: u64,
    bytes: Vec<u8>,
    relocs: Vec<FinalizedMachReloc>,
}

fn stencil_hash(isa_key: &str, namespaces: &[u32], stencil: &FunctionStencil) -> u64 {
    let mut h = DefaultHasher::new();
    isa_key.hash(&mut h);
    namespaces.hash(&mut h);
    stencil.hash(&mut h);
    h.finish()
}

/// Module-wide state of one compilation.
pub(crate) struct Cx<'t> {
    ty: &'t Typing,
    module: JITModule,
    /// Read-only module data containing `(nvars + 1)` byte offsets (`[off_0*8, ..., words*8]`).
    var_offsets: DataId,
    statics: SharedStatics,
    /// Compiled functions (`Typing::funcs`): declared ids and nativeness.
    fn_ids: Vec<FuncId>,
    fn_native: Vec<bool>,
    /// Mixed mode: the plan's regions not called yet (None: off).
    pub(super) regions: Option<RegionCursor<'t>>,
    /// The value store operations the code may call (`host->ref_op`).
    pub(super) refops: Option<std::sync::Arc<crate::exec::refops::RefOpTable>>,
    /// Functions translated but not compiled yet (`compile`, `flush`).
    pending: Vec<(FuncId, cranelift_codegen::ir::Function)>,
}

/// Cranelift flags: `TLX_JIT_OPT` = none|speed (default speed),
/// `TLX_JIT_VERIFY` turns the IR verifier on.
fn isa_flags() -> (settings::Flags, String) {
    let mut b = settings::builder();
    b.set("use_colocated_libcalls", "false").unwrap();
    b.set("is_pic", "false").unwrap();
    let env = tlx_base::knobs::Env::process();
    let opt = env.string_or_default("TLX_JIT_OPT");
    let opt_used = if b.set("opt_level", &opt).is_ok() {
        opt
    } else {
        b.set("opt_level", "speed").unwrap();
        "speed".to_string()
    };
    let verify = env.flag("TLX_JIT_VERIFY");
    b.set("enable_verifier", if verify { "true" } else { "false" }).unwrap();
    (settings::Flags::new(b), format!("opt={opt_used};verify={verify}"))
}

/// Compile a library: same functions and entry points as
/// `CGen::library`, calling the regions of the plan (mixed mode) where the
/// C code does.
/// Err if the host ISA is not supported or the library does not call the
/// regions as the C code does.
#[allow(clippy::too_many_arguments)]
pub fn library(
    verified: &crate::verify::Program<'_>,
    regions: Option<RegionPlan>,
    refops: Option<std::sync::Arc<crate::exec::refops::RefOpTable>>,
    action_names: &[String],
    inv_names: &[String],
) -> Result<JitLibrary, String> {
    library_with_cache(verified, regions, refops, action_names, inv_names, None)
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn library_with_cache(
    verified: &crate::verify::Program<'_>,
    regions: Option<RegionPlan>,
    refops: Option<std::sync::Arc<crate::exec::refops::RefOpTable>>,
    action_names: &[String],
    inv_names: &[String],
    cache: Option<&mut JitCache>,
) -> Result<JitLibrary, String> {
    let ty = verified.typing();
    let init = verified.init();
    let actions = verified.actions();
    let invariants = verified.predicates();
    let aprops = verified.transitions();
    let t0 = Instant::now();
    if let Some(plan) = &regions {
        crate::verify::enforce(plan.table.verify_typing(ty))?;
        if plan.sites.len() != plan.table.len() {
            return Err("region plan site count mismatch".into());
        }
    }
    let (flags, isa_key) = isa_flags();
    let isa = cranelift_native::builder().map_err(|e| e.to_string())?.finish(flags).map_err(|e| e.to_string())?;
    let mut module = JITModule::new(JITBuilder::with_isa(isa, default_libcall_names()));
    // Declare the read-only variable byte-offset table first so it always has
    // DataId(0) across restarts.
    let var_offsets = module.declare_data("var_offsets", Linkage::Local, false, false).map_err(|e| e.to_string())?;
    let mut off_bytes = Vec::with_capacity((ty.layout.offsets.len() + 1) * 8);
    for &o in &ty.layout.offsets {
        off_bytes.extend_from_slice(&((o * 8) as u64).to_le_bytes());
    }
    off_bytes.extend_from_slice(&((ty.layout.words * 8) as u64).to_le_bytes());
    let mut dd = DataDescription::new();
    dd.define(off_bytes.into_boxed_slice());
    dd.set_align(8);
    module.define_data(var_offsets, &dd).map_err(|e| e.to_string())?;
    let statics = cache.as_ref().map_or_else(SharedStatics::default, |c| c.statics.clone());
    let regions = regions.filter(|r| !r.table.is_empty()).map(RegionCursor::new);
    let (n_regions, regions_hash) = regions.as_ref().map_or((0, 0), |r| (r.table.len() as u32, r.table.hash()));
    let mut cx = Cx {
        ty,
        module,
        var_offsets,
        statics,
        fn_ids: Vec::new(),
        fn_native: Vec::new(),
        regions,
        refops: refops.clone(),
        pending: Vec::new(),
    };
    let mut fbc = FunctionBuilderContext::new();
    let mut ctx = cx.module.make_context();
    let mut code_bytes = 0;

    cx.functions(&mut ctx, &mut fbc, &mut code_bytes)?;

    let mut native = NativeSet::default();
    let init_r = init.ok_or(Unsupported("not lowered".into()));
    let mixing = cx.mixing_stmt(init, true);
    let (init_id, ok, mixed) = cx.define(
        &mut ctx,
        &mut fbc,
        "init_fn",
        Kind::Init,
        vec![(mixing, Box::new(|g: &mut Gen| g.action(init_r?)))],
        || "Init".into(),
        &mut code_bytes,
    )?;
    native.init = ok;
    native.mixed_init = mixed;
    let mut act_ids = Vec::new();
    for (i, a) in actions.iter().enumerate() {
        let what = || format!("action {}", action_names.get(i).map_or("?", |s| s.as_str()));
        let r = a.as_ref().ok_or(Unsupported("not lowered".into()));
        let mixing = cx.mixing_stmt(a.as_ref(), false);
        let (id, ok, mixed) = cx.define(
            &mut ctx,
            &mut fbc,
            &format!("act_{i}"),
            Kind::Action,
            vec![(mixing, Box::new(|g: &mut Gen| g.action(r?)))],
            what,
            &mut code_bytes,
        )?;
        native.actions.push(ok);
        native.mixed_actions.push(mixed);
        act_ids.push(id);
    }
    let mut inv_ids = Vec::new();
    for (i, p) in invariants.iter().enumerate() {
        let what = || format!("invariant {}", inv_names.get(i).map_or("?", |s| s.as_str()));
        let (id, ok, mixed) = cx.define_pred(&mut ctx, &mut fbc, &format!("inv_{i}"), Kind::Invariant, p, what, &mut code_bytes)?;
        native.invariants.push(ok);
        native.mixed_invariants.push(mixed);
        inv_ids.push(id);
    }
    let mut ap_ids = Vec::new();
    for (i, p) in aprops.iter().enumerate() {
        let (id, ok, mixed) = cx.define_pred(
            &mut ctx,
            &mut fbc,
            &format!("aprop_{i}"),
            Kind::ActionProperty,
            p,
            || format!("action property {}", p.name),
            &mut code_bytes,
        )?;
        native.action_properties.push(ok);
        native.mixed_action_properties.push(mixed);
        ap_ids.push(id);
    }
    native.mixed = [native.mixed_init]
        .iter()
        .chain(&native.mixed_actions)
        .chain(&native.mixed_invariants)
        .chain(&native.mixed_action_properties)
        .filter(|m| **m)
        .count();
    if let Some(r) = &cx.regions {
        r.finish()?;
    }

    // ABI entry points.
    let ptr = I64;
    let sig = |cx: &Cx, params: &[types::Type], ret: types::Type| {
        let mut s = cx.module.make_signature();
        s.params.extend(params.iter().map(|t| AbiParam::new(*t)));
        s.returns.push(AbiParam::new(ret));
        s
    };
    let words = ty.layout.words;
    let tlx_init = cx.trampoline(&mut ctx, &mut fbc, "tlx_init", sig(&cx, &[ptr, ptr], I32), init_id, &mut code_bytes)?;
    let tlx_next = cx.dispatch_actions(
        &mut ctx,
        &mut fbc,
        "tlx_next",
        sig(&cx, &[ptr, ptr, ptr, I32], I32),
        &act_ids,
        &native.actions,
        words,
        &mut code_bytes,
    )?;
    let tlx_inv = cx.dispatch(
        &mut ctx,
        &mut fbc,
        "tlx_invariant",
        sig(&cx, &[ptr, ptr, ptr, I32], I32),
        &inv_ids,
        &native.invariants,
        &[0, 1, 2],
        &mut code_bytes,
    )?;
    let tlx_ap = cx.dispatch(
        &mut ctx,
        &mut fbc,
        "tlx_action_property",
        sig(&cx, &[ptr, ptr, ptr, ptr, I32], I32),
        &ap_ids,
        &native.action_properties,
        &[0, 1, 2, 3],
        &mut code_bytes,
    )?;

    cx.flush(&mut code_bytes, &isa_key, cache)?;
    cx.module.finalize_definitions().map_err(|e| e.to_string())?;
    let f = |id: FuncId| cx.module.get_finalized_function(id);
    // SAFETY: the functions were defined with the signatures of the ABI
    // entry points.
    let entry = unsafe {
        EntryPoints {
            init: std::mem::transmute::<*const u8, tlx_native::native::InitFn>(f(tlx_init)),
            next: std::mem::transmute::<*const u8, tlx_native::native::NextFn>(f(tlx_next)),
            inv: std::mem::transmute::<*const u8, tlx_native::native::InvFn>(f(tlx_inv)),
            aprop: Some(std::mem::transmute::<*const u8, tlx_native::native::APropFn>(f(tlx_ap))),
            n_regions,
            regions_hash,
            refops: refops.map(|t| t as std::sync::Arc<dyn tlx_native::mixed::RefOps>),
        }
    };
    let Cx { module, statics, .. } = cx;
    let keep = Keep { module: Some(module), _statics: statics };
    // SAFETY: the entry points implement the ABI for these sizes and live
    // as long as `keep`.
    let lib = unsafe { NativeLib::from_entry_points(Box::new(keep), words, action_names.to_vec(), inv_names.to_vec(), entry) };
    Ok(JitLibrary { lib, native, compile_time: t0.elapsed(), code_bytes })
}

/// Only the fingerprint function of `words`-word states (for tests); the
/// first element keeps the code alive.
#[cfg(test)]
pub fn fingerprint_fn(words: usize) -> Result<(Box<dyn std::any::Any>, unsafe extern "C" fn(*const u64) -> u64), String> {
    let (flags, _) = isa_flags();
    let isa = cranelift_native::builder().map_err(|e| e.to_string())?.finish(flags).map_err(|e| e.to_string())?;
    let mut module = JITModule::new(JITBuilder::with_isa(isa, default_libcall_names()));
    let mut fbc = FunctionBuilderContext::new();
    let mut ctx = module.make_context();
    let id = define_fingerprint(&mut module, &mut ctx, &mut fbc, words, &mut 0)?;
    module.finalize_definitions().map_err(|e| e.to_string())?;
    // SAFETY: defined with this signature.
    let f = unsafe { std::mem::transmute::<*const u8, unsafe extern "C" fn(*const u64) -> u64>(module.get_finalized_function(id)) };
    Ok((Box::new(Keep { module: Some(module), _statics: SharedStatics::default() }), f))
}

impl<'t> Cx<'t> {
    /// Compile the function translated into `ctx` as `id`: later, with the
    /// others, in parallel (`flush`); at once when its machine code is
    /// printed (`TLX_JIT_DISASM`).
    fn compile(&mut self, ctx: &mut Context, id: FuncId, code_bytes: &mut usize) -> Result<(), String> {
        // `TLX_JIT_DISASM`: print the machine code of every function.
        let disasm = diag::enabled(Topic::Jit);
        if !disasm {
            let func = std::mem::replace(&mut ctx.func, cranelift_codegen::ir::Function::new());
            self.pending.push((id, func));
            self.module.clear_context(ctx);
            return Ok(());
        }
        ctx.set_disasm(disasm);
        self.module.define_function(id, ctx).map_err(|e| format!("{e:?}"))?;
        *code_bytes += ctx.compiled_code().map_or(0, |c| c.code_info().total_size as usize);
        if disasm {
            if let Some(v) = ctx.compiled_code().and_then(|c| c.vcode.as_ref()) {
                diag::emit(Topic::Jit, format_args!("function {id} ({}):\n{v}", ctx.func.name));
            }
        }
        self.module.clear_context(ctx);
        Ok(())
    }

    /// Compile the pending functions on several threads (Cranelift compiles
    /// a function independently of the others: calls and statics are
    /// relocations) and define them in the module, as `define_function`
    /// does: the same code, alignment and relocations. Functions whose exact
    /// `(isa_key, user_namespaces, FunctionStencil)` already exists in `cache`
    /// reuse their compiled machine bytes with relocations remapped to this
    /// module's ids.
    fn flush(&mut self, code_bytes: &mut usize, isa_key: &str, mut cache: Option<&mut JitCache>) -> Result<(), String> {
        type Compiled = Result<(u64, Vec<u8>, Vec<FinalizedMachReloc>), String>;
        let pending = std::mem::take(&mut self.pending);
        if pending.is_empty() {
            return Ok(());
        }
        let mut misses: Vec<(FuncId, cranelift_codegen::ir::Function, u64, Vec<u32>)> = Vec::new();
        let mut reused = 0u64;
        for (id, func) in pending {
            let namespaces: Vec<u32> = func.params.user_named_funcs().values().map(|n| n.namespace).collect();
            let hash = stencil_hash(isa_key, &namespaces, &func.stencil);
            let hit = cache.as_ref().and_then(|c| {
                c.entries.get(&hash)?.iter().find(|e| e.isa_key == isa_key && e.namespaces == namespaces && e.stencil == func.stencil)
            });
            if let Some(entry) = hit {
                let relocs: Vec<ModuleReloc> = entry.relocs.iter().map(|r| ModuleReloc::from_mach_reloc(r, &func, id)).collect();
                *code_bytes += entry.bytes.len();
                self.module.define_function_bytes(id, entry.align, &entry.bytes, &relocs).map_err(|e| format!("{e:?}"))?;
                reused += 1;
            } else {
                misses.push((id, func, hash, namespaces));
            }
        }
        if reused > 0 {
            #[cfg(test)]
            if let Some(c) = cache.as_deref_mut() {
                c.hits += reused as usize;
            }
            tlx_runtime::stats::add_count("JIT functions reused from cache", reused);
        }
        if misses.is_empty() {
            return Ok(());
        }
        let isa = self.module.isa();
        let next = std::sync::atomic::AtomicUsize::new(0);
        let threads = std::thread::available_parallelism().map_or(1, |n| n.get()).min(JIT_THREADS).min(misses.len());
        let compile_one = |(_, func, _, _): &(FuncId, cranelift_codegen::ir::Function, u64, Vec<u32>)| -> Compiled {
            let mut ctx = Context::for_function(func.clone());
            let align = ctx.compile(isa, &mut Default::default()).map_err(|e| format!("{e:?}"))?.buffer.alignment as u64;
            let code = ctx.compiled_code().expect("compiled");
            Ok((align, code.code_buffer().to_vec(), code.buffer.relocs().to_vec()))
        };
        let mut out: Vec<Option<Compiled>> = (0..misses.len()).map(|_| None).collect();
        let results = std::sync::Mutex::new(&mut out);
        std::thread::scope(|s| {
            for _ in 0..threads {
                s.spawn(|| loop {
                    let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    let Some(f) = misses.get(i) else { break };
                    let r = compile_one(f);
                    results.lock().unwrap()[i] = Some(r);
                });
            }
        });
        for ((id, func, hash, namespaces), r) in misses.into_iter().zip(out) {
            let (align, bytes, mach_relocs) = r.expect("every pending function was compiled")?;
            let relocs: Vec<ModuleReloc> = mach_relocs.iter().map(|r| ModuleReloc::from_mach_reloc(r, &func, id)).collect();
            *code_bytes += bytes.len();
            self.module.define_function_bytes(id, align, &bytes, &relocs).map_err(|e| format!("{e:?}"))?;
            if let Some(c) = cache.as_deref_mut() {
                c.entries.entry(hash).or_default().push(CachedFn {
                    isa_key: isa_key.to_string(),
                    namespaces,
                    stencil: func.stencil,
                    align,
                    bytes,
                    relocs: mach_relocs,
                });
            }
        }
        Ok(())
    }

    /// Declare and define `name` of `kind` with the body made by the first
    /// of `bodies` that translates (each with whether it is generated in
    /// mixed mode), or as a stub returning UNSUPPORTED. Returns its id,
    /// whether it is native and whether it calls regions.
    #[allow(clippy::type_complexity, clippy::too_many_arguments)]
    fn define<'b>(
        &mut self,
        ctx: &mut Context,
        fbc: &mut FunctionBuilderContext,
        name: &str,
        kind: Kind,
        bodies: Vec<(bool, Box<dyn FnOnce(&mut Gen) -> R<()> + 'b>)>,
        what: impl Fn() -> String,
        code_bytes: &mut usize,
    ) -> Result<(FuncId, bool, bool), String> {
        let sig = kind.signature(self);
        let id = self.module.declare_function(name, Linkage::Local, &sig).map_err(|e| e.to_string())?;
        let mut done = None;
        let n = bodies.len();
        for (k, (mixing, body)) in bodies.into_iter().enumerate() {
            ctx.func.signature = sig.clone();
            ctx.func.name = UserFuncName::user(0, id.as_u32());
            let calls = self.region_calls();
            let r = {
                let mut g = Gen::new(self, &mut ctx.func, fbc, kind);
                g.mixing = mixing;
                match body(&mut g) {
                    Ok(()) => {
                        g.finish();
                        Ok(())
                    }
                    Err(e) => Err(e),
                }
            };
            match r {
                Ok(()) => {
                    done = Some(self.region_calls() > calls);
                    break;
                }
                Err(Unsupported(why)) => {
                    if diag::enabled(Topic::Cgen) {
                        let how = if k + 1 < n { "not mixed" } else { "not native" };
                        diag::emit(Topic::Cgen, format_args!("jit: {} {how}: {why}", what()));
                    }
                    // The abandoned builder left its context mid-function.
                    *fbc = FunctionBuilderContext::new();
                    ctx.clear();
                }
            }
        }
        if done.is_none() {
            ctx.func.signature = sig;
            ctx.func.name = UserFuncName::user(0, id.as_u32());
            stub(&mut ctx.func, fbc);
        }
        self.compile(ctx, id, code_bytes)?;
        Ok((id, done.is_some(), done == Some(true)))
    }

    /// A predicate: in mixed mode if possible (as `CGen::pred`), else whole
    /// if possible, else its native prefix.
    #[allow(clippy::too_many_arguments)]
    fn define_pred(
        &mut self,
        ctx: &mut Context,
        fbc: &mut FunctionBuilderContext,
        name: &str,
        kind: Kind,
        p: &PredFn,
        what: impl Fn() -> String,
        code_bytes: &mut usize,
    ) -> Result<(FuncId, bool, bool), String> {
        let mut bodies: Vec<(bool, Box<dyn FnOnce(&mut Gen) -> R<()>>)> = Vec::new();
        if self.regions.as_ref().is_some_and(|r| r.oracle.mixes_pred(p)) {
            bodies.push((true, Box::new(|g: &mut Gen| g.pred_whole(p))));
        }
        let probe = self.probe(kind, &p.temps, |g| g.bool_expr(&p.body).map(|_| ()));
        if let Err(Unsupported(why)) = &probe {
            diag::emit(Topic::Cgen, format_args!("jit: predicate {} only partly native: {why}", p.name));
        }
        if probe.is_ok() {
            bodies.push((false, Box::new(|g: &mut Gen| g.pred_whole(p))));
        } else {
            bodies.push((false, Box::new(|g: &mut Gen| g.pred_prefix_fn(p))));
        }
        self.define(ctx, fbc, name, kind, bodies, what, code_bytes)
    }

    /// Whether an action / Init with body `f` is generated in mixed mode
    /// (as in `CGen::action`).
    fn mixing_stmt(&self, f: Option<&ActionFn>, init: bool) -> bool {
        match (&self.regions, f) {
            (Some(r), Some(f)) if init => r.oracle.mixes_action(f),
            (Some(r), Some(f)) => r.oracle.mixes_next(f),
            _ => false,
        }
    }

    fn region_calls(&self) -> usize {
        self.regions.as_ref().map_or(0, RegionCursor::calls)
    }

    /// Whether a region (still) has its call site at `site`.
    pub(super) fn has_region(&self, site: usize) -> bool {
        self.regions.as_ref().is_some_and(|r| r.has(site))
    }

    /// Whether a region (still) is called at `e` (either site of it).
    pub(super) fn has_region_at(&self, e: &Expr) -> bool {
        self.regions.as_ref().is_some_and(|r| r.has_at(e))
    }

    /// The next region called at `site` (`has_region`).
    pub(super) fn take_region(&mut self, site: usize) -> u32 {
        self.regions.as_mut().expect("mixed mode").take(site)
    }

    /// Whether `f` translates (into a scratch function of `kind`).
    pub(crate) fn probe(&mut self, kind: Kind, temps: &[Ty], f: impl FnOnce(&mut Gen) -> R<()>) -> R<()> {
        let mut func = cranelift_codegen::ir::Function::with_name_signature(UserFuncName::user(1, 0), kind.signature(self));
        let mut fbc = FunctionBuilderContext::new();
        let mut g = Gen::new(self, &mut func, &mut fbc, kind);
        g.set_temps(temps);
        f(&mut g)
    }

    /// The compiled functions (`Typing::funcs`) that can be native: as
    /// `CGen::functions`, a function calling a non-native one is not native
    /// (fixpoint), then all native ones are defined.
    fn functions(&mut self, ctx: &mut Context, fbc: &mut FunctionBuilderContext, code_bytes: &mut usize) -> Result<(), String> {
        let n = self.ty.funcs.len();
        self.fn_native = vec![true; n];
        for i in 0..n {
            let sig = match Kind::Func(i as u32).try_signature(self) {
                Ok(s) => s,
                Err(_) => {
                    self.fn_native[i] = false;
                    self.module.make_signature()
                }
            };
            let id = self.module.declare_function(&format!("fn_{i}"), Linkage::Local, &sig).map_err(|e| e.to_string())?;
            self.fn_ids.push(id);
        }
        // A function calling a non-native one is not native; re-probe the
        // survivors until no further function is rejected (the shared
        // rejection fixpoint, `fast::rejection_fixpoint`). This backend owns
        // the probe, the signature pre-pass/ids above and the definition
        // pass below.
        crate::exec::fast::rejection_fixpoint(|| {
            let mut changed = false;
            for i in 0..n {
                if !self.fn_native[i] {
                    continue;
                }
                let f = self.ty.funcs[i].clone();
                if let Err(Unsupported(why)) = self.probe(Kind::Func(i as u32), &f.temps, |g| g.function_body(&f)) {
                    diag::emit(Topic::Cgen, format_args!("jit: function {} not native: {why}", f.name));
                    self.fn_native[i] = false;
                    changed = true;
                }
            }
            changed
        });
        for i in 0..n {
            if !self.fn_native[i] {
                continue;
            }
            let f = self.ty.funcs[i].clone();
            let kind = Kind::Func(i as u32);
            let id = self.fn_ids[i];
            ctx.func.signature = kind.signature(self);
            ctx.func.name = UserFuncName::user(0, id.as_u32());
            {
                let mut g = Gen::new(self, &mut ctx.func, fbc, kind);
                g.set_temps(&f.temps);
                g.function_body(&f).map_err(|e| format!("function {}: {}", f.name, e.0))?;
                g.finish();
            }
            self.compile(ctx, id, code_bytes)?;
        }
        Ok(())
    }

    /// `name(args) { return target(args); }`
    fn trampoline(
        &mut self,
        ctx: &mut Context,
        fbc: &mut FunctionBuilderContext,
        name: &str,
        sig: Signature,
        target: FuncId,
        code_bytes: &mut usize,
    ) -> Result<FuncId, String> {
        let id = self.module.declare_function(name, Linkage::Local, &sig).map_err(|e| e.to_string())?;
        ctx.func.signature = sig;
        ctx.func.name = UserFuncName::user(0, id.as_u32());
        {
            let mut b = FunctionBuilder::new(&mut ctx.func, fbc);
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            let args = b.block_params(entry).to_vec();
            let callee = self.module.declare_func_in_func(target, b.func);
            let call = b.ins().call(callee, &args);
            let r = b.inst_results(call)[0];
            b.ins().return_(&[r]);
            b.seal_all_blocks();
            b.finalize();
        }
        self.compile(ctx, id, code_bytes)?;
        Ok(id)
    }

    /// `tlx_next(h, cx, s0, sel)`: allocates the next-state buffer `s1` once
    /// here and passes `(h, cx, s0, s1)` to `act_sel`, keeping `act_i`
    /// independent of the total state width `words` so unchanged actions hit
    /// `JitCache` across layout-miss restarts.
    #[allow(clippy::too_many_arguments)]
    fn dispatch_actions(
        &mut self,
        ctx: &mut Context,
        fbc: &mut FunctionBuilderContext,
        name: &str,
        sig: Signature,
        targets: &[FuncId],
        native: &[bool],
        words: usize,
        code_bytes: &mut usize,
    ) -> Result<FuncId, String> {
        let id = self.module.declare_function(name, Linkage::Local, &sig).map_err(|e| e.to_string())?;
        ctx.func.signature = sig;
        ctx.func.name = UserFuncName::user(0, id.as_u32());
        {
            let mut b = FunctionBuilder::new(&mut ctx.func, fbc);
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            let params = b.block_params(entry).to_vec();
            let sel = params[3];
            let ss = b.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, (words.max(1) * 8) as u32, 3));
            let s1 = b.ins().stack_addr(I64, ss, 0);
            let args = [params[0], params[1], params[2], s1];
            let default = b.create_block();
            let mut sw = Switch::new();
            let mut cases = Vec::new();
            for (i, t) in targets.iter().enumerate() {
                if native[i] {
                    let blk = b.create_block();
                    sw.set_entry(i as u128, blk);
                    cases.push((blk, *t));
                }
            }
            sw.emit(&mut b, sel, default);
            for (blk, t) in cases {
                b.switch_to_block(blk);
                let callee = self.module.declare_func_in_func(t, b.func);
                let call = b.ins().call(callee, &args);
                let r = b.inst_results(call)[0];
                b.ins().return_(&[r]);
            }
            b.switch_to_block(default);
            let u = b.ins().iconst(I32, UNSUPPORTED as i64);
            b.ins().return_(&[u]);
            b.seal_all_blocks();
            b.finalize();
        }
        self.compile(ctx, id, code_bytes)?;
        Ok(id)
    }

    /// `switch (sel) { case i: return f_i(args...); default: return UNSUPPORTED; }`
    /// where `sel` is the last parameter and `pass` the indices of the
    /// parameters passed on. Stub cases return UNSUPPORTED directly.
    #[allow(clippy::too_many_arguments)]
    fn dispatch(
        &mut self,
        ctx: &mut Context,
        fbc: &mut FunctionBuilderContext,
        name: &str,
        sig: Signature,
        targets: &[FuncId],
        native: &[bool],
        pass: &[usize],
        code_bytes: &mut usize,
    ) -> Result<FuncId, String> {
        let id = self.module.declare_function(name, Linkage::Local, &sig).map_err(|e| e.to_string())?;
        ctx.func.signature = sig;
        ctx.func.name = UserFuncName::user(0, id.as_u32());
        {
            let mut b = FunctionBuilder::new(&mut ctx.func, fbc);
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            let params = b.block_params(entry).to_vec();
            let sel = *params.last().unwrap();
            let args: Vec<_> = pass.iter().map(|i| params[*i]).collect();
            let default = b.create_block();
            let mut sw = Switch::new();
            let mut cases = Vec::new();
            for (i, t) in targets.iter().enumerate() {
                if native[i] {
                    let blk = b.create_block();
                    sw.set_entry(i as u128, blk);
                    cases.push((blk, *t));
                }
            }
            sw.emit(&mut b, sel, default);
            for (blk, t) in cases {
                b.switch_to_block(blk);
                let callee = self.module.declare_func_in_func(t, b.func);
                let call = b.ins().call(callee, &args);
                let r = b.inst_results(call)[0];
                b.ins().return_(&[r]);
            }
            b.switch_to_block(default);
            let u = b.ins().iconst(I32, UNSUPPORTED as i64);
            b.ins().return_(&[u]);
            b.seal_all_blocks();
            b.finalize();
        }
        self.compile(ctx, id, code_bytes)?;
        Ok(id)
    }
}

/// Define a fingerprint function: `tlx_fp_words(s, n)` (tlx_abi.h) unrolled.
#[cfg(test)]
fn define_fingerprint(
    module: &mut JITModule,
    ctx: &mut Context,
    fbc: &mut FunctionBuilderContext,
    n: usize,
    code_bytes: &mut usize,
) -> Result<FuncId, String> {
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(I64));
    sig.returns.push(AbiParam::new(I64));
    let id = module.declare_function("fp_words_test", Linkage::Local, &sig).map_err(|e| e.to_string())?;
    ctx.func.signature = sig;
    ctx.func.name = UserFuncName::user(0, id.as_u32());
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, fbc);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        let s = b.block_params(entry)[0];
        let h = gen::fp_words_ir(&mut b, s, n);
        b.ins().return_(&[h]);
        b.seal_all_blocks();
        b.finalize();
    }
    module.define_function(id, ctx).map_err(|e| format!("{e:?}"))?;
    *code_bytes += ctx.compiled_code().map_or(0, |c| c.code_info().total_size as usize);
    module.clear_context(ctx);
    Ok(id)
}

/// A function returning UNSUPPORTED.
fn stub(func: &mut cranelift_codegen::ir::Function, fbc: &mut FunctionBuilderContext) {
    let mut b = FunctionBuilder::new(func, fbc);
    let entry = b.create_block();
    b.append_block_params_for_function_params(entry);
    b.switch_to_block(entry);
    let u = b.ins().iconst(I32, UNSUPPORTED as i64);
    b.ins().return_(&[u]);
    b.seal_all_blocks();
    b.finalize();
}

#[cfg(test)]
mod tests {
    /// The JIT fingerprint is `tlx_fp_words` (tlx_abi.h): the reference
    /// values computed with cc, and the host's `fp_words` on longer states.
    #[test]
    fn fingerprint_matches_c() {
        let s: Vec<u64> = (0..23u64).map(|i| i * 0x1234567 + 7).collect();
        for line in include_str!("../../../tlx-native/tests/fp_c.txt").lines() {
            let (n, fp) = line.split_once(' ').unwrap();
            let n: usize = n.parse().unwrap();
            let (_keep, f) = super::fingerprint_fn(n).unwrap();
            // SAFETY: `s` has at least `n` words.
            assert_eq!(unsafe { f(s.as_ptr()) }.to_string(), fp, "{n} words");
        }
        let long: Vec<u64> = (0..300u64).map(|i| i.wrapping_mul(0x9e3779b97f4a7c15) ^ (i << 7)).collect();
        for n in [24, 31, 64, 65, 199, 300] {
            let (_keep, f) = super::fingerprint_fn(n).unwrap();
            // SAFETY: `long` has at least `n` words.
            assert_eq!(unsafe { f(long.as_ptr()) }, tlx_native::fp_words(&long[..n]), "{n} words");
        }
    }
}
