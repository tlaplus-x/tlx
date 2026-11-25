//! The native code of an `EncModel`: a JIT library and the generated C
//! library (`TLX_JIT`, docs/design.md §6.6).
//!
//! By default (`TLX_JIT=tier`) the model's functions are compiled with the
//! Cranelift JIT first (in milliseconds, before the search starts). The C
//! library is built with `-O2` in the background only once the search has
//! run for a while (`TLX_CC_DELAY_MS`), so that short runs never pay for
//! `cc`; it replaces the JIT library when loaded (its code is 4-25%
//! faster). A C library already in the cache is loaded at once instead
//! (a few ms), without JIT. If `cc` is missing or fails, the JIT
//! library stays. Both libraries call the same host regions (mixed mode),
//! so either can run at any time.
//!
//! Without the JIT (`TLX_JIT=0`, or a model the JIT does not compile as the
//! C code does) the C build and the loading of the library (on macOS the
//! first `dlopen` of a new library alone takes ~0.4s) run in the background
//! at once: until the library is ready the model runs as lowered IR or
//! interpreted, which gives the same results. Large sources are then also
//! built quickly with `-O0` (beside the `-O2` build, which replaces the
//! quick library when ready). `TLX_JIT=1` uses the JIT library only.
//!
//! A C build outlives tlx and lands in the cache, and concurrent runs share
//! it (see `tlx_native::build::start`). A run that ends before the delay has
//! passed starts the build at its end without waiting when the JIT compilation
//! took at least `TLX_CC_AT_EXIT_MS` (`at_exit_build`; after a layout-miss
//! restart the whole run so far counts), so that a short first run still fills
//! the cache for the next one.
//!
//! A model the driver discards for a widening restart is different: its
//! layout is replaced, so the library being built for it could never be
//! loaded, and one large translation unit per attempt would compete with
//! the search for the machine (`cancel_builds`, called from `EncModel::drop`
//! while the model is still `restartable`). That build is stopped instead of
//! being left to finish.
//!
//! In mixed mode the libraries come with their region table (the host side
//! of the regions they call), which they are loaded against.

use std::ops::Deref;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Condvar, Mutex, OnceLock};
use std::time::{Duration, Instant};

use tlx_eval::InterpModel;
use tlx_native::build::{self as cc, BuildOptions};
use tlx_native::mixed::{Args, Out, RefOps, RegionEnv, RegionError, RegionSig, Regions};
use tlx_native::native::NativeLib;
use tlx_runtime::stats::{self, Metric};
use tlx_runtime::Model;

use super::mixed::RegionTable;
use crate::cgen::CGen;
use crate::exec::refops::RefOpTable;
use crate::ir::ActionFn;
use crate::native_plan::{Mixed, NativeSet, RegionOracle};
use crate::settings::{Jit, Settings};
use crate::types::Typing;

/// Sources at least this large (bytes) are first built with `-O0`: `-O2`
/// takes ~10x longer on them (seconds), `-O0` code is still much faster
/// than IR.
const QUICK_FIRST_BYTES: usize = 256 << 10;

/// The native libraries of a model and which of its functions are native.
pub(super) struct Native {
    pub has: NativeSet,
    /// The regions the library calls (None: it calls none).
    pub regions: Option<RegionTable>,
    /// The value store operations the library calls (None: it calls none).
    refops: Option<Arc<RefOpTable>>,
    /// The `-O2` library (`TLX_JIT=1`: the JIT library), once loaded.
    opt: OnceLock<NativeLib>,
    /// The JIT library, or the `-O0` library of a large source, once
    /// loaded.
    quick: OnceLock<NativeLib>,
    /// The owning model is gone: skip remaining build stages (wakes up a
    /// delayed build).
    abandoned: AtomicBool,
    /// The driver discarded this model's layout (a layout miss widens it):
    /// the library being built can never be loaded, so a running build is
    /// stopped (`cancel_builds`). Unlike `abandoned`, this also stops a
    /// build already compiling.
    cancelled: AtomicBool,
    wake: (Mutex<()>, Condvar),
    /// A build stage has started.
    started: AtomicBool,
    /// No build stage is pending.
    done: AtomicBool,
    /// Build events to log (readiness, failure).
    events: Mutex<Vec<String>>,
    /// The generated C source (for the build started at the end of a run).
    src: Arc<str>,
    /// `TLX_CC_AT_EXIT_MS`: at least this much JIT compilation time starts
    /// the C build at the end of a short run (see `at_exit_build`).
    cc_at_exit: Duration,
    /// The JIT compilation time (µs; 0 when the JIT did not compile).
    jit_us: AtomicU64,
    /// The model follows a layout-miss restart (`set_restarted`).
    restarted: AtomicBool,
    t0: Instant,
}

impl Native {
    /// The best library loaded so far.
    #[inline]
    pub fn lib(&self) -> Option<&NativeLib> {
        self.opt.get().or_else(|| self.quick.get())
    }

    /// Stable identity of the selected write-once library slot within a model.
    pub(super) fn lib_slot(&self) -> Option<usize> {
        if self.opt.get().is_some() {
            Some(2)
        } else {
            self.quick.get().map(|_| 1)
        }
    }

    /// This model follows a layout-miss restart (see `at_exit_build`).
    pub(super) fn set_restarted(&self) {
        self.restarted.store(true, Ordering::Relaxed);
    }

    /// The driver discarded this model's layout (a layout miss widened it):
    /// its C library could never be loaded, so do not start a delayed build
    /// and stop the process of a build already running. The JIT library
    /// stays, so the results are unchanged (the C library is the faster one,
    /// not a different one).
    pub(super) fn cancel_builds(&self) {
        self.cancelled.store(true, Ordering::Release);
        let (m, cv) = &self.wake;
        let _g = m.lock().unwrap();
        cv.notify_all();
    }

    /// Whether `cancel_builds` was called.
    fn is_cancelled(&self) -> bool {
        self.cancelled.load(Ordering::Acquire)
    }

    /// Build events since the last call, and whether a build is still
    /// running (a build waiting for its delay is not).
    pub fn take_events(&self) -> (Vec<String>, bool) {
        let ev = std::mem::take(&mut *self.events.lock().unwrap());
        (ev, self.started.load(Ordering::Acquire) && !self.done.load(Ordering::Acquire))
    }

    /// Wait until `delay` has passed, the model is abandoned, or its builds
    /// were cancelled; whether the build must not start.
    fn wait(&self, delay: Duration) -> bool {
        let (m, cv) = &self.wake;
        let g = m.lock().unwrap();
        let _g = cv.wait_timeout_while(g, delay, |_| !(self.abandoned.load(Ordering::Acquire) || self.is_cancelled())).unwrap();
        self.abandoned.load(Ordering::Acquire) || self.is_cancelled()
    }

    /// Build and load `src` in stages (`-O0` first if large and not
    /// cached, then `-O2`); stops at the first failure, when abandoned, or
    /// when the layout was discarded (`cancel_builds`, see
    /// `Build::wait_or_cancel`).
    fn build_stages(&self, src: &str, quick_first: bool) {
        let opt = BuildOptions::default();
        let quick = BuildOptions { opt: "-O0".into(), ..opt.clone() };
        let stages: &[(&BuildOptions, &OnceLock<NativeLib>)] =
            if quick_first { &[(&quick, &self.quick), (&opt, &self.opt)] } else { &[(&opt, &self.opt)] };
        // With `-O0` first, the `-O2` build starts at once beside it, so that
        // it reaches the cache even if the run ends first (a build outlives
        // tlx, see `cc::start`).
        let mut opt_build = quick_first.then(|| cc::start(src, &opt).ok()).flatten();
        for (o, slot) in stages {
            if self.abandoned.load(Ordering::Relaxed) || self.is_cancelled() {
                // (The `-O0`-first path starts the `-O2` build beside the
                // first stage: stop that one too when the layout is gone.)
                self.stop(opt_build.take());
                break;
            }
            self.started.store(true, Ordering::Release);
            let cached = stats::on() && cc::cached(src, o).is_some();
            let t0 = Instant::now();
            let built = match opt_build.take_if(|_| o.opt == opt.opt) {
                Some(b) => b.wait_or_cancel(&self.cancelled),
                None => cc::start(src, o).and_then(|b| b.wait_or_cancel(&self.cancelled)),
            };
            stats::add_secs(&format!("C build {}", o.opt), t0.elapsed());
            stats::set(&format!("C build {} cache", o.opt), Metric::Text(if cached { "hit" } else { "miss" }.into()));
            if self.is_cancelled() {
                self.stop(opt_build.take());
                break;
            }
            let t1 = Instant::now();
            let check = self.regions.as_ref().map(TableCheck);
            let refops = self.refops.clone().map(|t| t as Arc<dyn RefOps>);
            // SAFETY: src comes only from CGen over verified IR, with self's
            // region/refop tables; generated buffers follow those signatures.
            // We trust the configured compiler/cache and their path resolution.
            let loaded = built.and_then(|p| unsafe { NativeLib::load_with(&p, check.as_ref().map(|c| c as &dyn Regions), refops) });
            stats::add_secs(&format!("native {} load", o.opt), t1.elapsed());
            match loaded {
                Ok(lib) => {
                    let _ = slot.set(lib);
                    stats::set(&format!("native {} ready at (since start)", o.opt), Metric::Secs(stats::since_start().as_secs_f64()));
                    self.event(format!("native code ({}) ready after {:.2}s", o.opt, self.t0.elapsed().as_secs_f64()));
                }
                Err(e) if self.lib().is_some() => {
                    self.event(format!("C build failed, keeping the JIT code: {e}"));
                    break;
                }
                Err(e) => {
                    self.event(format!("native code disabled: {e}"));
                    break;
                }
            }
        }
        self.done.store(true, Ordering::Release);
    }

    /// The value store operations the library calls.
    pub(super) fn refops(&self) -> Option<&RefOpTable> {
        self.refops.as_deref()
    }

    /// Stop a build started beside the current stage (the `-O2` build of the
    /// `-O0`-first path) when this model's layout was discarded.
    fn stop(&self, pending: Option<cc::Build>) {
        if let Some(b) = pending {
            let _ = b.wait_or_cancel(&self.cancelled);
        }
    }

    fn event(&self, e: String) {
        self.events.lock().unwrap().push(e);
    }

    /// The run ended before the delayed C build started (`TLX_CC_DELAY_MS`):
    /// if the JIT compilation was expensive (`TLX_CC_AT_EXIT_MS`), start the
    /// `-O2` build now without waiting, so that it lands in the cache for the
    /// next run (the build outlives tlx: `cc::start`). No-op without the JIT,
    /// when a build already started or finished, when the threshold is off,
    /// when the library is already cached, or when there is no compiler.
    ///
    /// A model that follows a layout-miss restart (`set_restarted`) counts
    /// the whole run so far instead of its own JIT compilation: each attempt
    /// compiles the JIT again (cheaply), the restarts cancelled the delayed
    /// builds of the earlier layouts, and the last attempt is often shorter
    /// than the delay, so that without this the layout the run settled on
    /// would never get a C library and every run would restart again with
    /// only JIT code.
    pub(super) fn at_exit_build(&self) {
        if self.cc_at_exit.is_zero() || self.started.load(Ordering::Acquire) || self.done.load(Ordering::Acquire) || self.is_cancelled() {
            return;
        }
        let spent = if self.restarted.load(Ordering::Relaxed) {
            stats::since_start()
        } else {
            Duration::from_micros(self.jit_us.load(Ordering::Acquire))
        };
        if spent < self.cc_at_exit {
            return;
        }
        let opts = BuildOptions::default();
        if cc::cached(&self.src, &opts).is_some() || !cc::compiler_available(&opts.cc) {
            return;
        }
        let _ = cc::start(&self.src, &opts);
    }
}

/// Why the compiled tier would have no native code at all, if so: no JIT
/// (a build without the `jit` feature, or `TLX_JIT=0`) and no C compiler.
/// The default tier then checks with the interpreter instead (`-compile`
/// still runs the IR).
pub fn native_unavailable() -> Option<String> {
    let s = Settings::global();
    if s.jit != Jit::Off && cfg!(feature = "jit") {
        return None;
    }
    let cc = BuildOptions::default().cc;
    (!cc::compiler_available(&cc)).then(|| format!("no JIT and no C compiler ({cc} not found): checking with the interpreter"))
}

/// The model's handle on its `Native`: abandons pending builds on drop.
pub(super) struct NativeHandle(Arc<Native>);

impl Deref for NativeHandle {
    type Target = Native;
    fn deref(&self) -> &Native {
        &self.0
    }
}

impl Drop for NativeHandle {
    fn drop(&mut self) {
        let _g = self.0.wake.0.lock().unwrap();
        self.0.abandoned.store(true, Ordering::Release);
        self.0.wake.1.notify_all();
    }
}

/// Generate native code for `f`: JIT-compile it and build and load the C
/// library, in the background unless `sync` (see the module documentation).
/// None if nothing could be generated or (`sync`) the build failed; a note
/// says what is native.
/// `mixed`: generate in mixed mode.
pub(super) fn build(
    f: &crate::verify::Program<'_>,
    base: &InterpModel,
    settings: &Settings,
    mixed: Option<Mixed>,
    notes: &mut Vec<String>,
) -> Option<NativeHandle> {
    let sync = settings.native_sync;
    let t0 = Instant::now();
    let oracle = mixed.as_ref().map(|m| m.oracle);
    let refops = RefOpTable::of(f);
    let mut gen = CGen::new(f).with_refops(refops.clone());
    if let Some(m) = mixed {
        gen = gen.with_mixed(m);
    }
    let gen = gen.library(base.action_names(), base.invariant_names());
    stats::add_secs("C generation", t0.elapsed());
    let plan = gen.plan;
    if !plan.regions.is_empty() {
        stats::set("host regions", Metric::Count(plan.regions.len() as u64));
    }
    stats::set("C source bytes", Metric::Count(gen.src.len() as u64));
    if !plan.native.any() {
        return None;
    }
    let src: Arc<str> = Arc::from(gen.src);
    let native = Arc::new(Native {
        has: plan.native,
        regions: (!plan.regions.is_empty()).then_some(plan.regions),
        refops,
        opt: OnceLock::new(),
        quick: OnceLock::new(),
        abandoned: AtomicBool::new(false),
        cancelled: AtomicBool::new(false),
        wake: (Mutex::new(()), Condvar::new()),
        started: AtomicBool::new(false),
        done: AtomicBool::new(false),
        events: Mutex::new(Vec::new()),
        src: src.clone(),
        cc_at_exit: settings.cc_at_exit,
        jit_us: AtomicU64::new(0),
        restarted: AtomicBool::new(false),
        t0: Instant::now(),
    });
    let summary = |n: &Native| summary(&n.has, n.regions.as_ref().map_or(0, RegionTable::len));
    let mode = settings.jit;
    // A synchronous C build, or loading a cached C library (a few ms: it
    // was loaded when it was built), replaces the JIT library at once: no
    // JIT then, unless the C library fails.
    let cached = mode == Jit::Tier && cc::cached(&src, &BuildOptions::default()).is_some();
    let sync = sync || cached;
    let mut jit_lib = None;
    if mode == Jit::Only || (mode == Jit::Tier && !sync) {
        jit_lib = jit(&native, f, base, oracle, &plan.sites, notes);
    }
    if let Some(lib) = jit_lib {
        if mode == Jit::Only {
            let _ = native.opt.set(lib);
            native.done.store(true, Ordering::Release);
            notes.push(summary(&native));
            return Some(NativeHandle(native));
        }
        let _ = native.quick.set(lib);
        stats::set("native JIT ready at (since start)", Metric::Secs(stats::since_start().as_secs_f64()));
        // The C library replaces it after a delay.
        let delay = settings.cc_delay;
        let n = native.clone();
        let spawned = tlx_base::stack::spawn(std::thread::Builder::new().name("tlx-cc".into()), move || {
            if delay.is_zero() || !n.wait(delay) {
                n.build_stages(&src, false);
            } else {
                n.done.store(true, Ordering::Release);
            }
        })
        .is_ok();
        if !spawned {
            native.done.store(true, Ordering::Release);
        }
        notes.push(summary(&native));
        return Some(NativeHandle(native));
    }
    if sync {
        native.build_stages(&src, false);
        let (events, _) = native.take_events();
        if native.lib().is_none() {
            // The C build failed: the JIT library then.
            let lib = if mode == Jit::Tier { jit(&native, f, base, oracle, &plan.sites, notes) } else { None };
            let Some(lib) = lib else {
                notes.extend(events);
                return None;
            };
            notes.extend(events.into_iter().map(|e| e.replace("native code disabled: ", "C build failed, using the JIT code: ")));
            let _ = native.opt.set(lib);
            notes.push(summary(&native));
            return Some(NativeHandle(native));
        }
    } else {
        let quick_first = src.len() >= QUICK_FIRST_BYTES && cc::cached(&src, &BuildOptions::default()).is_none();
        let n = native.clone();
        tlx_base::stack::spawn(std::thread::Builder::new().name("tlx-cc".into()), move || n.build_stages(&src, quick_first)).ok()?;
    }
    notes.push(summary(&native));
    Some(NativeHandle(native))
}

/// The region table a library is loaded against (only its size and hash
/// are checked: `HostRegions` evaluates the regions).
struct TableCheck<'a>(&'a RegionTable);

impl Regions for TableCheck<'_> {
    fn len(&self) -> u32 {
        self.0.len() as u32
    }
    fn hash(&self) -> u64 {
        self.0.hash()
    }
    fn sig(&self, rid: u32) -> &RegionSig {
        self.0.sig(rid)
    }
    fn eval(&self, _: u32, _: &Args<'_>, _: &mut RegionEnv<'_>) -> Result<Out, RegionError> {
        Err(RegionError("regions are not evaluated while loading".into()))
    }
}

/// JIT-compile the model (None unless its native functions and region
/// calls are the ones of the C library).
#[cfg(feature = "jit")]
#[allow(clippy::too_many_arguments)]
fn jit(
    native: &Native,
    f: &crate::verify::Program<'_>,
    base: &InterpModel,
    oracle: Option<&dyn RegionOracle>,
    sites: &[usize],
    notes: &mut Vec<String>,
) -> Option<NativeLib> {
    let regions = match (oracle, &native.regions) {
        (Some(oracle), Some(table)) => Some(crate::native_plan::RegionPlan { oracle, table, sites }),
        _ => None,
    };
    let r = crate::jit::library(f, regions, native.refops.clone(), base.action_names(), base.invariant_names());
    match r {
        Ok(j) => {
            stats::add_secs("JIT compile", j.compile_time);
            stats::set("JIT code bytes", Metric::Count(j.code_bytes as u64));
            native.jit_us.store(j.compile_time.as_micros().max(1) as u64, Ordering::Release);
            let (a, b) = (&j.native, &native.has);
            if a != b {
                notes.push(format!("JIT disabled: native functions differ from C ({a:?} vs {b:?})"));
                return None;
            }
            native.event(format!(
                "native code (JIT) ready after {:.3}s (compile {:.3}s)",
                native.t0.elapsed().as_secs_f64(),
                j.compile_time.as_secs_f64()
            ));
            Some(j.lib)
        }
        Err(e) => {
            notes.push(format!("JIT disabled: {e}"));
            None
        }
    }
}

#[cfg(not(feature = "jit"))]
fn jit(
    _: &Native,
    _: &crate::verify::Program<'_>,
    _: &InterpModel,
    _: Option<&dyn RegionOracle>,
    _: &[usize],
    notes: &mut Vec<String>,
) -> Option<NativeLib> {
    notes.push("TLX_JIT ignored: tlx was built without the `jit` feature".into());
    None
}

/// A library whose only action computes the VIEW (see
/// `Lowerer::lower_value_action`): JIT-compiled unless `TLX_JIT=0`, else
/// (or if the JIT fails) built with C; None if it is not native or the
/// build failed.
pub(super) fn build_view(typing: &Typing, f: &ActionFn, settings: &Settings, notes: &mut Vec<String>) -> Option<NativeLib> {
    let action = Some(f.clone());
    let actions = std::slice::from_ref(&action);
    let names = ["VIEW".to_string()];
    let verified = crate::verify::enforce(crate::verify::Program::view(typing, actions)).map_err(|e| notes.push(e)).ok()?;
    let refops = RefOpTable::of(&verified);
    let gen = CGen::new(&verified).with_refops(refops.clone()).library(&names, &[]);
    if !gen.plan.native.actions[0] {
        return None;
    }
    // `cfg!` (not `#[cfg]`) keeps `settings` used in a build without the
    // `jit` feature, where the block it guards is compiled out.
    if cfg!(feature = "jit") && settings.jit != Jit::Off {
        #[cfg(feature = "jit")]
        match crate::jit::library(&verified, None, refops.clone(), &names, &[]) {
            Ok(j) if j.native.actions[0] => {
                stats::add_secs("JIT compile (VIEW)", j.compile_time);
                return Some(j.lib);
            }
            Ok(_) => notes.push("JIT disabled for the VIEW: not native".into()),
            Err(e) => notes.push(format!("JIT disabled for the VIEW: {e}")),
        }
    }
    let t0 = Instant::now();
    let lib = tlx_native::build::build(&gen.src, &Default::default())
        // SAFETY: CGen emitted this VIEW from verified IR with these refops,
        // no regions and immutable metadata. Compiler/cache are trusted.
        .and_then(|p| unsafe { NativeLib::load_with(&p, None, refops.map(|t| t as Arc<dyn RefOps>)) });
    stats::add_secs("C build and load (VIEW)", t0.elapsed());
    match lib {
        Ok(lib) => Some(lib),
        Err(e) => {
            notes.push(format!("native VIEW disabled: {e}"));
            None
        }
    }
}

/// "native code: a/b actions, c/d invariants[, Init][, e/f action
/// properties][; mixed: m functions, r regions]".
fn summary(n: &NativeSet, regions: usize) -> String {
    let count = |v: &[bool]| format!("{}/{}", v.iter().filter(|x| **x).count(), v.len());
    let mut s = format!("native code: {} actions, {} invariants", count(&n.actions), count(&n.invariants));
    if n.init {
        s += ", Init";
    }
    if !n.action_properties.is_empty() {
        s += &format!(", {} action properties", count(&n.action_properties));
    }
    if regions > 0 {
        s += &format!("; mixed: {} functions, {regions} regions", n.mixed);
    }
    s
}
