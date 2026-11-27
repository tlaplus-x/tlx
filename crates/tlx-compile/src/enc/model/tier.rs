//! Native and mixed-mode tier dispatch, adaptive per-function selection,
//! native statistics reporting, and deliberate mismatch injection.
//!
//! `EncModel` runs whole generated functions through the native library or,
//! for functions with host regions, through `mixed`; `choose` decides per
//! mixed function between native and fallback code from the adaptive
//! timings. The layout-miss and definition-shape checks live here because
//! they decide whether a native error widens the layout.

use std::ffi::c_int;
use std::sync::atomic::Ordering;
use std::time::Instant;

use tlx_native::mixed::MixedCx;
use tlx_native::native::{Mixed, NativeLib};
use tlx_runtime::stats::{self, Path};
use tlx_runtime::{Model, ModelError};

use super::{EState, EncModel, MIXED};
use crate::cgen::UNSUPPORTED;
use crate::enc::adapt::{self, Choice, ACTION, STATE_PRED, TRANS_PRED};
use crate::enc::mixed::{FastRegions, HostRegions};
use crate::enc::native::Native;
use crate::settings::InjectKind;

impl EncModel {
    // ------------------------------------------------------------------
    // testing: deliberate mismatches

    /// Whether the current eligible result (of an injection of one of
    /// `kinds`) is the one to corrupt.
    pub(super) fn inject_now(&self, kinds: &[InjectKind]) -> Option<InjectKind> {
        let j = self.inject.filter(|j| kinds.contains(&j.kind))?;
        (self.inject_seen.fetch_add(1, Ordering::Relaxed) == j.after).then_some(j.kind)
    }

    /// Corrupt the compiled successors `buf` of `s` (if it is their turn).
    #[cold]
    pub(super) fn inject_successors(&self, s: &EState, buf: &mut Vec<Box<[u64]>>) {
        if buf.is_empty() {
            return;
        }
        match self.inject_now(&[InjectKind::Drop, InjectKind::Dup, InjectKind::Stale]) {
            Some(InjectKind::Drop) => {
                buf.pop();
            }
            Some(InjectKind::Dup) => buf.push(buf[buf.len() - 1].clone()),
            Some(InjectKind::Stale) => *buf.last_mut().unwrap() = s.words.clone(),
            _ => {}
        }
    }

    // ------------------------------------------------------------------
    // native functions

    pub(super) fn native_lib(&self, has: impl FnOnce(&Native) -> bool) -> Option<&NativeLib> {
        self.native.as_deref().filter(|n| has(n)).and_then(|n| n.lib())
    }

    /// Run `f` with the mixed-mode side of a call of the native library at
    /// level `level`: this worker's `MixedCx` and the library's regions.
    /// `func`: the function called (`adapt` kind and index), whose region
    /// evaluations the statistics count.
    fn mixed<R>(&self, level: u32, func: Option<(usize, usize)>, f: impl FnOnce(Mixed<'_>) -> R) -> R {
        let table = self.native.as_deref().and_then(|n| n.regions.as_ref()).expect("a library with regions");
        let fast = Some(FastRegions { prog: &self.fast.prog, progs: &self.fast_regions });
        let regions = HostRegions { ip: &self.base.ip, typing: &self.typing, table, memo: self.memo.exec_id(), fast };
        let gc_gen = self.store_gc_gen();
        MIXED.with(|m| match m.try_borrow_mut() {
            Ok(mut m) => {
                let (id, gen, cx) = &mut *m;
                // The decoded-state cache holds states of this model's layout
                // (and pre-GC handles become stale after a value-store sweep).
                if *id != self.id || *gen != gc_gen {
                    *id = self.id;
                    *gen = gc_gen;
                    cx.cache.clear();
                }
                let r = f(Mixed { cx: &mut *cx, regions: &regions, level });
                if stats::on() {
                    let (evals, errors) = table.drain_counts();
                    if let Some((kind, i)) = func {
                        stats::regions(kind, i, evals, errors);
                    }
                }
                r
            }
            // (Not expected: a native call within a native call.)
            Err(_) => f(Mixed { cx: &mut MixedCx::new(), regions: &regions, level }),
        })
    }

    /// `NativeLib::init_into`, with the library's regions if it has some.
    pub(super) fn lib_init(&self, lib: &NativeLib, buf: &mut Vec<Box<[u64]>>) -> c_int {
        if lib.n_regions() == 0 {
            return lib.init_into(buf);
        }
        self.mixed(0, None, |m| lib.init_mixed(m, buf))
    }

    /// `NativeLib::next_into` on `s`, with the library's regions if any.
    /// (Inlined: see `compiled_successors`.)
    #[inline(always)]
    pub(super) fn lib_next(&self, lib: &NativeLib, s: &EState, i: usize, buf: &mut Vec<Box<[u64]>>) -> c_int {
        if lib.n_regions() == 0 {
            return lib.next_into(&s.words, i as u32, buf);
        }
        self.mixed(s.level, Some((ACTION, i)), |m| lib.next_mixed(m, &s.words, i as u32, buf))
    }

    /// `NativeLib::invariant_raw` (also constraints and liveness state
    /// atoms) on `s` at level `level`, with the library's regions if any.
    pub(super) fn lib_inv(&self, lib: &NativeLib, s: &EState, i: usize, level: u32) -> c_int {
        if lib.n_regions() == 0 {
            return lib.invariant_raw(&s.words, i as u32);
        }
        self.mixed(level, Some((STATE_PRED, i)), |m| lib.invariant_mixed(m, &s.words, i as u32))
    }

    /// `NativeLib::action_property_raw` (also action constraints and
    /// liveness action atoms) on `s -> t` at level `level`, with the
    /// library's regions if any.
    pub(super) fn lib_aprop(&self, lib: &NativeLib, s: &EState, t: &EState, i: usize, level: u32) -> c_int {
        if lib.n_regions() == 0 {
            return lib.action_property_raw(&s.words, &t.words, i as u32);
        }
        self.mixed(level, Some((TRANS_PRED, i)), |m| lib.action_property_mixed(m, &s.words, &t.words, i as u32))
    }

    /// Whether function `i` of `kind` (`adapt::ACTION`, ...) is native and
    /// calls host regions.
    fn is_mixed(&self, kind: usize, i: usize) -> bool {
        self.native.as_deref().is_some_and(|n| {
            let v = match kind {
                ACTION => &n.has.mixed_actions,
                STATE_PRED => &n.has.mixed_invariants,
                _ => &n.has.mixed_action_properties,
            };
            v.get(i).copied().unwrap_or(false)
        })
    }

    /// How to run function `i` of `kind` now: natively (if it is), or, for
    /// a mixed function whose fallback is faster (`adapt`), by its
    /// fallback.
    #[inline]
    pub(super) fn choose(&self, kind: usize, i: usize) -> Choice {
        if self.adapt && self.is_mixed(kind, i) {
            if let Some(lib) = self.lib_id() {
                let warm = if self.memo.exec_id() != 0 { adapt::WARM } else { 0 };
                let choice = adapt::choose(self.id, lib, kind, i, warm);
                self.report_adaptive(kind, i);
                return choice;
            }
        }
        Choice { native: true, timed: false }
    }

    /// Catch accidental cross-model state use in debug builds. Release keeps
    /// the state/codec representation unchanged (see docs/unsafe-audit.md).
    #[inline]
    pub(super) fn check_state_model(&self, s: &EState) {
        #[cfg(debug_assertions)]
        assert_eq!(s.model, self.id, "EState belongs to another EncModel");
        #[cfg(not(debug_assertions))]
        let _ = s;
    }

    /// The identity of the native library in use (it changes when the C
    /// library replaces the JIT one).
    fn lib_id(&self) -> Option<usize> {
        self.native.as_deref().and_then(|n| n.lib_slot())
    }

    /// A timed call (`Choice::timed`) of function `i` of `kind` started at
    /// `t0`, of which `excluded` nanoseconds were spent outside it.
    pub(super) fn record(&self, kind: usize, i: usize, c: Choice, t0: Instant, excluded: u64) {
        let ns = (t0.elapsed().as_nanos() as u64).saturating_sub(excluded);
        adapt::record(self.id, self.lib_id().unwrap_or(0), kind, i, c.native, ns);
        self.report_adaptive(kind, i);
    }

    fn report_adaptive(&self, kind: usize, i: usize) {
        if stats::on() {
            let name = match kind {
                ACTION => self.base.action_names()[i].as_str(),
                STATE_PRED => self.invariants[i].name.as_ref(),
                _ => self.aprops[i].name.as_ref(),
            };
            adapt::report(self.id, kind, i, name);
        }
    }

    /// The statistics path of a native call of function `i` of `kind`.
    pub(super) fn native_path(&self, kind: usize, i: usize) -> Path {
        if self.is_mixed(kind, i) {
            Path::Mixed
        } else {
            Path::Native
        }
    }

    /// Name predicates at native indices, including constraints and escaped
    /// layouts. Each layout's registered region source is frozen on retirement.
    pub(in crate::enc) fn report_native_regions(&self) {
        // Search starts install the public property names. Extend them after
        // the run to name constraint tallies at their native predicate indices.
        stats::set_names(
            self.base.action_names(),
            &self.invariants.iter().map(|p| p.name.to_string()).collect::<Vec<_>>(),
            &self.aprops.iter().map(|p| p.name.to_string()).collect::<Vec<_>>(),
        );
        if !stats::on() {
            return;
        }
        if let Some(e) = &self.escape {
            for m in e.models() {
                m.report_native_regions();
            }
        }
    }

    /// `-stats`: the memo tables' hit rates and the host regions that took
    /// the most time, as report sections.
    pub(in crate::enc) fn report_stats(&self) {
        self.memo.report_stats();
        if let Some(e) = &self.escape {
            e.report();
            let vars: Vec<&str> = self.base.ip.prog.vars.iter().map(|v| &*v.name).collect();
            for (i, version) in e.models().iter().enumerate() {
                if let Some(t) = version.native.as_deref().and_then(|n| n.regions.as_ref()) {
                    stats::set_section(
                        &format!("escape version {i} mixed-mode regions by time (all workers; memo hits included)"),
                        t.report(&vars),
                    );
                    stats::set_section(
                        &format!("escape version {i} mixed-mode region evaluations by state variable read"),
                        t.report_by_var(&vars),
                    );
                }
            }
        }
        if let Some(t) = self.native.as_deref().and_then(|n| n.regions.as_ref()).filter(|_| stats::on()) {
            let vars: Vec<&str> = self.base.ip.prog.vars.iter().map(|v| &*v.name).collect();
            let text = t.report(&vars);
            if !text.is_empty() {
                stats::set_section("mixed-mode regions by time (all workers; memo hits included)", text);
                stats::set_section("mixed-mode region evaluations by state variable read", t.report_by_var(&vars));
            }
        }
        if let Some(t) = self.native.as_deref().and_then(|n| n.refops()).filter(|_| stats::on()) {
            let text = t.report();
            if !text.is_empty() {
                stats::set_section("value store operations called by native code", text);
            }
        }
    }

    /// Native build events since the last call, and whether a build is
    /// still running.
    pub(in crate::enc) fn native_events(&self) -> (Vec<String>, bool) {
        self.native.as_ref().map_or((Vec::new(), false), |n| n.take_events())
    }

    /// Interpret a native predicate's return code: Some(whether it holds),
    /// or None to evaluate it with the interpreter instead (unsupported, or
    /// a runtime error, which the interpreter reports exactly).
    pub(super) fn native_verdict(&self, rc: c_int, states: &[&EState]) -> Result<Option<bool>, ModelError> {
        match rc {
            1 => Ok(Some(true)),
            0 => Ok(Some(false)),
            UNSUPPORTED => Ok(None),
            _ => {
                // (After the search a miss widens nothing: the interpreter
                // decides, see `restartable`.)
                if self.restartable && self.escape.is_none() && !self.def_shapes.is_empty() {
                    self.check_def_fit(states)?;
                }
                Ok(None)
            }
        }
    }

    /// After a native predicate error: if a materialized definition's value
    /// does not fit its shape, record the miss (the run restarts widened).
    fn check_def_fit(&self, states: &[&EState]) -> Result<(), ModelError> {
        for s in states {
            // SAFETY: the matching encoder/program produced these words.
            // Active Dyn handles were published before this call.
            let vals = unsafe { self.layout.decode_state_unchecked(&s.words) };
            for (i, (d, shape)) in self.def_shapes.iter().enumerate() {
                if let Ok(v) = self.base.ip.eval_def_in_state(*d, &vals) {
                    if !shape.contains(&v) {
                        return Err(Self::record_miss(&self.def_miss, i, v));
                    }
                }
            }
        }
        Ok(())
    }
}
