//! Compiled, IR, and interpreted execution of `Init` and actions, the
//! predicate ladder, paranoid cross-checks, and GC-aware successor emission.
//!
//! Runs are speculative: a compiled or IR attempt fills a buffer, and the
//! interpreter re-runs the same (state, action) pair or predicate when the
//! attempt fails or is unsupported. The GC-aware variants retry in place so
//! interpreter side effects happen exactly once.

use std::time::Instant;

use tlx_eval::model::State as VState;
use tlx_native::native::OK;
use tlx_runtime::stats::Path;
use tlx_runtime::{ErrorKind, GcEvent, Model, ModelError, StoreGcRetry};

use super::{bailout_debug, EState, EmitGuard, EncModel, PredAt, TransientFallbackScope, MISS_MSG};
use crate::enc::adapt::{ACTION, STATE_PRED, TRANS_PRED};
use crate::enc::native::Native;
use crate::exec::fast;
use crate::paranoid::mismatch;
use crate::settings::InjectKind;

impl EncModel {
    // ------------------------------------------------------------------
    // Init and actions

    /// Run Init natively or as IR into `buf`. False if it is not compiled
    /// or failed (then `buf` is meaningless).
    pub(super) fn compiled_init(&self, buf: &mut Vec<Box<[u64]>>) -> bool {
        if let Some(lib) = self.native_lib(|n| n.has.init) {
            return self.lib_init(lib, buf) == OK;
        }
        if !self.init_exec_ok {
            return false;
        }
        let Some((prog, action)) = self.fast.init.as_ref().map(|action| (&self.fast.prog, action)) else { return false };
        // A large Init run as IR while the native library is being built:
        // switch to native Init as soon as it is ready.
        let pending = self.native.as_ref().is_some_and(|n| n.has.init);
        let mut switch = false;
        let mut emit = |w: &[u64]| {
            buf.push(w.into());
            if pending && buf.len().is_multiple_of(1024) && self.native_lib(|n| n.has.init).is_some() {
                switch = true;
                return Ok(false);
            }
            Ok(true)
        };
        let ok = fast::run_init_words(&fast::Run::words(&self.base.ip, &self.typing, prog, 0), action, &mut emit).is_ok();
        if switch {
            buf.clear();
            return self.compiled_init(buf);
        }
        ok
    }

    /// Interpreted Init (exact semantics, including error reporting).
    pub(super) fn interpreted_init(&self, out: &mut dyn FnMut(EState)) -> Result<(), ModelError> {
        let mut err = None;
        self.base.init_states(&mut |v| {
            if err.is_none() {
                match self.encode(&v) {
                    Ok(e) => out(e),
                    Err(e) => err = Some(e),
                }
            }
        })?;
        err.map_or(Ok(()), Err)
    }

    /// Interpreted Init with in-place value-store GC retry per initial state so
    /// interpreter side effects run once and generation stops immediately if
    /// `sink` returns false.
    pub(super) fn interpreted_init_gc(&self, sink: &mut dyn FnMut(GcEvent<EState>) -> bool) -> Result<(), ModelError> {
        let has_store = self.value_store().is_some();
        let mut err = None;
        self.base.init_states_while(&mut |v| match self.encode_gc(&v, has_store, sink) {
            Ok(Some(e)) => sink(GcEvent::Emit(e, 0)),
            Ok(None) => false,
            Err(e) => {
                err = Some(e);
                false
            }
        })?;
        err.map_or(Ok(()), Err)
    }

    /// `compiled_successors` of an action that may print: its output is held
    /// back in the returned vector instead of released immediately, so a
    /// `StoreFull` retry or interpreter fallback discards it cleanly and
    /// committed output is released exactly once.
    #[inline(never)]
    fn compiled_successors_printing_hold(
        &self,
        s: &EState,
        i: usize,
        native: bool,
        buf: &mut Vec<Box<[u64]>>,
    ) -> (Option<Path>, Vec<String>) {
        let mark = tlx_eval::Interp::hold_begin();
        let ok = self.compiled_successors(s, i, native, buf);
        let lines = tlx_eval::Interp::hold_end(mark);
        if ok.is_some() {
            if self.paranoid {
                self.cross_check_output(s, i, &lines);
            }
            (ok, lines)
        } else {
            (None, Vec::new())
        }
    }

    /// Paranoid: the lines a compiled run of action `i` on `s` printed
    /// (`printed`) are the interpreter's (as multisets).
    fn cross_check_output(&self, s: &EState, i: usize, printed: &[String]) {
        let vs = self.decode_current(s);
        let (_, mut want) =
            tlx_eval::Interp::hold_output(|| self.base.ip.without_effects(|| self.base.successor_values_of(&vs, i, &mut |_| {})));
        let mut got = printed.to_vec();
        want.sort();
        got.sort();
        if want != got {
            let what = format!("action {} on state\n{}", self.base.action_names()[i], self.base.render(&vs));
            mismatch(format_args!("{what}\nthe interpreter prints {want:?} but compiled code printed {got:?}"));
        }
    }

    /// Run action `i` on `s` natively (if `native`) or as IR into `buf`.
    /// The actual path on success, None if it is not compiled or failed.
    /// (Inlined into `run_action`: called once per action and state, a call
    /// costs about 3% of a search with cheap actions.)
    #[inline(always)]
    pub(super) fn compiled_successors(&self, s: &EState, i: usize, native: bool, buf: &mut Vec<Box<[u64]>>) -> Option<Path> {
        if self.escaped(s) {
            return None;
        }
        if let Some(lib) = self.native_lib(|n| native && n.has.actions[i]) {
            return (self.lib_next(lib, s, i, buf) == OK).then(|| self.native_path(ACTION, i));
        }
        let Some(f) = &self.actions[i] else { return None };
        if !self.exec_ok[i] {
            return None;
        }
        let decode = |w: &[u64]| self.cached_values(w, true);
        if let Some((prog, a)) = self.fast.actions[i].as_ref().map(|a| (&self.fast.prog, a)) {
            let mut emit = |w: &[u64]| {
                buf.push(w.into());
                Ok(true)
            };
            let run = fast::Run::words(&self.base.ip, &self.typing, prog, s.level).with_decoder(&decode).with_memo(self.memo.exec_id());
            // SAFETY: the matching encoder/program produced these words.
            // Active Dyn handles were published before this call.
            let r = unsafe { fast::run_action_words(&run, a, &s.words, &mut emit) };
            if let Err(e) = &r {
                bailout_debug(&format!("action {}", f.name), e);
            }
            return r.is_ok().then_some(Path::Ir);
        }
        None
    }

    /// The verdict of state predicate `idx` (of `invariants`) on `s` at
    /// level `level` from the IR executor (`pred_exec_ok`); None if it does
    /// not run there or fails (the interpreter then evaluates it).
    fn ir_predicate(&self, s: &EState, idx: usize, level: u32) -> Option<bool> {
        if self.escaped(s) {
            return None;
        }
        if !self.pred_exec_ok[idx] {
            return None;
        }
        let p = &self.invariants[idx];
        let decode = |w: &[u64]| self.cached_values(w, false);
        if let Some((prog, fp)) = self.fast.preds[idx].as_ref().map(|q| (&self.fast.prog, q)) {
            let run = fast::Run::words(&self.base.ip, &self.typing, prog, level).with_decoder(&decode).with_memo(self.memo.exec_id());
            // SAFETY: the matching encoder/program produced these words.
            // Active Dyn handles were published before this call.
            return match unsafe { fast::eval_pred_words(&run, fp, &s.words) } {
                Ok(b) => Some(b),
                Err(e) => {
                    bailout_debug(&format!("predicate {}", p.name), &e);
                    None
                }
            };
        }
        None
    }

    // ------------------------------------------------------------------
    // predicates: one ladder (`predicate`) for the invariants, CONSTRAINTs,
    // ACTION_CONSTRAINTs, action properties and liveness atoms

    /// Evaluate compiled predicate `p`: natively (unless the adaptive
    /// tiering runs the fallback, see `choose`), else by `steps` (a
    /// liveness action atom decided by a change of its subscript; `|| None`
    /// elsewhere), else in the IR executor (`ir_predicate`,
    /// `ir_trans_predicate`), else by `interp`, the interpreter, which has
    /// the last word (also on a native error: see `native_verdict`). With
    /// TLX_PARANOID every verdict not from `interp` is checked against it;
    /// `what(note)` describes the predicate and its states in a mismatch
    /// (`note`: how `steps` decided, else empty). Also the path taken (for
    /// the statistics).
    #[inline]
    pub(super) fn predicate(
        &self,
        p: PredAt<'_>,
        steps: impl FnOnce() -> Option<bool>,
        interp: impl Fn() -> Result<bool, ModelError>,
        what: impl Fn(&str) -> String,
    ) -> Result<(bool, Path), ModelError> {
        let kind = if p.t.is_some() { TRANS_PRED } else { STATE_PRED };
        let c = self.choose(kind, p.idx);
        let t0 = c.timed.then(Instant::now);
        let r = self.predicate_untimed(p, kind, c.native, steps, &interp, &what);
        if let Some(t0) = t0 {
            self.record(kind, p.idx, c, t0, 0);
        }
        r
    }

    /// GC-aware `predicate`: runs the fast path once, and only on `StoreFull`
    /// enters the cold per-predicate retry loop via `collect(force_drop_archive)`
    /// (falling back to the interpreter on retry 3) without replaying earlier
    /// predicates in the same check list.
    #[inline]
    pub(super) fn predicate_gc(
        &self,
        p: PredAt<'_>,
        steps: impl Fn() -> Option<bool>,
        interp: impl Fn() -> Result<bool, ModelError>,
        what: impl Fn(&str) -> String,
        collect: &mut dyn FnMut(bool) -> bool,
    ) -> Result<(bool, Path), ModelError> {
        match self.predicate(p, &steps, &interp, &what) {
            Err(e) if e.is_store_full() => self.retry_predicate_gc(p, &steps, &interp, &what, collect, e),
            other => other,
        }
    }

    #[cold]
    #[inline(never)]
    fn retry_predicate_gc(
        &self,
        p: PredAt<'_>,
        steps: &impl Fn() -> Option<bool>,
        interp: &impl Fn() -> Result<bool, ModelError>,
        what: &impl Fn(&str) -> String,
        collect: &mut dyn FnMut(bool) -> bool,
        first_err: ModelError,
    ) -> Result<(bool, Path), ModelError> {
        let mut last = first_err;
        for stage in StoreGcRetry::STAGES {
            if !collect(stage.force_drop_archive) {
                return Err(last);
            }
            let _fb = stage.transient_fallback.then(TransientFallbackScope::enter);
            match self.predicate(p, steps, interp, what) {
                Err(e) if e.is_store_full() => last = e,
                other => return other,
            }
        }
        Err(last)
    }

    /// `predicate` without the adaptive tiering's timing (natively only if
    /// `native`).
    #[inline]
    fn predicate_untimed(
        &self,
        p: PredAt<'_>,
        kind: usize,
        native: bool,
        steps: impl FnOnce() -> Option<bool>,
        interp: &impl Fn() -> Result<bool, ModelError>,
        what: &impl Fn(&str) -> String,
    ) -> Result<(bool, Path), ModelError> {
        let checked = |b: bool, note: &str| {
            if self.paranoid {
                self.check_verdict(b, interp(), || what(note));
            }
            b
        };
        let has_store = self.value_store().is_some();
        let skip_compiled = has_store && Self::transient_fallback();
        let mut path = Path::Interp;
        if !skip_compiled {
            let native = native && !self.escaped(p.s) && !p.t.is_some_and(|t| self.escaped(t));
            let has = |n: &Native| native && if p.t.is_some() { n.has.action_properties[p.idx] } else { n.has.invariants[p.idx] };
            if let Some(lib) = self.native_lib(has) {
                if has_store {
                    tlx_layout::store::clear_full_hit();
                }
                let mut rc = match p.t {
                    None => self.lib_inv(lib, p.s, p.idx, p.level),
                    Some(t) => self.lib_aprop(lib, p.s, t, p.idx, p.level),
                };
                if p.inject && self.inject.is_some() && (rc == 0 || rc == 1) && self.inject_now(&[InjectKind::Inv]).is_some() {
                    rc = 1 - rc;
                }
                let verdict = match p.t {
                    None => self.native_verdict(rc, &[p.s])?,
                    Some(t) => self.native_verdict(rc, &[p.s, t])?,
                };
                match verdict {
                    Some(b) => return Ok((checked(b, ""), self.native_path(kind, p.idx))),
                    None => {
                        if has_store && tlx_layout::store::take_full_hit() {
                            return Err(self.store_full_error());
                        }
                        path = Path::Fallback;
                    }
                }
            }
        } else {
            path = Path::Fallback;
        }
        if let Some(b) = steps() {
            return Ok((checked(b, " (as a change of its subscript)"), Path::Interp));
        }
        if !skip_compiled {
            if has_store {
                tlx_layout::store::clear_full_hit();
            }
            let ir = match p.t {
                None => self.ir_predicate(p.s, p.idx, p.level),
                Some(t) => self.ir_trans_predicate(p.s, t, p.idx, p.level),
            };
            if let Some(b) = ir {
                return Ok((checked(b, ""), Path::Ir));
            }
            if has_store && tlx_layout::store::take_full_hit() {
                return Err(self.store_full_error());
            }
        }
        Ok((interp()?, path))
    }

    /// The verdict of transition predicate `idx` (of `aprops`) on the step
    /// `s` -> `t` at level `level` from the closure-compiled executor
    /// (`aprop_exec_ok`); None if it does not run there or fails.
    fn ir_trans_predicate(&self, s: &EState, t: &EState, idx: usize, level: u32) -> Option<bool> {
        if self.escaped(s) || self.escaped(t) {
            return None;
        }
        if !self.aprop_exec_ok[idx] {
            return None;
        }
        let (prog, fp) = self.fast.aprops[idx].as_ref().map(|q| (&self.fast.prog, q))?;
        let decode = |w: &[u64]| self.cached_values(w, true);
        let run = fast::Run::words(&self.base.ip, &self.typing, prog, level).with_decoder(&decode).with_memo(self.memo.exec_id());
        // SAFETY: the matching encoder/program produced these words.
        // Active Dyn handles were published before this call.
        match unsafe { fast::eval_trans_words(&run, fp, &s.words, &t.words) } {
            Ok(b) => Some(b),
            Err(e) => {
                bailout_debug(&format!("action property {}", self.aprops[idx].name), &e);
                None
            }
        }
    }

    /// How `compiled_successors` runs action `i` (None: not compiled).
    pub(super) fn compiled_path(&self, i: usize, native: bool) -> Option<Path> {
        if self.native_lib(|n| native && n.has.actions[i]).is_some() {
            Some(self.native_path(ACTION, i))
        } else {
            (self.actions[i].is_some() && self.exec_ok[i]).then_some(Path::Ir)
        }
    }

    /// Successors of `s` by action `i` to `out`: compiled (natively if
    /// `native`) into a buffer, or on any error, by the interpreter for
    /// this pair. False if exploration is to stop; also the path taken
    /// (for the statistics).
    pub(super) fn run_action(
        &self,
        s: &EState,
        i: usize,
        native: bool,
        out: &mut dyn FnMut(EState, u32) -> bool,
    ) -> (Result<bool, ModelError>, Path) {
        let mut buf = Vec::new();
        tlx_eval::Interp::begin_random_scope();
        if let Some(e) = &self.escape {
            // Output is held transactionally by compiled_successors_printing_hold.
            // Other effects only have a whole-search journal, not an action
            // transaction, so they must run in the interpreter exactly once.
            if e.irreversible_actions[i] {
                return (self.interpreted_successors(s, i, out), Path::Interp);
            }
            if self.escaped(s) {
                e.guards.add(1);
                if let Some(r) = self.escape_action(s, i, out) {
                    return (r, Path::Fallback);
                }
                e.deopts.add(1);
                return (self.interpreted_successors(s, i, out), Path::Fallback);
            }
        }
        let has_store = self.value_store().is_some();
        if has_store {
            tlx_layout::store::clear_full_hit();
        }
        let (ok, pending_lines) = if self.prints[i] {
            self.compiled_successors_printing_hold(s, i, native, &mut buf)
        } else {
            (self.compiled_successors(s, i, native, &mut buf), Vec::new())
        };
        if let Some(path) = ok {
            if self.inject.is_some() {
                // Test hook: a miss where nothing restarts.
                if !self.restartable && self.inject_now(&[InjectKind::Miss]).is_some() {
                    return (Err(ModelError::of_kind(ErrorKind::LayoutMiss, MISS_MSG)), Path::Native);
                }
                self.inject_successors(s, &mut buf);
            }
            if self.paranoid {
                if let Err(e) = self.cross_check(s, i, &buf) {
                    return (Err(e), path);
                }
            }
            if !pending_lines.is_empty() {
                self.base.ip.release_output(pending_lines);
            }
            let r = self.emit_compiled(buf, s, i, out);
            (r, path)
        } else {
            let compiled = self.compiled_path(i, native).is_some();
            if has_store && tlx_layout::store::take_full_hit() {
                let path = self.compiled_path(i, native).unwrap_or(Path::Ir);
                return (Err(self.store_full_error()), path);
            }
            if let Some(e) = self.escape.as_ref().filter(|_| compiled) {
                e.guards.add(1);
                e.deopts.add(1);
                if let Some(r) = self.escape_action(s, i, out) {
                    return (r, Path::Fallback);
                }
            }
            // (Not counting runs the adaptive tiering gave the interpreter.)
            if self.actions[i].is_some() && (native || compiled) {
                self.bailouts.add(1);
            }
            let path = if compiled { Path::Fallback } else { Path::Interp };
            (self.interpreted_successors(s, i, out), path)
        }
    }

    /// GC-aware `run_action`: retries compiled action generation across
    /// `GcEvent::Collect` (dropping the archive on retry 2 and falling back to
    /// the interpreter on retry 3 so transient compiled intermediates cannot
    /// starve a small store), releases captured `PrintT` output once the
    /// compiled batch is committed, and finishes/delivers states strictly one
    /// at a time in order so first-failure order is preserved across retries.
    pub(super) fn run_action_gc(
        &self,
        s: &EState,
        i: usize,
        native: bool,
        sink: &mut dyn FnMut(GcEvent<EState>) -> bool,
    ) -> (Result<bool, ModelError>, Path) {
        tlx_eval::Interp::begin_random_scope();
        if let Some(e) = &self.escape {
            if e.irreversible_actions[i] {
                return (self.interpreted_successors_gc(s, i, sink), Path::Interp);
            }
            if self.escaped(s) {
                e.guards.add(1);
                if let Some(r) = self.escape_action(s, i, &mut |t, a| sink(GcEvent::Emit(t, a))) {
                    return (r, Path::Fallback);
                }
                e.deopts.add(1);
                return (self.interpreted_successors_gc(s, i, sink), Path::Fallback);
            }
        }
        let has_store = self.value_store().is_some();
        let mut buf = Vec::new();
        let mut tries = 0usize;
        let (ok, pending_lines) = loop {
            buf.clear();
            if has_store {
                tlx_layout::store::clear_full_hit();
            }
            let (ok, lines) = if self.prints[i] {
                self.compiled_successors_printing_hold(s, i, native, &mut buf)
            } else {
                (self.compiled_successors(s, i, native, &mut buf), Vec::new())
            };
            if ok.is_some() {
                break (ok, lines);
            }
            if has_store && tlx_layout::store::take_full_hit() {
                if let Some(stage) = StoreGcRetry::COMPILED_STAGES.get(tries) {
                    tries += 1;
                    if !sink(GcEvent::Collect { force_drop_archive: stage.force_drop_archive }) {
                        return (Ok(false), self.compiled_path(i, native).unwrap_or(Path::Ir));
                    }
                    continue;
                }
                // Even archive-free GC could not hold this compiled action's
                // transient intermediates: sweep the aborted attempt and fall
                // back to the interpreter (which evaluates intermediates as
                // `Value` without interning discarded temporaries).
                if !sink(GcEvent::Collect { force_drop_archive: true }) {
                    return (Ok(false), Path::Fallback);
                }
                let compiled = self.compiled_path(i, native).is_some();
                if self.actions[i].is_some() && (native || compiled) {
                    self.bailouts.add(1);
                }
                return (self.interpreted_successors_gc(s, i, sink), Path::Fallback);
            }
            break (None, Vec::new());
        };
        if let Some(path) = ok {
            if self.inject.is_some() {
                if !self.restartable && self.inject_now(&[InjectKind::Miss]).is_some() {
                    return (Err(ModelError::of_kind(ErrorKind::LayoutMiss, MISS_MSG)), Path::Native);
                }
                self.inject_successors(s, &mut buf);
            }
            if self.paranoid {
                if let Err(e) = self.cross_check_gc(s, i, &mut buf, sink) {
                    return (Err(e), path);
                }
            }
            let r = self.emit_compiled_gc(buf, s.level + 1, i as u32, pending_lines, sink);
            (r, path)
        } else {
            let compiled = self.compiled_path(i, native).is_some();
            if let Some(e) = self.escape.as_ref().filter(|_| compiled) {
                e.guards.add(1);
                e.deopts.add(1);
                if let Some(r) = self.escape_action(s, i, &mut |t, a| sink(GcEvent::Emit(t, a))) {
                    return (r, Path::Fallback);
                }
            }
            if self.actions[i].is_some() && (native || compiled) {
                self.bailouts.add(1);
            }
            let path = if compiled { Path::Fallback } else { Path::Interp };
            (self.interpreted_successors_gc(s, i, sink), path)
        }
    }

    /// Paranoid cross-check for compiled successors while keeping `buf` rooted
    /// across any `StoreFull` GC retry triggered by `check_store_slots`.
    fn cross_check_gc(
        &self,
        s: &EState,
        i: usize,
        buf: &mut Vec<Box<[u64]>>,
        sink: &mut dyn FnMut(GcEvent<EState>) -> bool,
    ) -> Result<(), ModelError> {
        let mut last = match self.cross_check(s, i, buf) {
            Ok(()) => return Ok(()),
            Err(e) if e.is_store_full() => e,
            Err(e) => return Err(e),
        };
        for stage in StoreGcRetry::STAGES {
            let held = std::mem::take(buf);
            let guard = EmitGuard::push_words(self.id, held);
            let ok = sink(GcEvent::Collect { force_drop_archive: stage.force_drop_archive });
            *buf = guard.take_words();
            if !ok {
                return Err(last);
            }
            match self.cross_check(s, i, buf) {
                Ok(()) => return Ok(()),
                Err(e) if e.is_store_full() => last = e,
                Err(e) => return Err(e),
            }
        }
        Err(last)
    }

    /// Paranoid cross-check for compiled Init while keeping `buf` rooted
    /// across any `StoreFull` GC retry triggered by `check_store_slots`.
    pub(super) fn cross_check_init_gc(
        &self,
        buf: &mut Vec<Box<[u64]>>,
        sink: &mut dyn FnMut(GcEvent<EState>) -> bool,
    ) -> Result<(), ModelError> {
        let mut last = match self.cross_check_init(buf) {
            Ok(()) => return Ok(()),
            Err(e) if e.is_store_full() => e,
            Err(e) => return Err(e),
        };
        for stage in StoreGcRetry::STAGES {
            let held = std::mem::take(buf);
            let guard = EmitGuard::push_words(self.id, held);
            let ok = sink(GcEvent::Collect { force_drop_archive: stage.force_drop_archive });
            *buf = guard.take_words();
            if !ok {
                return Err(last);
            }
            match self.cross_check_init(buf) {
                Ok(()) => return Ok(()),
                Err(e) if e.is_store_full() => last = e,
                Err(e) => return Err(e),
            }
        }
        Err(last)
    }

    /// Hand the compiled successors of `s` by action `i` to `out` strictly in
    /// order; false if exploration is to stop.
    fn emit_compiled(
        &self,
        mut buf: Vec<Box<[u64]>>,
        s: &EState,
        i: usize,
        out: &mut dyn FnMut(EState, u32) -> bool,
    ) -> Result<bool, ModelError> {
        if buf.is_empty() {
            return Ok(true);
        }
        if self.value_store().is_none() || buf.len() == 1 {
            for w in buf {
                let t = self.finish(w, s.level + 1)?;
                if !out(t, i as u32) {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        // Keep un-emitted words rooted in `PENDING_EMIT` while streaming one
        // state at a time in order so `out` sees the first failure before later
        // states' VIEW/SYMMETRY fingerprints are evaluated.
        buf.reverse();
        let guard = EmitGuard::push_words(self.id, buf);
        while let Some(w) = guard.pop_word() {
            let t = self.finish(w, s.level + 1)?;
            if !out(t, i as u32) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// GC-aware ordered emission of compiled successors: finishes and delivers
    /// states one at a time in order, retrying `finish` (VIEW/SYMMETRY) in
    /// place across `GcEvent::Collect` without re-running the action. Releases
    /// captured `PrintT` output once the first state's fingerprinting succeeds
    /// (or immediately if the batch is empty).
    pub(super) fn emit_compiled_gc(
        &self,
        mut buf: Vec<Box<[u64]>>,
        level: u32,
        action: u32,
        pending_lines: Vec<String>,
        sink: &mut dyn FnMut(GcEvent<EState>) -> bool,
    ) -> Result<bool, ModelError> {
        if buf.is_empty() {
            if !pending_lines.is_empty() {
                self.base.ip.release_output(pending_lines);
            }
            return Ok(true);
        }
        // Fast path for the common 1-successor action: zero `PENDING_EMIT`
        // touches unless `finish_or_return` actually hits `StoreFull`.
        if buf.len() == 1 {
            let w = buf.pop().unwrap();
            match self.finish_or_return(w, level) {
                Ok(t) => {
                    if !pending_lines.is_empty() {
                        self.base.ip.release_output(pending_lines);
                    }
                    return Ok(sink(GcEvent::Emit(t, action)));
                }
                Err((w, e)) if e.is_store_full() => {
                    return self.emit_compiled_gc_slow(vec![w], level, action, pending_lines, sink, Some(e));
                }
                Err((_, e)) => {
                    if !pending_lines.is_empty() {
                        self.base.ip.release_output(pending_lines);
                    }
                    return Err(e);
                }
            }
        }
        buf.reverse();
        self.emit_compiled_gc_slow(buf, level, action, pending_lines, sink, None)
    }

    #[cold]
    #[inline(never)]
    fn emit_compiled_gc_slow(
        &self,
        buf_rev: Vec<Box<[u64]>>,
        level: u32,
        action: u32,
        mut pending_lines: Vec<String>,
        sink: &mut dyn FnMut(GcEvent<EState>) -> bool,
        mut first_full: Option<ModelError>,
    ) -> Result<bool, ModelError> {
        let guard = EmitGuard::push_words(self.id, buf_rev);
        while let Some(w) = guard.pop_word() {
            let initial = match first_full.take() {
                Some(e) => Err((w, e)),
                None => self.finish_or_return(w, level),
            };
            let t = match initial {
                Ok(t) => t,
                Err((mut w_cur, mut last)) if last.is_store_full() => {
                    let mut finished = None;
                    for stage in StoreGcRetry::STAGES {
                        guard.push_word(w_cur);
                        if !sink(GcEvent::Collect { force_drop_archive: stage.force_drop_archive }) {
                            return Ok(false);
                        }
                        w_cur = guard.pop_word().expect("re-pushed emit word");
                        let _fb = stage.transient_fallback.then(TransientFallbackScope::enter);
                        match self.finish_or_return(w_cur, level) {
                            Ok(t) => {
                                finished = Some(t);
                                break;
                            }
                            Err((w_next, e2)) if e2.is_store_full() => {
                                w_cur = w_next;
                                last = e2;
                            }
                            Err((_, e2)) => {
                                if !pending_lines.is_empty() {
                                    self.base.ip.release_output(pending_lines);
                                }
                                return Err(e2);
                            }
                        }
                    }
                    match finished {
                        Some(t) => t,
                        None => return Err(last),
                    }
                }
                Err((_, e)) => {
                    if !pending_lines.is_empty() {
                        self.base.ip.release_output(pending_lines);
                    }
                    return Err(e);
                }
            };
            if !pending_lines.is_empty() {
                self.base.ip.release_output(std::mem::take(&mut pending_lines));
            }
            if !sink(GcEvent::Emit(t, action)) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Encode one interpreter state `v`, retrying in place across
    /// `GcEvent::Collect` if `StoreFull` occurs without re-running the
    /// interpreter action. Returns `Ok(None)` if the search stopped during GC.
    fn encode_gc(&self, v: &VState, has_store: bool, sink: &mut dyn FnMut(GcEvent<EState>) -> bool) -> Result<Option<EState>, ModelError> {
        let mut last = match self.encode(v) {
            Ok(e) => return Ok(Some(e)),
            Err(e) if has_store && e.is_store_full() => e,
            Err(e) => return Err(e),
        };
        for stage in StoreGcRetry::STAGES {
            if !sink(GcEvent::Collect { force_drop_archive: stage.force_drop_archive }) {
                return Ok(None);
            }
            let _fb = stage.transient_fallback.then(TransientFallbackScope::enter);
            match self.encode(v) {
                Ok(e) => return Ok(Some(e)),
                Err(e) if e.is_store_full() => last = e,
                Err(e) => return Err(e),
            }
        }
        Err(last)
    }

    /// Successors of `s` by action `i` from the interpreter; false if
    /// exploration is to stop.
    pub(super) fn interpreted_successors(
        &self,
        s: &EState,
        i: usize,
        out: &mut dyn FnMut(EState, u32) -> bool,
    ) -> Result<bool, ModelError> {
        let mut go_on = true;
        let mut err = None;
        self.base.successors_of(&self.decode_current(s), i, &mut |t, act| match self.encode(&t) {
            Ok(e) => {
                if self.escaped(&e) {
                    if let Some(escape) = &self.escape {
                        escape.observe(&t.vals);
                    }
                }
                let go = out(e, act);
                go_on &= go;
                go
            }
            Err(e) => {
                err = Some(e);
                go_on = false;
                false
            }
        })?;
        match err {
            Some(e) => Err(e),
            None => Ok(go_on),
        }
    }

    /// GC-aware interpreted successors: runs `base.successors_of` once and
    /// encodes/delivers each successor strictly in order with in-place GC
    /// retries, keeping interpreter effects (`Print`, `TLCSet`, files) exact
    /// and preserving first-failure order.
    pub(super) fn interpreted_successors_gc(
        &self,
        s: &EState,
        i: usize,
        sink: &mut dyn FnMut(GcEvent<EState>) -> bool,
    ) -> Result<bool, ModelError> {
        let has_store = self.value_store().is_some();
        let mut go_on = true;
        let mut err = None;
        self.base.successors_of(&self.decode_current(s), i, &mut |t, act| match self.encode_gc(&t, has_store, sink) {
            Ok(Some(e)) => {
                if self.escaped(&e) {
                    if let Some(escape) = &self.escape {
                        escape.observe(&t.vals);
                    }
                }
                let go = sink(GcEvent::Emit(e, act));
                go_on &= go;
                go
            }
            Ok(None) => {
                go_on = false;
                false
            }
            Err(e) => {
                err = Some(e);
                go_on = false;
                false
            }
        })?;
        match err {
            Some(e) => Err(e),
            None => Ok(go_on),
        }
    }
}
