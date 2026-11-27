//! The `tlx_runtime::Model` adapter of the compiled model (CODE-03).
//!
//! `EncModel` is observed through the runtime `Model` interface; the adapter
//! forwards every capability (initial states, successors, invariants,
//! constraints, transition properties, fingerprints, rendering and
//! checkpointing). Extracted from `model.rs`.

use std::sync::Arc;
use std::time::Instant;

use tlx_runtime::stats::{self, Path};
use tlx_runtime::{GcEvent, Model, ModelError, StoreGcRetry};
use tlx_value::Value;

use super::fingerprint::Fingerprint;
use super::{EState, EmitGuard, EncModel};
use crate::enc::adapt::ACTION;
use crate::settings::InjectKind;

impl Model for EncModel {
    type State = EState;

    fn uses_trace(&self) -> bool {
        self.base.uses_trace()
    }

    fn trace_replay_limit(&self) -> Option<&'static str> {
        self.base.trace_replay_limit()
    }

    fn state_values(&self, s: &EState) -> Option<Arc<[Value]>> {
        Some(self.values(s))
    }

    fn init_states(&self, out: &mut dyn FnMut(EState)) -> Result<(), ModelError> {
        let mut buf = Vec::new();
        let has_store = self.value_store().is_some();
        // (Random choices restart for each evaluation, as in the interpreter.)
        tlx_eval::Interp::begin_random_scope();
        if has_store {
            tlx_layout::store::clear_full_hit();
        }
        // (With -coverage, the interpreter counts what Init rejects.)
        if self.base.coverage || !self.compiled_init(&mut buf) {
            if !self.base.coverage && has_store && tlx_layout::store::take_full_hit() {
                return Err(self.store_full_error());
            }
            return self.interpreted_init(out);
        }
        if self.inject.is_some() && self.inject_now(&[InjectKind::Init]).is_some() {
            buf.pop();
        }
        if self.paranoid {
            self.cross_check_init(&buf)?;
        }
        if has_store {
            buf.reverse();
            let guard = EmitGuard::push_words(self.id, buf);
            while let Some(w) = guard.pop_word() {
                out(self.finish(w, 1)?);
            }
        } else {
            for w in buf {
                out(self.finish(w, 1)?);
            }
        }
        Ok(())
    }

    fn init_states_gc(&self, sink: &mut dyn FnMut(GcEvent<EState>) -> bool) -> Result<(), ModelError> {
        let has_store = self.value_store().is_some();
        tlx_eval::Interp::begin_random_scope();
        if self.base.coverage {
            return self.interpreted_init_gc(sink);
        }
        let mut buf = Vec::new();
        let mut tries = 0usize;
        let ok = loop {
            buf.clear();
            if has_store {
                tlx_layout::store::clear_full_hit();
            }
            if self.compiled_init(&mut buf) {
                break true;
            }
            if has_store && tlx_layout::store::take_full_hit() {
                if let Some(stage) = StoreGcRetry::COMPILED_STAGES.get(tries) {
                    tries += 1;
                    if !sink(GcEvent::Collect { force_drop_archive: stage.force_drop_archive }) {
                        return Ok(());
                    }
                    continue;
                }
                if !sink(GcEvent::Collect { force_drop_archive: true }) {
                    return Ok(());
                }
                return self.interpreted_init_gc(sink);
            }
            break false;
        };
        if !ok {
            return self.interpreted_init_gc(sink);
        }
        if self.inject.is_some() && self.inject_now(&[InjectKind::Init]).is_some() {
            buf.pop();
        }
        if self.paranoid {
            self.cross_check_init_gc(&mut buf, sink)?;
        }
        let _ = self.emit_compiled_gc(buf, 1, 0, Vec::new(), sink)?;
        Ok(())
    }

    fn successors(&self, s: &EState, out: &mut dyn FnMut(EState, u32) -> bool) -> Result<(), ModelError> {
        self.check_state_model(s);
        if self.base.symmetry_check_due() {
            self.base.check_symmetry_claim(&self.decode_current(s));
        }
        for i in 0..self.actions.len() {
            if !self.action_successors(s, i as u32, out)? {
                break;
            }
        }
        Ok(())
    }

    fn action_successors(&self, s: &EState, action: u32, out: &mut dyn FnMut(EState, u32) -> bool) -> Result<bool, ModelError> {
        self.check_state_model(s);
        if action == 0 && self.base.symmetry_check_due() {
            self.base.check_symmetry_claim(&self.decode_current(s));
        }
        let i = action as usize;
        // Generation mode (`-generate`): the random choices within actions
        // are the interpreter's (compiled actions enumerate every successor).
        let span = stats::span();
        if tlx_runtime::live::generating() {
            let r = self.interpreted_successors(s, i, out);
            span.action(i, Path::Interp);
            return r;
        }
        let c = self.choose(ACTION, i);
        if !c.timed {
            let (r, path) = self.run_action(s, i, c.native, out);
            span.action(i, path);
            return r;
        }
        // A timed call (adaptive tiering): without the time spent in `out`.
        let t0 = Instant::now();
        let mut excluded = 0u64;
        let mut timed_out = |t: EState, a: u32| {
            let t1 = Instant::now();
            let go = out(t, a);
            excluded += t1.elapsed().as_nanos() as u64;
            go
        };
        let (r, path) = self.run_action(s, i, c.native, &mut timed_out);
        self.record(ACTION, i, c, t0, excluded);
        span.action(i, path);
        r
    }

    fn action_successors_gc(&self, s: &EState, action: u32, sink: &mut dyn FnMut(GcEvent<EState>) -> bool) -> Result<bool, ModelError> {
        self.check_state_model(s);
        if action == 0 && self.base.symmetry_check_due() {
            self.base.check_symmetry_claim(&self.decode_current(s));
        }
        let i = action as usize;
        let span = stats::span();
        if tlx_runtime::live::generating() {
            let r = self.interpreted_successors_gc(s, i, sink);
            span.action(i, Path::Interp);
            return r;
        }
        let c = self.choose(ACTION, i);
        if !c.timed {
            let (r, path) = self.run_action_gc(s, i, c.native, sink);
            span.action(i, path);
            return r;
        }
        let t0 = Instant::now();
        let mut excluded = 0u64;
        let mut timed_sink = |ev: GcEvent<EState>| {
            let t1 = Instant::now();
            let go = sink(ev);
            excluded += t1.elapsed().as_nanos() as u64;
            go
        };
        let (r, path) = self.run_action_gc(s, i, c.native, &mut timed_sink);
        self.record(ACTION, i, c, t0, excluded);
        span.action(i, path);
        r
    }

    fn fingerprint(&self, s: &EState) -> u64 {
        self.check_state_model(s);
        s.fp
    }
    fn coarse_fingerprint(&self) -> bool {
        self.base.has_view_or_symmetry()
    }

    fn check_invariants(&self, s: &EState) -> Result<Option<usize>, ModelError> {
        self.check_state_model(s);
        // (Called on every state or step: nothing to do is cheap.)
        if self.base.invariant_names().is_empty() {
            return Ok(None);
        }
        self.invariants_violated(s)
    }

    fn check_invariants_gc(&self, s: &EState, collect: &mut dyn FnMut(bool) -> bool) -> Result<Option<usize>, ModelError> {
        self.check_state_model(s);
        if self.base.invariant_names().is_empty() {
            return Ok(None);
        }
        self.invariants_violated_gc(s, collect)
    }

    fn invariant_key(&self, _s: &EState, fp: u64) -> Option<u64> {
        // (A class fingerprint does not identify the state; hashing the
        // words costs about as much as the native invariants save.)
        (self.pure_invariants && matches!(self.fp, Fingerprint::Words)).then_some(fp)
    }

    fn constraint(&self, s: &EState) -> Result<bool, ModelError> {
        self.check_state_model(s);
        // (Called on every state or step: nothing to do is cheap.)
        let holds = self.base.constraint_exprs().is_empty() || self.constraints_hold(s)?;
        // `_POSSIBLE` predicates, by the interpreter until witnessed.
        if holds && self.base.possible_pending(false) {
            self.base.witness(&self.decode(s), None)?;
        }
        Ok(holds)
    }

    fn constraint_gc(&self, s: &EState, collect: &mut dyn FnMut(bool) -> bool) -> Result<bool, ModelError> {
        self.check_state_model(s);
        let holds = self.base.constraint_exprs().is_empty() || self.constraints_hold_gc(s, collect)?;
        if holds && self.base.possible_pending(false) {
            self.base.witness(&self.decode(s), None)?;
        }
        Ok(holds)
    }

    fn action_constraint(&self, s: &EState, t: &EState) -> Result<bool, ModelError> {
        self.check_state_model(s);
        self.check_state_model(t);
        // (Called on every state or step: nothing to do is cheap.)
        let holds = self.base.action_constraint_exprs().is_empty() || self.action_constraints_hold(s, t)?;
        if holds && self.base.possible_pending(true) {
            self.base.witness(&self.decode_current(s), Some(&self.decode(t)))?;
        }
        Ok(holds)
    }

    fn action_constraint_gc(&self, s: &EState, t: &EState, collect: &mut dyn FnMut(bool) -> bool) -> Result<bool, ModelError> {
        self.check_state_model(s);
        self.check_state_model(t);
        let holds = self.base.action_constraint_exprs().is_empty() || self.action_constraints_hold_gc(s, t, collect)?;
        if holds && self.base.possible_pending(true) {
            self.base.witness(&self.decode_current(s), Some(&self.decode(t)))?;
        }
        Ok(holds)
    }

    fn check_transition(&self, s: &EState, t: &EState) -> Result<Option<usize>, ModelError> {
        self.check_state_model(s);
        self.check_state_model(t);
        // (Called on every state or step: nothing to do is cheap.)
        if self.base.action_property_names().is_empty() {
            return Ok(None);
        }
        self.action_property_violated(s, t)
    }

    fn check_transition_gc(&self, s: &EState, t: &EState, collect: &mut dyn FnMut(bool) -> bool) -> Result<Option<usize>, ModelError> {
        self.check_state_model(s);
        self.check_state_model(t);
        if self.base.action_property_names().is_empty() {
            return Ok(None);
        }
        self.action_property_violated_gc(s, t, collect)
    }

    fn action_property_names(&self) -> &[String] {
        self.base.action_property_names()
    }
    fn extra_generated(&self) -> u64 {
        self.base.ip.composed_states.load(std::sync::atomic::Ordering::Relaxed)
    }

    fn stop_requested(&self) -> bool {
        self.base.stop_requested()
    }
    /// States are queued and written as their words (`StateCodec`).
    fn caps(&self) -> tlx_runtime::Caps<'_, EState> {
        tlx_runtime::Caps {
            format: Some(tlx_runtime::StateFormat::Words(self)),
            live_atoms: self.base.records_live_edges().then_some(self as _),
            effects: Some(self),
            checkpoint: Some(self),
            gc: self.value_store().map(|_| self as &dyn tlx_runtime::StoreGc<EState>),
        }
    }
    fn invariant_names(&self) -> &[String] {
        self.base.invariant_names()
    }

    fn action_names(&self) -> &[String] {
        self.base.action_names()
    }
    fn check_init_property(&self, s: &EState) -> Result<Option<String>, ModelError> {
        self.check_state_model(s);
        if !self.base.has_init_properties() {
            return Ok(None);
        }
        self.base.check_init_properties(&self.decode(s))
    }

    fn render(&self, s: &EState) -> String {
        self.check_state_model(s);
        self.base.render(&self.decode(s))
    }
}
