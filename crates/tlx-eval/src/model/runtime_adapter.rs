//! The `tlx_runtime::Model` adapter of the interpreted model (CODE-03).
//!
//! `InterpModel` is observed through the runtime `Model` interface; the
//! adapter forwards every capability (states, fingerprints, invariants,
//! constraints, transition properties, checkpointing) without a reduced
//! wrapper (`ARCH-10`). Extracted from `mod.rs`.

use super::*;
use tlx_runtime::Model;

impl Model for InterpModel {
    type State = State;

    fn uses_trace(&self) -> bool {
        self.ip.uses_trace()
    }

    fn trace_replay_limit(&self) -> Option<&'static str> {
        autosym::trace_replay_limit(self)
    }

    fn state_values(&self, s: &State) -> Option<Arc<[Value]>> {
        Some(s.vals.clone())
    }

    fn init_states(&self, out: &mut dyn FnMut(State)) -> Result<(), ModelError> {
        self.init_states_while(&mut |s| {
            out(s);
            true
        })
    }

    fn init_states_while(&self, out: &mut dyn FnMut(State) -> bool) -> Result<(), ModelError> {
        let mut err: Option<ModelError> = None;
        let mut emit = |s1: &[Option<Value>]| {
            // After an incomplete state, TLC still generates (counts) the
            // other initial states, and ignores them.
            if err.is_some() {
                self.count_generated();
                return Ok(true);
            }
            if let Some(e) = self.incomplete(s1, None) {
                self.count_generated();
                err = Some(e);
                return Ok(true);
            }
            match self.make_state_counted(s1, 1, "The initial state").map_err(|e| self.error(e)) {
                Ok(st) => Ok(out(st)),
                Err(e) => {
                    let msg = e.message.clone();
                    err = Some(e);
                    Err(EvalError::new(msg))
                }
            }
        };
        let r = self.ip.init_states(&self.init, &mut emit);
        if let Some(e) = err {
            return Err(e);
        }
        r.map_err(|e| self.error(e))
    }

    fn successors(&self, s: &State, out: &mut dyn FnMut(State, u32) -> bool) -> Result<(), ModelError> {
        if self.symmetry_check_due() {
            self.check_symmetry_claim(s);
        }
        // (With statistics, each action is timed on its own.)
        if stats::on() || self.actions.len() <= 1 {
            for i in 0..self.actions.len() {
                if !self.action_successors(s, i as u32, out)? {
                    break;
                }
            }
            return Ok(());
        }
        self.successors_all(s, out)
    }

    fn action_successors(&self, s: &State, action: u32, out: &mut dyn FnMut(State, u32) -> bool) -> Result<bool, ModelError> {
        let span = stats::span();
        let r = self.successors_of(s, action as usize, out);
        span.action(action as usize, stats::Path::Interp);
        r
    }

    fn fingerprint(&self, s: &State) -> u64 {
        s.fp
    }
    fn coarse_fingerprint(&self) -> bool {
        self.has_view_or_symmetry()
    }

    fn check_invariants(&self, s: &State) -> Result<Option<usize>, ModelError> {
        let cache = DefCache::over(self.memo(s), None);
        let cx = Ctx::state(&s.vals, s.level).with_cache(&cache);
        for i in 0..self.invariants.len() {
            let span = stats::span();
            let holds = self.invariant_holds(i, &cx);
            span.invariant(i, stats::Path::Interp);
            if !holds? {
                return Ok(Some(i));
            }
        }
        Ok(None)
    }

    fn constraint(&self, s: &State) -> Result<bool, ModelError> {
        let holds = self.all_hold(&self.constraints, &Ctx::state(&s.vals, s.level))?;
        if holds && self.possible_pending(false) {
            self.witness(s, None)?;
        }
        Ok(holds)
    }

    fn action_constraint(&self, s: &State, t: &State) -> Result<bool, ModelError> {
        if !self.action_constraints.is_empty() {
            let t1: Vec<Option<Value>> = t.vals.iter().cloned().map(Some).collect();
            if !self.all_hold(&self.action_constraints, &Ctx::action(&s.vals, &t1, s.level))? {
                return Ok(false);
            }
        }
        if self.possible_pending(true) {
            self.witness(s, Some(t))?;
        }
        Ok(true)
    }

    fn check_transition(&self, s: &State, t: &State) -> Result<Option<usize>, ModelError> {
        for i in 0..self.action_props.len() {
            let span = stats::span();
            let holds = self.check_action_property(s, t, i);
            span.aprop(i, stats::Path::Interp);
            if !holds? {
                return Ok(Some(i));
            }
        }
        Ok(None)
    }

    fn action_property_names(&self) -> &[String] {
        &self.action_prop_names
    }

    fn extra_generated(&self) -> u64 {
        self.ip.composed_states.load(std::sync::atomic::Ordering::Relaxed)
    }

    fn stop_requested(&self) -> bool {
        self.ip.exit_requested()
    }

    fn invariant_names(&self) -> &[String] {
        &self.invariant_names
    }

    /// States are written as values in checkpoints (`Persist`).
    fn caps(&self) -> tlx_runtime::Caps<'_, State> {
        tlx_runtime::Caps {
            format: Some(tlx_runtime::StateFormat::Bytes(self)),
            live_atoms: self.records_live_edges().then_some(self as _),
            effects: None,
            checkpoint: Some(self),
            gc: None,
        }
    }

    fn action_names(&self) -> &[String] {
        &self.action_names
    }

    fn check_init_property(&self, s: &State) -> Result<Option<String>, ModelError> {
        self.check_init_properties(s)
    }

    fn render(&self, s: &State) -> String {
        fmt_state(self.state_fields(&s.vals), false)
    }
}
