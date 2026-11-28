//! Encoded liveness atoms and the runtime liveness capability.

use std::cell::OnceCell;
use std::sync::Arc;

use tlx_eval::model::liveness::{AtomBits, StateAtom};
use tlx_runtime::stats;
use tlx_runtime::{ErrorKind, Model, ModelError};
use tlx_value::Value;

use super::{live_bits, EState, EncModel, PredAt, MISS_MSG};
use crate::settings::InjectKind;

impl EncModel {
    /// The state-atom bits of `s` for liveness checking (natively where
    /// compiled); `out` are the action-atom bits of its outgoing steps.
    pub(super) fn live_state_bits(&self, s: &EState, out: &[&[u64]]) -> Result<Vec<u64>, ModelError> {
        if self.inject.is_some() && !self.restartable && self.inject_now(&[InjectKind::Miss]).is_some() {
            return Err(ModelError::of_kind(ErrorKind::LayoutMiss, MISS_MSG));
        }
        let live = &self.base.live;
        let decoded = OnceCell::new();
        live_bits(live.state_atoms.len(), |k| match &live.state_atoms[k] {
            StateAtom::EnabledVia(t, _) => Ok(out.iter().any(|b| b[*t as usize / 64] >> (t % 64) & 1 == 1)),
            StateAtom::Pred(_) => self.live_state_atom(s, k, &decoded),
        })
    }

    /// State atom `k` (a predicate, not `EnabledVia`) on `s`, natively where
    /// compiled (`decoded`: the values of `s`, once decoded).
    fn live_state_atom(&self, s: &EState, k: usize, decoded: &OnceCell<Arc<[Value]>>) -> Result<bool, ModelError> {
        let live = &self.base.live;
        let idx = self.live_state[k].expect("compiled state atom");
        let span = stats::span();
        let (holds, path) = self.predicate(
            PredAt { idx, s, t: None, level: s.level, inject: false },
            || None,
            || live.eval_state_atom(&self.base.ip, k, decoded.get_or_init(|| self.values(s)), s.level).map_err(|e| self.base.error(e)),
            |_| format!("liveness state atom {k} on state\n{}", self.render(s)),
        )?;
        span.invariant(idx, path);
        Ok(holds)
    }

    /// The atoms of the tableaux on `s` (see `AtomBits::tableau`).
    /// The bits of the tableau state atoms on `s` (`AtomBits::tableau_bits`;
    /// the others 0, `EnabledVia` atoms false).
    fn live_tableau_bits(&self, s: &EState) -> Result<Vec<u64>, ModelError> {
        let live = &self.base.live;
        let decoded = OnceCell::new();
        let mut out = vec![0u64; live.state_atoms.len().div_ceil(64)];
        for &k in &live.tableau {
            if matches!(live.state_atoms[k as usize], StateAtom::Pred(_)) && self.live_state_atom(s, k as usize, &decoded)? {
                out[k as usize / 64] |= 1 << (k % 64);
            }
        }
        Ok(out)
    }

    fn live_tableau(&self, s: &EState) -> Result<(), ModelError> {
        let live = &self.base.live;
        let decoded = OnceCell::new();
        for &k in &live.tableau {
            match &live.state_atoms[k as usize] {
                StateAtom::Pred(_) => self.live_state_atom(s, k as usize, &decoded).map(drop)?,
                StateAtom::EnabledVia(..) => {
                    let v = decoded.get_or_init(|| self.values(s));
                    live.eval_state_atom(&self.base.ip, k as usize, v, s.level).map_err(|e| self.base.error(e))?;
                }
            }
        }
        Ok(())
    }

    /// The action-atom bits of the step `s -> t` for liveness checking;
    /// with `mask`, only those of the atoms in it (the others 0).
    pub(super) fn live_action_bits(&self, s: &EState, t: &EState, mask: Option<&[u64]>) -> Result<Vec<u64>, ModelError> {
        let live = &self.base.live;
        let decoded = OnceCell::new();
        let values = || decoded.get_or_init(|| (self.cached_values(&s.words, true), self.values(t)));
        live_bits(live.action_atoms.len(), |k| {
            if mask.is_some_and(|m| m[k / 64] >> (k % 64) & 1 == 0) {
                return Ok(false);
            }
            let span = stats::span();
            let (holds, path) = self.predicate(
                PredAt { idx: self.live_action + k, s, t: Some(t), level: s.level, inject: false },
                || {
                    let (vs, vt) = live.next_steps.get(k).is_some_and(|&b| b).then(values)?;
                    live.step_atom(&self.base.ip, k, vs, vt, s.level)
                },
                || {
                    let (vs, vt) = values();
                    live.eval_action_atom(&self.base.ip, k, vs, vt, s.level).map_err(|e| self.base.error(e))
                },
                |note| format!("liveness action atom {k}{note} on step\n{}\n->\n{}", self.render(s), self.render(t)),
            )?;
            span.aprop(self.live_action + k, path);
            Ok(holds)
        })
    }
}

impl AtomBits<EState> for EncModel {
    fn live_input(&self) -> Option<tlx_runtime::liveness::LiveInput<'_>> {
        self.base.live_input()
    }

    fn state(&self, s: &EState, out: &[&[u64]]) -> Result<Vec<u64>, ModelError> {
        self.check_state_model(s);
        self.live_state_bits(s, out)
    }
    fn action(&self, s: &EState, t: &EState) -> Result<Vec<u64>, ModelError> {
        self.check_state_model(s);
        self.check_state_model(t);
        self.live_action_bits(s, t, None)
    }
    fn action_masks(&self) -> Option<&tlx_runtime::ActionMasks> {
        self.base.live.action_masks.as_ref()
    }
    fn action_only(&self, s: &EState, t: &EState, mask: &[u64]) -> Result<Vec<u64>, ModelError> {
        self.check_state_model(s);
        self.check_state_model(t);
        self.live_action_bits(s, t, Some(mask))
    }
    fn tableau(&self, t: &EState) -> Result<(), ModelError> {
        self.check_state_model(t);
        self.live_tableau(t)
    }
    fn tableau_bits(&self, t: &EState) -> Result<Vec<u64>, ModelError> {
        self.check_state_model(t);
        self.live_tableau_bits(t)
    }
    fn has_action_atoms(&self) -> bool {
        !self.base.live.action_atoms.is_empty()
    }
    fn stage_state(&self, t: &EState) -> Option<Box<dyn std::any::Any + Send + Sync>> {
        self.check_state_model(t);
        self.value_store().is_some().then(|| Box::new(self.values(t)) as Box<dyn std::any::Any + Send + Sync>)
    }
    fn action_staged(&self, s: &EState, staged: &(dyn std::any::Any + Send + Sync)) -> Result<Vec<u64>, ModelError> {
        self.check_state_model(s);
        let vt = staged.downcast_ref::<Arc<[Value]>>().expect("staged EncModel state");
        let live = &self.base.live;
        let vs = self.cached_values(&s.words, true);
        live_bits(live.action_atoms.len(), |k| {
            if live.next_steps.get(k).is_some_and(|&b| b) {
                if let Some(holds) = live.step_atom(&self.base.ip, k, &vs, vt, s.level) {
                    return Ok(holds);
                }
            }
            live.eval_action_atom(&self.base.ip, k, &vs, vt, s.level).map_err(|e| self.base.error(e))
        })
    }
}
