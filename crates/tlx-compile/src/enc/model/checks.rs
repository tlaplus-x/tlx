//! Encoded-model checks and paranoid equivalence with the interpreter.

use std::cell::OnceCell;

use tlx_eval::EvalError;
use tlx_runtime::stats;
use tlx_runtime::{Model, ModelError};
use tlx_value::Value;

use super::{EState, EncModel, PredAt};
use crate::paranoid::{compare_states, mismatch, state_list};

impl EncModel {
    /// Paranoid: compare the compiled successors of `s` by action `i` with
    /// the interpreter's (as multisets: TLC counts duplicates as generated).
    pub(super) fn cross_check(&self, s: &EState, i: usize, compiled: &[Box<[u64]>]) -> Result<(), ModelError> {
        let vs = self.decode_current(s);
        let mut want: Vec<Vec<Value>> = Vec::new();
        // Not `successors_of`: that also fingerprints the successors (VIEW)
        // and counts failing ones as generated, which `finish` does as well.
        // (The compiled run had the side effects.)
        let r = self.base.ip.without_effects(|| self.base.successor_values_of(&vs, i, &mut |t| want.push(t.to_vec())));
        let got: Vec<Vec<Value>> = compiled
            .iter()
            // SAFETY: the matching encoder/program produced these words.
            // Active Dyn handles were published before this call.
            .map(|w| unsafe { self.layout.decode_state_unchecked(w) })
            .collect();
        let what = || format!("action {} on state\n{}", self.base.action_names()[i], self.base.render(&vs));
        if let Err(e) = r {
            // Compiled code must have failed (and left it to the
            // interpreter) where the interpreter reports an error.
            mismatch(format_args!(
                "{}\nthe interpreter fails ({}) but compiled code produced {} successor(s):\n{}",
                what(),
                e.message,
                got.len(),
                state_list(&self.base, &got)
            ));
        }
        self.check_store_slots(&what, &want, compiled)?;
        compare_states(&self.base, &what, want, got);
        Ok(())
    }

    /// Paranoid, with value store slots: the multisets of the slots'
    /// handles of the `compiled` states and of the interpreter's `want`
    /// states (stored) must be equal. The store interns by representation,
    /// so this checks that compiled code keeps how every function was built
    /// (`Value` equality, which `compare_states` checks, ignores it).
    pub(super) fn check_store_slots(
        &self,
        what: &dyn Fn() -> String,
        want: &[Vec<Value>],
        compiled: &[Box<[u64]>],
    ) -> Result<(), ModelError> {
        let Some(sem) = &self.sem else { return Ok(()) };
        let Some(store) = &sem.store else { return Ok(()) };
        let refs: Vec<usize> = (0..self.layout.vars.len()).filter(|&i| sem.ref_vars[i]).collect();
        if refs.is_empty() || want.len() != compiled.len() {
            return Ok(());
        }
        let mut got: Vec<Vec<u64>> = compiled.iter().map(|w| refs.iter().map(|&i| w[self.layout.offsets[i]]).collect()).collect();
        let mut exp: Vec<Vec<u64>> = Vec::with_capacity(want.len());
        for s in want {
            let mut row = Vec::with_capacity(refs.len());
            for &i in &refs {
                match store.freeze(&s[i]) {
                    Ok(h) => row.push(h),
                    Err(tlx_layout::store::StoreError::Full) => return Err(self.store_full_error()),
                    Err(_) => row.push(u64::MAX),
                }
            }
            exp.push(row);
        }
        got.sort_unstable();
        exp.sort_unstable();
        if got != exp {
            let show = |hs: &[Vec<u64>]| {
                hs.iter()
                    .map(|h| h.iter().map(|x| format!("{:?}", store.try_thaw(*x))).collect::<Vec<_>>().join(", "))
                    .collect::<Vec<_>>()
                    .join("\n  ")
            };
            mismatch(format_args!(
                "{}\nvalue store slots differ in representation:\ninterpreter:\n  {}\ncompiled:\n  {}",
                what(),
                show(&exp),
                show(&got)
            ));
        }
        Ok(())
    }

    /// Paranoid: compare the compiled initial states with the
    /// interpreter's.
    pub(super) fn cross_check_init(&self, compiled: &[Box<[u64]>]) -> Result<(), ModelError> {
        let mut want: Vec<Vec<Value>> = Vec::new();
        // The values only (not `init_states_until`: that also fingerprints
        // the states, and a VIEW may fail on them, which `finish` reports).
        // (The compiled run had the side effects.)
        let r = self.base.ip.without_effects(|| {
            self.base.ip.init_states(self.base.init_expr(), &mut |s1| {
                let vals = s1.iter().map(|v| -> Result<Value, EvalError> {
                    Ok(v.as_ref().ok_or_else(|| EvalError::new("an initial state is not completely specified"))?.normalize()?)
                });
                want.push(vals.collect::<Result<_, _>>()?);
                Ok(true)
            })
        });
        let got: Vec<Vec<Value>> = compiled
            .iter()
            // SAFETY: the matching encoder/program produced these words.
            // Active Dyn handles were published before this call.
            .map(|w| unsafe { self.layout.decode_state_unchecked(w) })
            .collect();
        if let Err(e) = r {
            mismatch(format_args!("Init: the interpreter fails ({}) but compiled code produced {} initial state(s)", e.message, got.len()));
        }
        self.check_store_slots(&|| "Init".to_string(), &want, compiled)?;
        compare_states(&self.base, &|| "Init".to_string(), want, got);
        Ok(())
    }

    /// The first invariant violated by `s`, if any (`check_invariants`).
    #[inline(never)]
    pub(super) fn invariants_violated(&self, s: &EState) -> Result<Option<usize>, ModelError> {
        let decoded = OnceCell::new();
        for i in 0..self.base.invariant_names().len() {
            let span = stats::span();
            let (holds, path) = self.predicate(
                PredAt { idx: i, s, t: None, level: s.level, inject: true },
                || None,
                || Ok(self.base.check_invariant(decoded.get_or_init(|| self.decode(s)), i)?.is_none()),
                |_| format!("invariant {} on state\n{}", self.base.invariant_names()[i], self.render(s)),
            )?;
            span.invariant(i, path);
            if !holds {
                return Ok(Some(i));
            }
        }
        Ok(None)
    }

    /// GC-aware `invariants_violated`: retries only the failing invariant `i`
    /// across `collect(force_drop_archive)` so earlier invariants' committed
    /// side effects (`TLCSet`, `PrintT`) are never replayed.
    #[inline(never)]
    pub(super) fn invariants_violated_gc(&self, s: &EState, collect: &mut dyn FnMut(bool) -> bool) -> Result<Option<usize>, ModelError> {
        let decoded = OnceCell::new();
        for i in 0..self.base.invariant_names().len() {
            let span = stats::span();
            let (holds, path) = self.predicate_gc(
                PredAt { idx: i, s, t: None, level: s.level, inject: true },
                || None,
                || Ok(self.base.check_invariant(decoded.get_or_init(|| self.decode(s)), i)?.is_none()),
                |_| format!("invariant {} on state\n{}", self.base.invariant_names()[i], self.render(s)),
                collect,
            )?;
            span.invariant(i, path);
            if !holds {
                return Ok(Some(i));
            }
        }
        Ok(None)
    }

    /// Whether every CONSTRAINT holds on `s` (`constraint`).
    #[inline(never)]
    pub(super) fn constraints_hold(&self, s: &EState) -> Result<bool, ModelError> {
        let decoded = OnceCell::new();
        for i in 0..self.base.constraint_exprs().len() {
            let span = stats::span();
            let (holds, path) = self.predicate(
                PredAt { idx: self.constraint_at + i, s, t: None, level: s.level, inject: false },
                || None,
                || self.base.check_constraint(decoded.get_or_init(|| self.decode(s)), i),
                |_| format!("CONSTRAINT {i} on state\n{}", self.render(s)),
            )?;
            span.invariant(self.constraint_at + i, path);
            if !holds {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// GC-aware `constraints_hold`: retries only the failing constraint `i`.
    #[inline(never)]
    pub(super) fn constraints_hold_gc(&self, s: &EState, collect: &mut dyn FnMut(bool) -> bool) -> Result<bool, ModelError> {
        let decoded = OnceCell::new();
        for i in 0..self.base.constraint_exprs().len() {
            let span = stats::span();
            let (holds, path) = self.predicate_gc(
                PredAt { idx: self.constraint_at + i, s, t: None, level: s.level, inject: false },
                || None,
                || self.base.check_constraint(decoded.get_or_init(|| self.decode(s)), i),
                |_| format!("CONSTRAINT {i} on state\n{}", self.render(s)),
                collect,
            )?;
            span.invariant(self.constraint_at + i, path);
            if !holds {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Whether every ACTION_CONSTRAINT holds on `s -> t` (`action_constraint`).
    #[inline(never)]
    pub(super) fn action_constraints_hold(&self, s: &EState, t: &EState) -> Result<bool, ModelError> {
        let decoded = OnceCell::new();
        for i in 0..self.base.action_constraint_exprs().len() {
            let span = stats::span();
            let (holds, path) = self.predicate(
                PredAt { idx: self.action_constraint_at + i, s, t: Some(t), level: s.level, inject: false },
                || None,
                || {
                    let (vs, vt) = decoded.get_or_init(|| (self.decode_current(s), self.decode(t)));
                    self.base.check_action_constraint(vs, vt, i)
                },
                |_| format!("ACTION_CONSTRAINT {i} on step\n{}\n->\n{}", self.render(s), self.render(t)),
            )?;
            span.aprop(self.action_constraint_at + i, path);
            if !holds {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// GC-aware `action_constraints_hold`: retries only the failing constraint `i`.
    #[inline(never)]
    pub(super) fn action_constraints_hold_gc(
        &self,
        s: &EState,
        t: &EState,
        collect: &mut dyn FnMut(bool) -> bool,
    ) -> Result<bool, ModelError> {
        let decoded = OnceCell::new();
        for i in 0..self.base.action_constraint_exprs().len() {
            let span = stats::span();
            let (holds, path) = self.predicate_gc(
                PredAt { idx: self.action_constraint_at + i, s, t: Some(t), level: s.level, inject: false },
                || None,
                || {
                    let (vs, vt) = decoded.get_or_init(|| (self.decode_current(s), self.decode(t)));
                    self.base.check_action_constraint(vs, vt, i)
                },
                |_| format!("ACTION_CONSTRAINT {i} on step\n{}\n->\n{}", self.render(s), self.render(t)),
                collect,
            )?;
            span.aprop(self.action_constraint_at + i, path);
            if !holds {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// The first action property violated by `s -> t`, if any (`check_transition`).
    #[inline(never)]
    pub(super) fn action_property_violated(&self, s: &EState, t: &EState) -> Result<Option<usize>, ModelError> {
        let decoded = OnceCell::new();
        for i in 0..self.base.action_property_names().len() {
            let span = stats::span();
            let (holds, path) = self.predicate(
                PredAt { idx: i, s, t: Some(t), level: s.level, inject: false },
                || None,
                || {
                    let (vs, vt) = decoded.get_or_init(|| (self.decode_current(s), self.decode(t)));
                    self.base.check_action_property(vs, vt, i)
                },
                |_| format!("action property {} on step\n{}\n->\n{}", self.base.action_property_names()[i], self.render(s), self.render(t)),
            )?;
            span.aprop(i, path);
            if !holds {
                return Ok(Some(i));
            }
        }
        Ok(None)
    }

    /// GC-aware `action_property_violated`: retries only the failing property `i`.
    #[inline(never)]
    pub(super) fn action_property_violated_gc(
        &self,
        s: &EState,
        t: &EState,
        collect: &mut dyn FnMut(bool) -> bool,
    ) -> Result<Option<usize>, ModelError> {
        let decoded = OnceCell::new();
        for i in 0..self.base.action_property_names().len() {
            let span = stats::span();
            let (holds, path) = self.predicate_gc(
                PredAt { idx: i, s, t: Some(t), level: s.level, inject: false },
                || None,
                || {
                    let (vs, vt) = decoded.get_or_init(|| (self.decode_current(s), self.decode(t)));
                    self.base.check_action_property(vs, vt, i)
                },
                |_| format!("action property {} on step\n{}\n->\n{}", self.base.action_property_names()[i], self.render(s), self.render(t)),
                collect,
            )?;
            span.aprop(i, path);
            if !holds {
                return Ok(Some(i));
            }
        }
        Ok(None)
    }

    /// Paranoid: fail unless the compiled verdict `b` of a predicate is the
    /// interpreter's (`interp`); `what` describes the predicate and states.
    pub(super) fn check_verdict(&self, b: bool, interp: Result<bool, ModelError>, what: impl FnOnce() -> String) {
        match interp {
            Ok(x) if x == b => {}
            Ok(x) => mismatch(format_args!("{}\ninterpreter: {x}\ncompiled:    {b}", what())),
            Err(e) => mismatch(format_args!("{}\nthe interpreter fails ({}) but compiled code gives {b}", what(), e.message)),
        }
    }
}

/// The interpreter's side effects across the restarts and resumes of the
/// compiled search.
impl tlx_runtime::Effects for EncModel {
    fn mark(&self) {
        self.base.ip.effects_mark();
    }
    fn worker_end(&self) {
        self.base.ip.effects_worker_end();
    }
    fn replaying(&self, on: bool) {
        self.base.ip.set_suppress_print(on);
    }
    fn interrupts(&self, e: &ModelError) -> bool {
        self.restartable && e.is_layout_miss()
    }
    fn resumes(&self, e: &ModelError) -> bool {
        self.interrupts(e)
    }
}
