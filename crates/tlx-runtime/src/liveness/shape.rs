//! A counterexample as TLC shows it, and the properties it violates.

use std::borrow::Cow;

use super::{LiveInput, LiveResult, Violation};
use crate::AtomBits;

/// A counterexample as TLC shows it (LiveWorker.printTrace): a state is
/// not repeated, so steps between equal states (which differ only in the
/// tableau) are left out, and a cycle of a single state is a stuttering one.
pub(super) struct Shape {
    /// The positions shown, in order.
    pub(super) shown: Vec<Shown>,
    /// The index in `shown` of the cycle's first state.
    pub(super) cycle: usize,
    /// The action of the step closing the cycle.
    close: u32,
}

pub(super) struct Shown {
    /// Its position in the counterexample (the first of its run of equal
    /// states) and the action of the step into it (None: initial).
    pub(super) pos: usize,
    into: Option<u32>,
    /// The last position of the run: the step leaving it goes to the next
    /// state shown (from the last one: to the cycle's first).
    pub(super) leave: usize,
}

impl Shape {
    /// The shape of the counterexample `seq`, which lists the positions of
    /// the prefix (the first `prefix` ones) and of the cycle (after its last
    /// position comes its first): a key identifying the state, the state and
    /// the action of the step leaving it.
    pub(super) fn new<S>(seq: &[(u32, &S, u32)], prefix: usize) -> Shape {
        let action = |k: usize| seq[k].2;
        let key = |p: &Shown| seq[p.pos].0;
        let mut shown: Vec<Shown> = Vec::new();
        let mut cycle = 0;
        for (k, &(s, _, _)) in seq.iter().enumerate() {
            if k == prefix {
                cycle = shown.len();
            }
            if shown.last().is_some_and(|p| key(p) == s) {
                if k == prefix {
                    cycle -= 1;
                }
                continue;
            }
            if let Some(p) = shown.last_mut() {
                p.leave = k - 1;
            }
            shown.push(Shown { pos: k, into: (k > 0).then(|| action(k - 1)), leave: seq.len() - 1 });
        }
        // The step closing the cycle; states at the end of the cycle equal to
        // its first one are not shown either.
        let first = key(&shown[cycle]);
        let mut close = action(seq.len() - 1);
        while shown.len() > cycle + 1 && shown.last().is_some_and(|p| key(p) == first) {
            close = shown.pop().and_then(|p| p.into).unwrap_or(close);
        }
        Shape { shown, cycle, close }
    }

    /// The index in `shown` of the state after shown state `k`.
    pub(super) fn next(&self, k: usize) -> usize {
        if k + 1 < self.shown.len() {
            k + 1
        } else {
            self.cycle
        }
    }
}

/// A liveness counterexample as shown (see `Shape`): the prefix and the
/// cycle, closed by a step back to the cycle's first state.
pub struct Lasso<S> {
    /// The states shown, each with the action of the step into it (None:
    /// the initial state; `STUTTER`: a stuttering step).
    pub states: Vec<(S, Option<u32>)>,
    /// The index in `states` of the cycle's first state.
    pub cycle: usize,
    /// The action of the step closing the cycle.
    pub close: u32,
}

impl<S> Lasso<S> {
    /// Whether the cycle is a stuttering one (a single state).
    pub fn stuttering(&self) -> bool {
        self.states.len() == self.cycle + 1
    }

    /// The index in `states` of the state after shown state `k`.
    pub fn next(&self, k: usize) -> usize {
        if k + 1 < self.states.len() {
            k + 1
        } else {
            self.cycle
        }
    }
}

/// The violation of the properties `names` found checking part `prop`,
/// with the counterexample `seq` of shape `sh` (see `Shape::new`).
pub(super) fn violated<S: Clone>(names: Vec<String>, prop: usize, seq: &[(u32, &S, u32)], sh: &Shape) -> LiveResult<S> {
    let states = sh.shown.iter().map(|p| (seq[p.pos].1.clone(), p.into)).collect();
    LiveResult::Violated(Violation { names, prop, lasso: Lasso { states, cycle: sh.cycle, close: sh.close } })
}

/// The names of the temporal properties of `input` that the
/// counterexample `sh` violates, each property evaluated alone on the
/// states shown (TLC's `Liveness.findViolatedProperties`, once the
/// counterexample is found): in the order of the PROPERTIES, each name
/// once. `state(k)` gives the state-atom bits of shown state `k`, `step(k)`
/// the action-atom bits of the step from it to the next one (`Shape::next`).
///
/// If an atom cannot be evaluated, no property is named (TLC reports the
/// error and leaves the property out; the atoms were evaluated on these
/// states when the counterexample was found, so this is not expected).
pub(super) fn violated_names<'a>(
    input: &LiveInput,
    sh: &Shape,
    state: &mut dyn FnMut(usize) -> Result<Cow<'a, tlx_live::Bits>, String>,
    step: &mut dyn FnMut(usize) -> Result<Cow<'a, tlx_live::Bits>, String>,
) -> Vec<String> {
    let bits: Result<Vec<_>, String> = (0..sh.shown.len()).map(|k| Ok((state(k)?, step(k)?))).collect();
    let Ok(bits) = bits else { return Vec::new() };
    let (states, steps): (Vec<_>, Vec<_>) = bits.into_iter().unzip();
    let mut names: Vec<String> = Vec::new();
    for ((name, _), f) in input.props.iter().zip(input.alone) {
        if !names.contains(name) && !tlx_live::eval_lasso(f, &states, &steps, sh.cycle) {
            names.push(name.clone());
        }
    }
    names
}

/// The action-atom bits of the step `s -> t`.
pub(super) fn step_bits<S>(bits: &(dyn AtomBits<S> + Sync), s: &S, t: &S) -> Result<Cow<'static, tlx_live::Bits>, String> {
    bits.action(s, t).map(|b| Cow::Owned(tlx_live::Bits::from_words(&b))).map_err(|e| e.message)
}
