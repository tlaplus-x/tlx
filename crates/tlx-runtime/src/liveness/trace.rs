//! Checking one simulated behavior (TLC's simulator).

use tlx_base::hash::FpMap;

use super::shape::{step_bits, violated, violated_names, Shape};
use super::{LiveInput, LiveResult, STUTTER};
use crate::{AtomBits, Model, ModelError};

/// Check the temporal properties TLC's way on one simulated behavior
/// (TLC's simulator: `LiveCheck1.checkTrace`): `trace` with the action into
/// each state, `succs[i]` all the successors of state `i` (for ENABLED);
/// `same` tells equal states apart from states with the same fingerprint.
pub fn check_trace<M: Model>(
    m: &M,
    input: &LiveInput,
    bits: &(dyn AtomBits<M::State> + Sync),
    trace: &[(M::State, Option<u32>)],
    succs: &[Vec<(M::State, u32)>],
    same: &dyn Fn(&M::State, &M::State) -> bool,
) -> LiveResult<M::State> {
    let states = match trace_states(m, bits, trace, succs, same) {
        Ok(t) => t,
        Err(e) => return LiveResult::Error(e),
    };
    for (i, (_, f)) in input.props.iter().enumerate() {
        if let Some(l) = tlx_live::check_trace(&states, f, &input.fairness) {
            let conc: Vec<u32> = l.prefix.iter().chain(&l.cycle).map(|s| trace_pos(s.conc)).collect();
            let seq: Vec<(u32, &M::State, u32)> =
                l.prefix.iter().chain(&l.cycle).zip(&conc).map(|(s, &c)| (s.node, &trace[c as usize].0, s.label)).collect();
            let sh = Shape::new(&seq, l.prefix.len());
            let names = violated_names(
                input,
                &sh,
                &mut |k| {
                    Ok(states
                        .iter()
                        .find(|t| t.conc == conc[sh.shown[k].pos])
                        .map_or_else(|| std::borrow::Cow::Owned(tlx_live::Bits::new()), |t| std::borrow::Cow::Borrowed(&t.bits)))
                },
                &mut |k| step_bits(bits, seq[sh.shown[k].pos].1, seq[sh.shown[sh.next(k)].pos].1),
            );
            return violated(names, i, &seq, &sh);
        }
    }
    LiveResult::Holds
}

/// The position in the behavior of a state of a `tlx_live::check_trace`
/// counterexample.
fn trace_pos(c: tlx_live::Conc) -> u32 {
    match c {
        tlx_live::Conc::State(i) => i,
        tlx_live::Conc::Succ { .. } => unreachable!("the product of a trace names its states"),
    }
}

/// The states of a behavior for `tlx_live::check_trace` (concrete state:
/// position in the behavior; graph node: fingerprint class). As TLC, steps
/// that leave the state unchanged are left out.
fn trace_states<M: Model>(
    m: &M,
    bits: &(dyn AtomBits<M::State> + Sync),
    trace: &[(M::State, Option<u32>)],
    succs: &[Vec<(M::State, u32)>],
    same: &dyn Fn(&M::State, &M::State) -> bool,
) -> Result<Vec<tlx_live::TraceState>, ModelError> {
    let mut nodes = FpMap::with_capacity(trace.len());
    let mut out = Vec::with_capacity(trace.len());
    for (i, (s, a)) in trace.iter().enumerate() {
        if i > 0 && same(&trace[i - 1].0, s) {
            continue;
        }
        let n = nodes.len() as u32;
        let node = *nodes.get_or_insert_with(m.fingerprint(s), || n);
        let stutter = bits.action(s, s)?;
        let mut outs = vec![stutter.clone()];
        for (t, _) in succs.get(i).map_or(&[][..], |v| v.as_slice()) {
            outs.push(bits.action(s, t)?);
        }
        let refs: Vec<&[u64]> = outs.iter().map(|b| b.as_slice()).collect();
        let sbits = bits.state(s, &refs)?;
        let step = if i > 0 { bits.action(&trace[i - 1].0, s)? } else { Vec::new() };
        out.push(tlx_live::TraceState {
            node,
            conc: i as u32,
            bits: tlx_live::Bits::from_words(&sbits),
            stutter: tlx_live::Bits::from_words(&stutter),
            step: tlx_live::Bits::from_words(&step),
            label: a.unwrap_or(STUTTER),
        });
    }
    Ok(out)
}
