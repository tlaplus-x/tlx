//! Cumulative observations are independent of the tierer's resettable state.
//! Revisiting an installed escape model must reuse its observation, even though
//! the existing tiering policy warms/samples again after every model switch.

use std::cell::RefCell;
use std::collections::HashMap;

use tlx_runtime::stats;

use super::{Tier, TIERS};

// Model identities never repeat; each Native has two write-once library slots.
type Key = (u64, usize, usize, usize);

#[derive(Default)]
struct Observation {
    sample_calls: [u64; 2],
    sample_ns: [u64; 2],
    decisions: [u64; 2],
    chosen: Option<bool>,
    means: Option<(f64, f64)>,
    phase: &'static str,
    dirty: bool,
}

thread_local! {
    static OBSERVATIONS: RefCell<HashMap<Key, Observation>> = RefCell::new(HashMap::new());
}

pub(super) fn observe(key: Key, tier: &Tier, sample: Option<(bool, u64, Option<bool>)>) {
    OBSERVATIONS.with(|rows| {
        let mut rows = rows.borrow_mut();
        let row = rows.entry(key).or_default();
        let phase = if tier.sampling {
            "sampling"
        } else if tier.chosen.is_none() {
            "warming"
        } else {
            "running"
        };
        row.dirty |= row.phase != phase;
        row.phase = phase;
        if let Some((native, ns, chosen)) = sample {
            row.sample_calls[(!native) as usize] += 1;
            row.sample_ns[(!native) as usize] += ns;
            if let Some(chosen) = chosen {
                row.decisions[(!chosen) as usize] += 1;
                row.chosen = Some(chosen);
                row.means = tier.means;
            }
            row.dirty = true;
        }
    });
}

/// Publish only changed observations, outside the timed adaptive evaluation.
pub(in crate::enc) fn publish(model: u64, kind: usize, i: usize, name: &str) {
    let lib = TIERS.with(|tiers| tiers.borrow().lib);
    OBSERVATIONS.with(|rows| {
        let mut rows = rows.borrow_mut();
        let row = rows.get_mut(&(model, lib, kind, i)).expect("observed adaptive call");
        if !row.dirty { return; }
        row.dirty = false;
        let thread = format!("{:?}", std::thread::current().id());
        let key = format!("adaptive_tiers_{model}_{thread}_{lib}_{kind}_{i}");
        let library = if lib == 1 { "quick" } else { "optimized" };
        let kind = ["action", "state_predicate", "transition_predicate"][kind];
        let chosen = match row.chosen { Some(true) => "mixed_native", Some(false) => "fallback", None => "undecided" };
        let phase = row.phase;
        let [nc, fc] = row.sample_calls;
        let [nt, ft] = row.sample_ns;
        let [nd, fd] = row.decisions;
        let (nm, fm) = row.means.map_or(("null".into(), "null".into()), |(n, f)| (n.to_string(), f.to_string()));
        stats::set_json(&key, format!(
            "{{\"model\":{model},\"worker\":{},\"library\":\"{library}\",\"kind\":{},\"index\":{i},\"name\":{},\"phase\":{},\"chosen\":{},\"sample_calls\":{{\"mixed_native\":{nc},\"fallback\":{fc}}},\"sample_ns\":{{\"mixed_native\":{nt},\"fallback\":{ft}}},\"decisions\":{{\"mixed_native\":{nd},\"fallback\":{fd}}},\"last_trimmed_mean_ns\":{{\"mixed_native\":{nm},\"fallback\":{fm}}}}}",
            stats::json_string(&thread), stats::json_string(kind), stats::json_string(name), stats::json_string(phase), stats::json_string(chosen)));
        stats::set_section(&key, format!("  {kind} {name} #{i} ({library}): {phase}, chosen {chosen}; samples mixed_native={nc} ({nt} ns), fallback={fc} ({ft} ns); decisions mixed_native={nd}, fallback={fd}\n"));
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::enc::adapt::{choose, record, ACTION, SAMPLES};

    #[test]
    fn revisiting_models_accumulates_without_inventing_libraries() {
        stats::enable(1);
        let models = [1 << 50, (1 << 50) + 1];
        for _ in 0..1000 {
            for model in models {
                // The tierer still resets on every switch, so both paths are
                // resampled. Reporting alone accumulates across those resets.
                for _ in 0..2 * SAMPLES {
                    let c = choose(model, 1, ACTION, 0, 0);
                    assert!(c.timed);
                    record(model, 1, ACTION, 0, c.native, if c.native { 300 } else { 100 });
                }
                publish(model, ACTION, 0, "alternating-model");
            }
        }
        OBSERVATIONS.with(|rows| {
            let rows = rows.borrow();
            assert_eq!(rows.len(), 2);
            for model in models {
                let row = &rows[&(model, 1, ACTION, 0)];
                assert_eq!(row.sample_calls, [32_000, 32_000]);
                assert_eq!(row.decisions, [0, 1000]);
                assert_eq!(row.sample_ns, [9_600_000, 3_200_000]);
            }
        });
        choose(models[0], 2, ACTION, 0, 0);
        publish(models[0], ACTION, 0, "alternating-model");
        OBSERVATIONS.with(|rows| assert_eq!(rows.borrow().len(), 3));
        assert_eq!(stats::json().matches("\"name\":\"alternating-model\"").count(), 3);
    }
}
