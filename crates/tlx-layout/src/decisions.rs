//! Why each slot of a layout got its shape (`-stats`).
//!
//! Shape inference notes the rejections it makes (a map that would need an
//! unproven key order, a union with too many kinds, an open-ended string
//! universe, ...) on the slot it is working on (`in_slot`); the compiled
//! tier's driver notes misses, widenings, bounds and fallbacks on a slot
//! directly (`note_for`). Off unless `enable` was called: every hook first
//! checks one relaxed load of a static.

use std::cell::Cell;
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Mutex;

use crate::layout::bitset_universe;
use crate::shape::Shape;

/// A slot of the layout: a state variable or a materialized definition
/// (by `DefId` index).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Slot {
    Var(u32),
    Def(u32),
}

static ON: AtomicBool = AtomicBool::new(false);

thread_local! {
    static CURRENT: Cell<Option<Slot>> = const { Cell::new(None) };
}

/// Per slot, the distinct notes in the order first seen, with how often
/// each was made.
static LOG: Mutex<BTreeMap<Slot, Vec<(String, u64)>>> = Mutex::new(BTreeMap::new());

/// Start recording (for the rest of the process).
pub fn enable() {
    ON.store(true, Ordering::Relaxed);
}

#[inline]
pub fn on() -> bool {
    ON.load(Ordering::Relaxed)
}

/// Run `f` with the notes it makes attributed to `slot`.
#[inline]
pub fn in_slot<T>(slot: Slot, f: impl FnOnce() -> T) -> T {
    if !on() {
        return f();
    }
    let prev = CURRENT.with(|c| c.replace(Some(slot)));
    let r = f();
    CURRENT.with(|c| c.set(prev));
    r
}

/// Note `what` on the slot being worked on (nothing outside `in_slot`).
#[inline]
pub(crate) fn note(what: impl FnOnce() -> String) {
    if !on() {
        return;
    }
    if let Some(slot) = CURRENT.with(|c| c.get()) {
        note_for(slot, what());
    }
}

/// Note `what` on `slot`.
pub fn note_for(slot: Slot, what: String) {
    if !on() {
        return;
    }
    let mut log = LOG.lock().unwrap_or_else(|e| e.into_inner());
    let notes = log.entry(slot).or_default();
    match notes.iter_mut().find(|(w, _)| *w == what) {
        Some((_, n)) => *n += 1,
        None => notes.push((what, 1)),
    }
}

/// The notes on `slot` so far, with their counts.
pub fn notes(slot: Slot) -> Vec<(String, u64)> {
    LOG.lock().unwrap_or_else(|e| e.into_inner()).get(&slot).cloned().unwrap_or_default()
}

/// A short description of a shape: its kind and the parameters that
/// decide its size (the full shape can be thousands of characters).
pub fn summary(s: &Shape) -> String {
    match s {
        Shape::Never => "Never".into(),
        Shape::Bool => "Bool".into(),
        Shape::Int { lo, hi } => format!("Int {lo}..{hi}"),
        Shape::Atom(u) => format!("Atom({})", u.len()),
        Shape::Set { elem, max_card } => match bitset_universe(elem) {
            Some(u) => format!("Set bitset({u}) of {}", summary(elem)),
            None => format!("Set sorted(max {max_card}) of {}", summary(elem)),
        },
        Shape::Seq { elem, max_len } => format!("Seq(max {max_len}) of {}", summary(elem)),
        Shape::Fcn { dom, range, witness, key_variants } => {
            if key_variants.is_empty() {
                format!("Fcn({} keys, {witness:?}) to {}", dom.len(), summary(range))
            } else {
                format!("Fcn({} keys, {witness:?}, {} key variants) to {}", dom.len(), key_variants.len(), summary(range))
            }
        }
        Shape::Map { key, range, witness } => {
            format!("Map(universe {}, {witness:?}) of {} to {}", key.cardinality().unwrap_or(0), summary(key), summary(range))
        }
        Shape::Record(fs) => format!("Record({} fields)", fs.len()),
        Shape::Tuple(es) => format!("Tuple({})", es.len()),
        Shape::Union(arms) => format!("Union({} arms)", arms.len()),
        Shape::Dyn => "Dyn".into(),
        Shape::Ref(_) => "Ref".into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::infer::Observer;
    use tlx_value::{Sym, Value};

    /// Observing functions with varying domains whose keys have no
    /// encoding in TLC order notes why the slot is `Dyn`, on that slot only.
    #[test]
    fn dyn_maps_note_their_reason_on_their_slot() {
        enable();
        let rec = |n: i64| Value::record(vec![(Sym::new("seq"), Value::tuple((0..n).map(Value::Int).collect()))]);
        let f = Value::fcn_rcd_from_pairs(vec![(rec(0), Value::Int(0)), (rec(1), Value::Int(1))]).unwrap();
        let g = Value::fcn_rcd_from_pairs(vec![(rec(2), Value::Int(0))]).unwrap();
        let mut obs = Observer::for_slots(vec![Slot::Def(901), Slot::Def(902)]);
        obs.observe(&[f, Value::Int(3)]);
        obs.observe(&[g, Value::Int(3)]);
        assert_eq!(obs.shapes[0], Shape::Dyn);
        let notes = super::notes(Slot::Def(901));
        assert!(notes.iter().any(|(w, _)| w.starts_with("Dyn: function keys")), "{notes:?}");
        assert!(super::notes(Slot::Def(902)).is_empty());
        assert_eq!(summary(&Shape::Int { lo: 0, hi: 3 }), "Int 0..3");
    }
}
