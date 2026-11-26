//! The limit on the number of elements of a materialized set: TLC's
//! `TLCGlobals.setBound`, set by `-maxSetSize` (default 10^6).
//!
//! TLC builds an enumerated set in a `ValueVec`, whose capacity may grow only
//! up to `setBound`; adding one more element once it is full fails with
//! "Attempted to construct a set with too many elements (>N)."
//! ([tlc-semantics.md] section 4). Two details of that check decide the
//! observable behavior:
//!
//! - A `ValueVec` starts with ten slots, and the bound is checked only when
//!   the vector has to grow. A set *appended to* may therefore hold up to
//!   `max(10, setBound)` elements: with `-maxSetSize 4`, the eleventh
//!   element is the first that fails, not the fifth.
//! - Some constructions preallocate the exact length (`IntervalValue.toSetEnum`,
//!   `SubsetValue.toSetEnum`, and a set literal), so they never grow and the
//!   bound does not apply to them at all.
//!
//! A set is *materialized* where TLC's enumeration asks for the normalized
//! order or otherwise builds the whole set: `[S -> T]`, `S \X T`, a record
//! set, a set former, a set filter over an enumerable set, a union or
//! difference of such sets, and the domain of a quantifier over them. The
//! streaming paths (`x' \in S`, `{x \in S : P}`, `SUBSET S` and
//! `kSubset(k, S)` bounds, printing) never build the set and are not limited,
//! and neither is a set that is already enumerated.
//!
//! The limit is a process-wide value, as in TLC: the command line sets it
//! once, before the model is loaded, and workers only read it.

use std::sync::atomic::{AtomicI64, Ordering};

use crate::{Result, ValueError};

/// TLC's default `-maxSetSize` (`TLCGlobals.setBound`).
pub const DEFAULT_MAX_SET_SIZE: i64 = 1_000_000;

/// The slots TLC's `ValueVec()` starts with (`V/ValueVec.java`): a growing
/// set can hold this many elements whatever the bound is.
const GROWTH_INITIAL: i64 = 10;

static MAX_SET_SIZE: AtomicI64 = AtomicI64::new(DEFAULT_MAX_SET_SIZE);

/// The most elements a materialized set may have.
pub fn max_set_size() -> i64 {
    MAX_SET_SIZE.load(Ordering::Relaxed)
}

/// Set the limit (`-maxSetSize`; TLC accepts a positive int).
pub fn set_max_set_size(n: i64) {
    debug_assert!(n >= 1);
    MAX_SET_SIZE.store(n.max(1), Ordering::Relaxed);
}

/// The most elements a set that is *grown* element by element may hold: the
/// bound, or the ten slots TLC's `ValueVec` starts with when the bound is
/// lower (its check runs only when the vector grows).
pub fn growth_limit() -> i64 {
    GROWTH_INITIAL.max(max_set_size())
}

/// TLC's error for a set that would hold more than [`max_set_size`] elements
/// (`ValueVec.ensureCapacity`).
pub fn too_many_elements() -> ValueError {
    ValueError::new(format!("Attempted to construct a set with too many elements (>{})", max_set_size()))
}

/// Check the length of a set that is about to be materialized by growing it:
/// `n` elements, or (for a construction stopped at the limit) `n` elements
/// plus the one that would exceed it.
pub fn check_set_size(n: usize) -> Result<()> {
    if n as i64 > growth_limit() {
        return Err(too_many_elements());
    }
    Ok(())
}

/// Push an element of a set that is being materialized. TLC's growing
/// `ValueVec` fails while adding the element that would exceed the limit, so
/// the collection stops there instead of building the whole set first (the
/// sources of a set former or a filter can be intervals of billions of
/// elements).
pub fn push(out: &mut Vec<crate::Value>, v: crate::Value) -> Result<()> {
    if out.len() as i64 >= growth_limit() {
        return Err(too_many_elements());
    }
    out.push(v);
    Ok(())
}
