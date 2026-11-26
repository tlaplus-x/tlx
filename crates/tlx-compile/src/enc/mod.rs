//! Compiled tier over encoded states (design.md §6).
//!
//! States are fixed-width word arrays in a speculated layout. Each action
//! instance runs as native code or lowered IR into a buffer; if anything
//! unexpected happens for a (state, action) pair — a runtime error or a
//! value that does not fit an intermediate layout — the buffer is discarded
//! and that pair is re-run by the interpreter, whose semantics are exact. A
//! successor state that does not fit the layout is a *layout miss*:
//! exploration stops, the driver widens the offending variable's shape and
//! restarts. Nothing restarts after the search: there a value that does
//! not fit a materialized definition is evaluated by the interpreter, and a
//! phase that still misses (`is_layout_miss`) is redone by the interpreter
//! (liveness, `-dump`: see tlx-cli).
//!
//! - `model`: `EncModel`, the runtime `Model` over encoded states;
//! - `native`: building and loading the generated C library;
//! - `mixed`: host regions of mixed-mode native code;
//! - `adapt`: per function, the faster of mixed native code and its
//!   fallback;
//! - `speculate`: shape speculation (hints, pre-run, materialization
//!   candidates);
//! - `driver`: `check`, the restart loop;
//! - `closure`: whether a layout can ever miss (archive elision);
//! - `diag`: diagnostics (coverage logging, IR dumps).

mod adapt;
mod cache;
mod closure;
mod diag;
mod driver;
mod escape;
pub mod mixed;
mod model;
mod native;
mod region_eq;
mod speculate;

pub use driver::{check, check_from, simulate, Checked};
pub use model::{EState, EncModel};
pub use native::native_unavailable;
pub use speculate::{hints, materialize_candidates, prerun_shapes, Prerun, PrerunBudget};
