//! tlx-eval: the reference interpreter (design.md §5) — constant evaluation,
//! TLC-style Init/Next enumeration, and an interpreted `Model`.

mod apply;
mod bags;
mod builtins;
mod code;
mod depth;
pub mod enumerate;
pub mod env;
pub mod error;
pub mod eval;
mod except;
pub mod interp;
mod java_order;
mod lazy;
mod memo;
pub mod model;
pub mod natives;
pub mod random;
mod seqfilter;
pub mod strings;
mod subsetfilter;

pub use error::EvalError;
pub use interp::{HoldMark, Interp, RunStats, SavedRegisters, SimConfig, SpecInfo};
pub use model::{FpMode, InterpModel, StateVals};
