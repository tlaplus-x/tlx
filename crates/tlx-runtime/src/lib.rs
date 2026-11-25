//! tlx-runtime: model-agnostic parallel state exploration (design.md §7).

pub mod cache_mem;
pub mod dump;
pub mod explore;
pub mod fpset;
pub mod io;
pub mod live;
pub mod liveness;
pub mod mem;
pub mod model;
pub mod queue;
pub mod simulate;
mod size;
pub mod stats;

pub use dump::{DumpObserver, DumpOptions};
pub use explore::{
    explore, explore_from, explore_observed, explore_resumable, ActionMasks, AfterCommit, AtomBits, CheckpointConfig, CheckpointEvent,
    Checkpointer, Coverage, CoverageReport, ExpandedBatch, LiveGraph, Options, Outcome, Outdegree, Progress, Recovery, Report, ResumePoint,
    SearchObserver, Start, Stats, TraceStep, TranscodeError,
};
pub use fpset::FpConfig;
pub use live::{CurrentAction, LiveStats};
pub use mem::MemBudget;
pub use model::{
    admits, Caps, Checkpointed, Effects, ErrorContext, ErrorKind, GcEvent, GcResult, Model, ModelError, Persist, StateFormat, StoreGc,
    StoreGcRetry,
};
pub use queue::StateCodec;
pub use simulate::{simulate, SimOptions, SimPhase, SimProgress};
