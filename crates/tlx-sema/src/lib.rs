//! tlx-sema: module loading, name resolution, INSTANCE expansion (design.md §3.2).

pub mod builtins;
pub mod hir;
pub mod optimize;
pub mod resolve;
pub mod source;
pub mod visit;

pub use resolve::{CfgLevelError, CfgNameError, CfgSubstError, Program, SemaError, SourceFile};
