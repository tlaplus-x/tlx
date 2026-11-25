//! tlx-layout: shapes and fixed-width state layouts of the compiled tier
//! (design.md §6.2).
//!
//! - `shape`: `Shape`s (static value types) and their operations;
//! - `infer`: speculative shape inference from observed values;
//! - `layout`: the fixed-width word layout derived from shapes, with
//!   canonical encode/decode and ranking between `Value`s and `u64` words;
//! - `layout_tree`: shapes compiled into `LayoutNode`s with the layout facts
//!   precomputed (the fast path of `layout`'s functions);
//! - `permute`: SYMMETRY permutations applied to encodings;
//! - `dynval`: the interner for values stored in `Dyn` slots;
//! - `scalar`: the immediate scalar handle schema shared by `dynval`,
//!   `store` and the C/JIT backends;
//! - `decisions`: why each slot got its shape (`-stats`);
//! - `store`: the run-owned value store of `Ref` slots (`TLX_VALUE_STORE`);
//! - `ser`: binary serialization of shapes, layouts and the `Dyn` interner.

pub mod decisions;
pub mod dynval;
pub mod escape;
pub mod infer;
pub mod layout;
pub mod layout_tree;
pub mod pack;
pub mod permute;
pub mod scalar;
pub mod ser;
pub mod shape;
pub mod store;

pub use layout::{Layout, Miss};
pub use layout_tree::LayoutNode;
pub use shape::Shape;
