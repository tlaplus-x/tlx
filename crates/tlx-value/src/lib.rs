//! tlx-value: dynamic TLA+ values with TLC-compatible semantics
//! (design.md §4–5, docs/tlc-semantics.md §1–4, §6–7).
//!
//! Canonical forms (so that structural equality/hash = semantic equality):
//! - a function whose domain is `1..n` (n >= 0, including the empty function)
//!   is a `Tuple`, a function whose domain is a non-empty set of strings is a
//!   `Record`, any other finite function is an `Fcn` with pairs sorted by key
//!   (`Value::fcn_from_pairs`); except that a function TLC builds as an
//!   `FcnRcdValue` over an enumerated domain stays an `Fcn` even with such a
//!   domain (`Value::fcn_rcd_from_pairs`, `FcnKind`): it compares, hashes,
//!   fingerprints and prints as its `Tuple` / `Record` form, but EXCEPT and
//!   application look its keys up by equality, like TLC;
//! - `Set` is sorted in TLC order without duplicates.
//!
//! `Interval` and `LazySet` are alternative set representations; they compare
//! and fingerprint as the set they denote.

pub mod arith;
pub mod error;
pub mod fingerprint;
pub mod fmt;
pub mod intern;
pub mod lazy;
pub mod limits;
pub mod ops;
pub mod order;
pub mod plan;
mod repr;
pub mod ser;
pub mod value;

pub use error::{ValueError, ValueErrorKind};
pub use intern::Sym;
pub use lazy::{CustomSet, LazyFcn, LazySet};
pub use value::{FcnDom, FcnKind, SymAtom, Value};

pub type Result<T> = std::result::Result<T, ValueError>;
