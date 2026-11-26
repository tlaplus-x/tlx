//! Applying a permutation of model values (a SYMMETRY element) directly to
//! encoded values, guided by their shape.
//!
//! A `PermPlan` is compiled once per (shape, permutation): atoms map through
//! a table, bitsets map their bit ranks, sorted-array sets permute their
//! elements and re-sort, functions over atom domains move their slots, maps
//! move their presence bits and slots, `Dyn` handles are permuted as values
//! and re-interned. The result is the canonical encoding of the permuted
//! value, so comparing or hashing it is equivalent to doing so on the
//! permuted value.
//!
//! Plans of fixed-position shapes (records, tuples, functions of atoms,
//! ints, atoms) are flattened into word-level copy / atom-map runs
//! (`PermPlan::Flat`), which is what most state variables become.

// Every plan type below is re-exported, so `tlx_layout::permute::*` remains the
// public entry point: explicit subgroup plans live in `explicit`, factorized
// symmetric-group product plans in `factor`.

mod explicit;
mod factor;
#[cfg(test)]
mod tests;

pub use explicit::*;
pub use factor::*;
