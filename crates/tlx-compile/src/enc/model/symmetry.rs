//! SYMMETRY on encodings: factorized partition-refinement canonicalization for
//! disjoint symmetric-group products `S_{n_1} x ... x S_{n_k}`, with explicit
//! `Vec<PermPlan>` fallback for arbitrary non-full subgroups.
//!
//! `order` compares and applies encoded words, `refine` performs deterministic
//! partition refinement, and `branch` runs the Case A/B branch-and-bound
//! completion of a single irreducible item.

mod branch;
mod order;
mod refine;
#[cfg(test)]
mod tests;

use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::sync::Arc;

use tlx_eval::InterpModel;
use tlx_layout::permute::{AtomPerm, DomMap, FactorGroupSpec, FactorPlan, PermPlan};
use tlx_layout::Layout;
use tlx_native::fp_words;
use tlx_runtime::ModelError;
use tlx_value::{Sym, Value};

use branch::choose_factorized_words;
use order::WordOrder;
use refine::FactorScratch;

use super::SemFp;

/// Compiled encoded-word SYMMETRY engine: factorized partition refinement for
/// disjoint symmetric-group products of any order (`|G| <= 720` and `|G| > 720`),
/// or explicit per-element `PermPlan` iteration for arbitrary non-full subgroups.
pub(super) enum SymmetryEngine {
    Factorized(FactorSymmetry),
    Explicit(SymmetryPlans),
}

/// Per-variable factorized symmetry plans for `prod_g Sym(K_g)`.
pub(super) struct FactorSymmetry {
    pub(super) fg: FactorGroupSpec,
    /// Precomputed identity image table for `fg` (zero-alloc identity evaluation).
    id_img: Box<[u16]>,
    /// One factor plan per variable in the layout (no `|G|` materialization).
    pub(super) plans: Vec<FactorPlan>,
    /// Precomputed: whether variable `i` contains any `>= 2`-word bitset.
    wide_bitset: Box<[bool]>,
    /// Precomputed: whether variable `i` contains any `Shape::Dyn` slot.
    has_dyn_var: Box<[bool]>,
    /// Precomputed: whether any variable in the layout contains `Shape::Dyn`.
    has_dyn: bool,
    /// Non-identity variables ordered for `orbit_fp`: zero-branching
    /// deterministic plans (`Atom`, `BitsetAtom`, invariant-payload `Fcn`/`Map`)
    /// first, then remaining variables narrowest-first.
    orbit_order: Box<[usize]>,
    /// Precomputed: every variable is `!has_dyn_or_ref() && is_orbit_cmp_safe()`,
    /// so `SymView` word-level TLC comparison is total and error-free.
    pub(super) all_orbit_cmp_safe: bool,
}

impl FactorSymmetry {
    fn new(fg: FactorGroupSpec, plans: Vec<FactorPlan>, layout: &Layout) -> Self {
        let id_img: Box<[u16]> = fg.identity_img().into();
        let wide_bitset: Box<[bool]> = plans.iter().map(FactorPlan::has_wide_bitset).collect();
        let has_dyn_var: Box<[bool]> = plans.iter().map(FactorPlan::has_dyn).collect();
        let has_dyn = has_dyn_var.iter().any(|&b| b);
        let orbit_order = build_orbit_order(layout, &plans);
        let all_orbit_cmp_safe = (0..layout.vars.len()).all(|i| {
            let n = layout.node(i);
            !n.has_dyn_or_ref() && n.is_orbit_cmp_safe()
        });
        Self { fg, id_img, plans, wide_bitset, has_dyn_var, has_dyn, orbit_order, all_orbit_cmp_safe }
    }
}

fn refinement_tier(plan: &FactorPlan) -> u8 {
    match plan {
        FactorPlan::Atom(_) => 0,
        FactorPlan::BitsetAtom { .. } => 1,
        FactorPlan::Fcn { dom: DomMap::DirectFactor { .. }, range, .. } if range.is_identity() => 2,
        FactorPlan::Map { key, range, .. } if range.is_identity() && key.atom_table().is_some_and(|t| t.direct_factor.is_some()) => 2,
        _ => 3,
    }
}

fn build_orbit_order(layout: &Layout, plans: &[FactorPlan]) -> Box<[usize]> {
    let width = |i: usize| layout.offsets.get(i + 1).copied().unwrap_or(layout.words) - layout.offsets[i];
    let mut order: Vec<usize> = (0..plans.len()).filter(|&i| !plans[i].is_identity()).collect();
    order.sort_by_key(|&i| (refinement_tier(&plans[i]), width(i), i));
    order.into()
}

/// Plans applying each SYMMETRY element to the state layout, with the order
/// its permutations must be visited in a fallible-by-value selection.
pub(super) struct SymmetryPlans {
    /// One plan per variable, indexed like `InterpModel::symmetry_maps()`.
    pub(super) group: Vec<Vec<PermPlan>>,
    /// Indices into `group` in the interpreter's fallible comparison order
    /// (`InterpModel::symmetry_maps_tlc_order`).
    pub(super) visit: Vec<usize>,
}

/// Compile encoded-word SYMMETRY support for `layout` (`None` if the model has
/// no symmetry or some variable's shape is not closed under the group).
pub(super) fn compile_symmetry(base: &InterpModel, layout: &Layout, notes: &mut Vec<String>) -> Option<SymmetryEngine> {
    if let Some(factors) = base.symmetry_factors() {
        let fg = FactorGroupSpec::new(&factors);
        let mut plans = Vec::with_capacity(layout.vars.len());
        for (i, s) in layout.vars.iter().enumerate() {
            match FactorPlan::compile(s, &fg) {
                Some(p) => plans.push(p),
                None => {
                    let name = base.ip.prog.vars.get(i).map_or("VIEW", |v| &*v.name);
                    notes.push(format!("symmetry: cannot permute the encoding of {name} ({s:?})"));
                    return None;
                }
            }
        }
        return Some(SymmetryEngine::Factorized(FactorSymmetry::new(fg, plans, layout)));
    }
    let maps = base.symmetry_maps();
    if maps.is_empty() {
        return None;
    }
    // The by-value fallback (and the error a comparison of incompatible values
    // raises) depends on the order permutations are visited; keep it.
    let visit = base.symmetry_maps_tlc_order()?;
    let mut group = Vec::with_capacity(maps.len());
    for m in maps {
        let m = m.clone();
        let perm: AtomPerm = Arc::new(move |v: &Value| match v {
            Value::ModelValue(s) => m.get(s).cloned().unwrap_or_else(|| v.clone()),
            _ => v.clone(),
        });
        let mut plans = Vec::with_capacity(layout.vars.len());
        for (i, s) in layout.vars.iter().enumerate() {
            match PermPlan::compile(s, &perm) {
                Some(p) => plans.push(p),
                None => {
                    let name = base.ip.prog.vars.get(i).map_or("VIEW", |v| &*v.name);
                    notes.push(format!("symmetry: cannot permute the encoding of {name} ({s:?})"));
                    return None;
                }
            }
        }
        group.push(plans);
    }
    if visit.len() != group.len() {
        // The orders must agree on the permutation set; otherwise fall back to
        // the interpreter rather than silently skipping orbit members.
        return None;
    }
    Some(SymmetryEngine::Explicit(SymmetryPlans { group, visit }))
}

/// The variables in the order `orbit_fp` compares them: by increasing
/// width (ties by position). Narrow variables are cheap to permute/refine,
/// often pinning all factors before wide variables are touched.
pub(super) fn symmetry_order(layout: &Layout) -> Vec<usize> {
    let n = layout.vars.len();
    let width = |i: usize| layout.offsets.get(i + 1).copied().unwrap_or(layout.words) - layout.offsets[i];
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by_key(|&i| (width(i), i));
    order
}

// ---------------------------------------------------------------------------
// Public entry points (`orbit_fp`, `least_perm_words_factorized`, `apply_factor_img`)
// ---------------------------------------------------------------------------

thread_local! {
    /// Scratch buffers of explicit `orbit_fp`: the least encoding so far and the
    /// permuted one.
    static ORBIT_BUF: RefCell<(Vec<u64>, Vec<u64>)> = const { RefCell::new((Vec::new(), Vec::new())) };
    /// Scratch buffers of factorized word-level canonicalization.
    static FACTOR_SCRATCH: RefCell<FactorScratch> = RefCell::new(FactorScratch::default());
}

/// Apply factorized flat image table `img` to all variables of `words` into
/// `dst` (exact encoding permutation, preserving handles and dynamic witnesses).
pub(super) fn apply_factor_img(fsym: &FactorSymmetry, layout: &Layout, img: &[u16], words: &[u64], dst: &mut Vec<u64>) {
    dst.resize(words.len(), 0);
    for (i, plan) in fsym.plans.iter().enumerate() {
        let r = layout.var_range(i);
        if plan.is_identity() {
            dst[r.clone()].copy_from_slice(&words[r]);
        } else {
            // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
            unsafe { plan.apply_unchecked(&fsym.fg, img, &words[r.clone()], &mut dst[r]) };
        }
    }
}

/// Select the TLC-least orbit representative directly on encoded words for a
/// factorized group (any order, including `|G| > 720`).
///
/// Returns `Some(false)` when `words` itself is least, `Some(true)` when a
/// non-identity representative was written into `best_buf`, or `None` when
/// any variable cannot be ordered safely on words and must fall back to
/// `InterpModel::least_factor_perm`.
pub(super) fn least_perm_words_factorized(
    fsym: &FactorSymmetry,
    order: &[usize],
    layout: &Layout,
    words: &[u64],
    best_buf: &mut Vec<u64>,
) -> Option<bool> {
    if !fsym.all_orbit_cmp_safe {
        return None;
    }
    FACTOR_SCRATCH.with(|s| {
        let mut scratch = s.borrow_mut();
        let non_id = choose_factorized_words(fsym, order, layout, words, None, WordOrder::Tlc, &mut scratch);
        if !non_id {
            return Some(false);
        }
        apply_factor_img(fsym, layout, scratch.img.as_slice(), words, best_buf);
        Some(true)
    })
}

/// Fingerprint of the canonical representative in the SYMMETRY orbit of `words`.
pub(super) fn orbit_fp(
    engine: &SymmetryEngine,
    order: &[usize],
    layout: &Layout,
    words: &[u64],
    sem: Option<&SemFp>,
    ref_digests: Option<&RefDigests<'_>>,
) -> Result<u64, ModelError> {
    match engine {
        SymmetryEngine::Factorized(fsym) => Ok(orbit_fp_factorized(fsym, layout, words, sem)),
        SymmetryEngine::Explicit(plans) => orbit_fp_explicit(&plans.group, order, layout, words, sem, ref_digests),
    }
}

pub(super) fn orbit_fp_factorized(fsym: &FactorSymmetry, layout: &Layout, words: &[u64], sem: Option<&SemFp>) -> u64 {
    let sem = sem.filter(|s| s.state_needs_canonical(layout));
    FACTOR_SCRATCH.with(|s| {
        let mut scratch = s.borrow_mut();
        let non_id = choose_factorized_words(fsym, &fsym.orbit_order, layout, words, sem, WordOrder::Orbit, &mut scratch);
        if !non_id && !fsym.has_dyn {
            return match sem {
                Some(s) => s.fp_state(layout, words),
                None => fp_words(words),
            };
        }
        let mut out_buf = std::mem::take(&mut scratch.out_buf);
        out_buf.resize(words.len(), 0);
        let img = if non_id { scratch.img.as_slice() } else { &fsym.id_img };
        for (i, plan) in fsym.plans.iter().enumerate() {
            let r = layout.var_range(i);
            let node = layout.node(i);
            if plan.is_identity() {
                out_buf[r.clone()].copy_from_slice(&words[r.clone()]);
                if let Some(s) = sem {
                    if let Some(store) = &s.store {
                        let refs = &s.state[s.var_refs[i].clone()];
                        if !refs.is_empty() {
                            let pin = store.pin();
                            for &off in refs {
                                out_buf[off] = pin.digest(out_buf[off]);
                            }
                        }
                    }
                    if node.has_dynamic_witness() {
                        node.canonicalize_orbit_words(&mut out_buf[r]);
                    }
                }
            } else {
                // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
                unsafe { plan.apply_orbit_unchecked(&fsym.fg, img, &words[r.clone()], &mut out_buf[r.clone()]) };
                if node.has_dynamic_witness() {
                    node.canonicalize_orbit_words(&mut out_buf[r]);
                }
            }
        }
        let fp = fp_words(&out_buf);
        scratch.out_buf = out_buf;
        fp
    })
}

/// Explicit fallback for arbitrary non-full subgroups: scans each `PermPlan`
/// in `group`, pruning at the first variable whose permuted encoding exceeds
/// the best one so far. Under persistent value-store pressure, `ref_digests`
/// supplies the semantic digest of each permuted top-level `Ref` variable
/// directly from decoded values without interning its permuted image.
pub(super) fn orbit_fp_explicit(
    group: &[Vec<PermPlan>],
    order: &[usize],
    layout: &Layout,
    words: &[u64],
    sem: Option<&SemFp>,
    ref_digests: Option<&RefDigests<'_>>,
) -> Result<u64, ModelError> {
    let offs = &layout.offsets;
    ORBIT_BUF.with(|b| {
        let mut b = b.borrow_mut();
        let (best, buf) = &mut *b;
        let mut base = Vec::new();
        let sem = sem.filter(|s| s.state_needs_canonical(layout));
        let start: &[u64] = match sem {
            Some(s) => {
                s.semantic_state(layout, words, &mut base);
                &base
            }
            None => words,
        };
        buf.resize(words.len(), 0);
        best.clear();
        'perm: for (pi, plans) in group.iter().enumerate() {
            let cur: &[u64] = if best.is_empty() { start } else { best };
            let mut less = false;
            for &i in order {
                let (lo, hi) = (offs[i], offs.get(i + 1).copied().unwrap_or(words.len()));
                let ref_digest = ref_digests.filter(|_| sem.is_some_and(|s| s.ref_vars[i]));
                match ref_digest {
                    Some(rd) => {
                        debug_assert_eq!(hi, lo + 1, "a value store slot is one handle");
                        buf[lo] = rd.digest(i, pi)?;
                    }
                    None => {
                        // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
                        unsafe { plans[i].apply_unchecked(&words[lo..hi], &mut buf[lo..hi]) };
                        if let Some(s) = sem {
                            if let Some(store) = &s.store {
                                let refs = &s.state[s.var_refs[i].clone()];
                                if !refs.is_empty() {
                                    let pin = store.pin();
                                    for &off in refs {
                                        buf[off] = pin.digest(buf[off]);
                                    }
                                }
                            }
                        }
                    }
                }
                if sem.is_some() && layout.node(i).has_dynamic_witness() {
                    layout.node(i).canonicalize_words(&mut buf[lo..hi]);
                }
                if !less {
                    match buf[lo..hi].cmp(&cur[lo..hi]) {
                        Ordering::Greater => continue 'perm,
                        Ordering::Less => less = true,
                        Ordering::Equal => {}
                    }
                }
            }
            if less {
                if best.is_empty() {
                    best.resize(words.len(), 0);
                }
                std::mem::swap(best, buf);
            }
        }
        Ok(fp_words(if best.is_empty() { start } else { best }))
    })
}

/// Semantic digests of permuted top-level `Ref` variables computed from
/// decoded values (see `orbit_fp_explicit`), avoiding the store allocation of
/// `PermPlan::Ref`.
pub(super) struct RefDigests<'a> {
    maps: &'a [HashMap<Sym, Value>],
    /// Decoded value of each top-level `Shape::Ref` variable, by variable index.
    vals: Box<[Option<Value>]>,
}

impl<'a> RefDigests<'a> {
    pub(super) fn new(layout: &Layout, words: &[u64], maps: &'a [HashMap<Sym, Value>]) -> Self {
        let vals = layout
            .vars
            .iter()
            .enumerate()
            .map(|(i, s)| match s {
                tlx_layout::Shape::Ref(_) => {
                    // SAFETY: valid words from the matching encoder/program,
                    // with published Dyn handles.
                    Some(unsafe { layout.node(i).decode_unchecked(&words[layout.offsets[i]..]) })
                }
                _ => None,
            })
            .collect();
        Self { maps, vals }
    }

    /// The semantic digest of variable `i`'s value under permutation `p`.
    /// `permute_shared` keeps a value the permutation leaves unchanged (and
    /// preserves its function-domain witness), so unchanged `Ref` values are
    /// not rebuilt for every candidate.
    fn digest(&self, i: usize, p: usize) -> Result<u64, ModelError> {
        let v = self.vals[i].as_ref().expect("ref_digests of a Ref variable");
        let m = &self.maps[p];
        let permuted = tlx_value::ops::permute_shared(v, &|s| m.get(&s).cloned())
            .map_err(|e| ModelError::new(format!("permute Ref variable: {e:?}")))?;
        let value = permuted.as_ref().unwrap_or(v);
        tlx_layout::store::digest_of_value(value).map_err(|e| ModelError::new(format!("value store digest: {e:?}")))
    }
}
