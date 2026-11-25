//! SYMMETRY on encodings: permutation plans and the orbit fingerprint.

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Arc;

use tlx_eval::InterpModel;
use tlx_layout::permute::{AtomPerm, PermPlan};
use tlx_layout::Layout;
use tlx_native::fp_words;
use tlx_runtime::ModelError;
use tlx_value::{Sym, Value};

use super::SemFp;

/// Plans applying each SYMMETRY element to the state layout, with the order
/// its permutations must be visited in a fallible-by-value selection.
pub(super) struct SymmetryPlans {
    /// One plan per variable, indexed like `InterpModel::symmetry_maps()`.
    pub(super) group: Vec<Vec<PermPlan>>,
    /// Indices into `group` in the interpreter's fallible comparison order
    /// (`InterpModel::symmetry_maps_tlc_order`).
    pub(super) visit: Vec<usize>,
}

/// Plans applying each SYMMETRY element to the state layout (`None` if the
/// model has no symmetry or some variable's shape cannot be permuted).
pub(super) fn compile_symmetry(base: &InterpModel, layout: &Layout, notes: &mut Vec<String>) -> Option<SymmetryPlans> {
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
    Some(SymmetryPlans { group, visit })
}

thread_local! {
    /// Scratch buffers of `orbit_fp`: the least encoding so far and the
    /// permuted one.
    static ORBIT_BUF: RefCell<(Vec<u64>, Vec<u64>)> = const { RefCell::new((Vec::new(), Vec::new())) };
}

/// The variables in the order `orbit_fp` compares them: by increasing
/// width (ties by position). Narrow variables are cheap to permute, and a
/// permutation that makes one of them greater is abandoned before the wide
/// ones (sets of records, ...) are permuted and re-sorted.
pub(super) fn symmetry_order(layout: &Layout) -> Vec<usize> {
    let n = layout.vars.len();
    let width = |i: usize| layout.offsets.get(i + 1).copied().unwrap_or(layout.words) - layout.offsets[i];
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by_key(|&i| (width(i), i));
    order
}

/// Fingerprint of the least encoding in the SYMMETRY orbit of `words` (a
/// canonical representative of the orbit), comparing the variables'
/// encodings lexicographically in the fixed `order`. A permutation is
/// abandoned at the first variable whose permuted encoding is greater than
/// the best one's. With value store handles or dynamic witnesses (`sem`),
/// encodings are compared and fingerprinted in canonical form.
///
/// Under persistent value-store pressure, `ref_digests` supplies the semantic
/// digest of each permuted top-level `Ref` variable directly from decoded
/// values, so completing a candidate never interns its permuted image. The
/// digest is the same word `SemFp::semantic_state` produces for the handle,
/// and the order, compared words and final `fp_words` are unchanged.
pub(super) fn orbit_fp(
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
        // The encoding compared: `words`, or canonicalized (handles as digests,
        // dynamic witness words zeroed).
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
        // `best` is empty while `words` itself is the least encoding.
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
                            if s.ref_vars[i] {
                                // (A value store slot is one handle.)
                                buf[lo] = s.store.as_ref().expect("ref_vars requires store").digest(buf[lo]);
                            }
                        }
                    }
                }
                if sem.is_some() && layout.node(i).has_dynamic_witness() {
                    layout.node(i).canonicalize_words(&mut buf[lo..hi]);
                }
                if !less {
                    match buf[lo..hi].cmp(&cur[lo..hi]) {
                        std::cmp::Ordering::Greater => continue 'perm,
                        std::cmp::Ordering::Less => less = true,
                        std::cmp::Ordering::Equal => {}
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
/// decoded values (see `orbit_fp`), avoiding the store allocation of
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
