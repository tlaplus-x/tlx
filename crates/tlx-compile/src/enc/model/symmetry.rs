//! SYMMETRY on encodings: permutation plans and the orbit fingerprint.

use std::cell::RefCell;
use std::sync::Arc;

use tlx_eval::InterpModel;
use tlx_layout::permute::{AtomPerm, PermPlan};
use tlx_layout::Layout;
use tlx_native::fp_words;
use tlx_value::Value;

use super::SemFp;

/// Plans applying each SYMMETRY element to the state layout (`None` if the
/// model has no symmetry or some variable's shape cannot be permuted).
pub(super) fn compile_symmetry(base: &InterpModel, layout: &Layout, notes: &mut Vec<String>) -> Option<Vec<Vec<PermPlan>>> {
    let maps = base.symmetry_maps();
    if maps.is_empty() {
        return None;
    }
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
    Some(group)
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
/// encodings lexicographically in the fixed `order`. `offs` are the word
/// offsets of the variables: a permutation is abandoned at the first
/// variable whose permuted encoding is greater than the best one's. With
/// value store handles (`sem`), encodings are compared and fingerprinted
/// with the handles' semantic digests in their place (a handle's number is
/// not canonical).
pub(super) fn orbit_fp(group: &[Vec<PermPlan>], order: &[usize], offs: &[usize], words: &[u64], sem: Option<&SemFp>) -> u64 {
    ORBIT_BUF.with(|b| {
        let mut b = b.borrow_mut();
        let (best, buf) = &mut *b;
        // The encoding compared: `words`, or with handles as digests.
        let mut base = Vec::new();
        let sem = sem.filter(|s| !s.state.is_empty());
        let start: &[u64] = match sem {
            Some(s) => {
                s.semantic(words, &s.state, &mut base);
                &base
            }
            None => words,
        };
        buf.resize(words.len(), 0);
        // `best` is empty while `words` itself is the least encoding.
        best.clear();
        'perm: for plans in group {
            let cur: &[u64] = if best.is_empty() { start } else { best };
            let mut less = false;
            for &i in order {
                let (lo, hi) = (offs[i], offs.get(i + 1).copied().unwrap_or(words.len()));

                // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
                unsafe { plans[i].apply_unchecked(&words[lo..hi], &mut buf[lo..hi]) };
                if let Some(s) = sem.filter(|s| s.ref_vars[i]) {
                    // (A value store slot is one handle.)
                    buf[lo] = s.store.digest(buf[lo]);
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
        fp_words(if best.is_empty() { start } else { best })
    })
}
