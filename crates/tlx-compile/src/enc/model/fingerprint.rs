//! Semantic fingerprints, VIEW evaluation and SYMMETRY reduction.

use std::cell::RefCell;

use tlx_eval::env::Env;
use tlx_eval::eval::Ctx;
use tlx_eval::StateVals;
use tlx_layout::permute::PermPlan;
use tlx_layout::{Layout, Shape};
use tlx_native::fp_words;
use tlx_runtime::stats::{self, C, T};
use tlx_runtime::{Model, ModelError};
use tlx_value::Value;

use super::symmetry::{
    apply_factor_img, least_perm_words_factorized, orbit_fp, orbit_fp_explicit, orbit_fp_factorized, FactorSymmetry, RefDigests,
    SymmetryEngine,
};
use super::{EState, EncModel, View};
use crate::paranoid::{mismatch, state_list};

/// Canonical fingerprints of encodings holding value store handles
/// (`Shape::Ref`) or dynamic function-domain witnesses (`FcnWitness::Dynamic`):
/// a handle is replaced by its semantic digest, and every trailing dynamic
/// witness word is zeroed before hashing or symmetry comparison so semantically
/// equal values always share one fingerprint.
pub(in crate::enc) struct SemFp {
    pub(in crate::enc) store: Option<tlx_layout::store::StoreRef>,
    /// The word offsets of the handles in a state.
    pub(in crate::enc) state: Box<[usize]>,
    /// The word offsets of the handles in the VIEW's encoding.
    pub(in crate::enc) view: Box<[usize]>,
    /// Per variable: its slot is one handle.
    pub(in crate::enc) ref_vars: Box<[bool]>,
    /// Per variable: range into `state` of that variable's handle offsets.
    pub(in crate::enc) var_refs: Box<[std::ops::Range<usize>]>,
}

thread_local! {
    static SEM_BUF: std::cell::RefCell<Vec<u64>> = const { std::cell::RefCell::new(Vec::new()) };
}

impl SemFp {
    /// For a layout (and the VIEW's shape, if fingerprinted by its
    /// encoding); None when neither holds handles nor dynamic witnesses.
    pub(super) fn of(layout: &Layout, view: Option<&Shape>) -> Option<SemFp> {
        let store = tlx_layout::layout::store_of(layout.vars.iter().chain(view));
        if store.is_none() && !layout.has_dynamic_witness && !view.is_some_and(Shape::has_dynamic_witness) {
            return None;
        }
        let mut state = Vec::new();
        let mut v = Vec::new();
        let mut var_refs = Vec::with_capacity(layout.vars.len());
        if store.is_some() {
            for (s, off) in layout.vars.iter().zip(&layout.offsets) {
                let start = state.len();
                tlx_layout::layout::ref_offsets(s, *off, &mut state).expect("value store handles at fixed positions");
                var_refs.push(start..state.len());
            }
            if let Some(s) = view {
                tlx_layout::layout::ref_offsets(s, 0, &mut v).expect("value store handles at fixed positions");
            }
        } else {
            var_refs.resize(layout.vars.len(), 0..0);
        }
        let ref_vars = layout.vars.iter().map(|s| matches!(s, Shape::Ref(_))).collect();
        Some(SemFp { store, state: state.into(), view: v.into(), ref_vars, var_refs: var_refs.into() })
    }

    pub(in crate::enc) fn state_needs_canonical(&self, layout: &Layout) -> bool {
        !self.state.is_empty() || layout.has_dynamic_witness
    }

    /// `words` of a state with handles replaced by digests and dynamic
    /// witness words zeroed.
    pub(in crate::enc) fn semantic_state(&self, layout: &Layout, words: &[u64], out: &mut Vec<u64>) {
        out.clear();
        out.extend_from_slice(words);
        if let Some(store) = &self.store {
            if !self.state.is_empty() {
                let pin = store.pin();
                for &i in &self.state {
                    out[i] = pin.digest(out[i]);
                }
            }
        }
        if layout.has_dynamic_witness {
            layout.canonicalize_state(out);
        }
    }

    /// `words` of a VIEW with handles replaced by digests and dynamic
    /// witness words zeroed.
    pub(in crate::enc) fn semantic_view(&self, node: &tlx_layout::LayoutNode, words: &[u64], out: &mut Vec<u64>) {
        out.clear();
        out.extend_from_slice(words);
        if let Some(store) = &self.store {
            if !self.view.is_empty() {
                let pin = store.pin();
                for &i in &self.view {
                    out[i] = pin.digest(out[i]);
                }
            }
        }
        if node.has_dynamic_witness() {
            node.canonicalize_words(out);
        }
    }

    /// The canonical fingerprint of encoded state `words`.
    pub(in crate::enc) fn fp_state(&self, layout: &Layout, words: &[u64]) -> u64 {
        if !self.state_needs_canonical(layout) {
            return fp_words(words);
        }
        SEM_BUF.with(|b| {
            let mut b = b.borrow_mut();
            self.semantic_state(layout, words, &mut b);
            fp_words(&b)
        })
    }

    /// The canonical fingerprint of encoded VIEW `words`.
    pub(in crate::enc) fn fp_view(&self, node: &tlx_layout::LayoutNode, words: &[u64]) -> u64 {
        if self.view.is_empty() && !node.has_dynamic_witness() {
            return fp_words(words);
        }
        SEM_BUF.with(|b| {
            let mut b = b.borrow_mut();
            self.semantic_view(node, words, &mut b);
            fp_words(&b)
        })
    }
}

/// How an `EncModel` fingerprints its states.
#[allow(clippy::large_enum_variant)] // one per model; boxing only adds an indirection on the fingerprint path
pub(super) enum Fingerprint {
    /// `fp_words` of the encoding (no VIEW or SYMMETRY).
    Words,
    /// SYMMETRY on encodings: factorized partition-refinement or explicit
    /// per-element plans (`orbit_fp`, comparing variables in `order`,
    /// narrowest first).
    Symmetry { engine: SymmetryEngine, order: Vec<usize> },
    /// VIEW computed into an encoding: the fingerprint is that of the
    /// VIEW's encoding.
    View(View),
    /// VIEW with SYMMETRY: the fingerprint of the VIEW (as in `View`) of
    /// the least state of the orbit in TLC's value order (`order` = TLC's
    /// variable order), chosen directly on encoded words (`LayoutNode::cmp_tlc_words`)
    /// with fallback to `InterpModel::least_factor_perm` / `least_perm` when a
    /// compared variable cannot be ordered on words.
    SymView { engine: SymmetryEngine, order: Vec<usize>, view: View },
    /// By value: the interpreter's (reduced) fingerprint, for a VIEW or
    /// SYMMETRY not handled on encodings (states are decoded for it).
    Values,
}

thread_local! {
    /// Scratch buffers of `EncModel::view_fp`: the extended state and the
    /// VIEW's encoding.
    static VIEW_BUF: RefCell<(Vec<u64>, Vec<u64>)> = const { RefCell::new((Vec::new(), Vec::new())) };
    /// Scratch buffers of `sym_view_fp`: the best permuted encoding so far and
    /// the candidate permutation's encoding.
    static PERM_BUF: RefCell<(Vec<u64>, Vec<u64>)> = const { RefCell::new((Vec::new(), Vec::new())) };
}

impl EncModel {
    /// Fingerprint of a state given by its encoding (VIEW and SYMMETRY
    /// handled on encodings, if any).
    #[inline]
    pub(super) fn words_fp(&self, words: &[u64], level: u32) -> Result<u64, ModelError> {
        if stats::on() {
            return self.words_fp_counted(words, level);
        }
        self.words_fp_untimed(words, level)
    }

    /// `words_fp`, counted and timed for the statistics.
    #[inline(never)]
    fn words_fp_counted(&self, words: &[u64], level: u32) -> Result<u64, ModelError> {
        stats::count(C::Fingerprints, 1);
        let span = stats::span();
        let fp = self.words_fp_untimed(words, level);
        span.end(T::Fingerprint);
        fp
    }

    #[inline]
    fn words_fp_untimed(&self, words: &[u64], level: u32) -> Result<u64, ModelError> {
        if let Some(e) = &self.escape {
            if words.len() > self.layout.words {
                return self.escape_fp(e, words, level);
            }
        }
        match &self.fp {
            Fingerprint::View(v) => self.view_fp(v, words, level),
            Fingerprint::Symmetry { engine, order } => match engine {
                SymmetryEngine::Factorized(fsym) => {
                    let fp = orbit_fp_factorized(fsym, &self.layout, words, self.sem.as_ref());
                    if self.paranoid {
                        let has_store = self.value_store().is_some();
                        if has_store {
                            tlx_layout::store::clear_full_hit();
                        }
                        self.check_factor_generators(fsym, words, Some(fp));
                        if has_store {
                            let _ = tlx_layout::store::take_full_hit();
                        }
                    }
                    Ok(fp)
                }
                SymmetryEngine::Explicit(plans) => {
                    let has_store = self.value_store().is_some();
                    if has_store {
                        tlx_layout::store::clear_full_hit();
                    }
                    if has_store && self.store_pressure() {
                        return self.symmetry_fp_values(&plans.group, order, words);
                    }
                    if self.paranoid {
                        self.check_permutations(&plans.group, words);
                        if has_store && tlx_layout::store::take_full_hit() {
                            return self.symmetry_fp_values(&plans.group, order, words);
                        }
                    }
                    let fp = orbit_fp_explicit(&plans.group, order, &self.layout, words, self.sem.as_ref(), None)?;
                    if has_store && tlx_layout::store::take_full_hit() {
                        // The failed insertion requested a collection: subsequent
                        // fingerprints take the digest path until it runs. Finish
                        // this one from decoded values instead of rematerializing
                        // the image on a retry.
                        return self.symmetry_fp_values(&plans.group, order, words);
                    }
                    Ok(fp)
                }
            },
            Fingerprint::SymView { engine, order, view } => self.sym_view_fp(engine, order, view, words, level),
            Fingerprint::Words | Fingerprint::Values => Ok(match &self.sem {
                Some(sem) => sem.fp_state(&self.layout, words),
                None => fp_words(words),
            }),
        }
    }

    fn escape_fp(&self, e: &crate::enc::escape::Escape, words: &[u64], level: u32) -> Result<u64, ModelError> {
        let vals = e.codec.decode(words);
        match &self.fp {
            Fingerprint::View(v) => self.escape_view_fp(v, &vals, level),
            Fingerprint::SymView { view, .. } => {
                let least = self.base.least_state_in_orbit(&vals).inspect_err(|_| self.base.count_generated())?;
                let vals = least.unwrap_or(vals);
                self.escape_view_fp(view, &vals, level)
            }
            Fingerprint::Symmetry { engine, order } => {
                let key = e.codec.key(words);
                if key.len() == self.layout.words {
                    return orbit_fp(engine, order, &self.layout, &key, self.sem.as_ref(), None);
                }
                match engine {
                    SymmetryEngine::Factorized(_) => {
                        let canon = self.base.canonical_total_orbit(&vals, order)?;
                        let canon_vals = canon.as_deref().unwrap_or(&vals);
                        let canon_words = e.codec.encode(canon_vals).map_err(|x| ModelError::new(format!("escape store: {x:?}")))?;
                        Ok(fp_words(&e.codec.key(&canon_words)))
                    }
                    SymmetryEngine::Explicit(_) => {
                        let mut best = key;
                        for p in 0..self.base.symmetry_maps().len() {
                            let vals = self.escape_permute(&vals, p)?;
                            let words = e.codec.encode(&vals).map_err(|x| ModelError::new(format!("escape store: {x:?}")))?;
                            let key = e.codec.key(&words);
                            let cmp = order.iter().find_map(|&i| {
                                let r = self.layout.var_range(i);
                                let c = key[r.clone()].cmp(&best[r]);
                                let c = c.then_with(|| {
                                    key.get(self.layout.words + i).unwrap_or(&0).cmp(best.get(self.layout.words + i).unwrap_or(&0))
                                });
                                (c != std::cmp::Ordering::Equal).then_some(c)
                            });
                            if cmp == Some(std::cmp::Ordering::Less) {
                                best = key;
                            }
                        }
                        Ok(fp_words(&best))
                    }
                }
            }
            Fingerprint::Words => Ok(fp_words(&e.codec.key(words))),
            Fingerprint::Values => {
                let vals: Vec<_> = vals.into_iter().map(Some).collect();
                self.base.make_state_counted(&vals, level, "state").map(|s| s.fp).map_err(|x| self.base.error(x))
            }
        }
    }

    /// Apply SYMMETRY element `p` to decoded values the way the interpreter
    /// does: `permute_shared` keeps a value that the permutation does not
    /// change, including its function-domain representation (an interval
    /// domain stays an interval, not a rebuilt enumerated function). Rebuilding
    /// unchanged functions changes what `EXCEPT`/application do with
    /// non-integer keys.
    fn escape_permute(&self, vals: &[Value], p: usize) -> Result<Vec<Value>, ModelError> {
        let m = &self.base.symmetry_maps()[p];
        vals.iter()
            .map(|v| {
                tlx_value::ops::permute_shared(v, &|s| m.get(&s).cloned())
                    .map(|image| image.unwrap_or_else(|| v.clone()))
                    .map_err(|x| self.base.error(x.into()))
            })
            .collect()
    }

    fn escape_view_fp(&self, v: &View, vals: &[Value], level: u32) -> Result<u64, ModelError> {
        let expr = self.base.view_expr().expect("VIEW");
        let val = self.base.ip.eval(expr, &Env::default(), &Ctx::state(vals, level)).and_then(|x| Ok(x.normalize()?)).map_err(|x| {
            self.base.count_generated();
            self.base.error(x)
        })?;
        let node = v.result_node();
        let mut out = vec![0; node.words()];
        if node.encode_semantic(&val, &mut out).is_err() {
            return tlx_layout::store::digest_of_value(&val)
                .map(|d| fp_words(&[u64::MAX, d]))
                .map_err(|x| ModelError::new(format!("escape VIEW: {x:?}")));
        }
        Ok(self.hash_view_words(v, &out))
    }

    fn hash_view_words(&self, v: &View, words: &[u64]) -> u64 {
        if let Some(orbit) = &v.orbit {
            return orbit.fingerprint(words);
        }
        match &self.sem {
            Some(sem) => sem.fp_view(v.result_node(), words),
            None => fp_words(words),
        }
    }

    /// Fingerprint of the VIEW of the least state of the SYMMETRY orbit of
    /// the state `words` (see `Fingerprint::SymView`).
    fn sym_view_fp(&self, engine: &SymmetryEngine, order: &[usize], v: &View, words: &[u64], level: u32) -> Result<u64, ModelError> {
        match engine {
            SymmetryEngine::Factorized(fsym) => self.sym_view_fp_factorized(fsym, order, v, words, level),
            SymmetryEngine::Explicit(plans) => self.sym_view_fp_explicit(&plans.group, &plans.visit, order, v, words, level),
        }
    }

    fn sym_view_fp_factorized(
        &self,
        fsym: &FactorSymmetry,
        order: &[usize],
        v: &View,
        words: &[u64],
        level: u32,
    ) -> Result<u64, ModelError> {
        let has_store = self.value_store().is_some();
        if has_store && self.store_pressure() {
            return self.sym_view_fp_values(v, words, level);
        }
        if has_store {
            tlx_layout::store::clear_full_hit();
        }
        if self.paranoid {
            self.check_factor_generators(fsym, words, None);
            if has_store && tlx_layout::store::take_full_hit() {
                return self.sym_view_fp_values(v, words, level);
            }
        }
        let word_res = PERM_BUF.with(|b| {
            let mut b = b.borrow_mut();
            let best_buf = &mut b.0;
            let non_id = least_perm_words_factorized(fsym, order, &self.layout, words, best_buf)?;
            if self.paranoid {
                self.check_sym_view_least_state(words, non_id, best_buf);
            }
            Some(if non_id { self.view_fp(v, best_buf, level) } else { self.view_fp(v, words, level) })
        });
        if let Some(fp) = word_res {
            return fp;
        }
        // Fallback: decode variables lazily and delegate to `InterpModel::least_factor_perm`
        // (already factorized in `tlx-eval` and supports arbitrary group orders).
        // SAFETY: the matching encoder/program produced these words.
        // Active Dyn handles were published before this call.
        let decode = |i: usize| unsafe { self.layout.node(i).decode_unchecked(&words[self.layout.offsets[i]..]) };
        let mut vals = StateVals::decoded(self.layout.vars.len(), &decode);
        let least = self.base.least_factor_perm(&mut vals).inspect_err(|_| self.base.count_generated())?;
        drop(vals);
        let Some(img) = least else {
            return self.view_fp(v, words, level);
        };
        PERM_BUF.with(|b| {
            let mut b = b.borrow_mut();
            let buf = &mut b.0;
            apply_factor_img(fsym, &self.layout, &img, words, buf);
            if has_store && tlx_layout::store::take_full_hit() {
                return self.sym_view_fp_values(v, words, level);
            }
            self.view_fp(v, buf, level)
        })
    }

    #[allow(clippy::too_many_arguments)] // group, visit order, variable order, VIEW, words, level
    fn sym_view_fp_explicit(
        &self,
        group: &[Vec<PermPlan>],
        visit: &[usize],
        order: &[usize],
        v: &View,
        words: &[u64],
        level: u32,
    ) -> Result<u64, ModelError> {
        let has_store = self.value_store().is_some();
        if has_store && self.store_pressure() {
            // Completing the winning permutation interns a permuted copy of
            // every `Ref` variable. When the live store is already close to
            // the budget, that allocation cannot fit after reclamation and
            // every retry rematerializes it; choose and evaluate the
            // representative on decoded values and fingerprint only the VIEW
            // result instead.
            return self.sym_view_fp_values(v, words, level);
        }
        if has_store {
            tlx_layout::store::clear_full_hit();
        }
        if self.paranoid {
            self.check_permutations(group, words);
            if has_store && tlx_layout::store::take_full_hit() {
                return self.sym_view_fp_values(v, words, level);
            }
        }
        let mut store_full = false;
        let word_res = PERM_BUF.with(|b| {
            let mut b = b.borrow_mut();
            let (best_buf, cand_buf) = &mut *b;
            let least = self.least_perm_words(group, visit, order, words, best_buf, cand_buf)?;
            // Completing the chosen representative permutes its remaining
            // variables, which may intern value-store images. A full store
            // keeps the old handle in the encoding, so retry after reclamation
            // instead of fingerprinting a partially permuted state.
            if has_store && tlx_layout::store::take_full_hit() {
                store_full = true;
                return None;
            }
            if self.paranoid {
                self.check_sym_view_least(group, words, least, best_buf);
            }
            Some(match least {
                None => self.view_fp(v, words, level),
                Some(_) => self.view_fp(v, best_buf, level),
            })
        });
        if store_full {
            // The failed insertion requested a collection; subsequent
            // fingerprints take the value path until it runs. Finish this one
            // on decoded values instead of rematerializing the permutation.
            return self.sym_view_fp_values(v, words, level);
        }
        if let Some(fp) = word_res {
            return fp;
        }
        // Fallback: decode variables lazily and delegate to `InterpModel::least_perm`.
        // SAFETY: the matching encoder/program produced these words.
        // Active Dyn handles were published before this call.
        let decode = |i: usize| unsafe { self.layout.node(i).decode_unchecked(&words[self.layout.offsets[i]..]) };
        let mut vals = StateVals::decoded(self.layout.vars.len(), &decode);
        let least = self.base.least_perm(&mut vals).inspect_err(|_| self.base.count_generated())?;
        drop(vals);
        let Some(p) = least else {
            return self.view_fp(v, words, level);
        };
        PERM_BUF.with(|b| {
            let mut b = b.borrow_mut();
            let buf = &mut b.0;
            buf.resize(words.len(), 0);
            for (i, plan) in group[p].iter().enumerate() {
                let r = self.layout.var_range(i);

                // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
                unsafe { plan.apply_unchecked(&words[r.clone()], &mut buf[r]) };
            }
            if has_store && tlx_layout::store::take_full_hit() {
                return self.sym_view_fp_values(v, words, level);
            }
            self.view_fp(v, buf, level)
        })
    }

    /// `Fingerprint::Symmetry` under persistent value-store pressure (or
    /// after an interning attempt failed): compare and hash the same canonical
    /// words, but take each permuted top-level `Ref` variable's digest from its
    /// decoded value instead of interning the image.
    fn symmetry_fp_values(&self, group: &[Vec<PermPlan>], order: &[usize], words: &[u64]) -> Result<u64, ModelError> {
        let digests = RefDigests::new(&self.layout, words, self.base.symmetry_maps());
        orbit_fp_explicit(group, order, &self.layout, words, self.sem.as_ref(), Some(&digests))
    }

    /// `SymView` fingerprint under persistent value-store pressure: select the
    /// least state of the SYMMETRY orbit on decoded values (the interpreter's
    /// selection), evaluate the VIEW there, and fingerprint only the VIEW's
    /// encoding. The encoded-word path would intern a permuted copy of every
    /// `Ref` variable before the VIEW is even evaluated.
    fn sym_view_fp_values(&self, v: &View, words: &[u64], level: u32) -> Result<u64, ModelError> {
        // SAFETY: the matching encoder/program produced these words.
        // Active Dyn handles were published before this call.
        let vals = unsafe { self.layout.decode_state_unchecked(words) };
        let least = self.base.least_state_in_orbit(&vals)?;
        let vals = least.unwrap_or(vals);
        self.view_values_fp(v, &vals, level)
    }

    /// The VIEW fingerprint of decoded values. A VIEW result with `Ref`
    /// positions is encoded with their semantic digests instead of interning
    /// the permuted values, producing exactly the canonical words
    /// `SemFp::fp_view` would hash for the handle encoding.
    fn view_values_fp(&self, v: &View, vals: &[Value], level: u32) -> Result<u64, ModelError> {
        let digest_refs = self.sem.as_ref().is_some_and(|s| !s.view.is_empty()) && v.orbit.is_none();
        if !digest_refs {
            return match self.view_encoded(v, vals, level)? {
                ViewEncoded::Words(w) => Ok(self.hash_view_words(v, &w)),
                ViewEncoded::Digest(d) => Ok(fp_words(&[u64::MAX, d])),
            };
        }
        let val = self.view_value(vals, level)?;
        let node = v.result_node();
        let mut out = vec![0u64; node.words()];
        if node.encode_ref_digested(&val, &mut out).is_err() {
            // The value does not fit its inferred shape (or escape mode is
            // active): fall back to the ordinary encoder and its conventions.
            return match self.view_encoded(v, vals, level)? {
                ViewEncoded::Words(w) => Ok(self.hash_view_words(v, &w)),
                ViewEncoded::Digest(d) => Ok(fp_words(&[u64::MAX, d])),
            };
        }
        // The `Ref` positions already hold their semantic digests; only the
        // trailing dynamic witness words remain to be canonicalized.
        if node.has_dynamic_witness() {
            node.canonicalize_words(&mut out);
        }
        Ok(fp_words(&out))
    }

    /// Whether an interning attempt already failed and the store is waiting
    /// for its next collection (or a retry escalated to the transient
    /// fallback). Fingerprints then avoid rematerializing permutation images
    /// until the store has been reclaimed.
    fn store_pressure(&self) -> bool {
        Self::transient_fallback() || self.value_store().is_some_and(|s| s.needs_gc())
    }

    /// Select the TLC-least orbit representative directly on encoded words,
    /// visiting the permutations in `visit` (the interpreter's fallible
    /// order, so the first incomparable pair is the same in both tiers) and
    /// comparing variables in `order` (TLC's variable order), permuting each
    /// variable lazily only while earlier variables tie.
    ///
    /// Returns `Some(None)` if `words` itself is least, `Some(Some(p))` if
    /// `group[p]` is least (with the full permuted encoding written into
    /// `best_buf`), or `None` if any compared variable could not be ordered
    /// on words (`Dyn`, incomparable union arms, etc.) and must fall back to
    /// `InterpModel::least_perm`.
    fn least_perm_words(
        &self,
        group: &[Vec<PermPlan>],
        visit: &[usize],
        order: &[usize],
        words: &[u64],
        best_buf: &mut Vec<u64>,
        cand_buf: &mut Vec<u64>,
    ) -> Option<Option<usize>> {
        debug_assert_eq!(order.len(), self.layout.vars.len());
        best_buf.resize(words.len(), 0);
        cand_buf.resize(words.len(), 0);
        let mut best: Option<usize> = None;
        let mut best_computed: usize = 0;

        'perm: for &pi in visit {
            let plans = &group[pi];
            for (k, &i) in order.iter().enumerate() {
                let r = self.layout.var_range(i);
                let plan_id = plans[i].is_identity();
                if plan_id && best.is_none_or(|bp| group[bp][i].is_identity()) {
                    // Identity vs identity on a non-Dyn/Ref variable is always Equal.
                    if best.is_some() && k == best_computed {
                        best_buf[r.clone()].copy_from_slice(&words[r]);
                        best_computed += 1;
                    }
                    continue;
                }
                // Never apply a non-identity plan to a Dyn/Ref-bearing variable
                // during candidate comparison: doing so would permanently intern
                // or freeze losing permutations into `dynval` or the value store.
                if self.layout.node(i).has_dyn_or_ref() {
                    return None;
                }
                let cand_var: &[u64] = if plan_id {
                    &words[r.clone()]
                } else {
                    // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
                    unsafe { plans[i].apply_unchecked(&words[r.clone()], &mut cand_buf[r.clone()]) };
                    &cand_buf[r.clone()]
                };
                let best_var: &[u64] = match best {
                    None => &words[r.clone()],
                    Some(bp) => {
                        if k == best_computed {
                            if group[bp][i].is_identity() {
                                best_buf[r.clone()].copy_from_slice(&words[r.clone()]);
                            } else {
                                // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
                                unsafe { group[bp][i].apply_unchecked(&words[r.clone()], &mut best_buf[r.clone()]) };
                            }
                            best_computed += 1;
                        }
                        &best_buf[r.clone()]
                    }
                };
                match self.layout.node(i).cmp_tlc_words(cand_var, best_var)? {
                    std::cmp::Ordering::Greater => continue 'perm,
                    std::cmp::Ordering::Equal => {}
                    std::cmp::Ordering::Less => {
                        for &j in &order[..=k] {
                            if plans[j].is_identity() {
                                let rj = self.layout.var_range(j);
                                cand_buf[rj.clone()].copy_from_slice(&words[rj]);
                            }
                        }
                        std::mem::swap(best_buf, cand_buf);
                        best = Some(pi);
                        best_computed = k + 1;
                        continue 'perm;
                    }
                }
            }
        }

        if let Some(bp) = best {
            for &i in &order[best_computed..] {
                let r = self.layout.var_range(i);
                if group[bp][i].is_identity() {
                    best_buf[r.clone()].copy_from_slice(&words[r]);
                } else {
                    // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
                    unsafe { group[bp][i].apply_unchecked(&words[r.clone()], &mut best_buf[r]) };
                }
            }
        }
        Some(best)
    }

    /// Paranoid: word-level `least_perm_words` agrees with `InterpModel::least_perm`
    /// on the chosen orbit representative and its permuted words. Different
    /// permutation indices are fine when they select the same tied minimum:
    /// the compared state decides, while an evaluation error or a genuinely
    /// different representative is still a mismatch.
    fn check_sym_view_least(&self, group: &[Vec<PermPlan>], words: &[u64], word_least: Option<usize>, best_buf: &[u64]) {
        // SAFETY: the matching encoder/program produced these words.
        // Active Dyn handles were published before this call.
        let original = unsafe { self.layout.decode_state_unchecked(words) };
        let decode = |i: usize| unsafe { self.layout.node(i).decode_unchecked(&words[self.layout.offsets[i]..]) };
        let mut vals = StateVals::decoded(self.layout.vars.len(), &decode);
        let want = self.base.least_perm(&mut vals);
        drop(vals);
        let interp_least = match want {
            Ok(p) => p,
            Err(e) => mismatch(format_args!(
                "VIEW+SYMMETRY least_perm on state\n{}\ninterpreter: Err({e:?})\ncompiled:    Ok({word_least:?})",
                state_list(&self.base, std::slice::from_ref(&original))
            )),
        };
        // The state the compiled walk selected: its permuted words, or `words`
        // itself for the identity.
        // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
        let compiled = unsafe { self.layout.decode_state_unchecked(if word_least.is_some() { best_buf } else { words }) };
        // The state the interpreter selected: its permutation applied to the
        // original values (the identity leaves them unchanged).
        let interp = match interp_least {
            None => original.clone(),
            Some(p) => {
                let Some(perm) = self.base.symmetry_maps().get(p) else {
                    mismatch(format_args!(
                        "VIEW+SYMMETRY least_perm on state\n{}\ninterpreter selected permutation {p} beyond symmetry_maps()",
                        state_list(&self.base, std::slice::from_ref(&original))
                    ))
                };
                let mut out = Vec::with_capacity(original.len());
                for v in &original {
                    match tlx_value::ops::permute(v, &|s| perm.get(&s).cloned()) {
                        Ok(x) => out.push(x),
                        Err(e) => mismatch(format_args!(
                            "VIEW+SYMMETRY least_perm on state\n{}\ninterpreter permutation {p}: {e:?}\ncompiled:    Ok({word_least:?})",
                            state_list(&self.base, std::slice::from_ref(&original))
                        )),
                    }
                }
                out
            }
        };
        if interp != compiled {
            mismatch(format_args!(
                "VIEW+SYMMETRY least_perm on state\n{}\ninterpreter ({interp_least:?}):\n{}\ncompiled ({word_least:?}):\n{}",
                state_list(&self.base, std::slice::from_ref(&original)),
                state_list(&self.base, std::slice::from_ref(&interp)),
                state_list(&self.base, std::slice::from_ref(&compiled))
            ));
        }
        if let Some(p) = word_least {
            let mut want_words = vec![0u64; words.len()];
            for (i, plan) in group[p].iter().enumerate() {
                let r = self.layout.var_range(i);
                // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
                unsafe { plan.apply_unchecked(&words[r.clone()], &mut want_words[r]) };
            }
            if best_buf != want_words.as_slice() {
                // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
                let st = unsafe { self.layout.decode_state_unchecked(words) };
                mismatch(format_args!(
                    "VIEW+SYMMETRY permuted words (perm {p}) on state\n{}\nexpected: {want_words:?}\ngot:      {best_buf:?}",
                    state_list(&self.base, &[st])
                ));
            }
        }
    }

    /// Paranoid: factorized word-level `SymView` agrees with
    /// `InterpModel::least_state_in_orbit` for any group order (including `|G| > 720`).
    fn check_sym_view_least_state(&self, words: &[u64], non_id: bool, best_buf: &[u64]) {
        // SAFETY: the matching encoder/program produced these words.
        // Active Dyn handles were published before this call.
        let original = unsafe { self.layout.decode_state_unchecked(words) };
        let interp = match self.base.least_state_in_orbit(&original) {
            Ok(Some(v)) => v,
            Ok(None) => original.clone(),
            Err(e) => mismatch(format_args!(
                "VIEW+SYMMETRY least_state_in_orbit on state\n{}\ninterpreter: Err({e:?})\ncompiled:    Ok(non_id={non_id})",
                state_list(&self.base, std::slice::from_ref(&original))
            )),
        };
        // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
        let compiled = unsafe { self.layout.decode_state_unchecked(if non_id { best_buf } else { words }) };
        if interp != compiled {
            mismatch(format_args!(
                "VIEW+SYMMETRY factorized least representative on state\n{}\ninterpreter:\n{}\ncompiled (non_id={non_id}):\n{}",
                state_list(&self.base, std::slice::from_ref(&original)),
                state_list(&self.base, std::slice::from_ref(&interp)),
                state_list(&self.base, std::slice::from_ref(&compiled))
            ));
        }
    }

    /// Paranoid: verify every adjacent transposition generator `(k, k+1)` of
    /// every factor applies identically to value-level `ops::permute`, and
    /// (for `Fingerprint::Symmetry`) preserves the exact orbit fingerprint.
    /// Since adjacent transpositions generate `prod_g Sym(K_g)`, this verifies
    /// full orbit invariance in `O(sum_g n_g)` checks even when `|G| > 720`.
    fn check_factor_generators(&self, fsym: &FactorSymmetry, words: &[u64], check_orbit: Option<u64>) {
        let has_store = self.value_store().is_some();
        // SAFETY: the matching encoder/program produced these words.
        // Active Dyn handles were published before this call.
        let vals = unsafe { self.layout.decode_state_unchecked(words) };
        let mut gen_img = fsym.fg.identity_img();
        let mut buf = Vec::with_capacity(words.len());
        for factor in fsym.fg.factors.iter() {
            let off = factor.offset;
            for k in 0..factor.keys.len() - 1 {
                gen_img[off + k] = (k + 1) as u16;
                gen_img[off + k + 1] = k as u16;
                apply_factor_img(fsym, &self.layout, &gen_img, words, &mut buf);
                if has_store && tlx_layout::store::peek_full_hit() {
                    return;
                }
                // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
                let got = unsafe { self.layout.decode_state_unchecked(&buf) };
                let want: Vec<Value> =
                    vals.iter().map(|v| tlx_value::ops::permute(v, &|m| fsym.fg.map_sym(m, &gen_img).cloned()).expect("permute")).collect();
                if got != want {
                    mismatch(format_args!(
                        "SYMMETRY (factorized): generator swap ({}, {}) on\n{}\ndecodes to\n{}\ninstead of\n{}",
                        factor.keys[k].as_str(),
                        factor.keys[k + 1].as_str(),
                        state_list(&self.base, std::slice::from_ref(&vals)),
                        state_list(&self.base, &[got]),
                        state_list(&self.base, &[want])
                    ));
                }
                if let Some(expected_fp) = check_orbit {
                    let gen_fp = orbit_fp_factorized(fsym, &self.layout, &buf, self.sem.as_ref());
                    if gen_fp != expected_fp {
                        mismatch(format_args!(
                            "SYMMETRY (factorized): orbit_fp not invariant under generator swap ({}, {}) on\n{}\noriginal fp: {expected_fp:#018x}\nswapped fp:  {gen_fp:#018x}",
                            factor.keys[k].as_str(),
                            factor.keys[k + 1].as_str(),
                            state_list(&self.base, std::slice::from_ref(&vals))
                        ));
                    }
                }
                gen_img[off + k] = k as u16;
                gen_img[off + k + 1] = (k + 1) as u16;
            }
        }
    }

    /// Paranoid: each permutation plan applied to `words` gives the
    /// encoding of the permuted values.
    fn check_permutations(&self, group: &[Vec<PermPlan>], words: &[u64]) {
        let has_store = self.value_store().is_some();
        // SAFETY: the matching encoder/program produced these words.
        // Active Dyn handles were published before this call.
        let vals = unsafe { self.layout.decode_state_unchecked(words) };
        let mut buf = vec![0u64; words.len()];
        for (plans, m) in group.iter().zip(self.base.symmetry_maps()) {
            for (i, p) in plans.iter().enumerate() {
                let r = self.layout.var_range(i);

                // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
                unsafe { p.apply_unchecked(&words[r.clone()], &mut buf[r.clone()]) };
            }
            if has_store && tlx_layout::store::peek_full_hit() {
                return;
            }
            // SAFETY: the matching encoder/program produced these words.
            // Active Dyn handles were published before this call.
            let got = unsafe { self.layout.decode_state_unchecked(&buf) };
            let want: Vec<Value> = vals.iter().map(|v| tlx_value::ops::permute(v, &|s| m.get(&s).cloned()).expect("permute")).collect();
            if got != want {
                mismatch(format_args!(
                    "SYMMETRY: the permuted encoding (permutation {m:?}) of\n{}\ndecodes to\n{}\ninstead of\n{}",
                    state_list(&self.base, std::slice::from_ref(&vals)),
                    state_list(&self.base, &[got]),
                    state_list(&self.base, &[want])
                ));
            }
        }
    }

    /// Fingerprint of the VIEW of the state `words`: natively, else in the
    /// IR executor, else in the interpreter (all produce the canonical
    /// encoding of the VIEW's value).
    fn view_fp(&self, v: &View, words: &[u64], level: u32) -> Result<u64, ModelError> {
        let has_store = self.value_store().is_some();
        let skip_compiled = has_store && Self::transient_fallback();
        VIEW_BUF.with(|b| {
            let mut b = b.borrow_mut();
            let (ext, out) = &mut *b;
            ext.clear();
            ext.extend_from_slice(words);
            ext.resize(v.typing.layout.words, 0);
            out.clear();
            if has_store {
                tlx_layout::store::clear_full_hit();
            }
            if !skip_compiled && v.compiled(&self.base, ext, level, out) {
                if self.paranoid {
                    match self.view_interpreted(v, words, level)? {
                        ViewEncoded::Words(want) if *out == want => {}
                        want => {
                            let st = self.base.render(&self.decode(&EState {
                                words: words.into(),
                                level,
                                fp: 0,
                                #[cfg(debug_assertions)]
                                model: self.id,
                            }));
                            mismatch(format_args!("VIEW on state\n{st}\ninterpreter: {want:?}\ncompiled:    {out:?}"));
                        }
                    }
                }
            } else {
                if !skip_compiled && has_store && tlx_layout::store::take_full_hit() {
                    return Err(self.store_full_error());
                }
                match self.view_interpreted(v, words, level)? {
                    ViewEncoded::Words(w) => *out = w,
                    ViewEncoded::Digest(d) => return Ok(fp_words(&[u64::MAX, d])),
                }
            }
            Ok(self.hash_view_words(v, out))
        })
    }

    /// The VIEW's encoding computed by the interpreter; a value that does
    /// not fit its shape is a layout miss of the VIEW definition (or, in
    /// escape mode, a semantic encoding or outlier digest).
    fn view_interpreted(&self, v: &View, words: &[u64], level: u32) -> Result<ViewEncoded, ModelError> {
        // SAFETY: the matching encoder/program produced these words.
        // Active Dyn handles were published before this call.
        let vals = unsafe { self.layout.decode_state_unchecked(words) };
        self.view_encoded(v, &vals, level)
    }

    /// Evaluate the VIEW expression on decoded state `vals`.
    fn view_value(&self, vals: &[Value], level: u32) -> Result<Value, ModelError> {
        let e = self.base.view_expr().expect("VIEW");
        self.base.ip.eval(e, &Env::default(), &Ctx::state(vals, level)).and_then(|x| Ok(x.normalize()?)).map_err(|e| {
            // (A state whose VIEW fails counts as generated.)
            self.base.count_generated();
            self.base.error(e)
        })
    }

    /// The VIEW of the decoded state `vals`, encoded in the VIEW's shape.
    /// Shared by `view_interpreted` and the pressure path of `sym_view_fp`.
    fn view_encoded(&self, v: &View, vals: &[Value], level: u32) -> Result<ViewEncoded, ModelError> {
        let val = self.view_value(vals, level)?;
        let node = v.result_node();
        let mut out = vec![0u64; node.words()];
        match node.encode(&val, &mut out) {
            Ok(()) => Ok(ViewEncoded::Words(out)),
            Err(m) if m.store_full => Err(self.store_full_error()),
            Err(_) if self.escape.is_some() => {
                if node.encode_semantic(&val, &mut out).is_ok() {
                    Ok(ViewEncoded::Words(out))
                } else {
                    tlx_layout::store::digest_of_value(&val)
                        .map(ViewEncoded::Digest)
                        .map_err(|x| ModelError::new(format!("escape VIEW: {x:?}")))
                }
            }
            Err(_) => match v.def {
                Some(def) => Err(Self::record_miss(&self.def_miss, def, val)),
                None => Err(ModelError::new("internal error: anonymous VIEW value does not fit its inferred shape")),
            },
        }
    }
}

/// Result of interpreting a `VIEW` expression for fingerprinting.
#[derive(Debug)]
enum ViewEncoded {
    /// Encoded in the VIEW shape's layout (`len == node.words()`).
    Words(Vec<u64>),
    /// Out-of-layout VIEW in escape mode: hash `[u64::MAX, digest]` directly
    /// without walking the VIEW shape's `SemFp` or `ProjectionOrbit`.
    Digest(u64),
}
