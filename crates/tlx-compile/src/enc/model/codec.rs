//! Encoded-state conversion, widening, queue codec and checkpoint capabilities.
//!
//! The state type and its raw construction trust boundary remain in the parent.

use std::cell::RefCell;
use std::sync::Arc;

use tlx_eval::model::State as VState;
use tlx_layout::Layout;
use tlx_runtime::stats::{self, C, T};
use tlx_runtime::{ErrorKind, ModelError};
use tlx_value::Value;

use super::{EState, EncModel, Fingerprint, DYN_FILE, MISS_MSG, SPECULATION_FILE};
use crate::paranoid::{mismatch, state_list};

impl EncModel {
    /// The run's value store (`TLX_VALUE_STORE`), if the layout has
    /// handles.
    pub fn value_store(&self) -> Option<&tlx_layout::store::StoreRef> {
        self.sem.as_ref().map(|s| &s.store)
    }

    /// The variable values of an encoded state.
    pub fn values(&self, s: &EState) -> Arc<[Value]> {
        self.check_state_model(s);
        self.cached_values(&s.words, false)
    }

    /// The variable values of the encoded state `words`, from the worker's
    /// cache of decoded states (`DECODED`). `current`: `words` is the state
    /// being expanded (all its actions and the action properties of its
    /// steps read it); otherwise it replaces the last other state decoded.
    pub(super) fn cached_values(&self, words: &[u64], current: bool) -> Arc<[Value]> {
        let hit = DECODED.with(|c| {
            let c = c.borrow();
            if c.model != self.id {
                return None;
            }
            c.slots.iter().find(|(w, v)| v.is_some() && **w == *words).and_then(|(_, v)| v.clone())
        });
        if let Some(vals) = hit {
            return vals;
        }
        stats::count(C::Decodes, 1);
        let span = stats::span();
        // SAFETY: the matching encoder/program produced these words.
        // Active Dyn handles were published before this call.
        let vals: Arc<[Value]> = match &self.escape {
            Some(e) if words.len() > self.layout.words => e.codec.decode(words).into(),
            _ => unsafe { self.layout.decode_state_unchecked(words) }.into(),
        };
        span.end(T::Decode);
        DECODED.with(|c| {
            let mut c = c.borrow_mut();
            if c.model != self.id {
                c.model = self.id;
                c.slots.iter_mut().for_each(|s| s.1 = None);
            }
            let (w, v) = &mut c.slots[if current { 0 } else { 1 }];
            w.clear();
            w.extend_from_slice(words);
            *v = Some(vals.clone());
        });
        vals
    }

    pub(super) fn decode(&self, s: &EState) -> VState {
        VState::new(self.values(s), s.level, s.fp)
    }

    /// `decode` of the state being expanded.
    pub(super) fn decode_current(&self, s: &EState) -> VState {
        VState::new(self.cached_values(&s.words, true), s.level, s.fp)
    }

    /// Encode an interpreter state; records a layout miss on failure.
    pub(super) fn encode(&self, v: &VState) -> Result<EState, ModelError> {
        stats::count(C::Encodes, 1);
        if let Some(e) = &self.escape {
            let words = e.codec.encode(&v.vals).map_err(|x| ModelError::new(format!("escape store: {x:?}")))?;
            let fp = if matches!(self.fp, Fingerprint::Values) {
                let vals: Vec<_> = v.vals.iter().cloned().map(Some).collect();
                self.base.make_state_counted(&vals, v.level, "state").map_err(|x| self.base.error(x))?.fp
            } else {
                self.words_fp(&words, v.level)?
            };
            return Ok(EState {
                words,
                level: v.level,
                fp,
                #[cfg(debug_assertions)]
                model: self.id,
            });
        }
        let mut words = vec![0u64; self.layout.words].into_boxed_slice();
        let span = stats::span();
        let encoded = self.layout.encode_state(&v.vals, &mut words);
        span.end(T::Encode);
        match encoded {
            Ok(()) => {
                let fp = if matches!(self.fp, Fingerprint::Values) {
                    let vals: Vec<_> = v.vals.iter().cloned().map(Some).collect();
                    self.base.make_state_counted(&vals, v.level, "state").map_err(|x| self.base.error(x))?.fp
                } else {
                    self.words_fp(&words, v.level)?
                };
                Ok(EState {
                    words,
                    level: v.level,
                    fp,
                    #[cfg(debug_assertions)]
                    model: self.id,
                })
            }
            Err(m) => {
                let var = m.var_index().unwrap_or(0);
                Err(Self::record_miss(&self.miss, var, v.vals[var].clone()))
            }
        }
    }

    /// Whether `migrate` evaluates nothing in the interpreter (no VIEW, no
    /// fingerprints by value): it can run on any number of threads, with no
    /// side effects.
    pub(in crate::enc) fn migrate_is_pure(&self) -> bool {
        matches!(self.fp, Fingerprint::Words | Fingerprint::Symmetry { .. })
    }

    /// Re-encode a state of an earlier model with layout `old` (whose shapes
    /// this layout's contain) in this model's layout and fingerprints.
    pub(in crate::enc) fn migrate(&self, old: &Layout, s: &EState) -> Result<EState, ModelError> {
        let new = &self.layout;
        let mut words = vec![0u64; new.words].into_boxed_slice();
        for i in 0..new.vars.len() {
            // SAFETY: the matching encoder/program produced these words.
            // Active Dyn handles were published before this call.
            if !unsafe {
                tlx_layout::layout_tree::transcode_unchecked(
                    old.node(i),
                    new.node(i),
                    &s.words[old.offsets[i]..],
                    &mut words[new.offsets[i]..],
                )
            } {
                return Err(ModelError::of_kind(ErrorKind::LayoutMiss, MISS_MSG));
            }
        }
        if self.paranoid {
            let mut want = vec![0u64; new.words];
            // SAFETY: the matching encoder/program produced these words.
            // Active Dyn handles were published before this call.
            let vals = unsafe { old.decode_state_unchecked(&s.words) };
            if new.encode_state(&vals, &mut want).is_err() || *words != *want {
                mismatch(format_args!(
                    "re-encoding a state in a widened layout: the transcoded encoding of\n{}\ndiffers from its encoding",
                    state_list(&self.base, &[vals])
                ));
            }
        }
        let fp = if matches!(self.fp, Fingerprint::Values) {
            // SAFETY: the matching encoder/program produced these words.
            // Active Dyn handles were published before this call.
            let vals: Vec<Option<Value>> = unsafe { new.decode_state_unchecked(&words) }.into_iter().map(Some).collect();
            self.base.make_state(&vals, s.level, "state").map_err(|e| self.base.error(e))?.fp
        } else {
            self.words_fp(&words, s.level)?
        };
        Ok(EState {
            words,
            level: s.level,
            fp,
            #[cfg(debug_assertions)]
            model: self.id,
        })
    }

    /// A state produced by compiled code (already encoded).
    pub(super) fn finish(&self, words: Box<[u64]>, level: u32) -> Result<EState, ModelError> {
        let fp = if matches!(self.fp, Fingerprint::Values) {
            // SAFETY: the matching encoder/program produced these words.
            // Active Dyn handles were published before this call.
            let vals: Vec<Option<Value>> = unsafe { self.layout.decode_state_unchecked(&words) }.into_iter().map(Some).collect();
            self.base.make_state_counted(&vals, level, "state").map_err(|e| self.base.error(e))?.fp
        } else {
            self.words_fp(&words, level)?
        };
        Ok(EState {
            words,
            level,
            fp,
            #[cfg(debug_assertions)]
            model: self.id,
        })
    }
}

thread_local! {
    /// Decoded states of `EncModel::cached_values` (per worker thread).
    static DECODED: RefCell<DecodeCache> = const { RefCell::new(DecodeCache { model: 0, slots: [(Vec::new(), None), (Vec::new(), None)] }) };
}

/// The last decoded states of one worker: the state being expanded (slot
/// 0) and the last other one (slot 1), with their encodings (a hit compares
/// all words: buffers are reused and fingerprints may collide).
struct DecodeCache {
    /// Id of the `EncModel` whose layout decoded them.
    model: u64,
    slots: [(Vec<u64>, Option<Arc<[Value]>>); 2],
}

/// Checkpoints: the string table, the shapes (the layout and the
/// materialized definitions, and the driver's state) and the `Dyn`
/// interner, so that a recovered run encodes states as this one does; the
/// TLCSet registers.
impl tlx_runtime::Checkpointed for EncModel {
    fn files(&self) -> Result<Vec<(String, Vec<u8>)>, String> {
        let mut w = tlx_value::ser::Writer::new();
        tlx_layout::ser::write_dyn_table(&mut w, &tlx_layout::dynval::snapshot())
            .map_err(|e| format!("cannot write the Dyn interner to a checkpoint: {e}"))?;
        Ok(vec![
            (tlx_eval::model::STRINGS_FILE.to_string(), tlx_eval::model::strings_snapshot()),
            (SPECULATION_FILE.to_string(), self.speculation.clone()),
            (DYN_FILE.to_string(), w.into_bytes()),
        ])
    }
    fn worker_snapshot(&self) -> Result<Vec<u8>, String> {
        self.base.ip.registers_snapshot()
    }
    fn main_snapshot(&self) -> Result<Vec<u8>, String> {
        self.base.ip.main_registers_snapshot()
    }
    fn restore_workers(&self, main: &[u8], snaps: &[Vec<u8>]) -> Result<(), String> {
        tlx_runtime::Checkpointed::restore_workers(&*self.base, main, snaps)
    }
}

/// Queued states are their encodings (docs/scale.md §5.1).
impl tlx_runtime::StateCodec<EState> for EncModel {
    fn words(&self) -> usize {
        self.escape.as_ref().map_or(self.layout.words, |e| e.codec.words())
    }
    fn encode(&self, s: &EState, out: &mut [u64]) -> u64 {
        self.check_state_model(s);
        match &self.escape {
            Some(e) => e.codec.queue_words(&s.words, out),
            None => out.copy_from_slice(&s.words),
        }
        s.fp
    }
    fn validate(&self, w: &[u64]) -> Result<(), String> {
        self.escape.as_ref().map_or_else(|| self.layout.validate_words(w), |e| e.codec.validate(w))
    }
    fn decode(&self, w: &[u64], depth: u32, fp: u64) -> EState {
        <Self as tlx_runtime::StateCodec<EState>>::validate(self, w).unwrap_or_else(|e| panic!("{e}"));
        // SAFETY: validation checks all active Dyn handles and publication.
        unsafe { self.decode_trusted(w, depth, fp) }
    }
    fn decode_into(&self, w: &[u64], depth: u32, fp: u64, old: EState) -> EState {
        <Self as tlx_runtime::StateCodec<EState>>::validate(self, w).unwrap_or_else(|e| panic!("{e}"));
        // SAFETY: validation checks all active Dyn handles and publication.
        unsafe { self.decode_into_trusted(w, depth, fp, old) }
    }
    unsafe fn decode_trusted(&self, w: &[u64], depth: u32, fp: u64) -> EState {
        EState {
            words: self.escape.as_ref().map_or_else(|| w.into(), |e| e.codec.compact(w)),
            level: depth,
            fp,
            #[cfg(debug_assertions)]
            model: self.id,
        }
    }
    unsafe fn decode_into_trusted(&self, w: &[u64], depth: u32, fp: u64, mut old: EState) -> EState {
        let w = match &self.escape {
            Some(e) if !e.codec.is_escaped(w) => &w[..self.layout.words],
            _ => w,
        };
        if old.words.len() != w.len() {
            // SAFETY: the caller guarantees the source encoding and publication.
            return unsafe { self.decode_trusted(w, depth, fp) };
        }
        old.words.copy_from_slice(w);
        EState {
            words: old.words,
            level: depth,
            fp,
            #[cfg(debug_assertions)]
            model: self.id,
        }
    }
}
