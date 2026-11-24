//! Experimental stable slots: the predicted inline payload and an optional
//! overflow handle per variable. The original layout never changes.
use std::sync::{Arc, OnceLock};

use crate::store::{StoreError, StoreRef};
use crate::Layout;
use tlx_value::Value;

pub struct EscapeLayout {
    pub layout: Arc<Layout>,
    store: OnceLock<StoreRef>,
    budget: usize,
}

impl EscapeLayout {
    pub fn new(layout: Arc<Layout>) -> Self {
        Self::with_budget(layout, 4 << 30)
    }

    pub fn with_budget(layout: Arc<Layout>, budget: usize) -> Self {
        Self { layout, store: OnceLock::new(), budget }
    }

    fn store(&self) -> &StoreRef {
        self.store.get_or_init(|| StoreRef::new(self.budget))
    }

    pub fn store_stats(&self) -> Option<crate::store::StoreStats> {
        self.store.get().map(|s| s.stats())
    }

    pub fn words(&self) -> usize {
        self.layout.words + self.layout.vars.len()
    }

    /// Inline state objects carry no suffix. Queue words always reserve it.
    pub fn is_escaped(&self, words: &[u64]) -> bool {
        words.len() > self.layout.words && words[self.layout.words..].iter().any(|&h| h != 0)
    }

    pub fn encode(&self, vals: &[Value]) -> Result<Box<[u64]>, StoreError> {
        self.encode_impl(vals, false)
    }

    /// Test the second physical form of a value that also fits inline.
    pub fn force_escape(&self, vals: &[Value]) -> Result<Box<[u64]>, StoreError> {
        self.encode_impl(vals, true)
    }

    fn encode_impl(&self, vals: &[Value], force: bool) -> Result<Box<[u64]>, StoreError> {
        assert_eq!(vals.len(), self.layout.vars.len());
        let mut words = vec![0; self.words()];
        for (i, v) in vals.iter().enumerate() {
            let range = self.layout.var_range(i);
            if force || self.layout.node(i).encode(v, &mut words[range.clone()]).is_err() {
                words[range].fill(0);
                words[self.layout.words + i] = self.store().freeze(v)?;
            }
        }
        if !self.is_escaped(&words) {
            words.truncate(self.layout.words);
        }
        Ok(words.into())
    }

    pub fn decode(&self, words: &[u64]) -> Vec<Value> {
        (0..self.layout.vars.len())
            .map(|i| match words.get(self.layout.words + i).copied().unwrap_or(0) {
                0 => self.layout.node(i).decode(&words[self.layout.var_range(i)]),
                h => self.store().thaw(h),
            })
            .collect()
    }

    /// Canonical fingerprint input. A forced escape which fits the initial
    /// codec is encoded inline here. Genuine outliers use semantic digests,
    /// never handle numbers; aliases in the overflow store have equal keys.
    pub fn key(&self, words: &[u64]) -> Box<[u64]> {
        if !self.is_escaped(words) {
            let mut out: Box<[u64]> = words[..self.layout.words].into();
            if self.layout.has_dynamic_witness {
                self.layout.canonicalize_state(&mut out);
            }
            return out;
        }
        let mut out = words.to_vec();
        let mut outlier = false;
        for i in 0..self.layout.vars.len() {
            let h = out[self.layout.words + i];
            let range = self.layout.var_range(i);
            if h == 0 {
                if self.layout.has_dynamic_witness {
                    self.layout.node(i).canonicalize_words(&mut out[range]);
                }
                continue;
            }
            let v = self.store().thaw(h);
            if self.layout.node(i).encode_semantic(&v, &mut out[range.clone()]).is_ok() {
                out[self.layout.words + i] = 0;
            } else {
                out[range].fill(0);
                outlier = true;
                out[self.layout.words + i] = self.store().digest(h);
            }
        }
        if !outlier {
            out.truncate(self.layout.words);
        }
        out.into()
    }

    pub fn queue_words(&self, words: &[u64], out: &mut [u64]) {
        assert_eq!(out.len(), self.words());
        out[..words.len()].copy_from_slice(words);
        out[words.len()..].fill(0);
    }

    pub fn compact(&self, words: &[u64]) -> Box<[u64]> {
        if self.is_escaped(words) {
            words.into()
        } else {
            words[..self.layout.words].into()
        }
    }

    pub fn validate(&self, words: &[u64]) -> Result<(), String> {
        if words.len() != self.words() && words.len() != self.layout.words {
            return Err("invalid escape state width".into());
        }
        for i in 0..self.layout.vars.len() {
            let h = words.get(self.layout.words + i).copied().unwrap_or(0);
            if h == 0 {
                self.layout.node(i).validate_canonical_words(&words[self.layout.var_range(i)])?;
            } else if !self.store.get().is_some_and(|s| s.is_valid(h)) {
                return Err("invalid escape handle".into());
            }
        }
        Ok(())
    }
}
