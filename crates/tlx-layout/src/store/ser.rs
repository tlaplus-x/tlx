//! Deterministic binary serialization and checked restoration of a `Store`'s
//! published node table (`model-store`, docs/value-store.md §7).
//!
//! Inherits `#![forbid(unsafe_code)]` from the parent `store` module.
//!
//! Format (`tlx_value::ser` varints inside a framed `model-store` file):
//! - `uvar` format version (`STORE_VERSION = 1`)
//! - `uvar` node count `n`
//! - `n` nodes in index order `0..n`, each a 1-byte body kind tag + payload:
//!   - `1` (`Body::Int`): `ivar` integer (must be outside the immediate range)
//!   - `2` (`Body::Set`): `uvar` len, `len` child handles (strictly TLC-sorted)
//!   - `3` (`Body::Interval`): `ivar` lo, `ivar` hi
//!   - `4` (`Body::Tuple`): `uvar` len, `len` child handles
//!   - `5` (`Body::Record`): `uvar` len (`>= 1`), `len` × (`uvar` `Sym` id, child handle) in strict `Sym` order
//!   - `6` (`Body::Fcn(_, Enumerated)`): `uvar` len, `len` key handles (strictly TLC-sorted), `len` value handles
//!   - `7` (`Body::Fcn(_, Interval)`): `uvar` len, `len` key handles (contiguous immediate ints), `len` value handles
//!
//! Each child handle is one `uvar`:
//! - `TAG_STR`, `TAG_MODEL_VALUE`, `TAG_BOOL`: the raw scalar handle word
//! - `TAG_INT`: `(zigzag(i) << TAG_BITS) | TAG_INT`
//! - `TAG_NODE`: `(index << TAG_BITS) | TAG_NODE` (0-based index, strictly `< i`)
//!
//! Restoring always allocates a fresh process-unique `Store` via `Store::new`
//! (`NEXT_UID`), never reusing an on-disk store id, checks each node's byte
//! charge against the remaining budget before allocating its body, and
//! publishes each validated body through `Store::intern` (keeping shard
//! indexing, collision handling, digest computation, and accounting in one
//! place) while rejecting invalid tags, unpublished `Sym` ids,
//! forward/cyclic/out-of-range node references, malformed or duplicate bodies,
//! and budget overflow.

use std::cmp::Ordering;
use std::sync::atomic::Ordering as AtomicOrdering;
use std::sync::{Arc, OnceLock};

use tlx_base::bytes::{unzigzag, zigzag};
use tlx_value::ser::{Reader, Writer};
use tlx_value::{FcnDom, Sym};

use super::order::cmp_tlc;
use super::{
    as_bool, as_int, bool_handle, immediate_value, int_handle, tag, Body, Node, Store, StoreError, INDEX_SHIFT, PAGE, PAGES, PAGE_BITS,
    STORE_BITS, TAG_BITS, TAG_BOOL, TAG_INT, TAG_MASK, TAG_MODEL_VALUE, TAG_NODE, TAG_STR,
};

/// Binary format version of `model-store`.
const STORE_VERSION: u64 = 1;

const STORE_MASK: u64 = (1 << STORE_BITS) - 1;

const B_INT: u8 = 1;
const B_SET: u8 = 2;
const B_INTERVAL: u8 = 3;
const B_TUPLE: u8 = 4;
const B_RECORD: u8 = 5;
const B_FCN_ENUM: u8 = 6;
const B_FCN_INTERVAL: u8 = 7;

impl Store {
    /// Convert a live handle of this store into its store-id-neutral
    /// checkpoint word (`store_id = 0` for `TAG_NODE`; immediates unchanged).
    pub fn checkpoint_handle(&self, h: u64) -> u64 {
        if tag(h) != TAG_NODE {
            return h;
        }
        assert_eq!((h >> TAG_BITS) & STORE_MASK, self.id, "value store {}: foreign handle {h:#x}", self.uid);
        h & !(STORE_MASK << TAG_BITS)
    }

    /// Convert a store-id-neutral checkpoint word into a live handle of this
    /// store (`store_id = 0 -> self.id` for `TAG_NODE`; immediates unchanged),
    /// rejecting non-zero checkpoint store ids, out-of-range node indices,
    /// invalid scalar tags/payloads, and unpublished `Sym` ids.
    pub fn recover_handle(&self, h: u64) -> Result<u64, String> {
        if tag(h) == TAG_NODE {
            if ((h >> TAG_BITS) & STORE_MASK) != 0 {
                return Err(format!("corrupt value store handle {h:#x}: non-zero checkpoint store id"));
            }
            let rewritten = h | (self.id << TAG_BITS);
            if self.node(rewritten).is_none() {
                return Err(format!("corrupt value store handle {h:#x}: node out of range"));
            }
            return Ok(rewritten);
        }
        if immediate_value(h).is_none() {
            return Err(format!("corrupt value store handle {h:#x}: invalid immediate handle"));
        }
        Ok(h)
    }

    fn node_at(&self, i: usize) -> Option<&Node> {
        self.pages.get(i >> PAGE_BITS)?.get()?.get(i & (PAGE - 1))?.get()
    }

    fn write_child(&self, w: &mut Writer, h: u64) -> Result<(), String> {
        match tag(h) {
            TAG_NODE => {
                if ((h >> TAG_BITS) & STORE_MASK) != self.id {
                    return Err(format!("value store {}: foreign child handle {h:#x}", self.uid));
                }
                let Some(idx) = (h >> INDEX_SHIFT).checked_sub(1) else {
                    return Err(format!("value store {}: zero node index in handle {h:#x}", self.uid));
                };
                w.uvar((idx << TAG_BITS) | TAG_NODE);
            }
            TAG_INT => {
                let i = as_int(h).expect("immediate integer handle");
                w.uvar((zigzag(i) << TAG_BITS) | TAG_INT);
            }
            TAG_BOOL | TAG_STR | TAG_MODEL_VALUE => w.uvar(h),
            t => return Err(format!("value store {}: invalid handle tag {t} in {h:#x}", self.uid)),
        }
        Ok(())
    }

    /// Serialize every published node of this store deterministically in index
    /// order. Must be called at a safepoint (no concurrent interning).
    pub fn write_snapshot(&self, w: &mut Writer) -> Result<(), String> {
        if self.is_full() {
            return Err("the value store exceeded its budget".into());
        }
        let n = usize::try_from(self.next.load(AtomicOrdering::Acquire)).map_err(|_| "value store node count out of range".to_string())?;
        w.uvar(STORE_VERSION);
        w.usize(n);
        for i in 0..n {
            let node = self.node_at(i).ok_or_else(|| format!("value store node {i} is not published"))?;
            match &node.body {
                Body::Int(v) => {
                    w.u8(B_INT);
                    w.ivar(*v);
                }
                Body::Set(es) => {
                    w.u8(B_SET);
                    w.usize(es.len());
                    for &h in es.iter() {
                        self.write_child(w, h)?;
                    }
                }
                Body::Interval(lo, hi) => {
                    w.u8(B_INTERVAL);
                    w.ivar(*lo);
                    w.ivar(*hi);
                }
                Body::Tuple(es) => {
                    w.u8(B_TUPLE);
                    w.usize(es.len());
                    for &h in es.iter() {
                        self.write_child(w, h)?;
                    }
                }
                Body::Record(fs) => {
                    w.u8(B_RECORD);
                    w.usize(fs.len());
                    for &(k, h) in fs.iter() {
                        w.uvar(k.id() as u64);
                        self.write_child(w, h)?;
                    }
                }
                Body::Fcn(kv, dom) => {
                    w.u8(if *dom == FcnDom::Interval { B_FCN_INTERVAL } else { B_FCN_ENUM });
                    let len = kv.len() / 2;
                    w.usize(len);
                    for &h in kv.iter() {
                        self.write_child(w, h)?;
                    }
                }
            }
        }
        Ok(())
    }

    /// Restore a `Store` from bytes written by `write_snapshot`, allocating a
    /// fresh process-unique `uid` (`NEXT_UID`), rewriting all child node
    /// handles to the new store's id, validating every node invariant and
    /// symbol id (`Sym::try_from_id`), checking each node's size against the
    /// remaining budget before allocating its body, and publishing through
    /// `Store::intern`.
    pub fn read_snapshot(r: &mut Reader<'_>, budget: usize) -> Result<Arc<Store>, String> {
        let corrupt = |msg: &str| format!("corrupt value store: {msg}");
        let de = |e: tlx_value::ser::DecodeError| format!("corrupt value store: {e}");
        let budget_err = |b: usize| format!("the checkpoint's value store exceeds its budget of {} MiB (-maxmem): raise -maxmem", b >> 20);
        let check_budget = |store: &Store, payload_bytes: Option<usize>| -> Result<(), String> {
            let used = store.bytes.load(AtomicOrdering::Relaxed);
            let node_size = payload_bytes.and_then(|p| std::mem::size_of::<OnceLock<Node>>().checked_add(p));
            let total = node_size.and_then(|sz| used.checked_add(sz));
            if total.is_none_or(|t| t > store.budget) {
                return Err(budget_err(store.budget));
            }
            Ok(())
        };

        let version = r.uvar().map_err(de)?;
        if version != STORE_VERSION {
            return Err(format!("the checkpoint's value store is of version {version}, this tlx reads version {STORE_VERSION}"));
        }
        let n = r.count(1).map_err(de)?;
        if n > PAGES * PAGE || u32::try_from(n).is_err() {
            return Err(corrupt("node count exceeds store capacity"));
        }
        let store = Store::new(budget);

        for i in 0..n {
            let kind = r.u8().map_err(de)?;
            let body = match kind {
                B_INT => {
                    check_budget(&store, Some(0))?;
                    let v = r.ivar().map_err(de)?;
                    if int_handle(v).is_some() {
                        return Err(corrupt(&format!("node {i}: immediate integer {v} stored as Body::Int")));
                    }
                    Body::Int(v)
                }
                B_SET => {
                    let len = r.count(1).map_err(de)?;
                    check_budget(&store, len.checked_mul(8))?;
                    let mut es = Vec::with_capacity(len);
                    for _ in 0..len {
                        es.push(read_child(r, &store, i as u64)?);
                    }
                    for w in es.windows(2) {
                        if cmp_tlc(&store, w[0], w[1]) != Ok(Ordering::Less) {
                            return Err(corrupt(&format!("node {i}: set elements not in strict canonical order")));
                        }
                    }
                    Body::Set(es.into())
                }
                B_INTERVAL => {
                    check_budget(&store, Some(0))?;
                    let lo = r.ivar().map_err(de)?;
                    let hi = r.ivar().map_err(de)?;
                    if lo <= hi {
                        let len = hi as i128 - lo as i128 + 1;
                        if len > i32::MAX as i128 {
                            return Err(corrupt(&format!("node {i}: interval length exceeds 32-bit limit")));
                        }
                    }
                    Body::Interval(lo, hi)
                }
                B_TUPLE => {
                    let len = r.count(1).map_err(de)?;
                    check_budget(&store, len.checked_mul(8))?;
                    let mut es = Vec::with_capacity(len);
                    for _ in 0..len {
                        es.push(read_child(r, &store, i as u64)?);
                    }
                    Body::Tuple(es.into())
                }
                B_RECORD => {
                    let len = r.count(2).map_err(de)?;
                    if len == 0 {
                        return Err(corrupt(&format!("node {i}: empty record")));
                    }
                    check_budget(&store, len.checked_mul(std::mem::size_of::<(Sym, u64)>()))?;
                    let mut fs: Vec<(Sym, u64)> = Vec::with_capacity(len);
                    for _ in 0..len {
                        let raw_id = r.uvar().map_err(de)?;
                        let id = u32::try_from(raw_id).map_err(|_| corrupt(&format!("node {i}: symbol id {raw_id} out of range")))?;
                        let k = Sym::try_from_id(id).ok_or_else(|| corrupt(&format!("node {i}: unpublished symbol id {id}")))?;
                        if fs.last().is_some_and(|(prev, _)| *prev >= k) {
                            return Err(corrupt(&format!("node {i}: record fields not in strict symbol order")));
                        }
                        let v = read_child(r, &store, i as u64)?;
                        fs.push((k, v));
                    }
                    Body::Record(fs.into())
                }
                B_FCN_ENUM | B_FCN_INTERVAL => {
                    let dom = if kind == B_FCN_INTERVAL { FcnDom::Interval } else { FcnDom::Enumerated };
                    let len = r.count(2).map_err(de)?;
                    check_budget(&store, len.checked_mul(16))?;
                    let mut kv = Vec::with_capacity(len * 2);
                    for _ in 0..len * 2 {
                        kv.push(read_child(r, &store, i as u64)?);
                    }
                    let keys = &kv[..len];
                    if dom == FcnDom::Interval {
                        if let Some(&first) = keys.first() {
                            let lo = int_of(&store, first)
                                .ok_or_else(|| corrupt(&format!("node {i}: interval function key is not an integer")))?;
                            for (k, &kh) in keys.iter().enumerate() {
                                let want = lo.checked_add(k as i64);
                                if want.is_none() || int_of(&store, kh) != want {
                                    return Err(corrupt(&format!("node {i}: interval function keys are not contiguous integers")));
                                }
                            }
                        }
                    } else {
                        for w in keys.windows(2) {
                            if cmp_tlc(&store, w[0], w[1]) != Ok(Ordering::Less) {
                                return Err(corrupt(&format!("node {i}: function keys not in strict canonical order")));
                            }
                        }
                        if keys.first().is_some_and(|k| tag(*k) == TAG_STR) && !keys.iter().all(|k| tag(*k) == TAG_STR) {
                            return Err(corrupt(&format!("node {i}: mixed string and non-string function keys")));
                        }
                    }
                    Body::Fcn(kv.into(), dom)
                }
                _ => return Err(corrupt(&format!("node {i}: unknown body tag {kind}"))),
            };

            let handle = match store.intern(body) {
                Ok(h) => h,
                Err(StoreError::Full) => return Err(budget_err(store.budget)),
                Err(StoreError::InvalidHandle(h)) => return Err(corrupt(&format!("node {i}: invalid child handle {h:#x}"))),
                Err(StoreError::NotFinite(e)) => return Err(corrupt(&format!("node {i}: {e}"))),
            };
            if handle != store.handle_of(i as u64) {
                return Err(corrupt(&format!("node {i}: duplicate node body")));
            }
        }

        r.finish().map_err(de)?;
        Ok(store)
    }
}

fn int_of(store: &Store, h: u64) -> Option<i64> {
    if let Some(i) = as_int(h) {
        return Some(i);
    }
    match &store.node(h)?.body {
        Body::Int(i) => Some(*i),
        _ => None,
    }
}

fn read_child(r: &mut Reader<'_>, store: &Store, current_node: u64) -> Result<u64, String> {
    let raw = r.uvar().map_err(|e| format!("corrupt value store: {e}"))?;
    match raw & TAG_MASK {
        TAG_NODE => {
            let idx = raw >> TAG_BITS;
            if idx >= current_node {
                return Err(format!("corrupt value store: node {current_node} references out-of-range/forward node {idx}"));
            }
            Ok(store.handle_of(idx))
        }
        TAG_INT => {
            let i = unzigzag(raw >> TAG_BITS);
            int_handle(i).ok_or_else(|| format!("corrupt value store: immediate integer {i} out of range"))
        }
        TAG_BOOL => as_bool(raw).map(bool_handle).ok_or_else(|| format!("corrupt value store: invalid boolean handle {raw:#x}")),
        TAG_STR | TAG_MODEL_VALUE => {
            let raw_id = raw >> TAG_BITS;
            let id = u32::try_from(raw_id).map_err(|_| format!("corrupt value store: symbol id {raw_id} out of range"))?;
            Sym::try_from_id(id).ok_or_else(|| format!("corrupt value store: unpublished symbol id {id}"))?;
            Ok(raw)
        }
        t => Err(format!("corrupt value store: unknown child handle tag {t}")),
    }
}
