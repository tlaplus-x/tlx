//! Candidate state storage for multi-worker BFS representative selection:
//! XOR-varint encoding, Stage 4 disk spilling/prefetching, and non-destructive
//! GC root scanning.

use std::sync::Arc;

use super::super::tracelog::LogRef;
use crate::io::{BlockRef, BlockStore, IoError, Pending, Prefetch, Spill};
use crate::queue::codec::{self, XorPrev};
use crate::queue::StateCodec;
use tlx_base::bytes::{get_uvar_trusted, put_uvar};

/// What a candidate kept needs besides its state (stored with the state).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::explore) struct Meta {
    /// The parent's trace-log entry.
    pub(super) parent: LogRef,
    pub(super) depth: u32,
    /// The action that generated it.
    pub(super) action: u32,
}

/// The states of the candidates one worker buffered, in the order they were
/// offered (see the parent module).
///
/// Every candidate's state is needed until the level is resolved (only then
/// is the representative of its class known), so a whole level of states is
/// held at a time. For a model with wide states and wide levels that is the
/// search's memory: MultiPaxos_MC buffers 335 words for each of more than
/// ten million candidates at its widest level, tens of GiB against the
/// 2 GiB the whole single-worker search needs, which the machine pays for
/// in page faults, memory traffic and cache misses (docs/scale.md). The
/// states of a level are alike, so with a state codec (the compiled tier)
/// each is stored XOR-varint encoded against the previous one, as the
/// queue's blocks are: the same candidates cost a few percent of that. A
/// model whose states are not words (the interpreter) keeps them, as
/// before.
///
/// Encoded, the records are appended to segments (`seg_bytes`, whole
/// records each, as the queue's); under memory pressure (`Order::spill`)
/// the full ones go to disk, and `resolve` reads them back in order, the
/// next one read ahead. Even encoded, a wide level is too much for a small
/// budget: MultiPaxos_MC's candidates took 1.5 GiB with 8 or 16 workers,
/// whatever the budget, and a run in a control group of 1.7 GiB (budget
/// 857 MiB) was killed.
///
/// A state stored encoded is decoded after the ones before it, so `resolve`
/// visits the candidates in the order they were offered. Which state of a
/// class represents it, the counts, the BFS positions (from the keys) and
/// the outdegrees do not depend on that order; which of several violations
/// of the level is reported first does (docs/compat.md, tier 3).
pub(in crate::explore) enum CandStore<'m, S> {
    /// The states as words, XOR-varint encoded against the previous one.
    Words(Box<Words<'m, S>>),
    /// The states themselves.
    Objects(Vec<Option<(S, Meta)>>),
}

/// A full segment of encoded candidates.
enum CandSeg {
    Mem(Vec<u8>),
    /// Handed to the writer thread.
    Pending(Arc<Pending>),
    Disk(BlockRef),
}

pub(in crate::explore) struct Words<'m, S> {
    codec: &'m dyn StateCodec<S>,
    /// The full segments, in order, and the one appended to (records are
    /// only appended).
    segs: Vec<CandSeg>,
    cur: Vec<u8>,
    seg_bytes: usize,
    /// The store of the segments spilled (created with the first one).
    store: Option<Arc<BlockStore>>,
    /// The state `codec.encode` writes before it is encoded.
    scratch: Vec<u64>,
    /// The last state pushed (the record the next one is relative to).
    enc: XorPrev,
    /// The last state decoded; the segment being decoded (`rd`, the
    /// `next` one in `segs`) and where in it the next record starts; the
    /// read ahead of a spilled segment.
    dec: XorPrev,
    rd: Vec<u8>,
    next: usize,
    pos: usize,
    ahead: Option<(usize, Arc<Prefetch>)>,
    /// How many records were pushed, and how many of them have been
    /// decoded (in order).
    pushed: usize,
    decoded: usize,
}

impl<S> Words<'_, S> {
    /// Make the next segment the one decoded (`rd`), reading it back if it
    /// was spilled (and reading the one after it ahead).
    fn load_next(&mut self, spill: &Spill) -> Result<(), IoError> {
        let k = self.next;
        self.next += 1;
        self.pos = 0;
        let Some(seg) = self.segs.get_mut(k) else {
            // (The last records: the segment appended to.)
            self.rd = std::mem::take(&mut self.cur);
            return Ok(());
        };
        let bytes = match std::mem::replace(seg, CandSeg::Mem(Vec::new())) {
            CandSeg::Mem(v) => v,
            CandSeg::Pending(p) => match p.settle::<Vec<u8>>() {
                Ok(r) => self.read_back(k, r)?,
                // (The write failed, recorded in the spill directory: the
                // data came back.)
                Err((v, _)) => v,
            },
            CandSeg::Disk(r) => self.read_back(k, r)?,
        };
        if let (Some(CandSeg::Disk(r)), Some(store)) = (self.segs.get(k + 1), &self.store) {
            self.ahead = Some((k + 1, spill.prefetch(store, r)));
        }
        self.rd = bytes;
        Ok(())
    }

    /// The bytes of spilled segment `k` (at `r`), deleted from the disk
    /// (an IO error is recorded in the spill directory by the store).
    fn read_back(&mut self, k: usize, r: BlockRef) -> Result<Vec<u8>, IoError> {
        let store = self.store.as_ref().expect("a store of the spilled candidates");
        let bytes = match self.ahead.take() {
            Some((at, p)) if at == k => p.wait(),
            _ => store.read(&r),
        };
        store.delete(r);
        bytes
    }
}

impl<'m, S> CandStore<'m, S> {
    /// The store of a worker, with `codec` if the model's states are words,
    /// in segments of `seg_bytes`.
    pub(super) fn new(codec: Option<&'m dyn StateCodec<S>>, seg_bytes: usize) -> CandStore<'m, S> {
        match codec {
            Some(codec) => CandStore::Words(Box::new(Words {
                codec,
                segs: Vec::new(),
                cur: Vec::new(),
                seg_bytes: seg_bytes.max(1),
                store: None,
                scratch: vec![0; codec.words()],
                enc: XorPrev::new(codec.words()),
                dec: XorPrev::new(codec.words()),
                rd: Vec::new(),
                next: 0,
                pos: 0,
                ahead: None,
                pushed: 0,
                decoded: 0,
            })),
            None => CandStore::Objects(Vec::new()),
        }
    }

    /// Buffer the state of `s` (`fp` its fingerprint) and `meta`: where it
    /// is (stored in `CandBuf::ats`). The state is encoded, not kept: a
    /// record is the action and depth (varints) and the XOR record of the
    /// state, whose log reference is the parent's.
    pub(super) fn push(&mut self, s: S, fp: u64, meta: Meta) -> u32 {
        match self {
            CandStore::Words(w) => {
                w.codec.encode(&s, &mut w.scratch);
                // (A segment holds whole records, within its capacity.)
                let most = codec::xor_max_size(w.scratch.len()) + 2 * 10;
                if w.cur.len() + most > w.cur.capacity() {
                    if !w.cur.is_empty() {
                        let full = std::mem::take(&mut w.cur);
                        w.segs.push(CandSeg::Mem(full));
                    }
                    w.cur.reserve_exact(w.seg_bytes.max(most));
                }
                put_uvar(&mut w.cur, meta.action as u64);
                put_uvar(&mut w.cur, meta.depth as u64);
                codec::put_xor(&mut w.cur, &mut w.enc, meta.parent, fp, &w.scratch);
                let at = w.pushed;
                w.pushed += 1;
                at as u32
            }
            CandStore::Objects(v) => {
                v.push(Some((s, meta)));
                (v.len() - 1) as u32
            }
        }
    }

    /// The state at `at` (from `CandBuf::ats`), which must not be before the
    /// last one passed: the records before it are decoded (the states of a
    /// level are stored encoded, see the type). An IO error reading a spilled
    /// segment back stops the search.
    pub(super) fn get(&mut self, at: u32, fp: u64, spill: &Spill) -> Result<(S, Meta), IoError> {
        match self {
            CandStore::Words(w) => {
                debug_assert!(at as usize >= w.decoded && (at as usize) < w.pushed, "candidates decoded in order");
                let (mut action, mut depth) = (0, 0);
                while w.decoded <= at as usize {
                    while w.pos >= w.rd.len() {
                        w.load_next(spill)?;
                    }
                    action = get_uvar_trusted(&w.rd, &mut w.pos) as u32;
                    depth = get_uvar_trusted(&w.rd, &mut w.pos) as u32;
                    codec::get_xor(&w.rd, &mut w.pos, &mut w.dec);
                    w.decoded += 1;
                }
                let meta = Meta { parent: w.dec.log, depth, action };
                // SAFETY: the records were written only by this codec's
                // encode in push, kept in memory or read back from disk with
                // their checksums verified; the XOR codec preserves the words.
                Ok((unsafe { w.codec.decode_trusted(&w.dec.words, depth, fp) }, meta))
            }
            CandStore::Objects(v) => Ok(v[at as usize].take().expect("the state of a candidate")),
        }
    }

    /// Hand the full segments in memory to the disk, and release those
    /// written (memory pressure: `Order::spill`).
    pub(super) fn spill(&mut self, spill: &Spill) -> Result<(), IoError> {
        let CandStore::Words(w) = self else { return Ok(()) };
        let mut err = None;
        for seg in &mut w.segs {
            match seg {
                CandSeg::Mem(v) if !v.is_empty() => {
                    let store = match &w.store {
                        Some(s) => s,
                        None => w.store.insert(spill.store("cands")?),
                    };
                    let p = spill.write_async(store, Box::new(std::mem::take(v)));
                    *seg = CandSeg::Pending(p);
                }
                CandSeg::Pending(p) => match p.try_settle::<Vec<u8>>() {
                    Some(Ok(r)) => *seg = CandSeg::Disk(r),
                    Some(Err((v, e))) => {
                        *seg = CandSeg::Mem(v);
                        err.get_or_insert(e);
                    }
                    None => {}
                },
                _ => {}
            }
        }
        err.map_or(Ok(()), Err)
    }

    /// Forget the states of the level resolved (the buffers are reused;
    /// spilled segments are deleted).
    pub(super) fn clear(&mut self) {
        match self {
            CandStore::Words(w) => {
                w.ahead = None;
                for seg in w.segs.drain(..) {
                    let r = match seg {
                        CandSeg::Mem(_) => continue,
                        CandSeg::Pending(p) => match p.settle::<Vec<u8>>() {
                            Ok(r) => r,
                            Err(_) => continue,
                        },
                        CandSeg::Disk(r) => r,
                    };
                    w.store.as_ref().expect("a store of the spilled candidates").delete(r);
                }
                // (The buffer appended to stays: the segment last decoded, or
                // the one appended to if none was full.)
                if w.cur.capacity() == 0 {
                    w.cur = std::mem::take(&mut w.rd);
                }
                w.cur.clear();
                w.rd = Vec::new();
                w.enc.reset();
                w.dec.reset();
                w.pushed = 0;
                w.decoded = 0;
                w.next = 0;
                w.pos = 0;
            }
            CandStore::Objects(v) => v.clear(),
        }
    }

    pub(super) fn shrink(&mut self) {
        match self {
            CandStore::Words(w) => {
                w.cur.shrink_to_fit();
                w.rd.shrink_to_fit();
            }
            CandStore::Objects(v) => v.shrink_to_fit(),
        }
    }

    /// The memory of the store (bytes, for the memory budget): segments in
    /// memory, also while being written.
    pub(super) fn bytes(&self) -> usize {
        match self {
            CandStore::Words(w) => {
                let segs: usize = w
                    .segs
                    .iter()
                    .map(|s| match s {
                        CandSeg::Mem(v) => v.capacity(),
                        CandSeg::Pending(_) => w.seg_bytes,
                        CandSeg::Disk(_) => 0,
                    })
                    .sum();
                std::mem::size_of::<Words<'_, S>>()
                    + segs
                    + w.cur.capacity()
                    + w.rd.capacity()
                    + w.ahead.as_ref().map_or(0, |_| w.seg_bytes)
                    + w.segs.capacity() * std::mem::size_of::<CandSeg>()
                    + 8 * (w.scratch.capacity() + w.enc.words.capacity() + w.dec.words.capacity())
            }
            CandStore::Objects(v) => v.capacity() * std::mem::size_of::<Option<(S, Meta)>>(),
        }
    }

    /// Non-destructively visit every unconsumed candidate state in this store
    /// for safepoint GC root scanning (safe both before and during `resolve`).
    pub(in crate::explore) fn visit_states(&mut self, visit: &mut dyn FnMut(crate::queue::StateRef<'_, S>)) -> Result<(), IoError> {
        match self {
            CandStore::Objects(v) => {
                for (s, _) in v.iter().flatten() {
                    visit(crate::queue::StateRef::Obj(s));
                }
                Ok(())
            }
            CandStore::Words(w) => {
                let mut rem = w.pushed.saturating_sub(w.decoded);
                if rem == 0 {
                    return Ok(());
                }
                let mut dec = w.dec.clone();
                let mut scan_buf = |buf: &[u8], start: usize, rem: &mut usize, dec: &mut XorPrev| {
                    let mut pos = start;
                    while *rem > 0 && pos < buf.len() {
                        let _action = get_uvar_trusted(buf, &mut pos);
                        let _depth = get_uvar_trusted(buf, &mut pos);
                        let _fp = codec::get_xor(buf, &mut pos, dec);
                        visit(crate::queue::StateRef::Words(&dec.words));
                        *rem -= 1;
                    }
                };
                if w.pos < w.rd.len() {
                    scan_buf(&w.rd, w.pos, &mut rem, &mut dec);
                }
                for seg in w.segs.iter_mut().skip(w.next) {
                    if rem == 0 {
                        break;
                    }
                    match seg {
                        CandSeg::Mem(v) => scan_buf(v, 0, &mut rem, &mut dec),
                        CandSeg::Pending(p) => match p.settle::<Vec<u8>>() {
                            Ok(r) => {
                                let store = w.store.as_ref().expect("a store of the spilled candidates");
                                let bytes = store.read(&r)?;
                                *seg = CandSeg::Disk(r);
                                scan_buf(&bytes, 0, &mut rem, &mut dec);
                            }
                            Err((v, _)) => {
                                scan_buf(&v, 0, &mut rem, &mut dec);
                                *seg = CandSeg::Mem(v);
                            }
                        },
                        CandSeg::Disk(r) => {
                            let store = w.store.as_ref().expect("a store of the spilled candidates");
                            let bytes = store.read(r)?;
                            scan_buf(&bytes, 0, &mut rem, &mut dec);
                        }
                    }
                }
                if rem > 0 && !w.cur.is_empty() {
                    scan_buf(&w.cur, 0, &mut rem, &mut dec);
                }
                debug_assert_eq!(rem, 0, "CandStore::visit_states missed {rem} candidates");
                Ok(())
            }
        }
    }
}

#[cfg(test)]
pub(super) struct Words3;

#[cfg(test)]
impl StateCodec<Vec<u64>> for Words3 {
    fn words(&self) -> usize {
        3
    }
    fn encode(&self, s: &Vec<u64>, out: &mut [u64]) -> u64 {
        out.copy_from_slice(s);
        0
    }
    fn decode(&self, w: &[u64], _depth: u32, _fp: u64) -> Vec<u64> {
        w.to_vec()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The states come back as pushed, skipping some, and again after
    /// `clear`: in memory, and with segments of a few records written to
    /// disk while being pushed (and read back ahead).
    #[test]
    fn encoded_candidates_roundtrip() {
        let codec = Words3;
        // (Parents that go up and down, actions and depths of any size.)
        let meta =
            |x: u64| Meta { parent: x.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> (x % 40), depth: (x % 1000) as u32, action: (x * 7) as u32 };
        let scratch = tlx_testkit::TempDir::new("cands");
        let dir = scratch.child_path("spill");
        let spill = Spill::new(crate::io::SpillConfig { dir: Some(dir.clone()), ..Default::default() });
        for spilling in [false, true] {
            let mut store = CandStore::new(Some(&codec as &dyn StateCodec<Vec<u64>>), 64);
            for _ in 0..2 {
                let states: Vec<Vec<u64>> = (0..50u64).map(|i| vec![i / 7, i * i, if i % 3 == 0 { 0 } else { u64::MAX - i }]).collect();
                let at: Vec<u32> = states
                    .iter()
                    .map(|s| {
                        let at = store.push(s.clone(), 0, meta(s[1]));
                        if spilling {
                            store.spill(&spill).unwrap();
                        }
                        at
                    })
                    .collect();
                assert_eq!(at, (0..50).collect::<Vec<u32>>());
                if spilling {
                    let CandStore::Words(w) = &store else { unreachable!() };
                    assert!(w.segs.len() > 5, "segments of a few records");
                    // (Some written, some still pending or in memory.)
                    store.spill(&spill).unwrap();
                }
                for i in (0..50).step_by(3).chain([49]) {
                    assert_eq!(store.get(i as u32, 0, &spill).unwrap(), (states[i].clone(), meta(states[i][1])));
                }
                store.clear();
            }
            assert_eq!(spill.counters().used, 0, "spilled segments deleted");
        }
        assert!(spill.counters().written > 0);
    }
}
