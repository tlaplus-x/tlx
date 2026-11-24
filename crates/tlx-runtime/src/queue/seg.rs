//! Segments in memory or on disk (docs/scale.md §5.3).
//!
//! The encoded blocks of a segment share a `Seg`: the segment's bytes in
//! memory (`Segment`), or where they are on disk. A segment nobody is
//! reading can be written to a block store (`Seg::spill`: handed to the
//! writer thread, its memory given back once written); it is read back
//! when one of its blocks is claimed (`Seg::get`), ahead of the claims if
//! prefetched (`Seg::prefetch`, on the reader thread), and its disk copy is
//! deleted then. The bytes a reader decodes are an `Arc<Segment>` it holds
//! while it reads (so the hot path does not touch the `Seg`); a segment
//! held by a reader is not spilled.

use std::sync::Arc;

use parking_lot::Mutex;

use super::{Charge, Mem, Segment};
use crate::io::{BlockRef, BlockStore, IoError, Pending, Prefetch, Spill};

/// A segment of encoded blocks: in memory, or spilled.
pub(crate) struct Seg {
    state: Mutex<State>,
}

enum State {
    Mem(Arc<Segment>),
    /// Handed to the writer thread (its memory stays counted in `ChargedBytes`
    /// until the write succeeds and frees the buffer; a failed write keeps the
    /// buffer and its charge alive).
    Pending {
        store: Arc<BlockStore>,
        p: Arc<Pending>,
        mem: Arc<Mem>,
    },
    /// On disk; `mem` counts it once read back.
    Disk {
        store: Arc<BlockStore>,
        r: BlockRef,
        mem: Arc<Mem>,
    },
    /// Being read back ahead of its claim.
    Fetch {
        store: Arc<BlockStore>,
        r: BlockRef,
        p: Arc<Prefetch>,
        mem: Arc<Mem>,
    },
    /// (Transient, while the state changes.)
    Empty,
}

/// Segment buffer handed to the asynchronous spill writer while retaining its
/// `Mem` charge until the write succeeds (or the failed buffer is taken back /
/// dropped).
struct ChargedBytes {
    data: Vec<u8>,
    _charge: Charge,
}

impl crate::io::Bytes for ChargedBytes {
    fn bytes(&self) -> &[u8] {
        &self.data
    }

    fn into_any(self: Box<Self>) -> Box<dyn std::any::Any + Send> {
        Box::new(self.data)
    }
}

/// Bytes of a segment for reading records (`Seg::bytes`): the segment in
/// memory, or a range read from disk.
pub(crate) enum Bytes {
    Shared(Arc<Segment>),
    Owned(Vec<u8>),
}

impl Seg {
    /// A segment in memory.
    pub(crate) fn new(seg: Segment) -> Arc<Seg> {
        Arc::new(Seg { state: Mutex::new(State::Mem(Arc::new(seg))) })
    }

    /// A segment of `data` read back from disk, counted in `mem`.
    fn loaded(data: Vec<u8>, mem: &Arc<Mem>) -> Arc<Segment> {
        Arc::new(Segment { charge: Mutex::new(Charge::new(data.capacity(), mem)), data })
    }

    /// The segment's bytes in memory: read back if spilled (waiting for
    /// its write or its prefetch; the disk copy is deleted). An error
    /// leaves the segment where it was.
    pub(crate) fn get(&self) -> Result<Arc<Segment>, IoError> {
        let mut st = self.state.lock();
        loop {
            match std::mem::replace(&mut *st, State::Empty) {
                State::Mem(s) => {
                    *st = State::Mem(s.clone());
                    return Ok(s);
                }
                State::Pending { store, p, mem } => {
                    *st = match p.settle() {
                        Ok(r) => State::Disk { store, r, mem },
                        // (A failed write keeps the data in memory.)
                        Err((data, _)) => State::Mem(Seg::loaded(data, &mem)),
                    };
                }
                State::Disk { store, r, mem } => match store.read(&r) {
                    Ok(data) => {
                        store.delete(r);
                        *st = State::Mem(Seg::loaded(data, &mem));
                    }
                    Err(e) => {
                        *st = State::Disk { store, r, mem };
                        return Err(e);
                    }
                },
                State::Fetch { store, r, p, mem } => match p.wait() {
                    Ok(data) => {
                        store.delete(r);
                        *st = State::Mem(Seg::loaded(data, &mem));
                    }
                    Err(e) => {
                        *st = State::Disk { store, r, mem };
                        return Err(e);
                    }
                },
                State::Empty => unreachable!("segment in transition"),
            }
        }
    }

    /// The segment's bytes, for reading its records once (the archive):
    /// the segment if in memory, else read from disk without keeping them
    /// in the segment (which stays on disk).
    pub(crate) fn bytes(&self) -> Result<Bytes, IoError> {
        let mut st = self.state.lock();
        loop {
            match std::mem::replace(&mut *st, State::Empty) {
                State::Mem(s) => {
                    *st = State::Mem(s.clone());
                    return Ok(Bytes::Shared(s));
                }
                State::Pending { store, p, mem } => {
                    if let Some(copy) = p.with_data(|d| d.to_vec()) {
                        *st = State::Pending { store, p, mem };
                        return Ok(Bytes::Owned(copy));
                    }
                    *st = match p.settle() {
                        Ok(r) => State::Disk { store, r, mem },
                        Err((data, _)) => State::Mem(Seg::loaded(data, &mem)),
                    };
                }
                State::Disk { store, r, mem } => {
                    let data = store.read(&r);
                    *st = State::Disk { store, r, mem };
                    return data.map(Bytes::Owned);
                }
                fetch @ State::Fetch { .. } => {
                    // (Read ahead for a claim: rare here.)
                    *st = fetch;
                    drop(st);
                    return self.get().map(Bytes::Shared);
                }
                State::Empty => unreachable!("segment in transition"),
            }
        }
    }

    /// Write the segment to `store` (on the writer thread) if it is in
    /// memory and nobody reads it. Whether it was handed over.
    pub(crate) fn spill(&self, spill: &Spill, store: &Arc<BlockStore>) -> Spilled {
        let mut st = self.state.lock();
        let State::Mem(s) = &mut *st else { return Spilled::Done };
        let Some(seg) = Arc::get_mut(s) else { return Spilled::Busy };
        let data = std::mem::take(&mut seg.data);
        let charge = seg.charge.get_mut().take();
        let mem = charge.mem.clone();
        *st = State::Pending { store: store.clone(), p: spill.write_async(store, Box::new(ChargedBytes { data, _charge: charge })), mem };
        Spilled::Now
    }

    /// Start reading the segment back if it is on disk.
    pub(crate) fn prefetch(&self, spill: &Spill) {
        let mut st = self.state.lock();
        if let State::Pending { p, .. } = &*st {
            // (Not written yet, or kept in memory: read when claimed.)
            let Some(Ok(r)) = p.try_done() else { return };
            let State::Pending { store, mem, .. } = std::mem::replace(&mut *st, State::Empty) else { unreachable!() };
            *st = State::Disk { store, r, mem };
        }
        if let State::Disk { .. } = &*st {
            let State::Disk { store, r, mem } = std::mem::replace(&mut *st, State::Empty) else { unreachable!() };
            let p = spill.prefetch(&store, &r);
            *st = State::Fetch { store, r, p, mem };
        }
    }

    /// Count the segment's memory (now, or once read back) in `mem`.
    pub(crate) fn move_to(&self, to: &Arc<Mem>) {
        let mut st = self.state.lock();
        match &mut *st {
            State::Mem(s) => s.charge.lock().move_to(to),
            State::Pending { mem, .. } | State::Disk { mem, .. } | State::Fetch { mem, .. } => *mem = to.clone(),
            State::Empty => {}
        }
    }
}

/// What `Seg::spill` did.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Spilled {
    /// Handed to the writer thread.
    Now,
    /// Not in memory (spilled already).
    Done,
    /// In memory, being read.
    Busy,
}

impl Drop for Seg {
    fn drop(&mut self) {
        // The disk copy is given back.
        match std::mem::replace(self.state.get_mut(), State::Empty) {
            State::Disk { store, r, .. } => store.delete(r),
            State::Fetch { store, r, p, .. } => {
                // (Not while the reader thread reads it.)
                let _ = p.wait();
                store.delete(r);
            }
            State::Pending { store, p, .. } => {
                if let Some(Ok(r)) = p.try_done() {
                    store.delete(r);
                }
            }
            State::Mem(_) | State::Empty => {}
        }
    }
}
