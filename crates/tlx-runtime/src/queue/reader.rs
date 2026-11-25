//! Reading a claimed block, state by state (`docs/scale.md` §5.2).
//!
//! A worker claims a block and reads its states through a `Reader`: objects
//! are taken from the end of the vector, encoded records are decoded with
//! the queue's `StateCodec` out of the block's segment bytes (read back from
//! disk first if it was spilled).

use std::sync::Arc;

use super::block::{Block, Kind, Segment};
use super::codec::{self, XorPrev};
use super::{StateCodec, Task};
use crate::io::IoError;

/// A block claimed by a worker, read state by state.
pub(crate) struct Reader<S> {
    block: Block<S>,
    /// Encoded: the bytes of the block's segment, once loaded (`load`).
    pub(super) data: Option<Arc<Segment>>,
    /// Encoded: the byte offset of the next record, and the records left.
    pos: usize,
    pub(super) left: usize,
}

impl<S> Reader<S> {
    /// A reader of `block` (whose segment is not loaded yet).
    pub(super) fn new(mut block: Block<S>, prev: &mut XorPrev) -> Reader<S> {
        let (pos, left) = match &mut block {
            Block::Objects { tasks, .. } => {
                // (Taken from the end.)
                tasks.reverse();
                (0, tasks.len())
            }
            Block::Encoded { start, n, .. } => {
                prev.reset();
                (*start as usize, *n as usize)
            }
        };
        Reader { block, data: None, pos, left }
    }

    /// Have the bytes of an encoded block in memory (reading its segment
    /// back if spilled).
    pub(crate) fn load(&mut self) -> Result<(), IoError> {
        if let (Some(seg), None) = (self.block.seg(), &self.data) {
            self.data = Some(seg.get()?);
        }
        Ok(())
    }

    /// The states left.
    pub(crate) fn left(&self) -> usize {
        self.left
    }

    /// Whether the block is a compressed one (moved to the archive whole
    /// once read, see `Queue::append`).
    #[inline]
    pub(crate) fn compressed(&self) -> bool {
        matches!(self.block, Block::Encoded { kind: Kind::Xor, .. })
    }

    /// The block read (all of it, also the states already read, if encoded).
    pub(crate) fn into_block(self) -> Block<S> {
        // (The segment's bytes are released: it may be spilled.)
        self.block
    }

    /// Non-destructively visit states held by this reader for safepoint root
    /// scanning. When `include_consumed` is true (a compressed block destined
    /// for a retained whole-block archive), visits the entire block; otherwise
    /// visits only the last `self.left` unread records so already-consumed
    /// frontier states can be reclaimed immediately.
    pub(crate) fn visit_states(
        &self,
        include_consumed: bool,
        cache: &mut super::SegCache,
        prev: &mut XorPrev,
        visit: &mut dyn FnMut(super::StateRef<'_, S>),
    ) -> Result<(), IoError> {
        if include_consumed {
            self.block.visit_states(cache, prev, visit)
        } else {
            self.block.visit_suffix(self.left, cache, prev, visit)
        }
    }

    /// The next state, decoded with `codec` (with `prev` the scratch of
    /// this reader, reusing `spare` if given).
    #[inline]
    pub(super) fn next(&mut self, codec: Option<&dyn StateCodec<S>>, prev: &mut XorPrev, spare: &mut Option<S>) -> Option<Task<S>> {
        if self.left == 0 {
            return None;
        }
        self.left -= 1;
        match &mut self.block {
            Block::Objects { tasks, .. } => tasks.pop(),
            Block::Encoded { kind, depth, .. } => {
                let codec = codec.expect("encoded block without a codec");
                let data = &self.data.as_ref().expect("reading a block not loaded").data;
                let (log, fp) = match kind {
                    Kind::Raw => {
                        let size = codec::raw_size(prev.words.len());
                        let r = codec::get_raw(&data[self.pos..self.pos + size], &mut prev.words);
                        self.pos += size;
                        r
                    }
                    Kind::Xor => {
                        let fp = codec::get_xor(data, &mut self.pos, prev);
                        (prev.log, fp)
                    }
                };
                // SAFETY: records originate in encode (or validate at recovery).
                // Seg::get verifies spilled bytes against the original BlockRef's
                // in-memory checksums before they reach this reader.
                let state = unsafe {
                    match spare.take() {
                        Some(old) => codec.decode_into_trusted(&prev.words, *depth, fp, old),
                        None => codec.decode_trusted(&prev.words, *depth, fp),
                    }
                };
                Some(Task { state, log, depth: *depth })
            }
        }
    }
}
