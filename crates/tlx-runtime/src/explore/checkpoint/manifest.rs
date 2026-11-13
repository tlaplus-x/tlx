//! The manifest of a checkpoint (`MANIFEST`): its format.

use tlx_value::ser::{Reader, Writer};

use super::Segments;
use crate::explore::resume::BaseCounters;
use crate::explore::{OutdegreeHist, OUTDEGREE_BUCKETS};

/// The version of the manifest's contents.
const VERSION: u64 = 4;

/// A file of the seen set's fingerprints (ascending).
#[derive(Clone, Debug)]
pub(super) struct FpSection {
    pub(super) name: String,
    pub(super) count: u64,
    /// It continues the previous one: their fingerprints are ascending
    /// together (the parts of the table).
    pub(super) joined: bool,
}

/// The manifest of a checkpoint.
#[derive(Clone)]
pub(super) struct Manifest {
    pub(super) number: u64,
    pub(super) identity: Vec<(String, String)>,
    /// The workers of the checkpointed search.
    pub(super) workers: usize,
    /// Stable history shard IDs are the dense range `0..shards`.
    /// Independent of the number of workers taking this checkpoint.
    pub(super) shards: usize,
    /// The depth of the queued states.
    pub(super) level: u32,
    /// The counters (its depth: of the search so far; the `-coverage`
    /// counts so far, empty if not counting).
    pub(super) base: BaseCounters,
    pub(super) distinct: u64,
    pub(super) queued: u64,
    /// The queue has the BFS positions of its states.
    pub(super) ordered: bool,
    /// The archive is complete (files `archive-<w>`).
    pub(super) archive: bool,
    /// The liveness edges are recorded (files `edges-<shard>`).
    pub(super) edges: bool,
    /// The states of the levels below this one were expanded before a
    /// resume (after a layout miss), and their liveness edges are recorded
    /// only at the end of the search, from the archive (`Shared::live_pre`);
    /// 0 if none.
    pub(super) pre_level: u32,
    /// The words of the encoded states (0: `Persist` bytes).
    pub(super) words: usize,
    /// The files of the seen set (the runs, then the parts of the table).
    pub(super) fp_sections: Vec<FpSection>,
    /// The files of the queue, in claim order.
    pub(super) queue_files: Vec<String>,
    /// The streams (`trace-<shard>`, ...) and their segments.
    pub(super) streams: Vec<(String, Segments)>,
    /// The files, with their sizes.
    pub(super) files: Vec<(String, u64)>,
    /// The model's files (`model-<name>`).
    pub(super) model_files: Vec<String>,
    /// Per worker, `Checkpointed::worker_snapshot`; `Checkpointed::main_snapshot`.
    pub(super) snapshots: Vec<Vec<u8>>,
    pub(super) main: Vec<u8>,
}

impl Manifest {
    pub(super) fn encode(&self) -> Vec<u8> {
        let mut w = Writer::new();
        w.uvar(VERSION);
        w.uvar(self.number);
        w.usize(self.identity.len());
        for (k, v) in &self.identity {
            w.str(k);
            w.str(v);
        }
        let b = &self.base;
        for x in [
            self.workers as u64,
            self.level as u64,
            b.init_generated,
            b.init_distinct,
            b.generated_after_init,
            self.distinct,
            self.queued,
            b.depth as u64,
        ] {
            w.uvar(x);
        }
        for &c in &b.outdegree.counts {
            w.uvar(c);
        }
        w.u8(self.ordered as u8 | (self.archive as u8) << 1 | (self.edges as u8) << 2);
        w.usize(self.words);
        w.usize(self.shards);
        w.usize(self.fp_sections.len());
        for f in &self.fp_sections {
            w.str(&f.name);
            w.uvar(f.count);
            w.u8(f.joined as u8);
        }
        w.usize(self.queue_files.len());
        for n in &self.queue_files {
            w.str(n);
        }
        w.usize(self.streams.len());
        for (name, segs) in &self.streams {
            w.str(name);
            w.usize(segs.len());
            for (f, n) in segs {
                w.str(f);
                w.uvar(*n);
            }
        }
        w.usize(self.files.len());
        for (name, len) in &self.files {
            w.str(name);
            w.uvar(*len);
        }
        w.usize(self.model_files.len());
        for n in &self.model_files {
            w.str(n);
        }
        w.usize(self.snapshots.len());
        for s in &self.snapshots {
            w.bytes(s);
        }
        w.bytes(&self.main);
        w.usize(b.coverage.len());
        for &c in &b.coverage {
            w.uvar(c);
        }
        w.uvar(u64::from(self.pre_level));
        w.into_bytes()
    }

    pub(super) fn decode(b: &[u8]) -> Result<Manifest, String> {
        let mut r = Reader::new(b);
        let e = |e: tlx_value::ser::DecodeError| format!("corrupt manifest: {e}");
        let version = r.uvar().map_err(e)?;
        if version != VERSION {
            return Err(format!("unsupported checkpoint version {version} (this tlx reads version {VERSION})"));
        }
        let number = r.uvar().map_err(e)?;
        let n = r.count(2).map_err(e)?;
        let mut identity = Vec::with_capacity(n);
        for _ in 0..n {
            let k = r.str().map_err(e)?.to_string();
            identity.push((k, r.str().map_err(e)?.to_string()));
        }
        let mut x = [0u64; 8];
        for v in &mut x {
            *v = r.uvar().map_err(e)?;
        }
        let mut outdegree = [0u64; OUTDEGREE_BUCKETS];
        for c in &mut outdegree {
            *c = r.uvar().map_err(e)?;
        }
        let flags = r.u8().map_err(e)?;
        let words = r.usize().map_err(e)?;
        let shards = r.usize().map_err(e)?;
        let n = r.count(3).map_err(e)?;
        let mut fp_sections = Vec::with_capacity(n);
        for _ in 0..n {
            let name = r.str().map_err(e)?.to_string();
            let count = r.uvar().map_err(e)?;
            fp_sections.push(FpSection { name, count, joined: r.u8().map_err(e)? != 0 });
        }
        let n = r.count(1).map_err(e)?;
        let mut queue_files = Vec::with_capacity(n);
        for _ in 0..n {
            queue_files.push(r.str().map_err(e)?.to_string());
        }
        let n = r.count(2).map_err(e)?;
        let mut streams = Vec::with_capacity(n);
        for _ in 0..n {
            let name = r.str().map_err(e)?.to_string();
            let k = r.count(2).map_err(e)?;
            let mut segs = Vec::with_capacity(k);
            for _ in 0..k {
                let f = r.str().map_err(e)?.to_string();
                segs.push((f, r.uvar().map_err(e)?));
            }
            streams.push((name, segs));
        }
        let n = r.count(2).map_err(e)?;
        let mut files = Vec::with_capacity(n);
        for _ in 0..n {
            let name = r.str().map_err(e)?.to_string();
            files.push((name, r.uvar().map_err(e)?));
        }
        let n = r.count(1).map_err(e)?;
        let mut model_files = Vec::with_capacity(n);
        for _ in 0..n {
            model_files.push(r.str().map_err(e)?.to_string());
        }
        let n = r.count(1).map_err(e)?;
        let mut snapshots = Vec::with_capacity(n);
        for _ in 0..n {
            snapshots.push(r.bytes().map_err(e)?.to_vec());
        }
        let main = r.bytes().map_err(e)?.to_vec();
        let n = r.count(1).map_err(e)?;
        let mut coverage = Vec::with_capacity(n);
        for _ in 0..n {
            coverage.push(r.uvar().map_err(e)?);
        }
        let pre_level = r.uvar().map_err(e)?;
        r.finish().map_err(e)?;
        let small = |v: u64| u32::try_from(v).map_err(|_| "corrupt manifest: a count out of range".to_string());
        Ok(Manifest {
            number,
            identity,
            workers: x[0] as usize,
            shards,
            level: small(x[1])?,
            base: BaseCounters {
                init_generated: x[2],
                init_distinct: x[3],
                generated_after_init: x[4],
                depth: small(x[7])?,
                outdegree: OutdegreeHist { counts: outdegree },
                coverage,
            },
            distinct: x[5],
            queued: x[6],
            ordered: flags & 1 != 0,
            archive: flags & 2 != 0,
            edges: flags & 4 != 0,
            pre_level: small(pre_level)?,
            words,
            fp_sections,
            queue_files,
            streams,
            files,
            model_files,
            snapshots,
            main,
        })
    }
}
