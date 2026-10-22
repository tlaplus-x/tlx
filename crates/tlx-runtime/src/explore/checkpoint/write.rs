//! Writing a checkpoint: the workers' parts, the shared files (jobs),
//! the manifest and the commit.

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::Instant;

use tlx_value::ser::Writer;

use super::manifest::{FpSection, Manifest};
use super::{
    chunked, AfterCommit, CkptRun, Event, Job, JobOut, Out, Part, Segments, ABORT_EXIT, CHUNK_BYTES, K_ARCHIVE, K_EDGES, K_FPSET,
    K_MANIFEST, K_MODEL, K_QUEUE, K_TRACE, MANIFEST, TABLE_PARTS_PER_WORKER, TABLE_PART_SLOTS,
};
use crate::explore::history::Shard;
use crate::explore::resume::BaseCounters;
use crate::explore::worker::WorkerState;
use crate::explore::Shared;
use crate::io::durable::DirCommit;
use crate::io::{checkpoint_dirs, Spill};
use crate::model::Model;
use crate::queue::codec::{put_xor, XorPrev};
use crate::queue::{Block, SegCache};
use crate::stats;

/// The last checkpoint a search committed: what the next one may link.
pub(super) struct Prev {
    dir: PathBuf,
    streams: std::collections::HashMap<String, Segments>,
    /// The files of the runs of the seen set.
    runs: std::collections::HashSet<String>,
    /// The bytes of its files the next checkpoint linked.
    linked: AtomicU64,
}

impl Prev {
    /// Link `files` of this checkpoint into directory `to`, adding them
    /// (with their sizes) to `out`; on failure, none (and false).
    fn link<'a>(&self, to: &Path, files: impl Iterator<Item = &'a String> + Clone, out: &mut Vec<(String, u64)>) -> bool {
        let n = out.len();
        let ok = link_files(&self.dir, to, files, out);
        self.linked.fetch_add(out[n..].iter().map(|f| f.1).sum(), Ordering::Relaxed);
        ok
    }
}

impl CkptRun {
    /// The number of the checkpoint being written: on from the one this
    /// search recovered from, if any.
    fn number(&self) -> u64 {
        self.base.load(Ordering::Relaxed) + self.ck.count() + 1
    }

    /// This search recovered from checkpoint `m` in directory `dir`: its
    /// first checkpoint links the recovered segments of the streams rather
    /// than write them again (the trace logs and liveness edges, as they
    /// were; the archive, which the recovery read into worker 0's part, as
    /// the prefix of `archive-0` that its first `archive_blocks` blocks
    /// are, or None if this search does not archive).
    pub(super) fn recovered(&self, dir: &Path, m: &Manifest, archive_blocks: Option<u64>) {
        let mut streams: std::collections::HashMap<String, Segments> = std::collections::HashMap::new();
        let mut archive = Segments::new();
        for w in 0..m.workers {
            if let Some((_, segs)) = m.streams.iter().find(|(n, _)| *n == format!("archive-{w}")) {
                // (Counted in the recovered blocks: all of them on the last.)
                archive.extend(segs.iter().map(|(f, _)| (f.clone(), 0)));
            }
        }
        for (name, segs) in &m.streams {
            if !name.starts_with("archive-") {
                streams.insert(name.clone(), segs.clone());
            }
        }
        if let (Some(k), Some(last)) = (archive_blocks, archive.last_mut()) {
            last.1 = k;
            streams.insert("archive-0".to_string(), archive);
        }
        let runs = std::collections::HashSet::new();
        *self.prev.lock() = Some(Arc::new(Prev { dir: dir.to_path_buf(), streams, runs, linked: AtomicU64::new(0) }));
        self.base.store(m.number, Ordering::Relaxed);
    }
}

/// Link `files` of directory `from` into `to`, adding them (with their
/// sizes) to `out`; on failure, none (and false).
fn link_files<'a>(from: &Path, to: &Path, files: impl Iterator<Item = &'a String> + Clone, out: &mut Vec<(String, u64)>) -> bool {
    let mut done = Vec::new();
    for f in files.clone() {
        let ok = std::fs::hard_link(from.join(f), to.join(f)).is_ok();
        let len = std::fs::metadata(to.join(f)).map(|m| m.len());
        match (ok, len) {
            (true, Ok(len)) => done.push((f.clone(), len)),
            _ => {
                for (f, _) in &done {
                    let _ = std::fs::remove_file(to.join(f));
                }
                let _ = std::fs::remove_file(to.join(f));
                return false;
            }
        }
    }
    out.extend(done);
    true
}

/// Write stream `name`, of `total` values now, to `tmp` for checkpoint
/// `number`: the segments of the previous checkpoint linked if they are
/// still a prefix (it had at most `total` values), then a segment of the
/// values from there on (`write(start, out)`), unless there are none. Its
/// segments; the files are added to `files`.
#[allow(clippy::too_many_arguments)] // the argument set of the hot-path/dispatch signature; a bundling struct would only rename them
fn write_stream(
    prev: Option<&Prev>,
    tmp: &Path,
    number: u64,
    name: &str,
    kind: u32,
    total: u64,
    files: &mut Vec<(String, u64)>,
    write: impl FnOnce(u64, &mut Out) -> Result<(), String>,
) -> Result<Segments, String> {
    let mut segs = Vec::new();
    let mut start = 0;
    if let Some((p, old)) = prev.and_then(|p| Some((p, p.streams.get(name)?))) {
        let n: u64 = old.iter().map(|s| s.1).sum();
        if n <= total && p.link(tmp, old.iter().map(|s| &s.0), files) {
            segs = old.clone();
            start = n;
        }
    }
    if start < total || segs.is_empty() {
        let file = format!("{name}.{number}");
        let mut out = Out::create(tmp, &file, kind)?;
        write(start, &mut out)?;
        files.push(out.close()?);
        segs.push((file, total - start));
    }
    stats::add_count("checkpoint values linked", start);
    Ok(segs)
}

impl<M: Model> Shared<'_, M> {
    /// At a level barrier (by its leader, or the only worker), the next
    /// level installed: whether to take a checkpoint now; if so, its
    /// directory is made and the workers are to write their parts
    /// (`CkptRun::now`).
    pub(in crate::explore) fn checkpoint_due(&self) -> bool {
        let Some(c) = &self.ckpt else { return false };
        if self.control().stopped() || self.frontier.queued() == 0 || !c.ck.due(self.seen.len() as u64) {
            return false;
        }
        let r = c.ck.dir(&self.opts.spill).and_then(|metadir| {
            c.ck.report(&Event::Start(&metadir));
            let dirs = checkpoint_dirs(&metadir);
            dirs.begin().map_err(|e| e.0)?;
            Ok(dirs)
        });
        match r {
            Ok(dirs) => {
                // The shared files, as jobs (the largest first).
                let mut jobs: Vec<Job> = (0..self.seen.run_count()).map(Job::Run).collect();
                let parts = (self.seen.table_slots() / TABLE_PART_SLOTS).clamp(1, TABLE_PARTS_PER_WORKER * self.slots.len());
                jobs.extend((0..parts).map(|part| Job::Table { part, parts }));
                jobs.extend((0..self.frontier.queued_lists()).map(Job::Queue));
                *c.jobs_done.lock() = jobs.iter().map(|_| None).collect();
                *c.jobs.lock() = jobs;
                c.next_job.store(0, Ordering::SeqCst);
                *c.tmp.lock() = Some((dirs, Instant::now()));
                c.now.store(true, Ordering::SeqCst);
                true
            }
            Err(e) => {
                c.ck.report(&Event::Failed(&e));
                // (Not again before the next interval.)
                *c.ck.last.lock() = (Instant::now(), self.seen.len() as u64);
                false
            }
        }
    }

    /// Whether a checkpoint is due (cheap: a solo worker asks after every
    /// narrow level).
    pub(in crate::explore) fn checkpoint_wanted(&self) -> bool {
        self.ckpt.as_ref().is_some_and(|c| c.ck.due(self.seen.len() as u64))
    }

    /// After every worker wrote its part: write the shared parts and the
    /// manifest, and commit (by the barrier leader, or the only worker).
    pub(in crate::explore) fn commit_checkpoint(&self) {
        let Some(c) = &self.ckpt else { return };
        c.now.store(false, Ordering::SeqCst);
        let Some((dirs, t0)) = c.tmp.lock().take() else { return };
        let parts: Vec<Option<Result<Part, String>>> = c.parts.lock().iter_mut().map(Option::take).collect();
        let jobs: Vec<Option<Result<JobOut, String>>> = c.jobs_done.lock().iter_mut().map(Option::take).collect();
        stats::add_secs("checkpoints: the files (in parallel)", t0.elapsed());
        let t1 = Instant::now();
        let r = self.write_shared(c, &dirs, parts, jobs);
        stats::add_secs("checkpoints: the manifest and the commit", t1.elapsed());
        *c.ck.last.lock() = (Instant::now(), self.seen.len() as u64);
        match r {
            Ok(bytes) => {
                let number = c.ck.count.fetch_add(1, Ordering::SeqCst) + 1;
                let time = t0.elapsed();
                stats::add_secs("checkpoints", time);
                stats::add_count("checkpoints taken", 1);
                stats::add_count("checkpoint bytes written", bytes);
                c.ck.report(&Event::Done { number, time, bytes, states: self.seen.len() as u64 });
                match c.ck.cfg.after {
                    // SAFETY: `_exit` ends the process; nothing is relied on after it.
                    AfterCommit::Abort(n) if n == number => unsafe { libc::_exit(ABORT_EXIT) },
                    AfterCommit::Stop(n) if n == number => {
                        c.ck.keep.store(true, Ordering::SeqCst);
                        self.control().stop();
                    }
                    _ => {}
                }
            }
            Err(e) => {
                dirs.abort();
                c.ck.report(&Event::Failed(&e));
            }
        }
    }

    /// Write the model's files and the manifest to `dirs.tmp()` (the
    /// workers wrote the rest: `parts`, `jobs`), then make it the
    /// checkpoint: the bytes written.
    fn write_shared(
        &self,
        c: &CkptRun,
        dirs: &DirCommit,
        parts: Vec<Option<Result<Part, String>>>,
        jobs: Vec<Option<Result<JobOut, String>>>,
    ) -> Result<u64, String> {
        let model = self.model;
        let tmp = dirs.tmp();
        let mut ps = Vec::with_capacity(parts.len());
        for p in parts {
            ps.push(p.ok_or("a worker did not write its part")??);
        }
        let mut files: Vec<(String, u64)> = ps.iter().flat_map(|p| p.files.iter().cloned()).collect();
        let streams: Vec<(String, Segments)> = ps.iter_mut().flat_map(|p| std::mem::take(&mut p.streams)).collect();
        // The seen set (its runs, then the parts of its table) and the queue.
        let mut fp_sections = Vec::new();
        let mut queue_files = Vec::new();
        let (mut queued, mut level) = (0u64, 0u32);
        let kinds = c.jobs.lock().clone();
        for (job, out) in kinds.iter().zip(jobs) {
            let out = out.ok_or("a checkpoint file was not written")??;
            match job {
                Job::Run(_) | Job::Table { .. } => {
                    let joined = matches!(job, Job::Table { part, .. } if *part > 0);
                    fp_sections.push(FpSection { name: out.file.0.clone(), count: out.count, joined });
                }
                Job::Queue(_) => {
                    queue_files.push(out.file.0.clone());
                    queued += out.count;
                    level = level.max(out.level);
                }
            }
            files.push(out.file);
        }
        // The model's files.
        let mut names = Vec::new();
        for (name, data) in model.caps().checkpoint_files()? {
            let mut out = Out::create(tmp, &format!("model-{name}"), K_MODEL)?;
            out.chunk(&data)?;
            files.push(out.close()?);
            names.push(name);
        }
        // The counters.
        let extra = model.extra_generated() - c.extra_at_start;
        let generated = self.worker_generated() + extra;
        let mut outdegree = self.base_outdegree.clone();
        for p in &ps {
            outdegree.merge(&p.outdegree);
        }
        let archive = self.retention.on && !self.retention.off() && ps.iter().all(|p| p.archived);
        let edges = ps.iter().all(|p| p.edges);
        let base = BaseCounters {
            init_generated: self.init_generated.load(Ordering::Relaxed),
            init_distinct: self.init_distinct.load(Ordering::Relaxed),
            generated_after_init: generated,
            depth: self.depth() as u32,
            outdegree,
            coverage: self.coverage_counts(),
        };
        let m = Manifest {
            number: c.number(),
            identity: c.ck.cfg.identity.clone(),
            workers: ps.len(),
            shards: self.history.lock().len(),
            level,
            base,
            distinct: self.seen.len() as u64,
            queued,
            ordered: self.order.is_some(),
            archive,
            edges,
            words: model.caps().codec().map_or(0, |c| c.words()),
            fp_sections,
            queue_files,
            streams,
            files,
            model_files: names,
            snapshots: ps.into_iter().map(|p| p.snapshot).collect(),
            main: model.caps().main_snapshot()?,
        };
        // (The bytes written: not those linked.)
        let linked = c.prev.lock().as_ref().map_or(0, |p| p.linked.load(Ordering::Relaxed));
        stats::add_count("checkpoint bytes linked", linked);
        let bytes = m.files.iter().map(|(_, n)| n).sum::<u64>() - linked;
        let runs = m.fp_sections.iter().filter(|f| f.name.starts_with("fpset-run-")).map(|f| f.name.clone()).collect();
        let streams = m.streams.iter().cloned().collect();
        let mut out = Out::create(tmp, MANIFEST, K_MANIFEST)?;
        out.chunk(&m.encode())?;
        out.close()?;
        // Commit: the new checkpoint replaces the old one (not while a
        // signal cleans the metadir up).
        dirs.commit().map_err(|e| e.0)?;
        *c.prev.lock() = Some(Arc::new(Prev { dir: dirs.cur().to_path_buf(), streams, runs, linked: AtomicU64::new(0) }));
        Ok(bytes)
    }

    /// Take the shared files of the checkpoint being written (`Job`) until
    /// none is left (each worker, after writing its part).
    pub(in crate::explore) fn checkpoint_jobs(&self, tmp: &Path) {
        let Some(c) = &self.ckpt else { return };
        loop {
            let i = c.next_job.fetch_add(1, Ordering::SeqCst);
            let Some(job) = c.jobs.lock().get(i).copied() else { return };
            let r = self.write_job(job, tmp);
            c.jobs_done.lock()[i] = Some(r);
        }
    }

    fn write_job(&self, job: Job, tmp: &Path) -> Result<JobOut, String> {
        match job {
            Job::Run(k) => {
                let name = format!("fpset-run-{}", self.seen.run_id(k));
                let prev = self.ckpt.as_ref().and_then(|c| c.prev.lock().clone());
                if let Some(p) = prev.filter(|p| p.runs.contains(&name)) {
                    let mut linked = Vec::new();
                    if p.link(tmp, std::iter::once(&name), &mut linked) {
                        let count = self.seen.run_len(k);
                        stats::add_count("checkpoint values linked", count);
                        return Ok(JobOut { file: linked.pop().expect("linked"), count, level: 0 });
                    }
                }
                let (file, count) = write_fps(tmp, &name, |f| self.seen.for_each_in_run(k, f))?;
                Ok(JobOut { file, count, level: 0 })
            }
            Job::Table { part, parts } => {
                // SAFETY: no worker inserts (they are at the level barrier,
                // writing the checkpoint); each part is taken once.
                let (file, count) =
                    write_fps(tmp, &format!("fpset-{part}"), |f| unsafe { self.seen.for_each_in_table_part(part, parts, f) })?;
                Ok(JobOut { file, count, level: 0 })
            }
            Job::Queue(l) => self.write_queue(l, tmp),
        }
    }

    /// Write the queued states of list `l` of the current level to
    /// `tmp/queue-<l>`.
    fn write_queue(&self, l: usize, tmp: &Path) -> Result<JobOut, String> {
        let model = self.model;
        let codec = model.caps().codec();
        let persist = model.caps().persist();
        if codec.is_none() && persist.is_none() {
            return Err("the model's states cannot be written".into());
        }
        let positions = self.order.as_ref().map(|o| o.current());
        let words = codec.map_or(0, |c| c.words());
        let mut out = Out::create(tmp, &format!("queue-{l}"), K_QUEUE)?;
        let mut q = QueueChunk::new(codec.is_some(), positions.is_some(), words);
        let (mut n, mut level) = (0u64, 0u32);
        let mut cache = SegCache::default();
        let mut prev = XorPrev::new(words);
        let mut enc = vec![0u64; words];
        let mut bytes = Vec::new();
        self.frontier.for_each_queued_in(l, |b: &Block<M::State>| -> Result<(), String> {
            level = b.depth();
            let pos = |log: u64| positions.as_ref().map_or(0, |p| p.pos(log));
            match b {
                Block::Objects { tasks, .. } => {
                    for t in tasks {
                        match codec {
                            Some(cd) => {
                                let fp = cd.encode(&t.state, &mut enc);
                                q.words(t.log, fp, &enc, pos(t.log));
                            }
                            None => {
                                bytes.clear();
                                persist.expect("persist").write_state(&t.state, &mut bytes)?;
                                q.bytes(t.log, model.fingerprint(&t.state), &bytes, pos(t.log));
                            }
                        }
                        n += 1;
                        q.flush_if_full(&mut out)?;
                    }
                }
                Block::Encoded { .. } => {
                    let r = b.records(&mut cache, &mut prev, |log, fp, w| -> Result<(), String> {
                        q.words(log, fp, w, pos(log));
                        n += 1;
                        q.flush_if_full(&mut out)
                    });
                    r.map_err(|e| e.0)??;
                }
            }
            Ok(())
        })?;
        q.flush(&mut out)?;
        Ok(JobOut { file: out.close()?, count: n, level })
    }
}

/// Write the fingerprints `each` calls its argument with (ascending) to
/// `tmp/name`: the file (name, size) and their number.
fn write_fps(
    tmp: &Path,
    name: &str,
    each: impl FnOnce(&mut dyn FnMut(u64) -> Result<(), String>) -> Result<(), String>,
) -> Result<((String, u64), u64), String> {
    let mut out = Out::create(tmp, name, K_FPSET)?;
    let mut buf: Vec<u64> = Vec::with_capacity(CHUNK_BYTES / 8);
    let mut n = 0u64;
    each(&mut |fp| {
        buf.push(fp);
        n += 1;
        if buf.len() == buf.capacity() {
            out.chunk(crate::io::as_bytes(&buf))?;
            buf.clear();
        }
        Ok(())
    })?;
    if !buf.is_empty() {
        out.chunk(crate::io::as_bytes(&buf))?;
    }
    Ok((out.close()?, n))
}

/// A chunk of the queue file being built: `u8 words?`, `u8 positions?`,
/// `uvar n`, the records (XOR-coded words: trace-log entry, fingerprint,
/// words; or: uvar entry, 8-byte fingerprint, the state's bytes), then the
/// positions (uvar each) if any.
struct QueueChunk {
    words: bool,
    positions: bool,
    n: u64,
    recs: Vec<u8>,
    pos: Writer,
    prev: XorPrev,
}

impl QueueChunk {
    fn new(words: bool, positions: bool, w: usize) -> QueueChunk {
        QueueChunk { words, positions, n: 0, recs: Vec::new(), pos: Writer::new(), prev: XorPrev::new(w) }
    }

    fn words(&mut self, log: u64, fp: u64, w: &[u64], pos: u64) {
        put_xor(&mut self.recs, &mut self.prev, log, fp, w);
        self.add(pos);
    }

    fn bytes(&mut self, log: u64, fp: u64, b: &[u8], pos: u64) {
        let mut w = Writer::new();
        w.uvar(log);
        w.bytes(b);
        self.recs.extend_from_slice(&fp.to_le_bytes());
        self.recs.extend_from_slice(w.as_bytes());
        self.add(pos);
    }

    fn add(&mut self, pos: u64) {
        self.n += 1;
        if self.positions {
            self.pos.uvar(pos);
        }
    }

    fn flush_if_full(&mut self, out: &mut Out) -> Result<(), String> {
        if self.recs.len() >= CHUNK_BYTES {
            self.flush(out)?;
        }
        Ok(())
    }

    fn flush(&mut self, out: &mut Out) -> Result<(), String> {
        if self.n == 0 {
            return Ok(());
        }
        let mut w = Writer::with_capacity(self.recs.len() + self.pos.len() + 16);
        w.u8(self.words as u8);
        w.u8(self.positions as u8);
        w.uvar(self.n);
        let mut b = w.into_bytes();
        b.extend_from_slice(&self.recs);
        b.extend_from_slice(self.pos.as_bytes());
        out.chunk(&b)?;
        self.n = 0;
        self.recs.clear();
        self.pos.clear();
        self.prev.reset();
        Ok(())
    }
}

impl<M: Model> WorkerState<'_, '_, M> {
    pub(in crate::explore) fn publish_history(&mut self) {
        self.shared.history.lock().put(std::mem::take(&mut self.shard));
    }

    pub(in crate::explore) fn lease_history(&mut self) {
        self.shard = self.shared.history.lock().take(self.me);
    }

    /// At a checkpoint: write this worker's assigned history shards and
    /// its part of the archive, then record the files and counters.
    pub(in crate::explore) fn checkpoint_part(&mut self) {
        let Some(c) = &self.shared.ckpt else { return };
        let Some(tmp) = c.tmp.lock().as_ref().map(|(d, _)| d.tmp().to_path_buf()) else { return };
        let r = self.write_part(&tmp);
        c.parts.lock()[self.me] = Some(r);
        self.shared.checkpoint_jobs(&tmp);
    }

    fn write_part(&mut self, tmp: &Path) -> Result<Part, String> {
        let shared = self.shared;
        let spill = &shared.opts.spill;
        let me = self.me;
        let c = shared.ckpt.as_ref().expect("checkpointing");
        let prev = c.prev.lock().clone();
        let prev = prev.as_deref();
        let number = c.number();
        let mut files = Vec::new();
        let mut streams = Vec::new();
        let history = shared.history.lock().snapshot();
        let mut edges = true;
        for entry in history.iter().skip(me).step_by(shared.slots.len()) {
            let shard = entry.lock();
            let shard = shard.as_ref().expect("history published before checkpoint writing");
            let mut out = HistoryWriter { prev, tmp, number, spill, files: &mut files, streams: &mut streams };
            out.write(shard)?;
            edges &= shard.edges.is_some();
        }
        let words = shared.model.caps().codec().map_or(0, |c| c.words());
        let archived = match self.local.archived() {
            Some(blocks) if blocks.iter().all(|b| b.encoded()) => {
                let name = format!("archive-{me}");
                let segs = write_stream(prev, tmp, number, &name, K_ARCHIVE, blocks.len() as u64, &mut files, |start, out| {
                    write_archive(&blocks[start as usize..], words, out)
                })?;
                streams.push((name, segs));
                true
            }
            _ => false,
        };
        let snapshot = shared.model.caps().worker_snapshot()?;
        Ok(Part { outdegree: self.outdegree.clone(), snapshot, archived, edges, files, streams })
    }
}

/// Write the records of the archived `blocks` (encoded, of `words` words):
/// chunks of (uvar depth, uvar n, uvar length, the XOR-coded records).
fn write_archive<S>(blocks: &[Block<S>], words: usize, out: &mut Out) -> Result<(), String> {
    let mut cache = SegCache::default();
    let mut prev = XorPrev::new(words);
    let mut enc = XorPrev::new(words);
    let mut chunk = Writer::new();
    let mut recs = Vec::new();
    for b in blocks {
        recs.clear();
        enc.reset();
        b.records(&mut cache, &mut prev, |log, fp, w| -> Result<(), String> {
            put_xor(&mut recs, &mut enc, log, fp, w);
            Ok(())
        })
        .map_err(|e| e.0)??;
        chunk.uvar(b.depth() as u64);
        chunk.uvar(b.len() as u64);
        chunk.bytes(&recs);
        if chunk.len() >= CHUNK_BYTES {
            out.chunk(chunk.as_bytes())?;
            chunk.clear();
        }
    }
    if !chunk.is_empty() {
        out.chunk(chunk.as_bytes())?;
    }
    Ok(())
}

/// Serialization of one stable history shard, regardless of its current
/// worker assignment. All shards have been published at the level barrier.
struct HistoryWriter<'a> {
    prev: Option<&'a Prev>,
    tmp: &'a Path,
    number: u64,
    spill: &'a Spill,
    files: &'a mut Vec<(String, u64)>,
    streams: &'a mut Vec<(String, Segments)>,
}

impl HistoryWriter<'_> {
    fn write<S>(&mut self, shard: &Shard<'_, S>) -> Result<(), String> {
        let Self { prev, tmp, number, spill, files, streams } = self;
        let (prev, tmp, number, spill) = (*prev, *tmp, *number, *spill);
        let id = shard.id;
        let name = format!("trace-{id}");
        let log = &shard.log;
        let segs = write_stream(prev, tmp, number, &name, K_TRACE, log.len() as u64, files, |start, out| {
            log.for_each_chunk(spill, start as usize, CHUNK_BYTES / 16, |c| out.chunk(crate::io::as_bytes(c)))
        })?;
        streams.push((name, segs));
        if let Some(e) = &shard.edges {
            let mut out = Out::create(tmp, &format!("edges-{id}"), K_EDGES)?;
            out.chunk(&e.header())?;
            files.push(out.close()?);
            let (fps, meta) = e.columns();
            let name = format!("edges-{id}-fps");
            let segs = write_stream(prev, tmp, number, &name, K_EDGES, fps.len() as u64, files, |start, out| {
                chunked(fps, spill, start as usize, CHUNK_BYTES / 8, |c| out.chunk(crate::io::as_bytes(c)))
            })?;
            streams.push((name, segs));
            let name = format!("edges-{id}-meta");
            let segs = write_stream(prev, tmp, number, &name, K_EDGES, meta.len() as u64, files, |start, out| {
                chunked(meta, spill, start as usize, CHUNK_BYTES / 4, |c| out.chunk(crate::io::as_bytes(c)))
            })?;
            streams.push((name, segs));
        }
        Ok(())
    }
}
