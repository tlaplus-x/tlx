//! Recovering a search from a checkpoint (`-recover`).

use std::fs::File;
use std::io::BufReader;
use std::path::{Path, PathBuf};
use std::sync::atomic::Ordering;
use std::sync::Arc;

use tlx_base::frame::FrameReader;
use tlx_value::ser::Reader;

use super::manifest::Manifest;
use super::{K_ARCHIVE, K_EDGES, K_FPSET, K_MANIFEST, K_MODEL, K_QUEUE, K_TRACE, MANIFEST};
use crate::explore::edges::{AtomBits, EdgeRec};
use crate::explore::frontier::{Local, Task};
use crate::explore::order::Positions;
use crate::explore::resume::BaseCounters;
use crate::explore::tracelog::{TraceLog, NO_PARENT};
use crate::explore::{fp_set_full, InitResult, Outcome, Shared, Stats};
use crate::io::checkpoint_dirs;
use crate::model::Model;
use crate::queue::codec::{get_xor, XorPrev};

/// A checkpoint to recover from (`-recover DIR`): its manifest and the
/// model's files, read and checked when opened; the rest is read when the
/// search starts from it (`explore_from` with `Start::Recover`).
pub struct Recovery {
    /// The checkpoint's directory, and the metadir it is in.
    dir: PathBuf,
    metadir: PathBuf,
    m: Manifest,
    model_files: Vec<(String, Vec<u8>)>,
}

impl std::fmt::Debug for Recovery {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Recovery").field("dir", &self.dir).field("number", &self.m.number).finish_non_exhaustive()
    }
}

/// Read the chunks of a framed file of `kind`.
struct In {
    path: PathBuf,
    r: FrameReader<BufReader<File>>,
}

impl In {
    fn open(path: PathBuf, kind: u32) -> Result<In, String> {
        let f = File::open(&path).map_err(|e| format!("cannot open {}: {e}", path.display()))?;
        let r = FrameReader::open(BufReader::with_capacity(1 << 20, f), kind).map_err(|e| format!("{}: {e}", path.display()))?;
        Ok(In { path, r })
    }

    fn chunk(&mut self) -> Result<Option<Vec<u8>>, String> {
        self.r.chunk().map_err(|e| format!("{}: {e}", self.path.display()))
    }
}

impl Recovery {
    /// The checkpoint of metadir `dir` (or `dir` itself, a checkpoint's
    /// directory): its manifest checked (format, tlx build, the files and
    /// their sizes) and the model's files read.
    pub fn open(dir: &Path) -> Result<Recovery, String> {
        let dirs = checkpoint_dirs(dir);
        let cdir = [dirs.cur().to_path_buf(), dir.to_path_buf(), dirs.old().to_path_buf()]
            .into_iter()
            .find(|d| d.join(MANIFEST).is_file())
            .ok_or_else(|| format!("no checkpoint in {}", dir.display()))?;
        let metadir = cdir.parent().map_or_else(|| PathBuf::from("."), Path::to_path_buf);
        let mut f = In::open(cdir.join(MANIFEST), K_MANIFEST)?;
        let m = f.chunk()?.ok_or_else(|| format!("{}: empty", f.path.display()))?;
        let m = Manifest::decode(&m)?;
        if f.chunk()?.is_some() {
            return Err(format!("{}: unexpected data", f.path.display()));
        }
        for (name, len) in &m.files {
            let p = cdir.join(name);
            match std::fs::metadata(&p) {
                Ok(md) if md.len() == *len => {}
                Ok(md) => return Err(format!("{}: {} bytes, the manifest says {len} (corrupt checkpoint)", p.display(), md.len())),
                Err(e) => return Err(format!("{}: {e} (incomplete checkpoint)", p.display())),
            }
        }
        let mut model_files = Vec::new();
        for name in &m.model_files {
            let mut f = In::open(cdir.join(format!("model-{name}")), K_MODEL)?;
            let data = f.chunk()?.unwrap_or_default();
            model_files.push((name.clone(), data));
        }
        Ok(Recovery { dir: cdir, metadir, m, model_files })
    }

    /// The identity of the checkpointed run (`CheckpointConfig::identity`).
    pub fn identity(&self) -> &[(String, String)] {
        &self.m.identity
    }

    /// The model's file `name` (`Checkpointed::files`).
    pub fn file(&self, name: &str) -> Option<&[u8]> {
        self.model_files.iter().find(|(n, _)| n == name).map(|(_, d)| &d[..])
    }

    /// The metadir the checkpoint is in (the recovered run's metadir).
    pub fn metadir(&self) -> &Path {
        &self.metadir
    }

    /// The checkpoint's directory.
    pub fn dir(&self) -> &Path {
        &self.dir
    }

    /// The distinct states found and the states queued at the checkpoint.
    pub fn distinct(&self) -> u64 {
        self.m.distinct
    }

    pub fn queued(&self) -> u64 {
        self.m.queued
    }

    /// The workers of the checkpointed search.
    pub fn workers(&self) -> usize {
        self.m.workers
    }

    /// What the recovered search starts from: the counters of the
    /// checkpointed search.
    pub(in crate::explore) fn base(&self) -> &BaseCounters {
        &self.m.base
    }

    fn input(&self, name: &str, kind: u32) -> Result<In, String> {
        In::open(self.dir.join(name), kind)
    }

    /// The chunks of stream `name` (of files of `kind`), its segments in
    /// order; None if the checkpoint does not have it.
    fn stream(&self, name: &str, kind: u32) -> Option<StreamIn<'_>> {
        let (_, segs) = self.m.streams.iter().find(|(n, _)| n == name)?;
        Some(StreamIn { rec: self, segs, at: 0, f: None, kind })
    }
}

/// Reading a stream (`Recovery::stream`).
struct StreamIn<'a> {
    rec: &'a Recovery,
    segs: &'a [(String, u64)],
    at: usize,
    f: Option<In>,
    kind: u32,
}

impl StreamIn<'_> {
    fn chunk(&mut self) -> Result<Option<Vec<u8>>, String> {
        loop {
            if self.f.is_none() {
                let Some((name, _)) = self.segs.get(self.at) else { return Ok(None) };
                self.f = Some(self.rec.input(name, self.kind)?);
            }
            match self.f.as_mut().expect("open").chunk()? {
                Some(c) => return Ok(Some(c)),
                None => {
                    self.f = None;
                    self.at += 1;
                }
            }
        }
    }
}

/// Recover from checkpoint `rec`: the seen set, the history shards, the
/// archive (into `seed`'s part, if the search archives), the queued states (to `seed`: the first level of the
/// search, in BFS order), the liveness edges (in the same history directory), the
/// workers' snapshots. An error reading the checkpoint fails the search
/// (`Outcome::Io`).
pub(in crate::explore) fn recover_phase<'m, M: Model>(
    shared: &Shared<'m, M>,
    seed: &mut Local<'_, 'm, M::State>,
    stats: &mut Stats,
    rec: &Recovery,
) -> InitResult {
    rec.m.base.restore_init(shared, stats);
    match recover(shared, seed, rec) {
        Ok(Ok(())) => Ok((Vec::new(), None)),
        Ok(Err(full)) => Ok((Vec::new(), Some(full))),
        Err(e) => {
            // (The checkpoint stays, as it is.)
            if let Some(c) = &shared.ckpt {
                c.ck.keep.store(true, Ordering::SeqCst);
            }
            Ok((Vec::new(), Some((Outcome::Io(format!("cannot recover from {}: {e}", rec.dir.display())), NO_PARENT))))
        }
    }
}

/// Populate the search-owned history directory; Ok(Err): the seen set is full.
fn recover<'m, M: Model>(
    shared: &Shared<'m, M>,
    seed: &mut Local<'_, 'm, M::State>,
    rec: &Recovery,
) -> Result<Result<(), crate::explore::Failure>, String> {
    let model = shared.model;
    let m = &rec.m;
    let words = model.caps().codec().map_or(0, |c| c.words());
    if words != m.words || (words == 0 && model.caps().persist().is_none()) {
        return Err(format!("its states have {} words, this model's {words}", m.words));
    }
    // The seen set: into the table, made large enough beforehand (the
    // sections are ascending, see `FpSet::reserve`); if it cannot be
    // (within the memory budget), every section becomes a run on disk, and
    // the search starts with an empty table (as after a rotation).
    let seen = &shared.seen;
    let total: u64 = m.fp_sections.iter().map(|f| f.count).sum();
    if total != m.distinct {
        return Err(format!("the fingerprint files hold {total} fingerprints, the manifest says {}", m.distinct));
    }
    // (Within the memory budget: half of it for the table.)
    let max_slots = if shared.budget.limited() { shared.budget.total() / 16 } else { usize::MAX };
    // SAFETY (here and below): the workers have not started.
    let in_table = unsafe { seen.reserve(total as usize, max_slots) } || !seen.takes_runs();
    if in_table && total as usize > seen.max_entries() + seen.len() {
        // (They cannot fit: the set is full, as the search would find it.)
        return Ok(Err(fp_set_full(seen)));
    }
    // (Joined sections are read as one: one run on disk.)
    let mut i = 0;
    while i < m.fp_sections.len() {
        let j = i + 1 + m.fp_sections[i + 1..].iter().take_while(|f| f.joined).count();
        let group = &m.fp_sections[i..j];
        i = j;
        let mut at = 0;
        let mut f: Option<In> = None;
        // The fingerprints of the group, chunk by chunk.
        let mut chunks = || -> Result<Option<Vec<u64>>, String> {
            loop {
                if f.is_none() {
                    let Some(sec) = group.get(at) else { return Ok(None) };
                    f = Some(rec.input(&sec.name, K_FPSET)?);
                }
                let Some(c) = f.as_mut().expect("open").chunk()? else {
                    f = None;
                    at += 1;
                    continue;
                };
                if c.len() % 8 != 0 {
                    return Err(format!("corrupt {}", group[at].name));
                }
                let mut fps = vec![0u64; c.len() / 8];
                crate::io::as_bytes_mut(&mut fps).copy_from_slice(&c);
                return Ok(Some(fps));
            }
        };
        let n: u64 = group.iter().map(|f| f.count).sum();
        let name = &group[0].name;
        if !in_table && seen.takes_runs() {
            // SAFETY: the workers have not started (see above).
            unsafe { seen.add_run(n as usize, &mut chunks) }.map_err(|e| format!("{name}: {e}"))?;
            continue;
        }
        let mut k = 0u64;
        while let Some(fps) = chunks()? {
            for fp in fps {
                match shared.insert_exclusive(fp) {
                    Ok(true) => k += 1,
                    Ok(false) => return Err(format!("corrupt {name} (a fingerprint occurs twice)")),
                    Err(_) => return Ok(Err(fp_set_full(seen))),
                }
            }
        }
        if k != n {
            return Err(format!("{name} holds {k} fingerprints, the manifest says {n}"));
        }
    }
    // The complete history directory, independent of the worker count.
    for w in 0..m.shards {
        let mut log = TraceLog::new(shared.opts.queue.seg_bytes);
        let mut f = rec.stream(&format!("trace-{w}"), K_TRACE).ok_or_else(|| format!("no trace log of shard {w}"))?;
        while let Some(c) = f.chunk()? {
            if c.len() % 16 != 0 {
                return Err(format!("corrupt trace-{w}"));
            }
            let mut es = vec![[0u64; 2]; c.len() / 16];
            crate::io::as_bytes_mut(&mut es).copy_from_slice(&c);
            for [p, fp] in es {
                log.push(p, fp);
            }
        }
        let edges = if let Some(atoms) = model.caps().live_atoms.filter(|_| m.edges) {
            let mut f = rec.input(&format!("edges-{w}"), K_EDGES)?;
            let head = f.chunk()?.ok_or_else(|| format!("edges-{w}: no header"))?;
            let missing = || format!("no liveness edges of shard {w}");
            let mut fps = rec.stream(&format!("edges-{w}-fps"), K_EDGES).ok_or_else(missing)?;
            let mut meta = rec.stream(&format!("edges-{w}-meta"), K_EDGES).ok_or_else(missing)?;
            Some(EdgeRec::read_from(
                atoms as &(dyn AtomBits<M::State> + Sync),
                shared.opts.queue.seg_bytes,
                &head,
                &mut || fps.chunk(),
                &mut || meta.chunk(),
            )?)
        } else {
            None
        };
        shared.history.lock().push(log, edges);
    }
    // The archive (if this search archives: else it cannot resume).
    if seed.archiving() {
        if m.archive {
            for w in 0..m.workers {
                read_archive(rec, w, words, seed, model.caps().codec(), &|| shared.relieve())?;
            }
        } else {
            shared.retention.drop_archive();
        }
    }
    // The queued states.
    read_queue(shared, seed, rec)?;
    model.caps().restore_workers(&m.main, &m.snapshots)?;
    Ok(Ok(()))
}

/// Read worker `w`'s part of the archive into `seed`'s, applying the
/// memory budget (`relieve`) as it grows (its segments may have to go to
/// disk, as in the checkpointed search).
fn read_archive<S>(
    rec: &Recovery,
    w: usize,
    words: usize,
    seed: &mut Local<'_, '_, S>,
    codec: Option<&dyn crate::StateCodec<S>>,
    relieve: &dyn Fn(),
) -> Result<(), String> {
    let Some(mut f) = rec.stream(&format!("archive-{w}"), K_ARCHIVE) else { return Ok(()) };
    let mut prev = XorPrev::new(words);
    let bad = || format!("corrupt archive-{w}");
    while let Some(c) = f.chunk()? {
        relieve();
        let mut r = Reader::new(&c);
        while !r.is_empty() {
            let depth = u32::try_from(r.uvar().map_err(|_| bad())?).map_err(|_| bad())?;
            let n = r.uvar().map_err(|_| bad())?;
            let b = r.bytes().map_err(|_| bad())?;
            prev.reset();
            let mut pos = 0;
            for _ in 0..n {
                if pos >= b.len() {
                    return Err(bad());
                }
                let fp = get_xor(b, &mut pos, &mut prev);
                codec.ok_or_else(&bad)?.validate(&prev.words).map_err(|e| format!("{}: {e}", bad()))?;
                seed.archive_words(prev.log, fp, depth, &prev.words);
            }
            seed.spill();
        }
    }
    Ok(())
}

/// A queued state read from a checkpoint: encoded (queued as it is) or
/// an object.
enum Queued<S> {
    Words { log: u64, fp: u64, words: Vec<u64> },
    Task(Task<S>),
}

impl<S> Queued<S> {
    /// Its trace-log entry.
    fn log(&self) -> u64 {
        match self {
            Queued::Words { log, .. } => *log,
            Queued::Task(t) => t.log,
        }
    }

    /// Queue it in `seed`'s next level, at depth `level`.
    fn push(self, seed: &mut Local<'_, '_, S>, level: u32) {
        match self {
            Queued::Words { log, fp, words } => seed.push_words(log, fp, level, &words),
            Queued::Task(t) => seed.push_new(t),
        }
    }
}

/// Read the queued states into `seed` (in BFS order: by position if the
/// checkpoint has them), and start choosing representatives from there.
/// Encoded states are queued encoded (the compressed blocks of the queue),
/// not decoded.
///
/// With one worker the order of expansion is BFS order, so states with
/// positions are sorted before they are queued: a whole level held at
/// once. With several (`shared.order`), a state's place in BFS order is
/// looked up by its trace-log entry (`Positions::pos`), not by its place
/// in the queue: each is queued as it is read, and only its entry and
/// position are kept, so the level stays compressed and within the memory
/// budget as it grows (`relieve`, as for the archive).
fn read_queue<M: Model>(shared: &Shared<'_, M>, seed: &mut Local<'_, '_, M::State>, rec: &Recovery) -> Result<(), String> {
    let model = shared.model;
    let m = &rec.m;
    let level = m.level;
    let bad = |what: &str| format!("corrupt queue ({what})");
    let mut prev = XorPrev::new(m.words);
    // (With positions and one worker: the states, sorted before they are queued.)
    let mut sorted: Vec<(u64, Queued<M::State>)> = Vec::new();
    // The trace-log entries of the states queued and their positions in BFS
    // order (choosing representatives): by the order read, else as recorded.
    let mut places: Vec<(u64, u64)> = Vec::new();
    let ordered = shared.order.is_some();
    let mut n = 0u64;
    for name in &m.queue_files {
        let mut f = rec.input(name, K_QUEUE)?;
        while let Some(c) = f.chunk()? {
            shared.relieve();
            let mut r = Reader::new(&c);
            let e = |e: tlx_value::ser::DecodeError| bad(&e.to_string());
            let words = r.u8().map_err(e)? != 0;
            let positions = r.u8().map_err(e)? != 0;
            let k = r.uvar().map_err(e)?;
            if words && model.caps().codec().is_none() {
                return Err(bad("encoded states"));
            }
            let mut items = Vec::with_capacity(k.min(1 << 16) as usize);
            let mut at = r.pos();
            prev.reset();
            for _ in 0..k {
                if at >= c.len() {
                    return Err(bad("short chunk"));
                }
                items.push(if words {
                    let fp = get_xor(&c, &mut at, &mut prev);
                    model.caps().codec().expect("checked above").validate(&prev.words).map_err(|e| bad(&e))?;
                    Queued::Words { log: prev.log, fp, words: prev.words.clone() }
                } else {
                    let p = model.caps().persist().ok_or_else(|| bad("states as bytes"))?;
                    let fp = u64::from_le_bytes(c.get(at..at + 8).ok_or_else(|| bad("short chunk"))?.try_into().expect("8 bytes"));
                    let mut r = Reader::new(&c[at + 8..]);
                    let log = r.uvar().map_err(e)?;
                    let state = p.read_state(r.bytes().map_err(e)?, level, fp)?;
                    at += 8 + r.pos();
                    Queued::Task(Task { state, log, depth: level })
                });
            }
            let mut r = Reader::new(&c[at..]);
            for q in items {
                let pos = if positions { r.uvar().map_err(e)? } else { n };
                n += 1;
                if positions && !ordered {
                    sorted.push((pos, q));
                    continue;
                }
                if ordered {
                    places.push((q.log(), pos));
                }
                q.push(seed, level);
            }
            r.finish().map_err(e)?;
            seed.spill();
        }
    }
    if n != m.queued {
        return Err(format!("the queue holds {n} states, the manifest says {}", m.queued));
    }
    sorted.sort_by_key(|(p, _)| *p);
    for (_, q) in sorted {
        q.push(seed, level);
    }
    if let Some(o) = &shared.order {
        // Each position of the level once.
        let mut taken = vec![false; places.len()];
        for &(_, p) in &places {
            let slot = usize::try_from(p).ok().and_then(|p| taken.get_mut(p)).ok_or_else(|| bad("a position past the level"))?;
            if std::mem::replace(slot, true) {
                return Err(bad("a position twice"));
            }
        }
        drop(taken);
        o.start(Arc::new(Positions::of_places(&places)));
    }
    Ok(())
}
