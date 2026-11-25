//! Checkpoints and recovery (docs/scale.md §9.2): a search stopped
//! right after a checkpoint (`AfterCommit::Stop`, as if killed) and
//! recovered from it gives the results of an uninterrupted search: the
//! same outcome, counts, depth and shortest traces (with one worker before
//! and after, the same trace and the same order of expansion), also with
//! other numbers of workers, encoded or serialized states, the liveness
//! behavior graph, representatives chosen in BFS order (coarse
//! fingerprints), and the disk tier. A damaged checkpoint is refused.

use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use tlx_testkit::report::{project, ComparisonPolicy, Counts, Projection, TracePolicy};

use tlx_runtime::io::{Spill, SpillConfig, SpillMode};
use tlx_runtime::{
    explore, explore_from, live, AfterCommit, AtomBits, Caps, CheckpointConfig, Checkpointed, Checkpointer, FpConfig, Model, ModelError,
    Options, Outcome, Persist, Recovery, Report, Start, StateCodec, StateFormat,
};

/// Levels of varying widths with shortcuts (as `tests/queue.rs`); states
/// `(level, index)`.
struct Layers {
    layers: u32,
    bad: Option<(u32, u32)>,
    /// Optional layer that raises a `ModelError` during expansion (simulating
    /// a layout miss to verify that `ResumePoint` keeps the archive intact).
    error_level: Option<u32>,
    /// States are encoded (else serialized with `Persist`).
    coded: bool,
    /// Exercise a codec's rejection of externally restored word handles.
    reject_words: bool,
    /// Record the liveness behavior graph.
    live: bool,
    /// The fingerprint is of the class `(level, index / 2)` (as a VIEW).
    coarse: bool,
    inv: Vec<String>,
    acts: Vec<String>,
    /// The order of expansion.
    log: Mutex<Vec<(u32, u32)>>,
    /// The worker snapshots given back when recovering.
    restored: Mutex<Vec<Vec<u8>>>,
}

const WORDS: usize = 2;

impl Layers {
    fn new(layers: u32, bad: Option<(u32, u32)>, coded: bool) -> Layers {
        Layers {
            layers,
            bad,
            error_level: None,
            coded,
            reject_words: false,
            live: false,
            coarse: false,
            inv: vec!["NotBad".into()],
            acts: vec!["Step".into(), "Jump".into()],
            log: Mutex::new(Vec::new()),
            restored: Mutex::new(Vec::new()),
        }
    }

    fn width(l: u32) -> u32 {
        match l % 30 {
            8..=11 => 400 + 37 * (l % 5),
            20 => 150,
            _ if l.is_multiple_of(7) => 3,
            _ => 2,
        }
    }
}

impl Model for Layers {
    type State = (u32, u32);
    tlx_runtime::model_without_checks!(but coarse_fingerprint);
    fn init_states(&self, out: &mut dyn FnMut((u32, u32))) -> Result<(), ModelError> {
        out((0, 0));
        out((0, 1));
        Ok(())
    }
    fn successors(&self, s: &(u32, u32), out: &mut dyn FnMut((u32, u32), u32) -> bool) -> Result<(), ModelError> {
        self.log.lock().unwrap().push(*s);
        if Some(s.0) == self.error_level {
            return Err(ModelError::new("simulated layout miss"));
        }
        let (l, i) = *s;
        if l + 1 >= self.layers {
            return Ok(());
        }
        let (w, w1) = (Layers::width(l), Layers::width(l + 1));
        let mut succ = Vec::new();
        if w1 >= w {
            succ.extend((i * w1 / w..(i + 1) * w1 / w).map(|j| (l + 1, j)));
        } else {
            succ.push((l + 1, i % w1));
        }
        succ.push((l + 1, (i * 7 + 3) % w1));
        if i % 5 == 0 && l + 2 < self.layers {
            succ.push((l + 2, (i * 13) % Layers::width(l + 2)));
        }
        for t in succ {
            if !out(t, (t.0 == l + 2) as u32) {
                return Ok(());
            }
        }
        Ok(())
    }
    fn fingerprint(&self, s: &(u32, u32)) -> u64 {
        let i = if self.coarse { s.1 / 2 } else { s.1 };
        ((s.0 as u64) << 32 | i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0x5678
    }
    fn coarse_fingerprint(&self) -> bool {
        self.coarse
    }
    fn check_invariants(&self, s: &(u32, u32)) -> Result<Option<usize>, ModelError> {
        Ok(if Some(*s) == self.bad { Some(0) } else { None })
    }
    fn invariant_names(&self) -> &[String] {
        &self.inv
    }
    fn action_names(&self) -> &[String] {
        &self.acts
    }
    fn render(&self, s: &(u32, u32)) -> String {
        format!("/\\ l = {}\n/\\ i = {}", s.0, s.1)
    }
    fn caps(&self) -> Caps<'_, (u32, u32)> {
        Caps {
            format: Some(if self.coded { StateFormat::Words(self) } else { StateFormat::Bytes(self) }),
            live_atoms: self.live.then_some(self as _),
            effects: None,
            checkpoint: Some(self),
            gc: None,
        }
    }
}

impl Checkpointed for Layers {
    fn worker_snapshot(&self) -> Result<Vec<u8>, String> {
        Ok(vec![live::current_worker().expect("a worker") as u8])
    }
    fn restore_workers(&self, _main: &[u8], snaps: &[Vec<u8>]) -> Result<(), String> {
        *self.restored.lock().unwrap() = snaps.to_vec();
        Ok(())
    }
}

/// State atom 0: an even index; action atom 0: a shortcut (two levels).
impl AtomBits<(u32, u32)> for Layers {
    fn state(&self, s: &(u32, u32), out: &[&[u64]]) -> Result<Vec<u64>, ModelError> {
        let jump = out.iter().any(|b| b[0] & 1 == 1);
        Ok(vec![u64::from(s.1.is_multiple_of(2)) | u64::from(jump) << 1])
    }
    fn action(&self, s: &(u32, u32), t: &(u32, u32)) -> Result<Vec<u64>, ModelError> {
        Ok(vec![u64::from(t.0 == s.0 + 2)])
    }
}

impl StateCodec<(u32, u32)> for Layers {
    fn words(&self) -> usize {
        WORDS
    }
    fn encode(&self, s: &(u32, u32), out: &mut [u64]) -> u64 {
        out.copy_from_slice(&[s.0 as u64, s.1 as u64]);
        self.fingerprint(s)
    }
    fn validate(&self, _w: &[u64]) -> Result<(), String> {
        if self.reject_words {
            Err("invalid external handle".into())
        } else {
            Ok(())
        }
    }
    fn decode(&self, w: &[u64], _depth: u32, fp: u64) -> (u32, u32) {
        let s = (w[0] as u32, w[1] as u32);
        assert_eq!(self.fingerprint(&s), fp);
        s
    }
}

impl Persist<(u32, u32)> for Layers {
    fn write_state(&self, s: &(u32, u32), out: &mut Vec<u8>) -> Result<(), String> {
        out.extend_from_slice(&s.0.to_le_bytes());
        out.extend_from_slice(&s.1.to_le_bytes());
        Ok(())
    }
    fn read_state(&self, b: &[u8], _depth: u32, fp: u64) -> Result<(u32, u32), String> {
        let b: [u8; 8] = b.try_into().map_err(|_| "a state of 8 bytes".to_string())?;
        let s = (u32::from_le_bytes(b[..4].try_into().unwrap()), u32::from_le_bytes(b[4..].try_into().unwrap()));
        if self.fingerprint(&s) != fp {
            return Err("fingerprint mismatch".into());
        }
        Ok(s)
    }
}

/// A metadir of its own for a test.
fn metadir(name: &str) -> PathBuf {
    tlx_testkit::toy::spill_dir("tlx-checkpoint", name)
}

fn spill_in(dir: &Path, mode: SpillMode, reused: bool) -> Spill {
    Spill::new(SpillConfig { mode, dir: Some(dir.to_path_buf()), reused, ..Default::default() })
}

/// Wait for a previous search's spill IO threads to drop their `BlockStore`
/// references (and release the directory `LOCK`) before the same process
/// opens that metadir again.
fn settle(spill: &Spill) {
    spill.wait_for_writes();
    spill.wait_for_reads();
}

const IDENTITY: &str = "test run";

/// Checkpoints every `states` new states; the search stops after the
/// `stop`-th (keeping it).
fn stopping(states: u64, stop: u64) -> Arc<Checkpointer> {
    Checkpointer::new(CheckpointConfig {
        every_states: Some(states),
        after: AfterCommit::Stop(stop),
        identity: vec![("run".into(), IDENTITY.into())],
        ..Default::default()
    })
}

/// No more checkpoints (the recovered one is removed at the end).
fn none() -> Arc<Checkpointer> {
    Checkpointer::new(CheckpointConfig::default())
}

fn opts(workers: usize, spill: Spill, ck: Option<Arc<Checkpointer>>) -> Options {
    Options { workers, check_deadlock: false, spill, checkpoint: ck, ..Default::default() }
}

/// What must not change: the outcome, the depth, the counts (if `exact`,
/// or the search completed: after a failure with several workers, how much
/// of its level was explored varies). EXACT compares the full state trace;
/// PARALLEL compares only its length.
const EXACT: ComparisonPolicy =
    ComparisonPolicy { left: Counts::Always, trace: TracePolicy::States, ..ComparisonPolicy::COUNTS_AND_LENGTH };
const PARALLEL: ComparisonPolicy = ComparisonPolicy {
    counts: Counts::OnSuccess,
    left: Counts::OnSuccess,
    trace: TracePolicy::Length,
    ..ComparisonPolicy::COUNTS_AND_LENGTH
};

fn summary(r: &Report<(u32, u32)>, policy: ComparisonPolicy) -> Projection<(u32, u32)> {
    project(r, policy)
}

/// Run `make()` with `kill` workers until its `stop`-th checkpoint (every
/// `every` states), then recover with `recover` workers: the report of the
/// recovered search, and the model it ran.
fn interrupted<M: Model>(
    make: &dyn Fn() -> M,
    kill: usize,
    recover: usize,
    every: u64,
    stop: u64,
    mode: SpillMode,
) -> (Report<M::State>, M) {
    let dir = metadir("run");
    let ck = stopping(every, stop);
    let first = make();
    let s1 = spill_in(&dir, mode, false);
    let r = explore(&first, &opts(kill, s1.clone(), Some(ck.clone())));
    settle(&s1);
    assert_eq!(ck.count(), stop, "checkpoints taken before the stop: {:?}", r.outcome);
    assert!(dir.join("checkpoint/MANIFEST").is_file());
    let rec = Recovery::open(&dir).expect("a checkpoint");
    assert_eq!(rec.identity(), [("run".to_string(), IDENTITY.to_string())]);
    assert_eq!(rec.workers(), kill);
    let m = make();
    let s2 = spill_in(&dir, mode, true);
    let r = explore_from(&m, &opts(recover, s2.clone(), Some(none())), Start::Recover(&rec), None).0;
    settle(&s2);
    // (Removed once the recovered search ended: the checkpoint, the
    // metadir made by the first search.)
    assert!(!dir.exists(), "{} left", dir.display());
    (r, m)
}

/// With one worker before and after, the recovered search is the
/// uninterrupted one: the same results, trace and order of expansion
/// (from the checkpoint on); with others, the same results, counts and
/// shortest traces. Encoded and serialized states.
#[test]
fn recovered_search_is_the_uninterrupted_one() {
    for bad in [None, Some((61, 5)), Some((70, 1))] {
        for coded in [true, false] {
            let make = || Layers::new(90, bad, coded);
            let reference = make();
            let want = summary(&explore(&reference, &opts(1, Spill::default(), None)), EXACT);
            let order = reference.log.lock().unwrap().clone();
            for stop in [1, 3] {
                let (r, m) = interrupted(&make, 1, 1, 400, stop, SpillMode::Auto);
                assert_eq!(summary(&r, EXACT), want, "bad {bad:?} coded {coded} stop {stop}");
                // (The recovered search expands the rest, in the same order.)
                let got = m.log.lock().unwrap().clone();
                assert!(order.ends_with(&got) && !got.is_empty(), "bad {bad:?} coded {coded} stop {stop}: order");
                assert_eq!(*m.restored.lock().unwrap(), vec![vec![0u8]]);
            }
            for (kill, recover) in [(1, 4), (4, 1), (8, 8), (3, 5)] {
                let (r, m) = interrupted(&make, kill, recover, 400, 2, SpillMode::Auto);
                assert_eq!(
                    summary(&r, PARALLEL),
                    summary(&explore(&make(), &opts(1, Spill::default(), None)), PARALLEL),
                    "bad {bad:?} coded {coded} {kill} -> {recover} workers"
                );
                assert_eq!(*m.restored.lock().unwrap(), (0..kill as u8).map(|w| vec![w]).collect::<Vec<_>>());
            }
        }
    }
}

use tlx_testkit::toy::canon;

/// Historical shards outlive their workers: shrinking and growing the
/// pool across two recoveries preserves the graph and shortest trace.
#[test]
fn repeated_recovery_with_fewer_workers_keeps_graph() {
    for pools in [[8, 1, 3], [2, 1, 8]] {
        repeated_recovery_with_fewer_workers(None, pools);
    }
}

#[test]
fn repeated_recovery_with_fewer_workers_keeps_trace() {
    for pools in [[8, 1, 3], [2, 1, 8]] {
        repeated_recovery_with_fewer_workers(Some((70, 1)), pools);
    }
}

fn repeated_recovery_with_fewer_workers(bad: Option<(u32, u32)>, [initial, fewer, more]: [usize; 3]) {
    for coded in [true, false] {
        for mode in [SpillMode::Auto, SpillMode::Always] {
            let make = || Layers { live: true, ..Layers::new(90, bad, coded) };
            let want = explore(&make(), &opts(1, Spill::default(), None));
            let dir = metadir("repeated");
            let first = stopping(400, 2);
            let s0 = spill_in(&dir, mode, false);
            explore(&make(), &opts(initial, s0.clone(), Some(first.clone())));
            settle(&s0);
            assert_eq!(first.count(), 2);
            for workers in [fewer, more] {
                let rec = Recovery::open(&dir).unwrap();
                let ck = stopping(400, 1);
                let s = spill_in(&dir, mode, true);
                let r = explore_from(&make(), &opts(workers, s.clone(), Some(ck.clone())), Start::Recover(&rec), None).0;
                settle(&s);
                assert_eq!(ck.count(), 1, "{:?}", r.outcome);
            }
            let rec = Recovery::open(&dir).unwrap();
            let s = spill_in(&dir, mode, true);
            let r = explore_from(&make(), &opts(1, s.clone(), Some(none())), Start::Recover(&rec), None).0;
            settle(&s);
            assert_eq!(summary(&r, PARALLEL), summary(&want, PARALLEL), "coded {coded}, bad {bad:?}, mode {mode:?}");
            if let Some(bad) = bad {
                assert_eq!(r.trace.first().unwrap().state.0, 0);
                assert_eq!(r.trace.last().unwrap().state, bad);
                for pair in r.trace.windows(2) {
                    let mut found = false;
                    make()
                        .successors(&pair[0].state, &mut |s, _| {
                            found |= s == pair[1].state;
                            true
                        })
                        .unwrap();
                    assert!(found, "invalid trace step");
                }
            } else {
                assert_eq!(
                    canon(r.live_graph.as_ref().unwrap().as_ref().unwrap()),
                    canon(want.live_graph.as_ref().unwrap().as_ref().unwrap())
                );
            }
            assert!(!dir.exists());
        }
    }
}

/// The liveness edges recorded before the checkpoint are in it: the
/// recovered search's behavior graph is the uninterrupted one's.
#[test]
fn recovered_search_records_the_whole_behavior_graph() {
    for coded in [true, false] {
        let make = || Layers { live: true, ..Layers::new(90, None, coded) };
        for (kill, recover) in [(1, 1), (4, 1), (1, 8), (3, 3)] {
            let want = explore(&make(), &opts(recover, Spill::default(), None));
            let want_graph = canon(want.live_graph.as_ref().and_then(|g| g.as_ref().ok()).expect("recorded graph"));
            let (r, _) = interrupted(&make, kill, recover, 300, 2, SpillMode::Auto);
            assert_eq!(summary(&r, PARALLEL), summary(&want, PARALLEL));
            assert!(r.live_atoms_ok);
            let got = canon(r.live_graph.as_ref().and_then(|g| g.as_ref().ok()).expect("recorded graph of the recovered search"));
            assert!(got == want_graph, "coded {coded} {kill} -> {recover} workers: graphs differ");
        }
    }
}

/// Coarse fingerprints (VIEW, SYMMETRY): the representatives are the
/// first states of their classes in BFS order, also across a recovery
/// (the checkpoint keeps the BFS positions of the queued states).
#[test]
fn recovered_search_keeps_the_representatives() {
    for bad in [None, Some((50, 3))] {
        for coded in [true, false] {
            let make = || Layers { coarse: true, ..Layers::new(90, bad, coded) };
            let want = summary(&explore(&make(), &opts(1, Spill::default(), None)), EXACT);
            for (kill, recover) in [(1, 1), (8, 1), (8, 8), (1, 6)] {
                let (r, _) = interrupted(&make, kill, recover, 300, 2, SpillMode::Auto);
                assert_eq!(
                    summary(&r, if kill == 1 && recover == 1 { EXACT } else { PARALLEL }),
                    summary(&explore(&make(), &opts(1, Spill::default(), None)), if kill == 1 && recover == 1 { EXACT } else { PARALLEL }),
                    "bad {bad:?} coded {coded} {kill} -> {recover}"
                );
                if bad.is_none() {
                    let got = summary(&r, EXACT);
                    assert_eq!(got.counts, want.counts);
                    assert_eq!(got.left, want.left);
                }
            }
        }
    }
}

/// Under the disk tier (everything spilled: the fingerprint set in runs
/// on disk, the queue's segments, the trace logs, the edges) the
/// checkpoint holds the same, and the recovered search goes on spilling.
#[test]
fn recovered_search_with_the_disk_tier() {
    for coded in [true, false] {
        let make = || Layers { live: true, ..Layers::new(90, Some((80, 1)), coded) };
        let want = summary(&explore(&make(), &opts(1, Spill::default(), None)), EXACT);
        for (kill, recover) in [(1, 1), (4, 2)] {
            let dir = metadir("disk");
            let ck = stopping(300, 2);
            let fp = FpConfig::default().with_disk_slots(1024);
            let o = |w, spill, ck| Options {
                fp,
                queue: tlx_runtime::queue::Config { seg_bytes: 4096, ..Default::default() },
                ..opts(w, spill, Some(ck))
            };
            let s1 = spill_in(&dir, SpillMode::Always, false);
            explore(&make(), &o(kill, s1.clone(), ck.clone()));
            settle(&s1);
            assert_eq!(ck.count(), 2);
            let rec = Recovery::open(&dir).expect("a checkpoint");
            let s2 = spill_in(&dir, SpillMode::Always, true);
            let r = explore_from(&make(), &o(recover, s2.clone(), none()), Start::Recover(&rec), None).0;
            settle(&s2);
            assert_eq!(
                summary(&r, if kill == 1 { EXACT } else { PARALLEL }),
                summary(&explore(&make(), &opts(1, Spill::default(), None)), if kill == 1 { EXACT } else { PARALLEL }),
                "coded {coded} {kill} -> {recover}"
            );
            if kill == 1 {
                assert_eq!(summary(&r, EXACT), want);
            }
            assert!(!dir.exists());
        }
    }
}

/// A damaged checkpoint is refused: a file of the wrong size when opened,
/// a corrupt chunk when read (the search fails with an IO error, and the
/// checkpoint is kept); one of another build cannot even be opened (see
/// `tlx_base::frame`).
#[test]
fn damaged_checkpoints_are_refused() {
    let make = || Layers::new(90, None, true);
    for (file, how) in [
        ("queue-0", "flip"),
        ("fpset-0", "flip"),
        ("trace-0.1", "flip"),
        ("trace-0.2", "flip"),
        ("fpset-0", "grow"),
        ("queue-0", "remove"),
        ("MANIFEST", "flip"),
    ] {
        let dir = metadir("damaged");
        let ck = stopping(400, 2);
        explore(&make(), &opts(1, spill_in(&dir, SpillMode::Auto, false), Some(ck)));
        let path = dir.join("checkpoint").join(file);
        let mut b = std::fs::read(&path).unwrap();
        match how {
            "flip" => {
                let i = b.len() - 40;
                b[i] ^= 0x10;
                std::fs::write(&path, &b).unwrap();
            }
            "grow" => {
                b.extend_from_slice(b"x");
                std::fs::write(&path, &b).unwrap();
            }
            _ => std::fs::remove_file(&path).unwrap(),
        }
        match Recovery::open(&dir) {
            Err(e) => assert!(file == "MANIFEST" || how != "flip", "{file} {how}: {e}"),
            Ok(rec) => {
                assert_eq!(how, "flip", "{file} {how}: opened");
                let r = explore_from(&make(), &opts(1, spill_in(&dir, SpillMode::Auto, true), Some(none())), Start::Recover(&rec), None).0;
                assert!(matches!(&r.outcome, Outcome::Io(m) if m.contains("checksum mismatch")), "{file}: {:?}", r.outcome);
                assert!(dir.join("checkpoint/MANIFEST").is_file(), "{file}: the checkpoint was removed");
            }
        }
        let _ = std::fs::remove_dir_all(&dir);
    }
}

/// A structurally valid, checksummed checkpoint still crosses a codec's
/// raw-handle boundary before any restored words can be used as states.
#[test]
fn recovered_words_pass_the_codec_validation_boundary() {
    let dir = metadir("validate-handles");
    let ck = stopping(30, 1);
    let first = Layers::new(30, None, true);
    explore(&first, &opts(1, spill_in(&dir, SpillMode::Auto, false), Some(ck.clone())));
    assert_eq!(ck.count(), 1);
    let rec = Recovery::open(&dir).unwrap();
    let mut restored = Layers::new(30, None, true);
    restored.reject_words = true;
    let r = explore_from(&restored, &opts(1, spill_in(&dir, SpillMode::Auto, true), Some(none())), Start::Recover(&rec), None).0;
    assert!(matches!(&r.outcome, Outcome::Io(e) if e.contains("invalid external handle")), "{:?}", r.outcome);
    assert!(restored.log.lock().unwrap().is_empty(), "no invalid state was expanded");
    assert!(dir.join("checkpoint/MANIFEST").is_file());
    std::fs::remove_dir_all(dir).unwrap();
}

/// A chain of states: every level is narrow, so several workers expand it
/// one of them alone (the others wait at the level barrier).
struct Chain(Vec<String>);

impl Model for Chain {
    type State = u32;
    tlx_runtime::model_without_checks!();
    fn init_states(&self, out: &mut dyn FnMut(u32)) -> Result<(), ModelError> {
        out(0);
        Ok(())
    }
    fn successors(&self, s: &u32, out: &mut dyn FnMut(u32, u32) -> bool) -> Result<(), ModelError> {
        if *s < 5000 {
            out(s + 1, 0);
        }
        Ok(())
    }
    fn fingerprint(&self, s: &u32) -> u64 {
        (*s as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15)
    }
    fn check_invariants(&self, _s: &u32) -> Result<Option<usize>, ModelError> {
        Ok(None)
    }
    fn invariant_names(&self) -> &[String] {
        &[]
    }
    fn action_names(&self) -> &[String] {
        &self.0
    }
    fn render(&self, s: &u32) -> String {
        format!("/\\ x = {s}")
    }
    fn caps(&self) -> Caps<'_, u32> {
        Caps { format: Some(StateFormat::Bytes(self)), ..Caps::default() }
    }
}

impl Persist<u32> for Chain {
    fn write_state(&self, s: &u32, out: &mut Vec<u8>) -> Result<(), String> {
        out.extend_from_slice(&s.to_le_bytes());
        Ok(())
    }
    fn read_state(&self, b: &[u8], _depth: u32, _fp: u64) -> Result<u32, String> {
        Ok(u32::from_le_bytes(b.try_into().map_err(|_| "4 bytes".to_string())?))
    }
}

/// Narrow levels expanded by one worker alone still get their checkpoints
/// (a due checkpoint ends the solo stretch at the next level), and the
/// search recovers from them.
#[test]
fn checkpoints_in_narrow_levels() {
    let make = || Chain(vec!["Step".into()]);
    for workers in [1, 4] {
        let dir = metadir("chain");
        let ck = stopping(1000, 3);
        explore(&make(), &opts(workers, spill_in(&dir, SpillMode::Auto, false), Some(ck.clone())));
        assert_eq!(ck.count(), 3, "{workers} workers");
        let rec = Recovery::open(&dir).expect("a checkpoint");
        let r = explore_from(&make(), &opts(workers, spill_in(&dir, SpillMode::Auto, true), Some(none())), Start::Recover(&rec), None).0;
        assert_eq!((r.outcome, r.stats.distinct, r.stats.generated, r.stats.depth), (Outcome::Ok, 5001, 5001, 5001));
        assert!(!dir.exists());
    }
}

/// Without a due checkpoint nothing is written; a search that ends
/// normally removes its checkpoint.
#[test]
fn checkpoints_are_removed_at_the_end() {
    let dir = metadir("end");
    let ck = Checkpointer::new(CheckpointConfig { every_states: Some(400), ..Default::default() });
    let r = explore(&Layers::new(90, None, true), &opts(2, spill_in(&dir, SpillMode::Auto, false), Some(ck.clone())));
    assert_eq!(r.outcome, Outcome::Ok);
    assert!(ck.count() >= 3, "{}", ck.count());
    assert!(!dir.exists());
    let ck = Checkpointer::new(CheckpointConfig { every: Some(std::time::Duration::from_secs(3600)), ..Default::default() });
    explore(&Layers::new(90, None, true), &opts(2, spill_in(&dir, SpillMode::Auto, false), Some(ck.clone())));
    assert_eq!(ck.count(), 0);
    assert!(!dir.exists());
}

/// The first checkpoint of a recovered search links the segments of the one
/// it recovered from (the trace logs, the liveness edges and the archive,
/// which the recovery read into worker 0's part) and writes only what came
/// after, numbering on from it; recovered again, the search is the
/// uninterrupted one.
#[test]
fn recovered_search_links_the_recovered_segments() {
    const RETAIN: Option<usize> = Some(1 << 30);
    let names = |dir: &Path| -> std::collections::BTreeSet<String> {
        std::fs::read_dir(dir.join("checkpoint")).unwrap().map(|e| e.unwrap().file_name().into_string().unwrap()).collect()
    };
    let segment = |f: &String| ["trace-", "edges-", "archive-"].iter().any(|p| f.starts_with(p)) && f.contains('.');
    for coded in [true, false] {
        let make = || Layers { live: true, ..Layers::new(90, None, coded) };
        let want = explore(&make(), &opts(1, Spill::default(), None));
        let dir = metadir(&format!("links-{coded}"));
        let first = stopping(400, 2);
        let s1 = spill_in(&dir, SpillMode::Auto, false);
        explore_from(&make(), &opts(4, s1.clone(), Some(first.clone())), Start::Init, RETAIN);
        settle(&s1);
        assert_eq!(first.count(), 2);
        let before: Vec<String> = names(&dir).into_iter().filter(segment).collect();
        if coded {
            assert!(before.iter().any(|f| f.starts_with("archive-1.")), "{before:?}");
        } else {
            assert!(!before.iter().any(|f| f.starts_with("archive-")), "{before:?}");
        }
        let rec = Recovery::open(&dir).unwrap();
        let ck = stopping(400, 1);
        let s2 = spill_in(&dir, SpillMode::Auto, true);
        let r = explore_from(&make(), &opts(2, s2.clone(), Some(ck.clone())), Start::Recover(&rec), RETAIN).0;
        settle(&s2);
        assert_eq!(ck.count(), 1, "{:?}", r.outcome);
        let after = names(&dir);
        // Every recovered segment is linked (the archive's of all four
        // workers, as worker 0's); the new ones are those of checkpoint 3.
        for f in &before {
            assert!(after.contains(f), "coded {coded}: {f} not linked: {after:?}");
        }
        let new: Vec<&String> = after.iter().filter(|f| segment(f) && !before.contains(f)).collect();
        assert!(!new.is_empty() && new.iter().all(|f| f.ends_with(".3")), "coded {coded}: {new:?}");
        let rec = Recovery::open(&dir).unwrap();
        let s3 = spill_in(&dir, SpillMode::Auto, true);
        let r = explore_from(&make(), &opts(1, s3.clone(), Some(none())), Start::Recover(&rec), RETAIN).0;
        settle(&s3);
        assert_eq!(summary(&r, PARALLEL), summary(&want, PARALLEL), "coded {coded}");
        assert_eq!(canon(r.live_graph.as_ref().unwrap().as_ref().unwrap()), canon(want.live_graph.as_ref().unwrap().as_ref().unwrap()));
        assert!(!dir.exists());
    }
}

/// An unencoded model (`StateFormat::Bytes`) must not write archive files
/// even when a worker archived zero blocks (`[].iter().all(Block::encoded)`
/// is vacuously true).
#[test]
fn unencoded_checkpoint_writes_no_archive_for_idle_workers() {
    let dir = metadir("unencoded-idle");
    let ck = stopping(1000, 1);
    let s = spill_in(&dir, SpillMode::Auto, false);
    explore_from(&Chain(vec!["Step".into()]), &opts(4, s.clone(), Some(ck.clone())), Start::Init, Some(1 << 30));
    settle(&s);
    assert_eq!(ck.count(), 1);
    let files: Vec<String> =
        std::fs::read_dir(dir.join("checkpoint")).unwrap().map(|e| e.unwrap().file_name().into_string().unwrap()).collect();
    assert!(!files.iter().any(|f| f.starts_with("archive-")), "{files:?}");
    let _ = std::fs::remove_dir_all(&dir);
}

/// Multi-worker positioned checkpoints (`coarse` = VIEW/SYMMETRY, or `coverage`)
/// recovered with one worker preserve exact BFS expansion order, counts,
/// coverage and traces under tight `maxmem`, `-spill always` (forcing
/// multi-run external merge-sort) and `-spill off` (compact in-memory sort).
#[test]
fn positioned_single_worker_recovery_preserves_bfs_order_and_bounds_memory() {
    for (coarse, coverage, bad) in [(true, false, None), (true, false, Some((50, 3))), (false, true, None), (false, true, Some((61, 5)))] {
        for coded in [true, false] {
            let make = || Layers { coarse, ..Layers::new(90, bad, coded) };
            let reference = make();
            let ref_opts = Options { coverage, ..opts(1, Spill::default(), None) };
            let ref_report = explore(&reference, &ref_opts);
            let want = summary(&ref_report, EXACT);
            let want_order = reference.log.lock().unwrap().clone();

            let cases: [(&str, SpillMode, usize); 3] = [
                ("tight-maxmem", SpillMode::Auto, 1 << 20),
                ("spill-always", SpillMode::Always, usize::MAX),
                ("spill-off", SpillMode::Off, 64 << 20),
            ];
            for (label, mode, maxmem) in cases {
                let scratch = tlx_testkit::TempDir::new(&format!("pos1-{coarse}-{coverage}-{coded}-{label}"));
                let dir = scratch.child_path("meta");
                let ck = stopping(300, 2);
                let s1 = spill_in(&dir, mode, false);
                let o1 = Options {
                    coverage,
                    queue: tlx_runtime::queue::Config { seg_bytes: 4096, ..Default::default() },
                    ..opts(8, s1.clone(), Some(ck.clone()))
                };
                explore(&make(), &o1);
                settle(&s1);
                assert_eq!(ck.count(), 2, "{label}: checkpoint count");

                let rec = Recovery::open(&dir).expect("checkpoint");
                let m = make();
                let s2 = spill_in(&dir, mode, true);
                let o2 = Options {
                    coverage,
                    maxmem,
                    fp: FpConfig::default().with_disk_slots(1024),
                    queue: tlx_runtime::queue::Config { seg_bytes: 4096, ..Default::default() },
                    ..opts(1, s2.clone(), Some(none()))
                };
                let (r, _) = explore_from(&m, &o2, Start::Recover(&rec), None);
                settle(&s2);

                assert_eq!(summary(&r, EXACT), want, "coarse={coarse} coverage={coverage} bad={bad:?} coded={coded} {label}");
                let got_order = m.log.lock().unwrap().clone();
                assert!(
                    want_order.ends_with(&got_order) && !got_order.is_empty(),
                    "coarse={coarse} coverage={coverage} bad={bad:?} coded={coded} {label}: expansion order diverged from exact BFS"
                );
                if coverage {
                    assert_eq!(
                        r.coverage, ref_report.coverage,
                        "coarse={coarse} coverage={coverage} bad={bad:?} coded={coded} {label}: coverage mismatch"
                    );
                }
                assert_eq!(s2.counters().used, 0, "{label}: leaked spill bytes");
                match mode {
                    SpillMode::Always => assert!(s2.counters().written > 0, "{label}: expected disk sort writes"),
                    SpillMode::Off => assert_eq!(s2.counters().written, 0, "{label}: wrote to disk with SpillMode::Off"),
                    SpillMode::Auto => {}
                }
                assert!(!dir.exists(), "{} left behind", dir.display());
            }
        }
    }
}

/// Recovering a positioned checkpoint with one worker under `-spill off` and a
/// generous budget keeps the layout-miss archive intact (does not trigger
/// stage-1 relief to drop it while sorting).
#[test]
fn positioned_single_worker_recovery_keeps_archive_without_pressure() {
    let make = |error_level| Layers { coarse: true, error_level, ..Layers::new(90, None, true) };
    let scratch = tlx_testkit::TempDir::new("pos1-keep-archive");
    let dir = scratch.child_path("meta");
    let ck = stopping(300, 2);
    let s1 = spill_in(&dir, SpillMode::Auto, false);
    explore_from(&make(None), &opts(4, s1.clone(), Some(ck.clone())), Start::Init, Some(1 << 30));
    settle(&s1);
    assert_eq!(ck.count(), 2);

    let rec = Recovery::open(&dir).expect("checkpoint");
    let s2 = spill_in(&dir, SpillMode::Off, true);
    let o2 = Options { maxmem: 512 << 20, ..opts(1, s2.clone(), Some(none())) };
    let (r, resume) = explore_from(&make(Some(80)), &o2, Start::Recover(&rec), Some(1 << 30));
    settle(&s2);
    assert!(matches!(r.outcome, Outcome::Error(_)), "{:?}", r.outcome);
    let rp = resume.expect("archive must remain intact when memory fits in budget");
    assert!(!rp.is_empty());
    assert_eq!(s2.counters().written, 0);
    assert!(!dir.exists());
}

/// Wide encoded model for destination-frontier spilling regressions: 8 initial
/// states fan out across multiple workers into `8 * fanout` (`< 1024`)
/// high-entropy level-1 states of `WIDE_WORDS` words (~32 KiB raw each,
/// sealing ~1 segment per state at `seg_bytes = 64 KiB`).
struct WideLayers {
    inits: u32,
    fanout: u32,
    inv: Vec<String>,
    acts: Vec<String>,
    log: Mutex<Vec<(u32, u32)>>,
}

const WIDE_WORDS: usize = 4096;

impl WideLayers {
    fn new(inits: u32, fanout: u32) -> WideLayers {
        WideLayers { inits, fanout, inv: Vec::new(), acts: vec!["Fan".into()], log: Mutex::new(Vec::new()) }
    }
}

impl Model for WideLayers {
    type State = (u32, u32);
    tlx_runtime::model_without_checks!(but coarse_fingerprint);
    fn init_states(&self, out: &mut dyn FnMut((u32, u32))) -> Result<(), ModelError> {
        for i in 0..self.inits {
            out((0, i));
        }
        Ok(())
    }
    fn successors(&self, s: &(u32, u32), out: &mut dyn FnMut((u32, u32), u32) -> bool) -> Result<(), ModelError> {
        self.log.lock().unwrap().push(*s);
        if s.0 == 0 {
            let base = s.1 * self.fanout;
            for j in 0..self.fanout {
                if !out((1, base + j), 0) {
                    return Ok(());
                }
            }
        }
        Ok(())
    }
    fn fingerprint(&self, s: &(u32, u32)) -> u64 {
        ((s.0 as u64) << 32 | s.1 as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0x1357_9BDF
    }
    fn coarse_fingerprint(&self) -> bool {
        true
    }
    fn check_invariants(&self, _: &(u32, u32)) -> Result<Option<usize>, ModelError> {
        Ok(None)
    }
    fn invariant_names(&self) -> &[String] {
        &self.inv
    }
    fn action_names(&self) -> &[String] {
        &self.acts
    }
    fn render(&self, s: &(u32, u32)) -> String {
        format!("/\\ l = {}\n/\\ i = {}", s.0, s.1)
    }
    fn caps(&self) -> Caps<'_, (u32, u32)> {
        Caps { format: Some(StateFormat::Words(self)), ..Caps::default() }
    }
}

impl StateCodec<(u32, u32)> for WideLayers {
    fn words(&self) -> usize {
        WIDE_WORDS
    }
    fn encode(&self, s: &(u32, u32), out: &mut [u64]) -> u64 {
        out[0] = s.0 as u64;
        out[1] = s.1 as u64;
        // Fill remaining words deterministically with high entropy so XOR-varint
        // records stay ~32-36 KiB and seal segments rapidly.
        let mut x = ((s.0 as u64) << 32 | (s.1 as u64 + 1)).wrapping_mul(0x9E37_79B9_7F4A_7C15);
        for slot in &mut out[2..] {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            *slot = x;
        }
        self.fingerprint(s)
    }
    fn decode(&self, w: &[u64], _depth: u32, fp: u64) -> (u32, u32) {
        let s = (w[0] as u32, w[1] as u32);
        assert_eq!(self.fingerprint(&s), fp);
        s
    }
}

/// Regression for destination frontier spilling during positioned single-worker
/// recovery: recovering fewer than 1,024 wide encoded states (200 states x ~36 KiB
/// at `seg_bytes = 64 KiB`, ~12.5 MiB total segments) must spill segments as they
/// seal instead of waiting for 1,024 records to accumulate.
#[test]
fn positioned_single_worker_recovery_spills_wide_destination_segments() {
    const INITS: u32 = 8;
    const FANOUT: u32 = 25;
    const WIDTH: u32 = INITS * FANOUT;
    const SEG_BYTES: usize = 64 << 10;
    let reference = WideLayers::new(INITS, FANOUT);
    let ref_report = explore(&reference, &opts(1, Spill::default(), None));
    let want = summary(&ref_report, EXACT);
    let want_order = reference.log.lock().unwrap().clone();

    for (label, mode, maxmem) in [("spill-always", SpillMode::Always, usize::MAX), ("auto-tight-maxmem", SpillMode::Auto, 4 << 20)] {
        let scratch = tlx_testkit::TempDir::new(&format!("wide-dest-{label}"));
        let dir = scratch.child_path("meta");
        let ck = stopping(100, 1);
        let s1 = spill_in(&dir, mode, false);
        let o1 = Options {
            queue: tlx_runtime::queue::Config { seg_bytes: SEG_BYTES, ..Default::default() },
            ..opts(4, s1.clone(), Some(ck.clone()))
        };
        explore(&WideLayers::new(INITS, FANOUT), &o1);
        settle(&s1);
        assert_eq!(ck.count(), 1, "{label}: expected checkpoint after level 1");

        let rec = Recovery::open(&dir).expect("checkpoint");
        let recovered = WideLayers::new(INITS, FANOUT);
        let s2 = spill_in(&dir, mode, true);
        let o2 = Options {
            maxmem,
            queue: tlx_runtime::queue::Config { seg_bytes: SEG_BYTES, ..Default::default() },
            ..opts(1, s2.clone(), Some(none()))
        };
        let (r, _) = explore_from(&recovered, &o2, Start::Recover(&rec), None);
        settle(&s2);

        assert_eq!(summary(&r, EXACT), want, "{label}: outcome/counts mismatch");
        let got_order = recovered.log.lock().unwrap().clone();
        assert_eq!(got_order.len(), WIDTH as usize, "{label}: expected all {WIDTH} level-1 states expanded after recovery");
        assert!(want_order.ends_with(&got_order), "{label}: BFS expansion order diverged");
        // Without per-segment spilling during recovery emission, all 200 wide
        // states (~200 x 64 KiB = ~12.5 MiB) remain resident until `finish` ends.
        // With immediate per-segment spilling, peak stays near the 8-segment
        // read-ahead window (~576 KiB) plus active write/open segment overhead.
        let queue_peak = r.frontier_peak;
        assert!(
            queue_peak <= 2 << 20,
            "{label}: destination frontier peak {queue_peak} bytes exceeded 2 MiB (expected ~10 segments of 64 KiB, not all {WIDTH} segments)"
        );
        assert!(s2.counters().written > 0, "{label}: expected spilled destination segments");
        assert_eq!(s2.counters().used, 0, "{label}: leaked spill bytes");
        assert!(!dir.exists(), "{} left behind", dir.display());
    }
}

/// Regression for slow and failing destination queue writes during wide-state
/// recovery:
/// 1. Slow background writes keep pending buffers counted in `frontier_peak`
///    and apply backpressure so peak stays bounded near the read-ahead window.
/// 2. Injecting a write failure specifically on destination queue writes aborts
///    recovery on the first error, preserves `Outcome::Io` and the checkpoint,
///    and never retains the rest of the level in RAM.
#[test]
fn positioned_single_worker_recovery_handles_slow_and_failing_destination_spills() {
    const INITS: u32 = 8;
    const FANOUT: u32 = 25;
    const WIDTH: u32 = INITS * FANOUT;
    const SEG_BYTES: usize = 64 << 10;
    let reference = WideLayers::new(INITS, FANOUT);
    let ref_report = explore(&reference, &opts(1, Spill::default(), None));
    let want = summary(&ref_report, EXACT);
    let want_order = reference.log.lock().unwrap().clone();

    // 1. Slow destination writes: pending async buffers stay charged and
    //    backpressure keeps `frontier_peak` bounded.
    let scratch_slow = tlx_testkit::TempDir::new("wide-dest-slow");
    let dir_slow = scratch_slow.child_path("meta");
    let ck_slow = stopping(100, 1);
    let s1 = spill_in(&dir_slow, SpillMode::Always, false);
    let o1 = Options {
        queue: tlx_runtime::queue::Config { seg_bytes: SEG_BYTES, ..Default::default() },
        ..opts(4, s1.clone(), Some(ck_slow.clone()))
    };
    explore(&WideLayers::new(INITS, FANOUT), &o1);
    settle(&s1);
    assert_eq!(ck_slow.count(), 1);

    let rec = Recovery::open(&dir_slow).expect("checkpoint");
    let recovered_slow = WideLayers::new(INITS, FANOUT);
    let s_slow = Spill::new(SpillConfig {
        mode: SpillMode::Always,
        dir: Some(dir_slow.clone()),
        reused: true,
        write_delay: Some(std::time::Duration::from_millis(2)),
        ..Default::default()
    });
    let o_slow = Options {
        queue: tlx_runtime::queue::Config { seg_bytes: SEG_BYTES, ..Default::default() },
        ..opts(1, s_slow.clone(), Some(none()))
    };
    let (r_slow, _) = explore_from(&recovered_slow, &o_slow, Start::Recover(&rec), None);
    settle(&s_slow);
    assert_eq!(summary(&r_slow, EXACT), want);
    let got_order = recovered_slow.log.lock().unwrap().clone();
    assert_eq!(got_order.len(), WIDTH as usize);
    assert!(want_order.ends_with(&got_order));
    assert!(r_slow.frontier_peak <= 2 << 20, "slow-write destination frontier peak {} exceeded 2 MiB", r_slow.frontier_peak);
    let total_written = s_slow.counters().written;
    assert_eq!(s_slow.counters().used, 0);
    assert!(!dir_slow.exists());

    // 2. Failing destination writes: fail strictly inside destination `queue-`
    //    writes (after all sorter runs succeed) and verify immediate `Outcome::Io`
    //    propagation, bounded frontier peak, and preserved checkpoint.
    let scratch_fail = tlx_testkit::TempDir::new("wide-dest-fail");
    let dir_fail = scratch_fail.child_path("meta");
    let ck_fail = stopping(100, 1);
    let s1 = spill_in(&dir_fail, SpillMode::Always, false);
    let o1 = Options {
        queue: tlx_runtime::queue::Config { seg_bytes: SEG_BYTES, ..Default::default() },
        ..opts(4, s1.clone(), Some(ck_fail.clone()))
    };
    explore(&WideLayers::new(INITS, FANOUT), &o1);
    settle(&s1);
    assert_eq!(ck_fail.count(), 1);

    // Destination queue writes ~192 segments (~7.5+ MiB of payload bytes) at the
    // tail of `total_written`; failing 5 MiB before the end guarantees all
    // sorter runs succeed and the first failure hits a destination `queue-` write.
    let fail_after = total_written.saturating_sub(5 << 20);
    let rec = Recovery::open(&dir_fail).expect("checkpoint");
    let recovered_fail = WideLayers::new(INITS, FANOUT);
    let s_fail = Spill::new(SpillConfig {
        mode: SpillMode::Always,
        dir: Some(dir_fail.clone()),
        reused: true,
        fail_after: Some(fail_after),
        ..Default::default()
    });
    let o_fail = Options {
        queue: tlx_runtime::queue::Config { seg_bytes: SEG_BYTES, ..Default::default() },
        ..opts(1, s_fail.clone(), Some(none()))
    };
    let (r_fail, _) = explore_from(&recovered_fail, &o_fail, Start::Recover(&rec), None);
    settle(&s_fail);
    match &r_fail.outcome {
        Outcome::Io(msg) => {
            assert!(msg.contains("fail_after") && msg.contains("queue-"), "expected destination queue spill failure, got: {msg}");
        }
        other => panic!("expected Outcome::Io from failed destination queue spill, got {other:?}"),
    }
    assert!(recovered_fail.log.lock().unwrap().is_empty(), "no states should be expanded after recovery I/O failure");
    assert!(dir_fail.join("checkpoint/MANIFEST").is_file(), "checkpoint must be preserved on recovery I/O failure");
    assert!(r_fail.frontier_peak <= 2 << 20, "failed destination spill retained too much frontier memory: {} bytes", r_fail.frontier_peak);
}
