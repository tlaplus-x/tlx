//! The level queues (`tlx_runtime::queue`) in searches: encoded states
//! (raw and XOR-varint blocks, tiny segments) and objects give the same
//! results, the same BFS order with one worker, and the same live queue
//! sizes as a FIFO; also with their segments (and the archive's) on disk.

use std::collections::HashSet;
use std::sync::Mutex;
use tlx_testkit::report::{project, ComparisonPolicy, Counts, Projection, TracePolicy};

use tlx_runtime::io::{Spill, SpillConfig, SpillMode};
use tlx_runtime::queue::{BlockKinds, Config};
use tlx_runtime::{
    explore, explore_resumable, live, AtomBits, Caps, Effects, FpConfig, Model, ModelError, Options, Outcome, Report, StateCodec,
    StateFormat,
};

/// Levels of varying widths (wide bulges, narrow stretches) with shortcuts;
/// states `(level, index)`. Records the expansion order and the live queue
/// size at each expansion.
struct Bulges {
    layers: u32,
    bad: Option<(u32, u32)>,
    /// Expansion fails when generating one of these (as a layout miss).
    traps: Vec<(u32, u32)>,
    /// Store states encoded (in `WORDS` words).
    coded: bool,
    /// Record the liveness behavior graph (atoms: see `AtomBits`).
    live: bool,
    /// Evaluating the action atoms of a step to one of these fails (as a
    /// layout miss: it interrupts the search).
    atom_traps: Vec<(u32, u32)>,
    inv: Vec<String>,
    acts: Vec<String>,
    log: Mutex<Vec<((u32, u32), u64)>>,
}

const WORDS: usize = 3;

impl Bulges {
    fn new(layers: u32, bad: Option<(u32, u32)>, coded: bool) -> Bulges {
        Bulges {
            layers,
            bad,
            traps: Vec::new(),
            coded,
            live: false,
            atom_traps: Vec::new(),
            inv: vec!["NotBad".into()],
            acts: vec!["Step".into(), "Jump".into()],
            log: Mutex::new(Vec::new()),
        }
    }

    fn width(l: u32) -> u32 {
        match l % 40 {
            10..=13 => 900 + 37 * (l % 5),
            20 => 300,
            _ if l.is_multiple_of(7) => 3,
            _ => 1,
        }
    }
}

impl Model for Bulges {
    type State = (u32, u32);
    tlx_runtime::model_without_checks!();
    fn init_states(&self, out: &mut dyn FnMut((u32, u32))) -> Result<(), ModelError> {
        out((0, 0));
        out((0, 1));
        Ok(())
    }
    fn successors(&self, s: &(u32, u32), out: &mut dyn FnMut((u32, u32), u32) -> bool) -> Result<(), ModelError> {
        self.log.lock().unwrap().push((*s, live::current().map_or(u64::MAX, |l| l.queue)));
        let (l, i) = *s;
        if l + 1 >= self.layers {
            return Ok(());
        }
        let (w, w1) = (Bulges::width(l), Bulges::width(l + 1));
        let mut succ = Vec::new();
        if w1 >= w {
            succ.extend((i * w1 / w..(i + 1) * w1 / w).map(|j| (l + 1, j)));
        } else {
            succ.push((l + 1, i % w1));
        }
        succ.push((l + 1, (i * 7 + 3) % w1));
        if i % 5 == 0 && l + 2 < self.layers {
            succ.push((l + 2, (i * 13) % Bulges::width(l + 2)));
        }
        for t in succ {
            if self.traps.contains(&t) {
                return Err(ModelError::new("trapped"));
            }
            if !out(t, (t.0 == l + 2) as u32) {
                return Ok(());
            }
        }
        Ok(())
    }
    fn fingerprint(&self, s: &(u32, u32)) -> u64 {
        ((s.0 as u64) << 32 | s.1 as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0x5678
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
            format: self.coded.then_some(StateFormat::Words(self)),
            live_atoms: self.live.then_some(self as _),
            effects: Some(self),
            checkpoint: None,
            gc: None,
        }
    }
}

impl Effects for Bulges {
    fn interrupts(&self, e: &ModelError) -> bool {
        // (As a layout miss of the compiled tier, while recording.)
        self.live && e.message == "trapped"
    }
}

/// State atom 0: an even index; action atom 0: a shortcut (two levels).
impl AtomBits<(u32, u32)> for Bulges {
    fn state(&self, s: &(u32, u32), out: &[&[u64]]) -> Result<Vec<u64>, ModelError> {
        let jump = out.iter().any(|b| b[0] & 1 == 1);
        Ok(vec![u64::from(s.1.is_multiple_of(2)) | u64::from(jump) << 1])
    }
    fn action(&self, s: &(u32, u32), t: &(u32, u32)) -> Result<Vec<u64>, ModelError> {
        if self.atom_traps.contains(t) {
            return Err(ModelError::new("trapped"));
        }
        Ok(vec![u64::from(t.0 == s.0 + 2)])
    }
}

impl StateCodec<(u32, u32)> for Bulges {
    fn words(&self) -> usize {
        WORDS
    }
    fn encode(&self, s: &(u32, u32), out: &mut [u64]) -> u64 {
        out.copy_from_slice(&[s.0 as u64, s.1 as u64, (s.0 as u64) << 40 | 0xff]);
        self.fingerprint(s)
    }
    fn decode(&self, w: &[u64], depth: u32, fp: u64) -> (u32, u32) {
        let s = (w[0] as u32, w[1] as u32);
        assert_eq!(w[2], (s.0 as u64) << 40 | 0xff);
        assert_eq!(self.fingerprint(&s), fp);
        // (Initial states are at depth 1; shortcuts make depth <= level + 1.)
        assert!(depth >= 1 && depth <= s.0 + 1, "depth {depth} of {s:?}");
        s
    }
}

const EXACT: ComparisonPolicy =
    ComparisonPolicy { left: Counts::Always, trace: TracePolicy::States, ..ComparisonPolicy::COUNTS_AND_LENGTH };
const PARALLEL: ComparisonPolicy =
    ComparisonPolicy { counts: Counts::OnSuccess, left: Counts::Ignore, trace: TracePolicy::States, ..ComparisonPolicy::COUNTS_AND_LENGTH };

fn summary(r: &Report<(u32, u32)>, policy: ComparisonPolicy) -> Projection<(u32, u32)> {
    project(r, policy)
}

fn configs() -> Vec<Config> {
    vec![
        Config::default(),
        Config { kinds: BlockKinds::Raw, seg_bytes: 64, ..Config::default() },
        Config { kinds: BlockKinds::Xor, seg_bytes: 64, ..Config::default() },
        Config { kinds: BlockKinds::Xor, seg_bytes: 1000, ..Config::default() },
        Config { kinds: BlockKinds::Objects, ..Config::default() },
        Config { kinds: BlockKinds::Auto, seg_bytes: 4096, compress_above: 8192 },
    ]
}

/// With one worker the expansion order is the exact BFS (FIFO) order, the
/// live queue size that of a FIFO, whatever the storage.
#[test]
fn one_worker_fifo_order() {
    for bad in [None, Some((61, 5))] {
        let reference = Bulges::new(130, bad, false);
        let want = summary(&explore(&reference, &Options { workers: 1, check_deadlock: false, ..Default::default() }), EXACT);
        let order = std::mem::take(&mut *reference.log.lock().unwrap());
        // The FIFO order: by level of discovery, then discovery order; the
        // queue holds the states discovered and not yet expanded.
        let mut seen: HashSet<(u32, u32)> = [(0, 0), (0, 1)].into();
        let mut fifo: Vec<(u32, u32)> = vec![(0, 0), (0, 1)];
        for (k, (s, queue)) in order.iter().enumerate() {
            assert_eq!(fifo[k], *s);
            assert_eq!(*queue, (fifo.len() - k - 1) as u64, "queue at {s:?}");
            let mut succ = Vec::new();
            reference
                .successors(s, &mut |t, _| {
                    succ.push(t);
                    true
                })
                .unwrap();
            fifo.extend(succ.into_iter().filter(|t| seen.insert(*t)));
        }
        for cfg in configs() {
            let m = Bulges::new(130, bad, true);
            let r = explore(&m, &Options { workers: 1, check_deadlock: false, queue: cfg, ..Default::default() });
            assert_eq!(summary(&r, EXACT), want, "{cfg:?}");
            assert_eq!(*m.log.lock().unwrap(), order, "{cfg:?}");
        }
    }
}

/// Several workers: the same depth, counts and shortest traces as one.
#[test]
fn workers_match_bfs() {
    for (layers, bad) in [(200, None), (200, Some((131, 400))), (90, Some((52, 2)))] {
        let want = explore(&Bulges::new(layers, bad, false), &Options { workers: 1, check_deadlock: false, ..Default::default() });
        for cfg in configs() {
            for coded in [false, true] {
                for workers in [2, 3, 8] {
                    let m = Bulges::new(layers, bad, coded);
                    let opts = Options {
                        workers,
                        check_deadlock: false,
                        safepoint_every: if workers == 3 { 7 } else { 0 },
                        queue: cfg,
                        ..Default::default()
                    };
                    let r = explore(&m, &opts);
                    assert_eq!(
                        summary(&r, ComparisonPolicy { trace: TracePolicy::LengthAndLast, ..PARALLEL }),
                        summary(&want, ComparisonPolicy { trace: TracePolicy::LengthAndLast, ..PARALLEL }),
                        "{cfg:?} coded {coded} {workers} workers"
                    );
                }
            }
        }
    }
}

/// A search stopped by an error resumes from its resume point (retained
/// states come from the blocks) as if uninterrupted.
#[test]
fn resumed_search_with_blocks() {
    for cfg in configs() {
        for workers in [1, 4] {
            let opts = Options { workers, check_deadlock: false, queue: cfg, ..Default::default() };
            let want = summary(&explore(&Bulges::new(160, None, false), &opts), EXACT);
            let mut from = None;
            for trap in [(3, 0), (12, 500), (91, 2)] {
                let mut tm = Bulges::new(160, None, true);
                tm.traps = vec![trap];
                let (r, c) = explore_resumable(&tm, &opts, from.take(), Some(usize::MAX));
                assert!(matches!(&r.outcome, Outcome::Error(e) if e.message == "trapped"), "{trap:?}");
                from = Some(c.expect("resume point"));
            }
            let m = Bulges::new(160, None, true);
            let (r, c) = explore_resumable(&m, &opts, from, None);
            assert!(c.is_none());
            assert_eq!(summary(&r, EXACT), want, "{cfg:?} {workers} workers");
        }
    }
}

/// Resuming from the archive (docs/scale.md §6): stopped anywhere in wide
/// levels whose blocks are partly objects, partly compressed (moved to the
/// archive whole), and re-encoded (`transcode`) before resuming, the search
/// ends as if uninterrupted: same counts, and with one worker the same
/// counterexample (the trace logs are continued). The archive holds the
/// states compressed.
#[test]
fn resumed_search_from_archive() {
    let mixed = Config { kinds: BlockKinds::Auto, seg_bytes: 4096, compress_above: 20_000 };
    for cfg in [mixed, Config { kinds: BlockKinds::Xor, ..Config::default() }, Config::default()] {
        for workers in [1, 4] {
            for bad in [None, Some((61, 5))] {
                let opts = Options { workers, check_deadlock: false, queue: cfg, ..Default::default() };
                let want = explore(&Bulges::new(130, bad, false), &opts);
                let mut from = None;
                for trap in [(10, 7), (11, 900), (12, 0), (13, 950), (13, 951), (20, 299), (51, 930)] {
                    let mut tm = Bulges::new(130, bad, true);
                    tm.traps = vec![trap];
                    let (r, c) = explore_resumable(&tm, &opts, from.take(), Some(usize::MAX));
                    if !matches!(&r.outcome, Outcome::Error(e) if e.message == "trapped") {
                        // (The trap's level was already expanded.)
                        continue;
                    }
                    let c = c.expect("resume point");
                    assert_eq!(c.words(), WORDS);
                    // Compressed: a few bytes per state (objects would take
                    // 24 + 24 bytes each).
                    if cfg.kinds == BlockKinds::Xor && c.len() > 10_000 {
                        assert!(c.bytes() < 30 * c.len(), "{} bytes for {} states", c.bytes(), c.len());
                    }
                    let n = c.len();
                    let mut sampled = 0;
                    assert!(c.sample(100, |w, d| {
                        sampled += 1;
                        w.len() == WORDS && d >= 1
                    }));
                    assert_eq!(sampled, n.min(100));
                    // Re-encode (the same encoding, through the words).
                    let c = c
                        .transcode(3, WORDS, |w, _, out| {
                            out.copy_from_slice(w);
                            Ok::<_, ()>(tm.fingerprint(&(w[0] as u32, w[1] as u32)))
                        })
                        .unwrap();
                    assert_eq!(c.len(), n);
                    from = Some(c);
                }
                let m = Bulges::new(130, bad, true);
                let (r, c) = explore_resumable(&m, &opts, from, None);
                assert!(c.is_none());
                if workers == 1 {
                    assert_eq!(summary(&r, EXACT), summary(&want, EXACT), "{cfg:?} bad {bad:?}");
                } else {
                    assert_eq!(
                        summary(&r, ComparisonPolicy { trace: TracePolicy::Length, ..PARALLEL }),
                        summary(&want, ComparisonPolicy { trace: TracePolicy::Length, ..PARALLEL }),
                        "{cfg:?} {workers} workers bad {bad:?}"
                    );
                }
            }
        }
    }
}

/// Without disk, the archive is dropped when it exceeds its limit (bytes; counted by
/// segments, here small): no resume point then.
#[test]
fn archive_over_its_limit() {
    let queue = Config { seg_bytes: 4096, ..Config::default() };
    let opts = Options {
        workers: 2,
        check_deadlock: false,
        queue,
        spill: Spill::new(SpillConfig { mode: SpillMode::Off, ..Default::default() }),
        ..Default::default()
    };
    let mut tm = Bulges::new(130, None, true);
    tm.traps = vec![(51, 930)];
    let (r, c) = explore_resumable(&tm, &opts, None, Some(1 << 20));
    assert!(matches!(&r.outcome, Outcome::Error(e) if e.message == "trapped"));
    assert!(c.expect("resume point").bytes() <= 2 << 20);
    let (r, c) = explore_resumable(&tm, &opts, None, Some(4096));
    assert!(matches!(&r.outcome, Outcome::Error(e) if e.message == "trapped"));
    assert!(c.is_none());
}

/// Hitting the in-memory archive limit spills, preserving a late resume point.
#[test]
fn archive_limit_spills_instead_of_losing_resume() {
    for workers in [1, 4] {
        let sp = spill("archive-limit", SpillMode::Auto, |_| {});
        let opts = Options {
            workers,
            check_deadlock: false,
            spill: sp.clone(),
            queue: Config { seg_bytes: 4096, ..Config::default() },
            ..Default::default()
        };
        let mut tm = Bulges::new(130, None, true);
        tm.traps = vec![(51, 930)];
        let (r, c) = explore_resumable(&tm, &opts, None, Some(4096));
        assert!(matches!(&r.outcome, Outcome::Error(e) if e.message == "trapped"));
        let c = c.expect("limit must preserve the resume archive on disk");
        // Auto mode and an unlimited memory budget: only the explicit archive
        // limit triggers spilling. Writes are asynchronous, so wait before
        // checking their counters (a retained archive can still be pending).
        sp.wait_for_writes();
        assert!(sp.counters().written > 0);
        let plain = Bulges::new(130, None, true);
        let want = explore(&plain, &opts);
        let (got, _) = explore_resumable(&plain, &opts, Some(c), None);
        assert_eq!(summary(&got, if workers == 1 { EXACT } else { PARALLEL }), summary(&want, if workers == 1 { EXACT } else { PARALLEL }));
        // Resuming drops archive segments, but the writer may still own their
        // stores. Drain its requests before checking errors and cleanup.
        sp.wait_for_writes();
        assert!(sp.error().is_none());
        assert!(sp.dir().is_none());
    }
}

use tlx_testkit::toy::canon;

/// A resumed search records the behavior graph too (the levels
/// before its resume point are expanded again after the search), the same
/// as an uninterrupted search's; an atom error that interrupts the search
/// (a layout miss) stops it, and it resumes.
#[test]
fn resumed_search_records_the_behavior_graph() {
    let live = |coded: bool| Bulges { live: true, ..Bulges::new(130, None, coded) };
    for cfg in [
        Config::default(),
        Config { kinds: BlockKinds::Objects, ..Config::default() },
        Config { kinds: BlockKinds::Auto, seg_bytes: 4096, compress_above: 20_000 },
    ] {
        for workers in [1, 4] {
            let opts = Options { workers, check_deadlock: false, queue: cfg, ..Default::default() };
            let want = explore(&live(true), &opts);
            assert_eq!(want.outcome, Outcome::Ok);
            let want_graph = canon(want.live_graph.as_ref().and_then(|g| g.as_ref().ok()).expect("recorded graph"));
            let mut from = None;
            let mut stops = 0;
            for (trap, in_atom) in [((3, 0), false), ((12, 500), true), ((20, 299), false), ((51, 930), true)] {
                let mut tm = live(true);
                if in_atom {
                    tm.atom_traps = vec![trap];
                } else {
                    tm.traps = vec![trap];
                }
                let (r, c) = explore_resumable(&tm, &opts, from.take(), Some(usize::MAX));
                assert!(matches!(&r.outcome, Outcome::Error(e) if e.message == "trapped"), "{trap:?} {:?}", r.outcome);
                assert!(r.live_graph.is_none());
                from = Some(c.expect("resume point"));
                stops += 1;
            }
            assert_eq!(stops, 4);
            let (r, c) = explore_resumable(&live(true), &opts, from, None);
            assert!(c.is_none());
            assert_eq!((r.stats.distinct, r.stats.generated), (want.stats.distinct, want.stats.generated));
            let got = canon(r.live_graph.as_ref().and_then(|g| g.as_ref().ok()).expect("recorded graph of the resumed search"));
            assert_eq!(got.initial, want_graph.initial, "{cfg:?} {workers} workers: initial states");
            assert!(got == want_graph, "{cfg:?} {workers} workers: graphs differ");
        }
    }
}

/// A spill directory of its own for a test.
fn spill(name: &str, mode: SpillMode, f: impl FnOnce(&mut SpillConfig)) -> Spill {
    let dir = tlx_testkit::toy::spill_dir("tlx-queue-spill", name);
    let mut cfg = SpillConfig { mode, dir: Some(dir), ..Default::default() };
    f(&mut cfg);
    Spill::new(cfg)
}

/// Queue parameters for spilling: segments small enough that the wide
/// levels have more than the read-ahead window (whose segments stay in
/// memory).
fn spill_configs() -> Vec<Config> {
    vec![
        Config { kinds: BlockKinds::Xor, seg_bytes: 600, ..Config::default() },
        Config { kinds: BlockKinds::Raw, seg_bytes: 1000, ..Config::default() },
        Config { kinds: BlockKinds::Auto, seg_bytes: 1000, compress_above: 8192 },
    ]
}

/// The queue's segments on disk (`-spill always`), read back ahead of
/// the claims: with one worker the same expansion order (FIFO), counts,
/// live queue sizes and trace; with several the same depth, counts and
/// shortest traces.
#[test]
fn spilled_queue_gives_the_same_search() {
    for bad in [None, Some((61, 5))] {
        let reference = Bulges::new(130, bad, false);
        let want = explore(&reference, &Options { workers: 1, check_deadlock: false, ..Default::default() });
        let order = std::mem::take(&mut *reference.log.lock().unwrap());
        for cfg in spill_configs() {
            for workers in [1, 3, 8] {
                let m = Bulges::new(130, bad, true);
                let sp = spill("same", SpillMode::Always, |_| {});
                let r = explore(&m, &Options { workers, check_deadlock: false, queue: cfg, spill: sp.clone(), ..Default::default() });
                if workers == 1 {
                    assert_eq!(summary(&r, EXACT), summary(&want, EXACT), "{cfg:?}");
                    assert_eq!(*m.log.lock().unwrap(), order, "{cfg:?}");
                } else {
                    let want = explore(&reference, &Options { workers: 1, check_deadlock: false, ..Default::default() });
                    assert_eq!(
                        summary(&r, ComparisonPolicy { trace: TracePolicy::LengthAndLast, ..PARALLEL }),
                        summary(&want, ComparisonPolicy { trace: TracePolicy::LengthAndLast, ..PARALLEL }),
                        "{cfg:?} {workers} workers"
                    );
                }
                // Queue destruction can leave asynchronous requests holding
                // their stores. Wait for release before asserting disk cleanup.
                sp.wait_for_writes();
                sp.wait_for_reads();
                let c = sp.counters();
                assert!(c.read > 0 && sp.error().is_none(), "{cfg:?} {workers} workers: {c:?}");
                assert_eq!(c.used, 0, "{cfg:?} {workers} workers: the disk space given back");
                assert!(sp.dir().is_none());
            }
        }
    }
}

/// A budget far below what the process uses: the stages up to the queue's
/// spilling apply at once; the search is the same.
#[test]
fn tiny_budget_spills_the_queue() {
    let reference = Bulges::new(130, None, false);
    let want = explore(&reference, &Options { workers: 1, check_deadlock: false, ..Default::default() });
    for workers in [1, 8] {
        let m = Bulges::new(130, None, true);
        let sp = spill("tiny", SpillMode::Auto, |_| {});
        let queue = Config { seg_bytes: 600, ..Config::default() };
        let opts = Options {
            workers,
            check_deadlock: false,
            queue,
            spill: sp.clone(),
            maxmem: 1 << 20,
            fp: FpConfig::fixed_mib(32),
            ..Default::default()
        };
        let r = explore(&m, &opts);
        assert_eq!(
            summary(&r, ComparisonPolicy { trace: TracePolicy::Ignore, ..PARALLEL }),
            summary(&want, ComparisonPolicy { trace: TracePolicy::Ignore, ..PARALLEL }),
            "{workers} workers"
        );
        // (Neither a trace nor liveness: only the queue reads back.)
        let c = sp.counters();
        assert!(c.read > 0 && sp.error().is_none(), "{workers} workers: {c:?}");
    }
}

/// IO errors while spilling the queue stop the search with `Outcome::Io`:
/// a failing write, the disk quota.
#[test]
fn queue_spill_errors_stop_the_search() {
    for workers in [1, 8] {
        let queue = Config { seg_bytes: 4096, ..Config::default() };
        let sp = spill("fail", SpillMode::Always, |c| c.fail_after = Some(64 << 10));
        let r = explore(
            &Bulges::new(200, None, true),
            &Options { workers, check_deadlock: false, queue, spill: sp.clone(), ..Default::default() },
        );
        match &r.outcome {
            Outcome::Io(msg) => assert!(msg.contains("injected write error"), "{msg}"),
            o => panic!("{o:?}"),
        }
        let sp = spill("quota", SpillMode::Always, |c| c.maxdisk = Some(48 << 10));
        let r = explore(
            &Bulges::new(200, None, true),
            &Options { workers, check_deadlock: false, queue, spill: sp.clone(), ..Default::default() },
        );
        match &r.outcome {
            Outcome::Io(msg) => assert!(msg.contains("-maxdisk"), "{msg}"),
            o => panic!("{o:?}"),
        }
        assert!(sp.counters().peak <= 48 << 10);
    }
}

/// The archive's segments on disk (`-spill always`, as under memory
/// pressure instead of dropping the archive): the search resumes from it
/// (re-encoded, written to disk again) as if uninterrupted.
#[test]
fn resumed_search_from_spilled_archive() {
    for cfg in [
        Config { kinds: BlockKinds::Xor, seg_bytes: 4096, ..Config::default() },
        Config { kinds: BlockKinds::Auto, seg_bytes: 4096, compress_above: 20_000 },
    ] {
        for workers in [1, 4] {
            for bad in [None, Some((61, 5))] {
                let opts = Options { workers, check_deadlock: false, queue: cfg, ..Default::default() };
                let want = explore(&Bulges::new(130, bad, false), &opts);
                let sp = spill("archive", SpillMode::Always, |_| {});
                let opts = Options { spill: sp.clone(), ..opts };
                let mut from = None;
                let mut resumed = 0;
                for trap in [(10, 7), (12, 0), (13, 951), (20, 299), (51, 930)] {
                    let mut tm = Bulges::new(130, bad, true);
                    tm.traps = vec![trap];
                    let (r, c) = explore_resumable(&tm, &opts, from.take(), Some(usize::MAX));
                    if !matches!(&r.outcome, Outcome::Error(e) if e.message == "trapped") {
                        continue;
                    }
                    let c = c.expect("resume point");
                    let n = c.len();
                    // (On disk: little in memory.)
                    if n > 20_000 {
                        assert!(c.bytes() < 4 * n, "{} bytes for {n} states", c.bytes());
                    }
                    assert!(c.sample(100, |w, d| w.len() == WORDS && d >= 1));
                    let c = c
                        .transcode(3, WORDS, |w, _, out| {
                            out.copy_from_slice(w);
                            Ok::<_, ()>(tm.fingerprint(&(w[0] as u32, w[1] as u32)))
                        })
                        .unwrap();
                    assert_eq!(c.len(), n);
                    from = Some(c);
                    resumed += 1;
                }
                assert!(resumed >= 3);
                let m = Bulges::new(130, bad, true);
                let (r, c) = explore_resumable(&m, &opts, from, None);
                assert!(c.is_none());
                if workers == 1 {
                    assert_eq!(summary(&r, EXACT), summary(&want, EXACT), "{cfg:?} bad {bad:?}");
                } else {
                    assert_eq!(
                        summary(&r, ComparisonPolicy { trace: TracePolicy::Length, ..PARALLEL }),
                        summary(&want, ComparisonPolicy { trace: TracePolicy::Length, ..PARALLEL }),
                        "{cfg:?} {workers} workers bad {bad:?}"
                    );
                }
                assert!(sp.error().is_none());
                drop(r);
                sp.wait_for_writes();
                sp.wait_for_reads();
                assert!(sp.dir().is_none(), "the spill files are gone with the search");
            }
        }
    }
}

/// A resumed search records the behavior graph from a spilled archive too.
#[test]
fn spilled_archive_records_the_behavior_graph() {
    let live = |coded: bool| Bulges { live: true, ..Bulges::new(130, None, coded) };
    let queue = Config { kinds: BlockKinds::Auto, seg_bytes: 4096, compress_above: 20_000 };
    for workers in [1, 4] {
        let opts = Options { workers, check_deadlock: false, queue, ..Default::default() };
        let want = explore(&live(true), &opts);
        let want_graph = canon(want.live_graph.as_ref().and_then(|g| g.as_ref().ok()).expect("recorded graph"));
        let sp = spill("live", SpillMode::Always, |_| {});
        let opts = Options { spill: sp.clone(), ..opts };
        let mut from = None;
        for trap in [(12, 500), (51, 930)] {
            let mut tm = live(true);
            tm.traps = vec![trap];
            let (r, c) = explore_resumable(&tm, &opts, from.take(), Some(usize::MAX));
            assert!(matches!(&r.outcome, Outcome::Error(e) if e.message == "trapped"), "{trap:?} {:?}", r.outcome);
            from = Some(c.expect("resume point"));
        }
        let (r, _) = explore_resumable(&live(true), &opts, from, None);
        assert_eq!((r.stats.distinct, r.stats.generated), (want.stats.distinct, want.stats.generated));
        let got = canon(r.live_graph.as_ref().and_then(|g| g.as_ref().ok()).expect("recorded graph of the resumed search"));
        assert!(got == want_graph, "{workers} workers: graphs differ");
        assert!(sp.error().is_none());
    }
}
