//! The disk layer in searches (docs/scale.md §10): trace logs spilled to
//! disk give the same results and traces; IO errors stop the search with a
//! clear message; pressure from the memory budget spills.

use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use tlx_runtime::io::{Spill, SpillConfig, SpillMode};
use tlx_runtime::{explore, FpConfig, Model, ModelError, Options, Outcome};

use tlx_testkit::toy::Counters;

/// A fresh spill directory for a test.
fn test_dir(name: &str) -> PathBuf {
    tlx_testkit::toy::spill_dir("tlx-spill-test", name)
}

fn spill(name: &str, mode: SpillMode, f: impl FnOnce(&mut SpillConfig)) -> Spill {
    let mut cfg = SpillConfig { mode, dir: Some(test_dir(name)), ..Default::default() };
    f(&mut cfg);
    Spill::new(cfg)
}

/// Options with small blocks (4 KiB: 256 trace-log entries).
fn opts(workers: usize, spill: Spill) -> Options {
    let mut o = Options { workers, check_deadlock: false, spill, ..Default::default() };
    o.queue.seg_bytes = 4096;
    o
}

#[test]
fn spilled_trace_logs_give_the_same_results() {
    let m = Counters::new(120, Some((100, 37)), 1);
    for workers in [1, 4] {
        let plain = explore(&m, &opts(workers, Spill::new(SpillConfig { mode: SpillMode::Off, ..Default::default() })));
        let sp = spill("same", SpillMode::Always, |_| {});
        let r = explore(&m, &opts(workers, sp.clone()));
        assert_eq!(r.outcome, Outcome::InvariantViolated("NotBad".into()));
        assert_eq!(r.outcome, plain.outcome);
        // (Several workers stop at a violation after a varying amount of
        // work.)
        if workers == 1 {
            assert_eq!(r.stats, plain.stats);
        }
        assert_eq!(r.stats.depth, plain.stats.depth);
        let states = |t: &[tlx_runtime::TraceStep<(u32, u32)>]| t.iter().map(|s| s.state).collect::<Vec<_>>();
        assert_eq!(r.trace.len(), 138);
        if workers == 1 {
            assert_eq!(states(&r.trace), states(&plain.trace));
        }
        assert_eq!(r.trace.last().unwrap().state, (100, 37));
        let c = sp.counters();
        assert!(c.blocks >= 10 && c.read > 0, "{c:?}");
        // The trace was read back; the directory is gone with the logs.
        sp.wait_for_writes();
        sp.wait_for_reads();
        assert!(sp.dir().is_none());
        assert!(sp.error().is_none());
        // A complete search: the same statistics.
        let ok = Counters::new(120, None, 1);
        let sp = spill("same-ok", SpillMode::Always, |_| {});
        let r = explore(&ok, &opts(workers, sp.clone()));
        assert_eq!(r.outcome, Outcome::Ok);
        assert_eq!(r.stats, explore(&ok, &opts(workers, Spill::new(SpillConfig { mode: SpillMode::Off, ..Default::default() }))).stats);
        assert!(sp.counters().blocks > 0);
    }
}

#[test]
fn write_error_stops_the_search() {
    let m = Counters::new(200, None, 1);
    for workers in [1, 4] {
        let sp = spill("inject", SpillMode::Always, |c| c.fail_after = Some(64 << 10));
        let r = explore(&m, &opts(workers, sp.clone()));
        match &r.outcome {
            Outcome::Io(msg) => assert!(msg.contains("injected write error") && msg.contains("trace-"), "{msg}"),
            o => panic!("{o:?}"),
        }
        assert!(r.trace.is_empty());
        assert!(r.stats.distinct < 201 * 201, "the search stopped early");
    }
}

#[test]
fn disk_quota_stops_the_search() {
    let m = Counters::new(200, None, 1);
    let sp = spill("quota", SpillMode::Always, |c| c.maxdisk = Some(32 << 10));
    let r = explore(&m, &opts(2, sp.clone()));
    match &r.outcome {
        Outcome::Io(msg) => assert!(msg.contains("-maxdisk"), "{msg}"),
        o => panic!("{o:?}"),
    }
    assert!(sp.counters().peak <= 32 << 10);
}

/// Linear chain `0 -> 1 -> ... -> max` that sabotages `trace-0.spill` unlink on
/// the final state (by renaming it aside and creating a directory at its path,
/// causing `remove_file` to fail deterministically regardless of privileges).
struct SabotageTraceCleanup {
    max: u32,
    bad_at: Option<u32>,
    dir: PathBuf,
    spill: Spill,
    inv: Vec<String>,
    acts: Vec<String>,
}

impl Model for SabotageTraceCleanup {
    type State = u32;
    tlx_runtime::model_without_checks!();
    fn init_states(&self, out: &mut dyn FnMut(u32)) -> Result<(), ModelError> {
        out(0);
        Ok(())
    }
    fn successors(&self, &s: &u32, out: &mut dyn FnMut(u32, u32) -> bool) -> Result<(), ModelError> {
        if s < self.max {
            out(s + 1, 0);
        }
        Ok(())
    }
    fn fingerprint(&self, &s: &u32) -> u64 {
        (s as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0x5A5A
    }
    fn check_invariants(&self, &s: &u32) -> Result<Option<usize>, ModelError> {
        if s == self.max {
            self.spill.wait_for_writes();
            let target = std::fs::read_dir(&self.dir)
                .unwrap()
                .flatten()
                .map(|e| e.path())
                .find(|p| p.file_name().and_then(|n| n.to_str()).is_some_and(|n| n.starts_with("trace-") && n.ends_with(".spill")))
                .expect("expected a spilled trace-*.spill file in metadir");
            let retained = self.dir.join("retained-trace.spill");
            std::fs::rename(&target, &retained).unwrap();
            std::fs::create_dir(&target).unwrap();
        }
        Ok((self.bad_at == Some(s)).then_some(0))
    }
    fn invariant_names(&self) -> &[String] {
        &self.inv
    }
    fn action_names(&self) -> &[String] {
        &self.acts
    }
    fn render(&self, s: &u32) -> String {
        format!("x = {s}")
    }
}

#[test]
fn cleanup_unlink_error_surfaces_on_ok_and_preserves_model_failure_precedence() {
    // 1. Otherwise successful run: final trace-store unlink failure must return
    //    `Outcome::Io` instead of `Outcome::Ok`.
    let scratch_ok = tlx_testkit::TempDir::new("spill-cleanup-ok");
    let dir_ok = scratch_ok.child_path("meta");
    let sp_ok = Spill::new(SpillConfig { mode: SpillMode::Always, dir: Some(dir_ok.clone()), ..Default::default() });
    let m_ok = SabotageTraceCleanup {
        max: 5000,
        bad_at: None,
        dir: dir_ok,
        spill: sp_ok.clone(),
        inv: vec!["Inv".into()],
        acts: vec!["Step".into()],
    };
    let r_ok = explore(&m_ok, &opts(1, sp_ok.clone()));
    sp_ok.wait_for_writes();
    sp_ok.wait_for_reads();
    match &r_ok.outcome {
        Outcome::Io(msg) => assert!(msg.contains("cannot remove the spill file") && msg.contains("trace-"), "{msg}"),
        other => panic!("expected Outcome::Io for failed final spill unlink, got {other:?}"),
    }

    // 2. Model failure precedence: an invariant violation must not be replaced
    //    by a subsequent cleanup unlink error.
    let scratch_inv = tlx_testkit::TempDir::new("spill-cleanup-inv");
    let dir_inv = scratch_inv.child_path("meta");
    let sp_inv = Spill::new(SpillConfig { mode: SpillMode::Always, dir: Some(dir_inv.clone()), ..Default::default() });
    let m_inv = SabotageTraceCleanup {
        max: 5000,
        bad_at: Some(5000),
        dir: dir_inv,
        spill: sp_inv.clone(),
        inv: vec!["Inv".into()],
        acts: vec!["Step".into()],
    };
    let r_inv = explore(&m_inv, &opts(1, sp_inv.clone()));
    assert_eq!(r_inv.outcome, Outcome::InvariantViolated("Inv".into()));
    sp_inv.wait_for_writes();
    sp_inv.wait_for_reads();
    assert!(sp_inv.error().is_some_and(|e| e.0.contains("cannot remove the spill file")), "expected cleanup error to be triggered on drop");
}

#[test]
fn memory_pressure_spills_trace_logs() {
    // A budget far below what the process uses: stage 2 starts at once.
    let m = Counters::new(1000, Some((999, 990)), 1);
    let plain = explore(&m, &opts(1, Spill::new(SpillConfig { mode: SpillMode::Off, ..Default::default() })));
    for workers in [1, 3] {
        let sp = spill("pressure", SpillMode::Auto, |_| {});
        let mut o = opts(workers, sp.clone());
        o.maxmem = 1 << 20;
        o.fp = FpConfig::fixed_mib(32);
        let r = explore(&m, &o);
        assert_eq!(r.outcome, plain.outcome);
        if workers == 1 {
            assert_eq!(r.stats, plain.stats);
        }
        assert_eq!(r.trace.len(), plain.trace.len());
        assert!(sp.counters().blocks > 0, "{:?}", sp.counters());
        assert!(sp.error().is_none());
        sp.wait_for_writes();
        sp.wait_for_reads();
        assert!(sp.dir().is_none());
    }
    // `-spill off`: nothing written.
    let sp = Spill::new(SpillConfig { mode: SpillMode::Off, dir: Some(test_dir("off")), ..Default::default() });
    let mut o = opts(1, sp.clone());
    o.maxmem = 1 << 20;
    o.fp = FpConfig::fixed_mib(32);
    let r = explore(&m, &o);
    assert_eq!(r.outcome, plain.outcome);
    assert_eq!(sp.counters().blocks, 0);
}

/// `n` initial states (counters `(i, 0)`) and their successors `(i, 1)`;
/// records the blocks written to the spill directory when the initial
/// states are all generated.
struct ManyInits {
    n: u32,
    spill: Spill,
    blocks_after_init: AtomicU64,
    inv: Vec<String>,
    acts: Vec<String>,
}

impl Model for ManyInits {
    type State = (u32, u32);
    tlx_runtime::model_without_checks!();
    fn init_states(&self, out: &mut dyn FnMut((u32, u32))) -> Result<(), ModelError> {
        for i in 0..self.n {
            out((i, 0));
        }
        self.blocks_after_init.store(self.spill.counters().blocks, Ordering::SeqCst);
        Ok(())
    }
    fn successors(&self, s: &(u32, u32), out: &mut dyn FnMut((u32, u32), u32) -> bool) -> Result<(), ModelError> {
        if s.1 == 0 {
            out((s.0, 1), 0);
        }
        Ok(())
    }
    fn fingerprint(&self, s: &(u32, u32)) -> u64 {
        ((s.0 as u64) << 32 | s.1 as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0x1234
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
        format!("/\\ x = {}\n/\\ y = {}", s.0, s.1)
    }
}

#[test]
fn memory_pressure_applies_while_generating_initial_states() {
    // A budget far below what the process uses: the trace log of the
    // initial states goes to disk while they are generated, not only once
    // the workers start.
    for workers in [1, 3] {
        let sp = spill("init", SpillMode::Auto, |_| {});
        let m =
            ManyInits { n: 200_000, spill: sp.clone(), blocks_after_init: AtomicU64::new(0), inv: Vec::new(), acts: vec!["Next".into()] };
        let mut o = opts(workers, sp.clone());
        o.maxmem = 1 << 20;
        o.fp = FpConfig::fixed_mib(32);
        let r = explore(&m, &o);
        assert_eq!(r.outcome, Outcome::Ok);
        assert_eq!((r.stats.distinct, r.stats.depth), (400_000, 2));
        assert!(m.blocks_after_init.load(Ordering::SeqCst) > 0, "nothing spilled during the initial states: {:?}", sp.counters());
        assert!(sp.error().is_none());
    }
}
