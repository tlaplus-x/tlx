//! The fingerprint set's disk tier in searches (docs/scale.md §4.2):
//! a set of small tables rotating to disk gives the results of the
//! in-memory set with any number of workers (the same traces with one), also
//! under memory pressure, when resuming, and with the representatives of a
//! coarse fingerprint; IO errors stop the search with `Outcome::Io`.

use std::path::PathBuf;
use tlx_testkit::report::{project, ComparisonPolicy, Projection};

use tlx_runtime::io::{Spill, SpillConfig, SpillMode};
use tlx_runtime::{explore, explore_resumable, FpConfig, Model, ModelError, Options, Outcome, Report};

type S = (u32, u32, u32);

/// Three counters below `n`: increments, and a jump back that finds old
/// states again (duplicates from far earlier levels). `bad` violates the
/// invariant; checking `trap` fails (an evaluation error).
struct Mesh {
    n: u32,
    bad: Option<S>,
    trap: Option<S>,
    inv: Vec<String>,
    acts: Vec<String>,
}

impl Mesh {
    fn new(n: u32) -> Mesh {
        Mesh { n, bad: None, trap: None, inv: vec!["Inv".into()], acts: vec!["A".into(), "B".into(), "C".into(), "Back".into()] }
    }
}

impl Model for Mesh {
    type State = S;
    tlx_runtime::model_without_checks!();
    fn init_states(&self, out: &mut dyn FnMut(S)) -> Result<(), ModelError> {
        out((0, 0, 0));
        out((1, 0, 0));
        Ok(())
    }
    fn successors(&self, s: &S, out: &mut dyn FnMut(S, u32) -> bool) -> Result<(), ModelError> {
        let (a, b, c) = *s;
        let n = self.n;
        if a + 1 < n && !out((a + 1, b, c), 0) {
            return Ok(());
        }
        if b + 1 < n && !out((a, b + 1, c), 1) {
            return Ok(());
        }
        if c + 1 < n && !out((a, b, c + 1), 2) {
            return Ok(());
        }
        out((a / 2, b, c / 3), 3);
        Ok(())
    }
    fn fingerprint(&self, s: &S) -> u64 {
        let x = (s.0 as u64) << 40 | (s.1 as u64) << 20 | s.2 as u64;
        let x = (x ^ (x >> 31)).wrapping_mul(0x9E37_79B9_7F4A_7C15);
        x ^ (x >> 29)
    }
    fn check_invariants(&self, s: &S) -> Result<Option<usize>, ModelError> {
        if Some(*s) == self.trap {
            return Err(ModelError::new("trapped"));
        }
        Ok((Some(*s) == self.bad).then_some(0))
    }
    fn invariant_names(&self) -> &[String] {
        &self.inv
    }
    fn action_names(&self) -> &[String] {
        &self.acts
    }
    fn render(&self, s: &S) -> String {
        format!("/\\ a = {}\n/\\ b = {}\n/\\ c = {}", s.0, s.1, s.2)
    }
}

/// A fresh spill directory for a test.
fn test_dir(name: &str) -> PathBuf {
    tlx_testkit::toy::spill_dir("tlx-fpset-disk", name)
}

fn spill(name: &str, mode: SpillMode, maxdisk: Option<u64>, fail_after: Option<u64>) -> Spill {
    Spill::new(SpillConfig { mode, dir: Some(test_dir(name)), maxdisk, fail_after, ..Default::default() })
}

/// The disk tier from the start, with the smallest tables (1024 slots: a
/// rotation every 768 new states).
fn forced(workers: usize, name: &str) -> Options {
    Options {
        workers,
        check_deadlock: false,
        fp: FpConfig::default().with_disk_slots(1024),
        spill: spill(name, SpillMode::Always, None, None),
        ..Default::default()
    }
}

fn memory(workers: usize) -> Options {
    Options { workers, check_deadlock: false, spill: spill("mem", SpillMode::Off, None, None), ..Default::default() }
}

/// The number of rotations to disk and merges of runs so far (all tests
/// of this process: they only add to them).
fn disk_counts() -> (u64, u64) {
    tlx_runtime::stats::enable(8);
    let count = |k: &str| match tlx_runtime::stats::metric(k) {
        Some(tlx_runtime::stats::Metric::Count(n)) => n,
        _ => 0,
    };
    (count("fpset rotations to disk"), count("fpset run merges"))
}

/// What must not depend on where the fingerprints are.
fn summary(r: &Report<S>) -> Projection<S> {
    project(r, ComparisonPolicy::COUNTS_AND_LENGTH)
}

/// The results of the in-memory set, with 1, 3 and 8 workers; with one
/// worker the same counts at an early stop and the same trace.
#[test]
fn rotating_to_disk_gives_the_same_results() {
    let m = Mesh::new(24);
    let want = summary(&explore(&m, &memory(1)));
    assert_eq!(want.outcome, Outcome::Ok);
    assert!(want.counts.as_ref().unwrap().distinct > 10_000, "{want:?}");
    for workers in [1, 3, 8] {
        let (rotations, merges) = disk_counts();
        let o = forced(workers, "same");
        let r = explore(&m, &o);
        assert_eq!(summary(&r), want, "{workers} workers");
        // (Everything written was given back, once the IO threads have
        // dropped the stores of the requests they finished.)
        o.spill.wait_for_writes();
        o.spill.wait_for_reads();
        assert_eq!(o.spill.counters().used, 0);
        // (It did go to disk: how often depends on when the workers reach
        // the safepoints that rotate, so only that it happened.)
        let (r2, m2) = disk_counts();
        assert!(r2 > rotations + 1 && m2 > merges, "{rotations} -> {r2} rotations, {merges} -> {m2} merges");
    }
    // A violation deep in the search: the counts at the stop, the trace.
    let bad = Mesh { bad: Some((20, 17, 23)), ..Mesh::new(24) };
    let r1 = explore(&bad, &memory(1));
    assert_eq!(r1.outcome, Outcome::InvariantViolated("Inv".into()));
    let r = explore(&bad, &forced(1, "violation"));
    assert_eq!(summary(&r), summary(&r1));
    assert_eq!(r.trace.iter().map(|t| t.state).collect::<Vec<_>>(), r1.trace.iter().map(|t| t.state).collect::<Vec<_>>());
    for workers in [3, 8] {
        let r = explore(&bad, &forced(workers, "violation"));
        // Parallel failures compare verdict and shortest length, without counts or exact states.
        assert_eq!(r.outcome, r1.outcome, "{workers} workers");
        assert_eq!(r.trace.len(), r1.trace.len(), "{workers} workers");
    }
}

/// A small memory budget makes the set rotate (stage 5 of memory
/// pressure); the results do not change. With `-spill off` the same budget
/// fills the set.
#[test]
fn memory_pressure_rotates_to_disk() {
    let m = Mesh::new(40);
    let want = summary(&explore(&m, &memory(1)));
    for workers in [1, 4] {
        let o = Options {
            maxmem: 1 << 20,
            fp: FpConfig::growing(1 << 20).with_initial(1024),
            spill: spill("budget", SpillMode::Auto, None, None),
            ..memory(workers)
        };
        let (rotations, _) = disk_counts();
        assert_eq!(summary(&explore(&m, &o)), want, "{workers} workers");
        assert!(disk_counts().0 > rotations, "{workers} workers");
        let off = Options { spill: spill("budget-off", SpillMode::Off, None, None), ..o };
        assert!(matches!(explore(&m, &off).outcome, Outcome::FpSetFull { .. }), "{workers} workers");
    }
}

/// Resuming from a resume point (a layout miss) into a set that rotates to
/// disk: the results of the search that did not stop.
#[test]
fn resuming_into_the_disk_tier() {
    let m = Mesh::new(24);
    let want = summary(&explore(&m, &memory(1)));
    for workers in [1, 4] {
        let trapped = Mesh { trap: Some((10, 12, 9)), ..Mesh::new(24) };
        let (r, c) = explore_resumable(&trapped, &forced(workers, "trap"), None, Some(usize::MAX));
        assert!(matches!(&r.outcome, Outcome::Error(e) if e.message == "trapped"), "{:?}", r.outcome);
        let from = c.expect("resume point").try_map(2, Ok::<_, ()>).unwrap();
        let (r, c) = explore_resumable(&m, &forced(workers, "resumed"), Some(from), None);
        assert!(c.is_none());
        assert_eq!(summary(&r), want, "{workers} workers");
    }
}

/// IO errors while rotating (an injected write error, `-maxdisk`) stop the
/// search with `Outcome::Io`.
#[test]
fn io_errors_stop_the_search() {
    let m = Mesh::new(24);
    for workers in [1, 4] {
        let o = Options { spill: spill("fail", SpillMode::Always, None, Some(64 << 10)), ..forced(workers, "") };
        let r = explore(&m, &o);
        let Outcome::Io(msg) = &r.outcome else { panic!("{:?} with {workers} workers", r.outcome) };
        assert!(msg.contains("injected write error"), "{msg}");
        assert!(r.trace.is_empty());
        let o = Options { spill: spill("maxdisk", SpillMode::Always, Some(48 << 10), None), ..forced(workers, "") };
        let r = explore(&m, &o);
        let Outcome::Io(msg) = &r.outcome else { panic!("{:?} with {workers} workers", r.outcome) };
        assert!(msg.contains("-maxdisk"), "{msg}");
    }
}
