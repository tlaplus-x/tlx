//! Counting the coverage with several workers chooses the representatives
//! in BFS order (`explore::order`) and records the liveness behavior graph
//! too: the graph is the one worker's up to node numbering, the
//! coverage counts are the same, and an atom of the tableaux that fails on
//! a new state is reported (or interrupts the search) as with one worker.

use tlx_runtime::{explore, AtomBits, Caps, Effects, Model, ModelError, Options, Outcome, Report};
use tlx_testkit::report::{project, ComparisonPolicy, Projection, TracePolicy};

type S = (u32, u32);

/// A grid `0..=n` x `0..=n` with steps `x + 1`, `y + 1` and both; from the
/// last column, `x + 1` leaves the model (the constraint). Every state but
/// the corners is found by several actions, so the coverage credits the
/// representative's. Expanding a state costs about `spin` iterations of a
/// busy loop, so that levels are expanded in parallel.
struct Grid {
    n: u32,
    spin: u32,
    /// Evaluating the atoms of the tableaux on this state fails, with
    /// this message ("miss" interrupts the search, as a layout miss).
    trap: Option<(S, &'static str)>,
    inv: Vec<String>,
    acts: Vec<String>,
}

impl Grid {
    fn new(n: u32, spin: u32) -> Grid {
        Grid { n, spin, trap: None, inv: Vec::new(), acts: vec!["X".into(), "Y".into(), "XY".into()] }
    }
}

impl Model for Grid {
    type State = S;
    fn init_states(&self, out: &mut dyn FnMut(S)) -> Result<(), ModelError> {
        out((0, 0));
        out((0, 1));
        Ok(())
    }
    fn successors(&self, s: &S, out: &mut dyn FnMut(S, u32) -> bool) -> Result<(), ModelError> {
        let mut h = s.0 as u64;
        for i in 0..self.spin {
            h = std::hint::black_box(h.wrapping_mul(31).wrapping_add(i as u64));
        }
        let (x, y) = *s;
        let _ = (y < self.n && !out((x, y + 1), 1))
            || (x <= self.n && !out((x + 1, y), 0))
            || (x < self.n && y < self.n && !out((x + 1, y + 1), 2));
        Ok(())
    }
    fn fingerprint(&self, s: &S) -> u64 {
        ((s.0 as u64) << 32 | s.1 as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0x2468
    }
    fn coarse_fingerprint(&self) -> bool {
        false
    }
    fn check_invariants(&self, _s: &S) -> Result<Option<usize>, ModelError> {
        Ok(None)
    }
    fn check_init_property(&self, _s: &S) -> Result<Option<String>, ModelError> {
        Ok(None)
    }
    fn constraint(&self, s: &S) -> Result<bool, ModelError> {
        Ok(s.0 <= self.n)
    }
    fn action_constraint(&self, _s: &S, _t: &S) -> Result<bool, ModelError> {
        Ok(true)
    }
    fn check_transition(&self, _s: &S, _t: &S) -> Result<Option<usize>, ModelError> {
        Ok(None)
    }
    fn action_property_names(&self) -> &[String] {
        &[]
    }
    fn extra_generated(&self) -> u64 {
        0
    }
    fn stop_requested(&self) -> bool {
        false
    }
    fn invariant_names(&self) -> &[String] {
        &self.inv
    }
    fn action_names(&self) -> &[String] {
        &self.acts
    }
    fn render(&self, s: &S) -> String {
        format!("/\\ x = {}\n/\\ y = {}", s.0, s.1)
    }
    fn caps(&self) -> Caps<'_, S> {
        Caps { format: None, live_atoms: Some(self), effects: Some(self), checkpoint: None, gc: None }
    }
}

impl Effects for Grid {
    fn interrupts(&self, e: &ModelError) -> bool {
        e.message == "miss"
    }
}

/// State atom 0: `x + y` divisible by 3; 1: some step increments `x`
/// (ENABLED, from the steps); action atom 0: the step increments `x`.
impl AtomBits<S> for Grid {
    fn state(&self, s: &S, out: &[&[u64]]) -> Result<Vec<u64>, ModelError> {
        let inc = out.iter().any(|b| b[0] & 1 == 1);
        Ok(vec![u64::from((s.0 + s.1).is_multiple_of(3)) | u64::from(inc) << 1])
    }
    fn action(&self, s: &S, t: &S) -> Result<Vec<u64>, ModelError> {
        Ok(vec![u64::from(t.0 > s.0)])
    }
    fn tableau(&self, t: &S) -> Result<(), ModelError> {
        match self.trap {
            Some((at, message)) if at == *t => Err(ModelError::new(message)),
            _ => Ok(()),
        }
    }
}

fn opts(workers: usize, coverage: bool) -> Options {
    Options { workers, coverage, check_deadlock: false, ..Default::default() }
}

/// What must not depend on the number of workers.
fn summary(r: &Report<S>) -> Projection<S> {
    project(r, ComparisonPolicy { trace: TracePolicy::Ignore, coverage_graph: true, ..ComparisonPolicy::COUNTS_AND_LENGTH })
}

#[test]
fn counting_coverage_records_the_one_worker_graph() {
    let m = Grid::new(60, 2000);
    let one = summary(&explore(&m, &opts(1, true)));
    assert_eq!(one.outcome, Outcome::Ok);
    assert!(one.graph.as_ref().is_some_and(|g| g.nodes.len() == 61 * 61), "the graph of one worker");
    // (Without counting: the same graph, with the first inserters.)
    assert_eq!(summary(&explore(&m, &opts(4, false))).graph, one.graph);
    for workers in [2, 4] {
        for run in 0..3 {
            assert_eq!(summary(&explore(&m, &opts(workers, true))), one, "{workers} workers, run {run}");
        }
    }
}

#[test]
fn tableau_atom_errors_on_representatives() {
    // An error: reported by liveness (no graph), the search goes on.
    let m = Grid { trap: Some(((7, 5), "boom")), ..Grid::new(30, 500) };
    let one = summary(&explore(&m, &opts(1, true)));
    assert_eq!(one.outcome, Outcome::Ok);
    assert_eq!(one.graph, None);
    assert_eq!(one.live_error.as_deref(), Some("boom"));
    for workers in [2, 4] {
        assert_eq!(summary(&explore(&m, &opts(workers, true))), one, "{workers} workers");
    }
    // An error that interrupts the search (a layout miss): it stops there.
    let m = Grid { trap: Some(((7, 5), "miss")), ..Grid::new(30, 500) };
    for workers in [1, 2, 4] {
        let r = explore(&m, &opts(workers, true));
        assert!(matches!(&r.outcome, Outcome::Error(e) if e.message == "miss"), "{workers} workers: {:?}", r.outcome);
        assert!(r.live_graph.is_none());
    }
}
