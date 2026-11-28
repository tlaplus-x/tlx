//! Explicit comparison policies for runtime reports. Elapsed time and trace
//! actions are intentionally absent: the migrated tests compared state traces.
use tlx_runtime::{Coverage, Outcome, Outdegree, Report};

use crate::toy::{canon, Canon};

#[derive(Clone, Copy, Debug)]
pub enum Counts {
    Always,
    OnSuccess,
    Ignore,
}

impl Counts {
    fn includes(self, outcome: &Outcome) -> bool {
        match self {
            Self::Always => true,
            Self::OnSuccess => *outcome == Outcome::Ok,
            Self::Ignore => false,
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum TracePolicy {
    Ignore,
    Length,
    LengthAndLast,
    States,
}

/// Counts after a parallel failure depend on how far its level was expanded.
/// Select each statistic separately: checkpoint tests also compare queued states,
/// while safepoint tests compare outdegree only after a complete search.
#[derive(Clone, Copy, Debug)]
pub struct ComparisonPolicy {
    pub counts: Counts,
    pub left: Counts,
    pub outdegree: Counts,
    pub init_distinct: bool,
    pub trace: TracePolicy,
    pub coverage_graph: bool,
}

impl ComparisonPolicy {
    pub const COUNTS_AND_LENGTH: Self = Self {
        counts: Counts::Always,
        left: Counts::Ignore,
        outdegree: Counts::Ignore,
        init_distinct: false,
        trace: TracePolicy::Length,
        coverage_graph: false,
    };
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateCounts {
    pub distinct: u64,
    pub generated: u64,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Trace<S> {
    Ignored,
    Length(usize),
    LengthAndLast { length: usize, last: Option<S> },
    States(Vec<S>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Projection<S> {
    pub outcome: Outcome,
    pub depth: u32,
    pub counts: Option<StateCounts>,
    pub left: Option<u64>,
    pub outdegree: Option<Outdegree>,
    pub init_distinct: Option<u64>,
    pub trace: Trace<S>,
    pub coverage: Option<Coverage>,
    pub graph: Option<Canon>,
    pub live_error: Option<String>,
}

pub fn project<S: Clone>(report: &Report<S>, policy: ComparisonPolicy) -> Projection<S> {
    let trace = match policy.trace {
        TracePolicy::Ignore => Trace::Ignored,
        TracePolicy::Length => Trace::Length(report.trace.len()),
        TracePolicy::LengthAndLast => {
            Trace::LengthAndLast { length: report.trace.len(), last: report.trace.last().map(|t| t.state.clone()) }
        }
        TracePolicy::States => Trace::States(report.trace.iter().map(|t| t.state.clone()).collect()),
    };
    Projection {
        outcome: report.outcome.clone(),
        depth: report.stats.depth,
        counts: policy
            .counts
            .includes(&report.outcome)
            .then_some(StateCounts { distinct: report.stats.distinct, generated: report.stats.generated }),
        left: policy.left.includes(&report.outcome).then_some(report.stats.left),
        outdegree: policy.outdegree.includes(&report.outcome).then_some(report.stats.outdegree),
        init_distinct: policy.init_distinct.then_some(report.stats.init_distinct),
        trace,
        coverage: policy.coverage_graph.then(|| report.coverage.clone()).flatten(),
        graph: policy
            .coverage_graph
            .then(|| report.live_graph.as_ref().map(|g| canon(g.as_ref().expect("a graph in the budget"))))
            .flatten(),
        live_error: policy.coverage_graph.then(|| report.live_error.as_ref().map(|e| e.message.clone())).flatten(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tlx_runtime::{explore, LiveGraph, ModelError, Options, TraceStep};

    fn fixture() -> Report<u32> {
        let mut r = explore(&crate::toy::Counters::new(1, None, 1), &Options { check_deadlock: false, ..Default::default() });
        let mut graph = LiveGraph {
            init: vec![0, 0],
            fps: vec![17, 23],
            off: vec![0, 2, 3],
            tgt: vec![1, 0, 1],
            state_pat: vec![0, 1],
            state_pats: vec![vec![1].into(), vec![2].into()],
            action_pats: vec![vec![4].into(), vec![8].into()],
            ..Default::default()
        };
        for id in [0, 1, 0] {
            graph.edge_pat.push(id);
        }
        r.live_graph = Some(Ok(graph));
        Report {
            stats: r.stats,
            outcome: r.outcome,
            trace: vec![
                TraceStep { state: 0, action: None },
                TraceStep { state: 1, action: Some(0) },
                TraceStep { state: 2, action: Some(1) },
            ],
            trace_note: None,
            trace_store_full: false,
            elapsed: r.elapsed,
            in_init: false,
            live_graph: r.live_graph,
            live_witness: r.live_witness,
            live_error: None,
            live_atoms_ok: true,
            coverage: Some(Coverage { init_generated: 2, generated: vec![3, 4], distinct: vec![1, 2] }),
            frontier_peak: 0,
        }
    }

    const MUTATIONS: &[fn(&mut Report<u32>)] = &[
        |r| r.outcome = Outcome::Deadlock,
        |r| r.stats.depth += 1,
        |r| r.stats.distinct += 1,
        |r| r.stats.generated += 1,
        |r| r.stats.left += 1,
        |r| r.stats.init_distinct += 1,
        |r| r.stats.outdegree.min += 1,
        |r| r.stats.outdegree.max += 1,
        |r| r.stats.outdegree.mean += 1,
        |r| r.stats.outdegree.p95 += 1,
        |r| r.trace[1].state += 7,
        |r| {
            r.trace.pop();
        },
        |r| r.coverage.as_mut().unwrap().init_generated += 1,
        |r| r.coverage.as_mut().unwrap().generated[0] += 1,
        |r| r.coverage.as_mut().unwrap().distinct[0] += 1,
        |r| r.coverage = None,
        |r| r.live_graph = None,
        |r| r.live_graph.as_mut().unwrap().as_mut().unwrap().init.push(1),
        |r| r.live_graph.as_mut().unwrap().as_mut().unwrap().fps[0] += 1,
        |r| r.live_graph.as_mut().unwrap().as_mut().unwrap().state_pats[0][0] += 1,
        |r| r.live_graph.as_mut().unwrap().as_mut().unwrap().tgt.swap(0, 1),
        |r| r.live_graph.as_mut().unwrap().as_mut().unwrap().action_pats[0][0] += 1,
        |r| r.live_error = Some(ModelError::new("atom failure")),
    ];

    #[test]
    fn every_selected_report_field_rejects_a_difference() {
        let all = ComparisonPolicy {
            left: Counts::Always,
            outdegree: Counts::Always,
            init_distinct: true,
            trace: TracePolicy::States,
            coverage_graph: true,
            ..ComparisonPolicy::COUNTS_AND_LENGTH
        };
        let want = project(&fixture(), all);
        for (i, mutate) in MUTATIONS.iter().enumerate() {
            let mut different = fixture();
            mutate(&mut different);
            assert_ne!(project(&different, all), want, "mutation {i} escaped");
        }
    }

    #[test]
    fn trace_policies_preserve_length_endpoint_and_full_state_contracts() {
        let r = fixture();
        let mut middle = fixture();
        middle.trace[1].state = 99;
        let mut last = fixture();
        last.trace.last_mut().unwrap().state = 99;
        let mut shorter = fixture();
        shorter.trace.remove(1);
        for (trace, rejects_middle, rejects_last, rejects_length) in [
            (TracePolicy::Ignore, false, false, false),
            (TracePolicy::Length, false, false, true),
            (TracePolicy::LengthAndLast, false, true, true),
            (TracePolicy::States, true, true, true),
        ] {
            let policy = ComparisonPolicy { trace, ..ComparisonPolicy::COUNTS_AND_LENGTH };
            let want = project(&r, policy);
            assert_eq!(project(&middle, policy) != want, rejects_middle);
            assert_eq!(project(&last, policy) != want, rejects_last);
            assert_eq!(project(&shorter, policy) != want, rejects_length);
            let mut empty = fixture();
            empty.trace.clear();
            assert_eq!(project(&empty, policy) != want, rejects_length);
        }
    }

    #[test]
    fn parallel_failure_masks_only_selected_statistics() {
        for outcome in [Outcome::Ok, Outcome::Deadlock, Outcome::InvariantViolated("Inv".into())] {
            for counts in [Counts::Always, Counts::OnSuccess, Counts::Ignore] {
                let policy = ComparisonPolicy { counts, left: counts, outdegree: counts, ..ComparisonPolicy::COUNTS_AND_LENGTH };
                let mut r = fixture();
                r.outcome = outcome.clone();
                let want = project(&r, policy);
                r.stats.distinct += 1;
                r.stats.generated += 1;
                r.stats.left += 1;
                r.stats.outdegree.max += 1;
                let included = match counts {
                    Counts::Always => true,
                    Counts::OnSuccess => outcome == Outcome::Ok,
                    Counts::Ignore => false,
                };
                assert_eq!(project(&r, policy) != want, included);
                r.stats.depth += 1;
                assert_ne!(project(&r, policy), want, "depth always matters");
            }
        }
    }
    // Independent copies of the former tuple assertions are intentionally kept
    // only here as migration oracles. Runtime consumers use the named policy.
    fn states(r: &Report<u32>) -> Vec<u32> {
        r.trace.iter().map(|t| t.state).collect()
    }
    fn counts(r: &Report<u32>) -> (u64, u64) {
        (r.stats.distinct, r.stats.generated)
    }
    fn successful_counts(r: &Report<u32>) -> Option<(u64, u64)> {
        (r.outcome == Outcome::Ok).then(|| counts(r))
    }
    fn successful_outdegree(r: &Report<u32>) -> Option<(u64, u64, Outdegree)> {
        (r.outcome == Outcome::Ok).then_some((r.stats.distinct, r.stats.generated, r.stats.outdegree))
    }
    fn legacy_graph(r: &Report<u32>) -> Option<String> {
        r.live_graph.as_ref().map(|g| {
            let g = g.as_ref().unwrap();
            let init: Vec<_> = g.init.iter().map(|&i| g.fps[i as usize]).collect();
            let mut nodes: Vec<_> = (0..g.len())
                .map(|i| {
                    let edges: Vec<_> = (g.off[i]..g.off[i + 1])
                        .map(|e| (g.fps[g.tgt[e] as usize], g.action_pats[g.edge_pat.get(e) as usize].to_vec()))
                        .collect();
                    (g.fps[i], g.state_pats[g.state_pat[i] as usize].to_vec(), edges)
                })
                .collect();
            nodes.sort_by_key(|n| n.0);
            format!("{:?}", (init, nodes))
        })
    }

    #[test]
    fn old_and_named_assertion_ledger_agrees() {
        type Legacy = fn(&Report<u32>) -> String;
        let base = ComparisonPolicy::COUNTS_AND_LENGTH;
        let parallel = ComparisonPolicy { counts: Counts::OnSuccess, ..base };
        let exact = ComparisonPolicy { left: Counts::Always, trace: TracePolicy::States, ..base };
        let ledger: &[(&str, ComparisonPolicy, Legacy)] = &[
            ("checkpoint/exact", exact, |r| {
                format!(
                    "{:?}",
                    (&r.outcome, r.stats.depth, Some((r.stats.distinct, r.stats.generated, r.stats.left)), states(r), r.trace.len())
                )
            }),
            ("checkpoint/parallel", ComparisonPolicy { left: Counts::OnSuccess, ..parallel }, |r| {
                format!(
                    "{:?}",
                    (
                        &r.outcome,
                        r.stats.depth,
                        (r.outcome == Outcome::Ok).then_some((r.stats.distinct, r.stats.generated, r.stats.left)),
                        Vec::<u32>::new(),
                        r.trace.len()
                    )
                )
            }),
            ("coarse_order", ComparisonPolicy { outdegree: Counts::Always, ..base }, |r| {
                format!("{:?}", (&r.outcome, r.stats.distinct, r.stats.generated, r.stats.depth, r.stats.outdegree, r.trace.len()))
            }),
            ("explore/bfs", ComparisonPolicy { trace: TracePolicy::LengthAndLast, ..parallel }, |r| {
                format!("{:?}", (&r.outcome, r.stats.depth, successful_counts(r), r.trace.len(), states(r).last()))
            }),
            (
                "explore/resume",
                ComparisonPolicy { outdegree: Counts::OnSuccess, init_distinct: true, trace: TracePolicy::LengthAndLast, ..parallel },
                |r| {
                    format!(
                        "{:?}",
                        (&r.outcome, r.stats.depth, r.stats.init_distinct, successful_outdegree(r), r.trace.len(), states(r).last())
                    )
                },
            ),
            ("fpset_disk", base, |r| format!("{:?}", (&r.outcome, r.stats.distinct, r.stats.generated, r.stats.depth, r.trace.len()))),
            ("ordered_edges", ComparisonPolicy { trace: TracePolicy::Ignore, coverage_graph: true, ..base }, |r| {
                format!(
                    "{:?}",
                    (
                        &r.outcome,
                        r.stats.distinct,
                        r.stats.generated,
                        r.stats.depth,
                        &r.coverage,
                        legacy_graph(r),
                        r.live_error.as_ref().map(|e| &e.message)
                    )
                )
            }),
            ("queue/exact", exact, |r| format!("{:?}", (&r.outcome, r.stats.depth, Some(counts(r)), r.stats.left, states(r)))),
            ("queue/parallel-states", ComparisonPolicy { trace: TracePolicy::States, ..parallel }, |r| {
                format!("{:?}", (&r.outcome, r.stats.depth, successful_counts(r), 0, states(r)))
            }),
            ("queue/parallel-last", ComparisonPolicy { trace: TracePolicy::LengthAndLast, ..parallel }, |r| {
                format!("{:?}", (&r.outcome, r.stats.depth, successful_counts(r), r.trace.len(), states(r).last()))
            }),
            ("queue/parallel-length", parallel, |r| format!("{:?}", (&r.outcome, r.stats.depth, successful_counts(r), r.trace.len()))),
            ("queue/counts-only", ComparisonPolicy { trace: TracePolicy::Ignore, ..parallel }, |r| {
                format!("{:?}", (&r.outcome, r.stats.depth, successful_counts(r)))
            }),
            ("safepoint", ComparisonPolicy { outdegree: Counts::OnSuccess, trace: TracePolicy::LengthAndLast, ..parallel }, |r| {
                format!("{:?}", (&r.outcome, r.stats.depth, successful_outdegree(r), r.trace.len(), states(r).last()))
            }),
        ];
        let mut comparisons = 0;
        for (name, policy, old) in ledger {
            for outcome in [Outcome::Ok, Outcome::Deadlock, Outcome::InvariantViolated("Inv".into())] {
                for mutate in MUTATIONS.iter().chain([(|_: &mut Report<u32>| {}) as fn(&mut Report<u32>)].iter()) {
                    let mut left = fixture();
                    left.outcome = outcome.clone();
                    let mut right = fixture();
                    right.outcome = outcome.clone();
                    mutate(&mut right);
                    assert_eq!(project(&left, *policy) == project(&right, *policy), old(&left) == old(&right), "{name} / {outcome:?}");
                    comparisons += 1;
                }
            }
        }
        assert_eq!(comparisons, 13 * 3 * 24);
    }

    #[test]
    fn canonical_graph_retains_order_and_multiplicity_across_node_numbering() {
        let original = fixture().live_graph.unwrap().unwrap();
        let mut renumbered = fixture().live_graph.unwrap().unwrap();
        renumbered.fps.reverse();
        renumbered.state_pat.reverse();
        renumbered.init = vec![1, 1];
        renumbered.off = vec![0, 1, 3];
        renumbered.tgt = vec![0, 0, 1];
        renumbered.edge_pat = Default::default();
        for id in [0, 0, 1] {
            renumbered.edge_pat.push(id);
        }
        assert_eq!(canon(&original), canon(&renumbered));
        renumbered.init.pop();
        assert_ne!(canon(&original), canon(&renumbered), "initial multiplicity matters");
    }
}
