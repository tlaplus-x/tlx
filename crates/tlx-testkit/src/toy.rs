use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use tlx_runtime::{LiveGraph, Model, ModelError};

pub struct Counters {
    n: u32,
    init_copies: usize,
    bad: Option<(u32, u32)>,
    inv: Vec<String>,
    acts: Vec<String>,
}

impl Counters {
    pub fn new(n: u32, bad: Option<(u32, u32)>, init_copies: usize) -> Counters {
        Counters { n, bad, init_copies, inv: vec!["NotBad".into()], acts: vec!["IncX".into(), "IncY".into()] }
    }
}

impl Model for Counters {
    type State = (u32, u32);
    tlx_runtime::model_without_checks!();
    fn init_states(&self, out: &mut dyn FnMut((u32, u32))) -> Result<(), ModelError> {
        for _ in 0..self.init_copies {
            out((0, 0));
        }
        Ok(())
    }
    fn successors(&self, s: &(u32, u32), out: &mut dyn FnMut((u32, u32), u32) -> bool) -> Result<(), ModelError> {
        if s.0 < self.n && !out((s.0 + 1, s.1), 0) {
            return Ok(());
        }
        if s.1 < self.n {
            out((s.0, s.1 + 1), 1);
        }
        Ok(())
    }
    fn fingerprint(&self, s: &(u32, u32)) -> u64 {
        ((s.0 as u64) << 32 | s.1 as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0x1234
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
        format!("/\\ x = {}\n/\\ y = {}", s.0, s.1)
    }
}

/// Fingerprint-based graph identity, independent of node storage indices.
/// Initial states and outgoing edges retain their original order and multiplicity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Canon {
    pub initial: Vec<u64>,
    pub nodes: Vec<CanonNode>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanonNode {
    pub fingerprint: u64,
    pub state_atoms: Vec<u64>,
    pub edges: Vec<CanonEdge>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanonEdge {
    pub target: u64,
    pub action_atoms: Vec<u64>,
}

pub fn canon(g: &LiveGraph) -> Canon {
    let initial = g.init.iter().map(|&i| g.fps[i as usize]).collect();
    let mut nodes: Vec<_> = (0..g.len())
        .map(|i| CanonNode {
            fingerprint: g.fps[i],
            state_atoms: g.state_pats[g.state_pat[i] as usize].to_vec(),
            edges: g
                .off
                .range(i)
                .map(|e| CanonEdge { target: g.fps[g.tgt[e] as usize], action_atoms: g.action_pats[g.edge_pat.get(e) as usize].to_vec() })
                .collect(),
        })
        .collect();
    nodes.sort_by_key(|n| n.fingerprint);
    Canon { initial, nodes }
}

pub fn spill_dir(tag: &str, name: &str) -> PathBuf {
    static NEXT: AtomicU64 = AtomicU64::new(0);
    std::env::temp_dir().join(format!("{tag}-{}-{name}-{}", std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counters_keep_initial_multiplicity_and_action_order() {
        for copies in [1, 2] {
            let model = Counters::new(1, Some((1, 0)), copies);
            let mut init = Vec::new();
            model.init_states(&mut |state| init.push(state)).unwrap();
            assert_eq!(init, vec![(0, 0); copies]);
            let mut next = Vec::new();
            model
                .successors(&(0, 0), &mut |state, action| {
                    next.push((state, action));
                    true
                })
                .unwrap();
            assert_eq!(next, [((1, 0), 0), ((0, 1), 1)]);
            assert_eq!(model.check_invariants(&(1, 0)).unwrap(), Some(0));
            assert_eq!(model.fingerprint(&(1, 0)), (1u64 << 32).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0x1234);
        }
    }

    #[test]
    fn spill_paths_are_unique_and_not_created() {
        let first = spill_dir("ar15", "same");
        let second = spill_dir("ar15", "same");
        assert_ne!(first, second);
        assert!(!first.exists());
        assert!(!second.exists());
    }
}
