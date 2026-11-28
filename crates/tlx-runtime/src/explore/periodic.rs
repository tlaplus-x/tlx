//! Geometric checks on the completed records of a quiescent BFS level.
use std::sync::atomic::{AtomicU64, Ordering};

use parking_lot::Mutex;

use super::{edges, Outcome, Shared, NO_PARENT};
use crate::liveness::{recorded, RecordedWitness};
use crate::model::Model;

pub(super) struct Periodic {
    expanded: AtomicU64,
    next: AtomicU64,
    pub(super) witness: Mutex<Option<RecordedWitness>>,
}

impl Periodic {
    pub(super) fn new() -> Self {
        let name = "TLX_LIVE_CHECK_FIRST";
        let first = tlx_base::knobs::Env::process().num(name).unwrap_or_else(|_| tlx_base::knobs::default_num(name));
        Self { expanded: AtomicU64::new(0), next: AtomicU64::new(first), witness: Mutex::new(None) }
    }

    pub(super) fn add(&self, expanded: u64) {
        self.expanded.fetch_add(expanded, Ordering::Relaxed);
    }

    pub(super) fn due(&self) -> bool {
        self.expanded.load(Ordering::Relaxed) >= self.next.load(Ordering::Relaxed)
    }

    /// All workers have published their history shards and wait here. Scan only
    /// the graph; replaying a lasso can collect the value store and must wait
    /// until after the search has released its roots.
    pub(super) fn check<M: Model>(&self, shared: &Shared<'_, M>) {
        self.next.store(self.expanded.load(Ordering::Relaxed).saturating_mul(2), Ordering::Relaxed);
        if !shared.live_pre.lock().is_empty() {
            return; // The initial levels still need reconstruction at finalization.
        }
        let shards = shared.history.lock().snapshot();
        let mut guards: Vec<_> = shards.iter().map(|shard| shard.lock()).collect();
        let Some(records) = guards.iter_mut().map(|g| g.as_mut()?.edges.as_mut()).collect::<Option<Vec<_>>>() else { return };
        let budget = shared.opts.maxmem;
        let base = if budget == usize::MAX {
            0
        } else {
            let (_, _, bytes) = edges::build_bytes(records.iter().map(|r| &**r));
            let base = crate::mem::live_base();
            if base.saturating_add(bytes) > budget {
                return;
            }
            base
        };
        let graph = match edges::build_graph(records, &shared.opts.spill, true, false) {
            Ok(Some(g)) => g,
            Ok(None) => return,
            Err(e) => {
                shared.fail(Outcome::Io(e.0), NO_PARENT);
                return;
            }
        };
        let guard = crate::mem::RssGuard::periodic(budget, base, graph.bytes());
        let input = shared.live_atoms.unwrap().live_input().unwrap();
        crate::stats::add_count("liveness: periodic checks", 1);
        if let Ok(Some(witness)) = recorded::scan(&input, graph, shared.slots.len(), guard) {
            *self.witness.lock() = Some(witness);
            shared.control().stop();
        }
    }
}
