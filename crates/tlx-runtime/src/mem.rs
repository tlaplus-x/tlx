//! The memory budget of a search (docs/scale.md §2): one soft limit
//! (`-maxmem`) for everything the search holds — the fingerprint set, the
//! frontier, the trace logs, the archive of expanded states (for resuming
//! after a layout miss), the liveness edges and the memo tables — plus what it does not
//! control (values of interpreted states, caches, native code), estimated
//! from the process's resident memory.
//!
//! Accounting is by tables, segments and blocks (never per state): the
//! components count their memory where they allocate it, each in a `Gauge`
//! registered with the budget (`MemBudget::register`, one per `Component`),
//! a monitor thread samples the resident memory every 50 ms, and the
//! search compares the registered gauges' sum (`MemBudget::accounted`) with
//! the budget at a few points (`explore::Shared::relieve`, the growth of
//! the fingerprint set).
//!
//! Over budget, the components give memory back in this order (docs/scale.md §2.3; with
//! `-spill off` stages 2 and 3 only record that they were reached):
//!
//! 1. the archive is spilled (or dropped when disk is disabled), and the
//!    evaluation caches' allowance is halved (`crate::cache_mem`);
//! 2. the trace logs are written to disk (`crate::io`);
//! 3. the liveness edge logs are written to disk;
//! 4. the frontier compresses its new blocks whatever its size;
//! 5. the fingerprint set stops growing: it rotates to disk (its table
//!    becomes a sorted run, `crate::fpset`); with `-spill off` it grows
//!    only into the room left, then fills up to its hard limit: the run
//!    fails with a full fingerprint set, asking for a larger `-maxmem`.

use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};
use std::sync::{Arc, OnceLock};

/// The memory a component holds (bytes), and the most it held at a time:
/// counted where it allocates and frees, by tables, segments and blocks.
#[derive(Default)]
pub struct Gauge {
    bytes: AtomicUsize,
    peak: AtomicUsize,
}

impl Gauge {
    pub const fn new() -> Gauge {
        Gauge { bytes: AtomicUsize::new(0), peak: AtomicUsize::new(0) }
    }

    /// `n` bytes more.
    #[inline]
    pub fn add(&self, n: usize) {
        let b = self.bytes.fetch_add(n, Ordering::Relaxed) + n;
        self.peak.fetch_max(b, Ordering::Relaxed);
    }

    /// `n` bytes fewer.
    #[inline]
    pub fn sub(&self, n: usize) {
        self.bytes.fetch_sub(n, Ordering::Relaxed);
    }

    /// The bytes held now.
    pub fn bytes(&self) -> usize {
        self.bytes.load(Ordering::Relaxed)
    }

    /// The most bytes held at a time.
    pub fn peak(&self) -> usize {
        self.peak.load(Ordering::Relaxed)
    }
}

/// The part of a gauge one writer (a worker, a thread's cache) published:
/// the writer sets its size from time to time, the gauge takes the
/// difference, so that it holds the sum of the parts.
#[derive(Default)]
pub struct Part(AtomicUsize);

impl Part {
    /// This part of `g` is now `bytes`.
    #[inline]
    pub fn set(&self, g: &Gauge, bytes: usize) {
        let old = self.0.swap(bytes, Ordering::Relaxed);
        if bytes >= old {
            g.add(bytes - old);
        } else {
            g.sub(old - bytes);
        }
    }

    /// The bytes last published.
    pub fn get(&self) -> usize {
        self.0.load(Ordering::Relaxed)
    }
}

/// A component that counts its memory in a gauge (the gauge itself, or a
/// structure holding one), for the registry of a budget.
pub trait Meter: Send + Sync {
    fn gauge(&self) -> &Gauge;
}

impl Meter for Gauge {
    fn gauge(&self) -> &Gauge {
        self
    }
}

impl Meter for &'static Gauge {
    fn gauge(&self) -> &Gauge {
        self
    }
}

/// The components of a search that account for their memory (in the
/// order of the pressure stages that relieve them, see the module doc).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Component {
    /// The archive of expanded states (stage 1).
    Archive,
    /// The evaluation caches of all threads (`crate::cache_mem`; stage 1).
    Caches,
    /// The workers' trace logs (stage 2).
    TraceLogs,
    /// The workers' liveness edge logs (stage 3).
    LiveEdges,
    /// The frontier's queue (stage 4).
    Frontier,
    /// The representatives' candidates buffered by the workers (VIEW,
    /// SYMMETRY: until the end of their level).
    Candidates,
    /// The fingerprint set: its table, old table, the Bloom filters and
    /// indexes of its runs, a merge in progress (stage 5).
    FpSet,
}

/// The gauges of the components (`MemBudget::register`): one per
/// component.
#[derive(Default)]
pub struct Registry {
    meters: Vec<(Component, Arc<dyn Meter>)>,
}

impl Registry {
    /// Count the memory of component `c` in `m`.
    ///
    /// # Panics
    /// If `c` is registered already.
    pub fn register(&mut self, c: Component, m: Arc<dyn Meter>) {
        assert!(self.of(c).is_none(), "{c:?} registered twice");
        self.meters.push((c, m));
    }

    fn of(&self, c: Component) -> Option<&Gauge> {
        self.meters.iter().find(|(k, _)| *k == c).map(|(_, m)| m.gauge())
    }

    /// The gauge of component `c`.
    ///
    /// # Panics
    /// If `c` is not registered.
    pub fn gauge(&self, c: Component) -> &Gauge {
        self.of(c).unwrap_or_else(|| panic!("no gauge registered for {c:?}"))
    }

    /// The bytes of component `c` now (0 if not registered).
    pub fn bytes(&self, c: Component) -> usize {
        self.of(c).map_or(0, Gauge::bytes)
    }

    /// The most bytes of component `c` at a time (0 if not registered).
    pub fn peak(&self, c: Component) -> usize {
        self.of(c).map_or(0, Gauge::peak)
    }

    /// The bytes of all components now.
    pub fn total(&self) -> usize {
        self.meters.iter().map(|(_, m)| m.gauge().bytes()).sum()
    }
}

/// The stages of memory pressure (docs/scale.md §2.3).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u32)]
pub enum Stage {
    /// Within the budget.
    None = 0,
    /// The archive (for resuming after a layout miss) was dropped, or the
    /// evaluation caches' allowance halved.
    Archive = 1,
    /// The trace logs are spilled to disk (or would be, with `-spill off`).
    TraceLog = 2,
    /// The liveness edge logs are spilled to disk (or would be).
    LiveEdges = 3,
    /// The frontier compresses whatever its size.
    Frontier = 4,
    /// The fingerprint set stopped growing (and rotates to disk).
    FpSet = 5,
}

impl Stage {
    fn of(n: u32) -> Stage {
        match n {
            0 => Stage::None,
            1 => Stage::Archive,
            2 => Stage::TraceLog,
            3 => Stage::LiveEdges,
            4 => Stage::Frontier,
            _ => Stage::FpSet,
        }
    }

    /// A description (for `-stats`).
    pub fn describe(self) -> &'static str {
        match self {
            Stage::None => "0 (within the budget)",
            Stage::Archive => "1 (archive to disk, or dropped with -spill off; memo tables shrunk)",
            Stage::TraceLog => "2 (trace logs to disk; only recorded with -spill off)",
            Stage::LiveEdges => "3 (liveness edges to disk; only recorded with -spill off)",
            Stage::Frontier => "4 (frontier compressed, then to disk; only compressed with -spill off)",
            Stage::FpSet => "5 (fingerprint set to disk; stopped growing with -spill off)",
        }
    }
}

/// The budget of a search and its state.
pub struct MemBudget {
    /// The budget (bytes); `usize::MAX`: unlimited.
    total: usize,
    accounted_peak: AtomicUsize,
    /// The resident memory last sampled (bytes; 0 before any sample).
    rss: AtomicUsize,
    /// The highest pressure stage reached.
    stage: AtomicU32,
    /// The gauges of the components counted against the budget.
    meters: Registry,
}

impl MemBudget {
    pub fn new(total: usize) -> MemBudget {
        MemBudget {
            total,
            accounted_peak: AtomicUsize::new(0),
            rss: AtomicUsize::new(0),
            stage: AtomicU32::new(0),
            meters: Registry::default(),
        }
    }

    /// Count the memory of component `c` in `m` (before the search starts).
    pub fn register(&mut self, c: Component, m: Arc<dyn Meter>) {
        self.meters.register(c, m);
    }

    /// The gauges of the components.
    pub fn meters(&self) -> &Registry {
        &self.meters
    }

    /// The memory the components account for (bytes).
    pub fn accounted(&self) -> usize {
        let bytes = self.meters.total();
        self.accounted_peak.fetch_max(bytes, Ordering::Relaxed);
        bytes
    }

    /// Highest registered total sampled by the budget (not the sum of peaks).
    pub fn accounted_peak(&self) -> usize {
        self.accounted();
        self.accounted_peak.load(Ordering::Relaxed)
    }

    /// The budget in bytes (`usize::MAX`: unlimited).
    pub fn total(&self) -> usize {
        self.total
    }

    /// Whether there is a limit.
    pub fn limited(&self) -> bool {
        self.total != usize::MAX
    }

    /// Sample the resident memory of the process.
    pub fn sample(&self) {
        if let Some(r) = rss_bytes() {
            self.rss.store(r, Ordering::Relaxed);
        }
    }

    /// The memory in use, given what the components account for: at least
    /// the resident memory last sampled (which includes what they do not
    /// account for).
    pub fn used(&self, accounted: usize) -> usize {
        accounted.max(self.rss.load(Ordering::Relaxed))
    }

    /// Record that stage `s` was reached.
    pub fn reach(&self, s: Stage) {
        self.stage.fetch_max(s as u32, Ordering::Relaxed);
    }

    /// The highest stage reached.
    pub fn stage(&self) -> Stage {
        Stage::of(self.stage.load(Ordering::Relaxed))
    }
}

/// Have the allocator return the memory freed to the OS (set by the
/// program that chose the allocator: the runtime does not know it).
static PURGE: OnceLock<fn()> = OnceLock::new();

/// Set the allocator's purge (`purge`); the first call wins.
pub fn set_purge(f: fn()) {
    let _ = PURGE.set(f);
}

/// Have the allocator return the memory freed to the OS now, rather than
/// after its delay (or never), so that the resident memory sampled next
/// shows what was freed: under memory pressure, once components wrote
/// their memory to disk, and before liveness checking measures where it
/// starts from. Nothing without a purge (`set_purge`).
pub fn purge() {
    if let Some(f) = PURGE.get() {
        f();
    }
}

/// Liveness checking after the search may use at least this fraction of
/// the budget (1/LIVE_SHARE) beyond the memory the process holds when it
/// starts (`live_limit`).
pub const LIVE_SHARE: usize = 4;

/// The limit of the process's resident memory while liveness checking
/// builds its graphs (`usize::MAX`: none), given the budget and the
/// resident memory `base` when it started (after the search freed its
/// structures): the budget, but at least `base` plus a quarter of the
/// budget. The memory the process holds anyway (native code, the
/// allocator's arenas and pages, worker stacks: on Linux with transparent
/// huge pages it can exceed a small budget by itself) does not fail a
/// small graph; only what liveness adds counts, against what the budget
/// leaves free, but never less than a quarter of it.
pub fn live_limit(budget: usize, base: usize) -> usize {
    if budget == usize::MAX {
        return usize::MAX;
    }
    budget.max(base.saturating_add(budget / LIVE_SHARE))
}

/// Liveness checks that sample the resident memory as its graphs grow
/// (rather than compute their size) allow it to grow at least this much
/// (bytes) beyond its start: the threads, allocator pages and code that
/// any checking touches first (a few MiB) would otherwise fail a tiny
/// graph under a tiny budget.
pub const LIVE_RSS_SLACK: usize = 8 << 20;

/// The resident memory of the process when liveness checking starts
/// (bytes; 0 if unknown): after a purge, so that the search's structures,
/// freed by now, do not count.
pub fn live_base() -> usize {
    purge();
    rss_bytes().unwrap_or(0)
}

/// The memory budget of liveness checking (`-maxmem`, bytes; `usize::MAX`:
/// none): as its graphs grow, the process's resident memory is checked
/// against a limit set when it starts (`live_limit`).
#[derive(Clone, Copy)]
pub struct RssGuard {
    pub budget: usize,
    /// The limit of the resident memory (bytes).
    limit: usize,
    /// Remaining allocation budget after the recorded behavior graph.
    available: usize,
}

impl RssGuard {
    /// The guard of liveness checking starting now, with the budget
    /// `budget`: `recorded` bytes of the resident memory are the behavior
    /// graph recorded by the search, which liveness adds (its size was
    /// checked against the same limit when it was built).
    pub fn new(budget: usize, recorded: usize) -> RssGuard {
        if budget == usize::MAX {
            return RssGuard { budget, limit: usize::MAX, available: usize::MAX };
        }
        let base = live_base().saturating_sub(recorded);
        let limit = live_limit(budget, base).max(base.saturating_add(LIVE_RSS_SLACK));
        if crate::stats::on() {
            let m = crate::stats::MEMORY;
            crate::stats::set(&format!("{m}RSS when liveness starts (without its graph)"), crate::stats::Metric::Bytes(base as u64));
            crate::stats::set(&format!("{m}RSS limit of liveness"), crate::stats::Metric::Bytes(limit as u64));
        }
        let available = live_limit(budget, base).saturating_sub(base).saturating_sub(recorded);
        RssGuard { budget, limit, available }
    }

    /// Search structures are still resident during an optional periodic scan.
    /// Charge the recorded graph against the headroom measured before its build.
    pub(crate) fn periodic(budget: usize, base: usize, recorded: usize) -> Self {
        let available = if budget == usize::MAX { budget } else { budget.saturating_sub(base).saturating_sub(recorded) };
        Self { budget, limit: budget, available }
    }

    /// Ok while the process is within the limit, else the message of the
    /// failure, `what` (described lazily) being what grows.
    pub(crate) fn check(&self, what: &dyn Fn() -> String) -> Result<(), String> {
        if self.limit == usize::MAX {
            return Ok(());
        }
        match rss_bytes() {
            Some(rss) if rss > self.limit => {
                // (Over the limit: maybe with memory freed but not yet
                // returned to the OS, e.g. the buffers of grown arrays.)
                purge();
                match rss_bytes() {
                    Some(rss) if rss > self.limit => Err(crate::explore::liveness_memory_error(&what(), rss, self.budget)),
                    _ => Ok(()),
                }
            }
            _ => Ok(()),
        }
    }

    /// The memory check of a product graph (`tlx_live::check_lasso_within`):
    /// records its largest size for `-stats`, and stops it over the budget
    /// (the message in `err`).
    pub(crate) fn product<'a>(
        &'a self,
        peak: &'a mut (usize, usize, usize),
        err: &'a mut Option<String>,
    ) -> impl FnMut(usize, usize, usize) -> bool + 'a {
        let gauge = Gauge::new();
        let part = Part::default();
        move |nodes, edges, bytes| {
            part.set(&gauge, bytes);
            if gauge.bytes() > peak.2 {
                *peak = (nodes, edges, bytes);
            }
            if gauge.bytes() > self.available {
                *err = Some(crate::explore::liveness_memory_error(
                    &format!("the liveness automaton and product ({nodes} nodes, {edges} edges so far)"),
                    self.budget.saturating_add(gauge.bytes() - self.available),
                    self.budget,
                ));
                return false;
            }
            match self
                .check(&|| format!("the product of the behavior graph and a property's automaton ({nodes} nodes, {edges} edges so far)"))
            {
                Ok(()) => true,
                Err(e) => {
                    *err = Some(e);
                    false
                }
            }
        }
    }
}

/// The resident memory of this process (bytes), if known: on macOS its
/// physical footprint (resident and compressed memory, as Activity Monitor
/// shows), on Linux its anonymous resident memory (the resident set less
/// its file-backed pages). Neither counts the pages of the executable and
/// the shared libraries (9-12 MiB of tlx's own code on Linux): the kernel
/// can drop them at any time and read them again, and they do not grow
/// with the run.
pub fn rss_bytes() -> Option<usize> {
    #[cfg(target_os = "macos")]
    {
        // SAFETY: an all-zero `rusage_info_v2` is a valid value (all its
        // fields are integers), and `proc_pid_rusage` initializes it.
        let mut info: libc::rusage_info_v2 = unsafe { std::mem::zeroed() };
        // SAFETY: `info` is a valid `rusage_info_v2`, the flavor asked for
        // (`RUSAGE_INFO_V2` fills exactly that struct), and the call writes
        // only it.
        let r = unsafe { libc::proc_pid_rusage(libc::getpid(), libc::RUSAGE_INFO_V2, (&mut info as *mut libc::rusage_info_v2).cast()) };
        (r == 0).then_some(info.ri_phys_footprint as usize)
    }
    #[cfg(target_os = "linux")]
    {
        // (statm: size, resident, shared (file-backed and shared memory
        // pages), ... in pages.)
        let statm = std::fs::read_to_string("/proc/self/statm").ok()?;
        let mut f = statm.split_whitespace().skip(1);
        let resident: usize = f.next()?.parse().ok()?;
        let shared: usize = f.next()?.parse().ok()?;
        let pages = resident.saturating_sub(shared);
        // SAFETY: sysconf has no preconditions.
        let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
        (page > 0).then(|| pages * page as usize)
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        None
    }
}

/// The physical memory of the process (bytes; 4 GiB if unknown): the
/// machine's, or on Linux the memory limit of the process's control group
/// if that is lower (a container, a systemd unit with `MemoryMax`), as the
/// JVM does for TLC's heap. Without it a run in a container whose limit is
/// below half of the host's memory would take a budget it cannot have and
/// be killed by the kernel instead of spilling.
pub fn physical_bytes() -> usize {
    static PHYS: OnceLock<usize> = OnceLock::new();
    *PHYS.get_or_init(|| {
        let machine = machine_bytes();
        #[cfg(target_os = "linux")]
        if let Some(limit) = cgroup_limit() {
            return machine.min(limit);
        }
        machine
    })
}

/// The physical memory of the machine (bytes; 4 GiB if unknown).
fn machine_bytes() -> usize {
    #[cfg(unix)]
    {
        // SAFETY: sysconf has no preconditions.
        let (pages, page) = unsafe { (libc::sysconf(libc::_SC_PHYS_PAGES), libc::sysconf(libc::_SC_PAGESIZE)) };
        if pages > 0 && page > 0 {
            return (pages as usize).saturating_mul(page as usize);
        }
    }
    4 << 30
}

/// The memory limit of the process's control group (the lowest of its own
/// and its ancestors' within the mounted hierarchy), if any.
#[cfg(target_os = "linux")]
fn cgroup_limit() -> Option<usize> {
    let groups = std::fs::read_to_string("/proc/self/cgroup").ok()?;
    let read = |p: &std::path::Path| std::fs::read_to_string(p).ok();
    cgroup_limit_in(&groups, &read)
}

/// `cgroup_limit` with `/proc/self/cgroup` given as `groups` and files
/// read by `read`: cgroup v2 (`0::/path`, `memory.max` and `memory.high` of the group and its
/// ancestors under /sys/fs/cgroup), else v1 (the `memory` controller's
/// `memory.limit_in_bytes` under /sys/fs/cgroup/memory). "max", and v1's
/// "unlimited" (a page-rounded `i64::MAX`), mean no limit.
#[cfg(any(target_os = "linux", test))]
fn cgroup_limit_in(groups: &str, read: &dyn Fn(&std::path::Path) -> Option<String>) -> Option<usize> {
    use std::path::Path;
    let limit_of = |text: Option<String>| -> Option<usize> {
        let v = text?.trim().parse::<u64>().ok()?;
        (v < 1 << 60).then_some(v as usize)
    };
    // (The group's path, then each ancestor's, up to the mount point.)
    let lowest = |root: &Path, path: &str, file: &str| -> Option<usize> {
        let mut dir = root.join(path.trim_start_matches('/'));
        let mut best: Option<usize> = None;
        loop {
            if let Some(l) = limit_of(read(&dir.join(file))) {
                best = Some(best.map_or(l, |b| b.min(l)));
            }
            if dir == root || !dir.pop() {
                return best;
            }
        }
    };
    let mut v1 = None;
    for line in groups.lines() {
        let mut parts = line.splitn(3, ':');
        let (Some(id), Some(controllers), Some(path)) = (parts.next(), parts.next(), parts.next()) else { continue };
        if id == "0" && controllers.is_empty() {
            // (`memory.high` throttles the group above it: a limit too.)
            let root = Path::new("/sys/fs/cgroup");
            let (max, high) = (lowest(root, path, "memory.max"), lowest(root, path, "memory.high"));
            if let Some(l) = max.into_iter().chain(high).min() {
                return Some(l);
            }
        } else if controllers.split(',').any(|c| c == "memory") {
            v1 = lowest(Path::new("/sys/fs/cgroup/memory"), path, "memory.limit_in_bytes");
        }
    }
    v1
}

/// The default budget: half of the physical memory (docs/scale.md §2.1).
///
/// Not the memory available when the run starts: a run's limits (e.g. when
/// its fingerprint set is full) would then depend on what else happens to
/// run on the machine. Like TLC (whose defaults are fractions of the
/// physical memory), the same run on the same machine gets the same budget.
pub fn default_budget() -> usize {
    physical_bytes() / 2
}

/// Parse a budget (`-maxmem`, `TLX_MAXMEM`): a fraction in (0,1) of the
/// physical memory, or a size: MiB, or with a suffix `K`, `M`, `G` or `T`
/// (powers of 1024; also `KB`, `MiB`, ...; the grammar is shared in
/// `size`). At least 1 MiB.
pub fn parse_budget(v: &str) -> Option<usize> {
    let v = v.trim();
    if let Ok(f) = v.parse::<f64>() {
        if f > 0.0 && f < 1.0 {
            return Some(((physical_bytes() as f64 * f) as usize).max(1 << 20));
        }
    }
    let (digits, suffix) = crate::size::digits_and_suffix(v);
    let n: usize = digits.parse().ok()?;
    let bytes = n.checked_mul(1usize << crate::size::shift_of(suffix)?)?;
    (bytes >= 1 << 20).then_some(bytes)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn budgets() {
        assert_eq!(parse_budget("512"), Some(512 << 20));
        assert_eq!(parse_budget("512M"), Some(512 << 20));
        assert_eq!(parse_budget("8G"), Some(8 << 30));
        assert_eq!(parse_budget("8gib"), Some(8 << 30));
        assert_eq!(parse_budget("2048K"), Some(2 << 20));
        assert_eq!(parse_budget("1"), Some(1 << 20));
        assert_eq!(parse_budget("0.5"), Some(physical_bytes() / 2));
        for bad in ["0", "1.5", "-1", "x", "12Q", "", "100K"] {
            assert_eq!(parse_budget(bad), None, "{bad}");
        }
    }

    #[test]
    fn cgroup_limits() {
        use std::path::Path;
        let files = |fs: &'static [(&'static str, &'static str)]| {
            move |p: &Path| fs.iter().find(|(k, _)| Path::new(k) == p).map(|(_, v)| v.to_string())
        };
        // v2: the lowest limit of the group and its ancestors; "max" is none.
        let fs = files(&[
            ("/sys/fs/cgroup/a/b/memory.max", "max\n"),
            ("/sys/fs/cgroup/a/memory.max", "1073741824\n"),
            ("/sys/fs/cgroup/memory.max", "4294967296\n"),
        ]);
        assert_eq!(cgroup_limit_in("0::/a/b\n", &fs), Some(1 << 30));
        let fs = files(&[("/sys/fs/cgroup/a/memory.max", "1073741824"), ("/sys/fs/cgroup/a/memory.high", "805306368")]);
        assert_eq!(cgroup_limit_in("0::/a\n", &fs), Some(768 << 20));
        assert_eq!(cgroup_limit_in("0::/\n", &files(&[("/sys/fs/cgroup/memory.max", "max")])), None);
        // A container: its group is the namespace root.
        assert_eq!(cgroup_limit_in("0::/\n", &files(&[("/sys/fs/cgroup/memory.max", "536870912")])), Some(512 << 20));
        // v1: the memory controller's line; "unlimited" is a huge number.
        let v1 = "12:pids:/x\n4:cpu,cpuacct:/x\n3:memory:/docker/abc\n";
        let fs = files(&[("/sys/fs/cgroup/memory/docker/abc/memory.limit_in_bytes", "2147483648")]);
        assert_eq!(cgroup_limit_in(v1, &fs), Some(2 << 30));
        let fs = files(&[("/sys/fs/cgroup/memory/docker/abc/memory.limit_in_bytes", "9223372036854771712")]);
        assert_eq!(cgroup_limit_in(v1, &fs), None);
        // Nothing readable: no limit.
        assert_eq!(cgroup_limit_in("0::/a\n", &files(&[])), None);
        assert_eq!(cgroup_limit_in("", &files(&[])), None);
    }

    #[test]
    fn resident_memory() {
        let r = rss_bytes().expect("resident memory");
        assert!(r > 1 << 20, "{r}");
    }

    #[test]
    fn gauges_and_parts() {
        let g = Gauge::new();
        g.add(10);
        g.add(5);
        g.sub(12);
        assert_eq!((g.bytes(), g.peak()), (3, 15));
        // Two writers' parts: the gauge holds their sum.
        let (a, b) = (Part::default(), Part::default());
        a.set(&g, 100);
        b.set(&g, 50);
        assert_eq!((g.bytes(), g.peak()), (153, 153));
        a.set(&g, 20);
        assert_eq!((g.bytes(), a.get()), (73, 20));
        b.set(&g, 0);
        a.set(&g, 0);
        assert_eq!((g.bytes(), g.peak()), (3, 153));
    }

    #[test]
    fn registry() {
        static CACHES: Gauge = Gauge::new();
        let mut b = MemBudget::new(1 << 30);
        let queue = Arc::new(Gauge::new());
        b.register(Component::Frontier, queue.clone());
        b.register(Component::Caches, Arc::new(&CACHES));
        queue.add(1 << 20);
        CACHES.add(7);
        assert_eq!(b.accounted(), (1 << 20) + 7);
        assert_eq!(b.meters().bytes(Component::Frontier), 1 << 20);
        assert_eq!(b.meters().bytes(Component::TraceLogs), 0);
        assert_eq!(b.meters().gauge(Component::Caches).peak(), 7);
        queue.sub(1 << 20);
        assert_eq!(b.accounted(), 7);
        assert_eq!((b.meters().peak(Component::Frontier), b.meters().peak(Component::FpSet)), (1 << 20, 0));
        assert_eq!(b.used(b.accounted()), 7);
    }

    #[test]
    #[should_panic(expected = "registered twice")]
    fn registered_once() {
        let mut r = Registry::default();
        r.register(Component::Archive, Arc::new(Gauge::new()));
        r.register(Component::Archive, Arc::new(Gauge::new()));
    }

    #[test]
    fn stages() {
        let b = MemBudget::new(1 << 30);
        assert_eq!(b.stage(), Stage::None);
        b.reach(Stage::Frontier);
        b.reach(Stage::Archive);
        assert_eq!(b.stage(), Stage::Frontier);
        assert_eq!(b.used(5), 5);
        b.sample();
        assert!(b.used(5) > 1 << 20);
    }

    #[test]
    fn liveness_limits() {
        assert_eq!(live_limit(usize::MAX, 1 << 30), usize::MAX);
        // Within the budget: the budget.
        assert_eq!(live_limit(128 << 20, 40 << 20), 128 << 20);
        // The process holds most of it already: at least a quarter more.
        assert_eq!(live_limit(128 << 20, 120 << 20), 152 << 20);
        assert_eq!(live_limit(128 << 20, 160 << 20), 192 << 20);
        assert!(live_base() > 1 << 20);
    }
}
