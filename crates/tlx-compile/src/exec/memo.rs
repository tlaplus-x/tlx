//! Memoization of pure interpreter fallbacks (docs/mixed-mode.md §8): the
//! IR executor keeps, per thread, the results of
//! `ExprKind::Interp` nodes keyed by the node and an exact encoding of
//! everything the node's value depends on — the values of its IR-bound
//! locals (`binds`) and the current-state variables it can read.
//!
//! A node is memoized only if it is pure: no primes, `UNCHANGED`,
//! `ENABLED` or temporal operators, no volatile builtins (`TLCGet`,
//! `TLCSet`, `RandomElement`, `Print`, ...: `Builtin::is_volatile`), no
//! cfg-overridden builtins, through every definition, constant
//! substitution, by-name argument and operator argument it can reach. The
//! same walk collects the state variables it can read. Pure TLA+
//! expressions evaluate to the same value every time, so a hit returns
//! exactly what evaluation would; errors are not memoized (the evaluation
//! is redone and fails again). Keys are exact (no fingerprints): encoded
//! words of encoded inputs and state variables, a structural encoding of
//! boxed ones (a lazy value as input disables memoization of that call).
//!
//! The table is direct-mapped (a colliding entry replaces the old one)
//! with a byte budget (the table is cleared when it is exceeded: the
//! thread's share of `TLX_MEMO_MB`, or less, of the memory budget's
//! allowance for caches, `tlx_runtime::cache_mem`); a node
//! whose hit rate stays low, or whose misses are cheap, is no longer
//! memoized on that thread, until a later probation (`REPROBE_FIRST`). Off in the IR executor's own runs (only the mixed-mode regions
//! of the compiled tier turn it on); see docs/configuration.md.
//!
//! The same tables hold the results of mixed-mode host regions
//! (`enc::mixed::HostRegions`, on by default in mixed mode), keyed by the
//! region's inputs and the words of the state variables it reads.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::Instant;

use tlx_eval::env::Env;
use tlx_eval::Interp;
use tlx_runtime::cache_mem::{self, Published};
use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{self, DefId, ExprKind as H, LocalId, OpRef};
use tlx_value::{FcnDom, Value};

use crate::binding::{deferred_local, Flow, Policy, Scope, State};
use crate::ir::{Deferred, Expr};

/// Configuration (from `Settings`).
struct Config {
    /// Table slots per thread (a power of two).
    slots: usize,
    /// Byte budget of all threads (keys and estimated result sizes): each
    /// thread of a search gets its share (`thread_budget`).
    budget: usize,
    stats: bool,
}

fn config() -> &'static Config {
    static C: OnceLock<Config> = OnceLock::new();
    C.get_or_init(|| {
        let s = crate::settings::Settings::global();
        // (The report is a section of `-stats`.)
        Config { slots: s.memo_slots, budget: s.memo_mb << 20, stats: s.memo_stats && tlx_runtime::stats::on() }
    })
}

/// The byte budget of the calling thread's table: its share of `TLX_MEMO_MB`
/// among the threads of the search, or less, its share of the memory
/// budget's allowance for caches (`tlx_runtime::cache_mem`, which shrinks
/// under memory pressure).
fn thread_budget() -> usize {
    (config().budget / cache_mem::threads()).min(cache_mem::share()).max(cache_mem::MIN_SHARE)
}

/// After this many lookups, a node with fewer than `MIN_HIT_PERMILLE`
/// hits per thousand is no longer memoized: its keys and entries cost more
/// than they save (YoYoAllGraphs: 17% hits, slower and +60 MB).
const PROBATION: u64 = 4096;
const MIN_HIT_PERMILLE: u64 = 200;
/// Also no longer memoized after probation: a node whose misses (timed
/// during probation, see `probation_timer`) take less than this on
/// average: a hit saves less than building and comparing keys costs
/// (measured on Allocator, bcastByz, YoYo).
const MIN_MISS_NS: u64 = 3000;
/// A node disabled after a probation is on probation again after this many
/// calls skipped, then after 4 times as many each time, up to
/// `REPROBE_MAX`. The tables are per thread: with several workers each
/// table sees a share of the states, and a thread's first lookups (in the
/// small early levels, on a cold table) can miss a node that hits 99% of
/// the time later (MCMongoReplReconfig: nodes saving most of the region
/// time were disabled on some of 8 workers, never on 1).
const REPROBE_FIRST: u64 = 16 * PROBATION;
const REPROBE_MAX: u64 = 1 << 26;

static SCOPE_IDS: AtomicU64 = AtomicU64::new(1);

/// Monotonically incremented on every value-store GC sweep so per-thread memo
/// tables (whose `Cached::Words` results may contain swept `Shape::Ref`
/// handles) flush stale entries without cross-thread coordination.
static STORE_GC_GEN: AtomicU64 = AtomicU64::new(0);

/// Current value-store GC generation for per-thread cache invalidation.
#[inline]
pub(crate) fn store_gc_gen() -> u64 {
    STORE_GC_GEN.load(Ordering::Acquire)
}

/// Advance the value-store GC generation after a sweep.
pub(crate) fn invalidate_for_store_gc() {
    STORE_GC_GEN.fetch_add(1, Ordering::Release);
}

/// The lifetime of one lowering's IR (owned by the model that runs it):
/// memo entries refer to IR nodes by address, so the per-thread tables
/// are reset when a thread starts executing another scope's IR. Dropping
/// the scope's statistics are a section of the `-stats` report
/// (`report_stats`; collected with `TLX_MEMO_STATS=1`).
pub struct MemoScope {
    id: u64,
    on: bool,
    label: String,
}

impl MemoScope {
    /// A new scope (`label` names it in the statistics), not memoizing.
    pub fn new(label: &str) -> MemoScope {
        MemoScope { id: SCOPE_IDS.fetch_add(1, Ordering::Relaxed), on: false, label: label.to_string() }
    }

    /// A new scope that memoizes (tests).
    pub fn always(label: &str) -> MemoScope {
        MemoScope::with(true, label)
    }

    /// A new scope that memoizes if `on`.
    pub fn with(on: bool, label: &str) -> MemoScope {
        let mut s = MemoScope::new(label);
        s.on |= on;
        s
    }

    /// The scope id to give the executor (0: memoization off).
    pub fn exec_id(&self) -> u64 {
        if self.on {
            self.id
        } else {
            0
        }
    }
}

impl MemoScope {
    /// Add this scope's statistics to the `-stats` report (if `-stats` and
    /// `TLX_MEMO_STATS` are on): call after the search, when the worker
    /// threads have flushed their counters.
    pub fn report_stats(&self) {
        if self.on && config().stats {
            MEMO.with(|m| m.borrow_mut().flush_stats());
            report(self.id, &self.label);
        }
    }
}

impl Drop for MemoScope {
    fn drop(&mut self) {
        if self.on && config().stats {
            // (Whatever `report_stats` did not take.)
            if let Some(g) = GLOBAL.lock().unwrap_or_else(|e| e.into_inner()).as_mut() {
                g.remove(&self.id);
            }
        }
    }
}

/// Lookups and hits of the calling thread in its current scope (tests).
#[doc(hidden)]
pub fn thread_counts() -> (u64, u64) {
    MEMO.with(|m| m.borrow().nodes.values().fold((0, 0), |(l, h), n| (l + n.lookups, h + n.hits)))
}

// ----------------------------------------------------------------------
// purity and read sets

/// What a node's value depends on.
#[derive(Debug, PartialEq, Eq)]
pub struct Deps {
    /// Current-state variables it can read (sorted).
    pub vars: Vec<u32>,
}

/// The dependencies of `Interp { expr, binds, deferred, env }`, or None if
/// it is not pure (see the module documentation).
pub fn analyze(ip: &Interp, expr: &hir::Expr, binds: &[(LocalId, Expr)], deferred: &[Deferred], env: &Env) -> Option<Deps> {
    let mut a = Analyzer { binds, deferred, defs: HashSet::new(), locals: HashSet::new(), vars: Vec::new(), pure: true };
    let mut s = State::new(ip, Scope::Shared, env.clone());
    s.walk(&mut a, expr, 0);
    if !a.pure {
        return None;
    }
    a.vars.sort_unstable();
    a.vars.dedup();
    Some(Deps { vars: a.vars })
}

/// The purity and read-set policy of the shared environment-aware walk
/// (`crate::binding`): a node whose value depends on more than its arguments
/// — a `'`/`UNCHANGED`/`ENABLED`, a volatile or overridden builtin, an action
/// or temporal operator — makes the whole node impure, and every variable
/// reached by a pure walk is a dependency. It keeps every environment reached
/// (a free local resolves in any enclosing closure that bound it) and counts
/// no structural depth.
struct Analyzer<'a> {
    binds: &'a [(LocalId, Expr)],
    deferred: &'a [Deferred],
    defs: HashSet<DefId>,
    locals: HashSet<LocalId>,
    vars: Vec<u32>,
    pure: bool,
}

/// Builtins whose value depends on more than their arguments.
fn impure_builtin(ip: &Interp, op: B) -> bool {
    matches!(op, B::Prime | B::Unchanged | B::Enabled) || op.is_volatile() || ip.is_builtin_overridden(op)
}

impl Policy for Analyzer<'_> {
    fn node(&mut self, s: &mut State<'_>, e: &hir::Expr, _depth: usize) -> Flow {
        if !self.pure {
            return Flow::Done;
        }
        match &*e.kind {
            H::Var(v) => self.vars.push(v.0),
            H::Builtin { op, .. } if impure_builtin(s.ip, *op) => {
                self.pure = false;
                return Flow::Done;
            }
            H::BoxAction { .. } | H::AngleAction { .. } | H::Fairness { .. } | H::TemporalQuant { .. } => {
                self.pure = false;
                return Flow::Done;
            }
            _ => {}
        }
        Flow::Children
    }

    fn def(&mut self, s: &mut State<'_>, d: DefId) -> bool {
        if !self.defs.insert(d) || s.ip.has_def_value(d) || s.ip.is_const_def(d) {
            return false;
        }
        let def = &s.ip.prog.defs[d.idx()];
        if let Some(b) = def.builtin {
            if impure_builtin(s.ip, b) {
                self.pure = false;
            }
            return false;
        }
        true
    }

    fn pending_def(&mut self, _s: &mut State<'_>, _d: DefId) {
        self.pure = false;
    }

    /// A free local: an input (bound by the IR), a deferred argument (its
    /// expression is part of the node), or bound in an environment.
    fn local(&mut self, s: &mut State<'_>, l: LocalId, _depth: usize) -> bool {
        if !self.locals.insert(l) || self.binds.iter().any(|(x, _)| *x == l) {
            return false;
        }
        if let Some(d) = self.deferred.iter().find(|d| deferred_local(d) == l) {
            match d {
                Deferred::Thunk(_, e) | Deferred::Once(_, e) | Deferred::Lambda(_, _, e) => s.walk(self, e, 0),
                Deferred::OpRef(_, r) => self.op(s, *r, 0),
            }
            return false;
        }
        true
    }

    fn constant(&mut self, s: &mut State<'_>, c: hir::ConstId, depth: usize) {
        if let Some(r) = s.ip.const_op_ref(c) {
            self.op(s, r, depth);
        } else if let Some(d) = s.ip.const_def(c) {
            s.def(self, d);
        }
    }

    fn op_builtin(&mut self, s: &mut State<'_>, b: B) {
        if impure_builtin(s.ip, b) {
            self.pure = false;
        }
    }
}

// ----------------------------------------------------------------------
// keys

/// Tags of the key encoding (each item is a tag, then its payload; lengths
/// make the encoding prefix-free, hence injective).
const T_BOOL: u64 = 1;
const T_INT: u64 = 2;
const T_ENC: u64 = 3;
const T_VBOOL: u64 = 4;
const T_VINT: u64 = 5;
const T_STR: u64 = 6;
const T_MODEL: u64 = 7;
const T_SET: u64 = 8;
const T_INTERVAL: u64 = 9;
const T_TUPLE: u64 = 10;
const T_RECORD: u64 = 11;
const T_FCN: u64 = 12;
// Application/EXCEPT can distinguish equal pairs by their domain witness.
// A separate tag preserves it without increasing the encoded key's size.
const T_FCN_INTERVAL: u64 = 13;

/// Append the exact key encoding of an unboxed boolean.
pub(crate) fn push_bool(b: bool, out: &mut Vec<u64>) {
    out.extend([T_BOOL, b as u64]);
}

/// Append the exact key encoding of an unboxed integer.
pub(crate) fn push_int(i: i64, out: &mut Vec<u64>) {
    out.extend([T_INT, i as u64]);
}

/// Append the exact key encoding of encoded words.
pub(crate) fn push_words(w: &[u64], out: &mut Vec<u64>) {
    out.extend([T_ENC, w.len() as u64]);
    out.extend_from_slice(w);
}

/// Append the exact structural encoding of `v` to `out` (two values have
/// the same encoding iff they have the same representation); false for
/// lazy values.
pub(crate) fn push_value(v: &Value, out: &mut Vec<u64>) -> bool {
    match v {
        Value::Bool(b) => out.extend([T_VBOOL, *b as u64]),
        Value::Int(i) => out.extend([T_VINT, *i as u64]),
        Value::Str(s) => out.extend([T_STR, s.id() as u64]),
        Value::ModelValue(s) => out.extend([T_MODEL, s.id() as u64]),
        Value::Interval(a, b) => out.extend([T_INTERVAL, *a as u64, *b as u64]),
        Value::Set(xs) | Value::Tuple(xs) => {
            out.extend([if matches!(v, Value::Set(_)) { T_SET } else { T_TUPLE }, xs.len() as u64]);
            return xs.iter().all(|x| push_value(x, out));
        }
        Value::Record(fs) => {
            out.extend([T_RECORD, fs.len() as u64]);
            return fs.iter().all(|(k, x)| {
                out.push(k.id() as u64);
                push_value(x, out)
            });
        }
        Value::Fcn(ps, dom) => {
            out.extend([
                match dom {
                    FcnDom::Enumerated => T_FCN,
                    FcnDom::Interval => T_FCN_INTERVAL,
                },
                ps.len() as u64,
            ]);
            return ps.iter().all(|(k, x)| push_value(k, out) && push_value(x, out));
        }
        Value::LazySet(_) | Value::LazyFcn(_) => return false,
    }
    true
}

fn hash_words(node: usize, ws: &[u64]) -> u64 {
    const K: u64 = 0x517c_c1b7_2722_0a95;
    let mut h = (node as u64).wrapping_mul(K);
    for &w in ws {
        h = (h.rotate_left(5) ^ w).wrapping_mul(K);
    }
    h ^ (h >> 29)
}

/// Approximate heap size of `v` (at most `cap`; shared parts are counted
/// as if they were not).
fn approx_bytes(v: &Value, cap: usize) -> usize {
    fn go(v: &Value, acc: &mut usize, cap: usize) {
        if *acc >= cap {
            return;
        }
        *acc += 32;
        match v {
            Value::Set(xs) | Value::Tuple(xs) => xs.iter().for_each(|x| go(x, acc, cap)),
            Value::Record(fs) => fs.iter().for_each(|(_, x)| go(x, acc, cap)),
            Value::Fcn(ps, _) => ps.iter().for_each(|(k, x)| {
                go(k, acc, cap);
                go(x, acc, cap);
            }),
            Value::LazySet(_) | Value::LazyFcn(_) => *acc += 256,
            _ => {}
        }
    }
    let mut acc = 0;
    go(v, &mut acc, cap);
    acc.min(cap)
}

// ----------------------------------------------------------------------
// per-thread table

/// A memoized node.
pub(crate) struct NodeInfo {
    /// The variables read; None: not memoized (impure, or disabled
    /// after probation).
    vars: Option<Rc<[u32]>>,
    pub label: String,
    lookups: u64,
    hits: u64,
    /// Calls with a lazy input (not memoized).
    unkeyed: u64,
    inserts: u64,
    /// Time spent evaluating on misses / building keys (TLX_MEMO_STATS).
    miss_ns: u64,
    key_ns: u64,
    /// The current probation's lookups and hits (`lookups` and `hits`
    /// are the totals of the statistics).
    probation_lookups: u64,
    probation_hits: u64,
    /// Misses timed during probation, and their time.
    probation_misses: u64,
    probation_ns: u64,
    disabled: bool,
    /// Calls skipped since disabled, and how many start a new probation.
    skipped: u64,
    reprobe: u64,
}

/// A memoized result: a value, or the words of an encoding (mixed-mode
/// regions with encoded results).
#[derive(Clone, Debug, PartialEq)]
pub(crate) enum Cached {
    Val(Value),
    Words(Box<[u64]>),
}

impl From<Value> for Cached {
    fn from(v: Value) -> Cached {
        Cached::Val(v)
    }
}

impl Cached {
    fn bytes(&self, cap: usize) -> usize {
        match self {
            Cached::Val(v) => approx_bytes(v, cap),
            Cached::Words(w) => 16 + w.len() * 8,
        }
    }
}

struct Entry {
    node: usize,
    hash: u64,
    key: Box<[u64]>,
    val: Cached,
    bytes: usize,
}

/// Slots a table starts with (or fewer, if the configured size is
/// smaller): it doubles up to the configured size as entries fill half of
/// it, so that the threads of a search that memoizes little do not each
/// hold (and touch) a full table of 4 MiB (65536 slots of 64 bytes).
const START_SLOTS: usize = 1024;

struct Memo {
    scope: u64,
    gc_gen: u64,
    nodes: tlx_base::hash::FxMap<usize, NodeInfo>,
    slots: Vec<Option<Entry>>,
    /// The configured size (slots) that `slots` grows to.
    max_slots: usize,
    /// Occupied slots.
    used: usize,
    bytes: usize,
    /// `bytes` as published for the memory budget (`tlx_runtime::cache_mem`).
    published: Published,
    evictions: u64,
    flushes: u64,
    key: Vec<u64>,
}

impl Memo {
    fn new() -> Memo {
        Memo {
            scope: 0,
            gc_gen: 0,
            nodes: Default::default(),
            slots: Vec::new(),
            max_slots: 0,
            used: 0,
            bytes: 0,
            published: Published::default(),
            evictions: 0,
            flushes: 0,
            key: Vec::new(),
        }
    }

    /// Switch to scope `scope` (dropping everything of another scope) and
    /// flush cached entries if a value-store GC sweep happened (preserving
    /// per-node probation statistics).
    fn enter(&mut self, scope: u64, slots: usize) {
        let gc_gen = store_gc_gen();
        if self.scope != scope {
            self.flush_stats();
            self.scope = scope;
            self.gc_gen = gc_gen;
            self.nodes.clear();
            self.clear_table();
        } else if self.gc_gen != gc_gen {
            self.gc_gen = gc_gen;
            self.clear_table();
        }
        if self.max_slots != slots {
            self.max_slots = slots;
            self.slots = (0..slots.min(START_SLOTS)).map(|_| None).collect();
            self.used = 0;
            self.bytes = 0;
            self.published.update(0);
        }
    }

    fn clear_table(&mut self) {
        self.slots.iter_mut().for_each(|s| *s = None);
        self.used = 0;
        self.bytes = 0;
        self.published.update(0);
    }

    /// Double the table (direct-mapped: the entry of slot `i` moves to
    /// slot `i` or `i + len`, so no entry is lost).
    fn grow(&mut self) {
        let n = self.slots.len() * 2;
        let mut slots: Vec<Option<Entry>> = (0..n).map(|_| None).collect();
        for e in self.slots.drain(..).flatten() {
            let i = e.hash as usize & (n - 1);
            slots[i] = Some(e);
        }
        self.slots = slots;
    }

    fn lookup(&self, node: usize, hash: u64, key: &[u64]) -> Option<Cached> {
        let s = self.slots.get(hash as usize & (self.slots.len() - 1))?.as_ref()?;
        (s.node == node && s.hash == hash && *s.key == *key).then(|| s.val.clone())
    }

    /// Insert (replacing the slot's entry; clearing the table first if the
    /// byte budget `budget` would be exceeded: see `thread_budget`).
    fn insert(&mut self, node: usize, hash: u64, key: &[u64], val: Cached, budget: usize) {
        let bytes = 64 + key.len() * 8 + val.bytes(budget);
        if bytes > budget / 16 {
            return;
        }
        if self.bytes + bytes > budget {
            self.clear_table();
            self.flushes += 1;
        }
        let mut i = hash as usize & (self.slots.len() - 1);
        if let Some(old) = self.slots[i].take() {
            self.bytes -= old.bytes;
            self.evictions += 1;
        } else {
            self.used += 1;
            if self.used * 2 > self.slots.len() && self.slots.len() < self.max_slots {
                self.grow();
                i = hash as usize & (self.slots.len() - 1);
            }
        }
        self.bytes += bytes;
        self.slots[i] = Some(Entry { node, hash, key: key.into(), val, bytes });
        self.published.update(self.bytes);
    }

    /// Add this thread's statistics to the global ones.
    fn flush_stats(&mut self) {
        if !config().stats || self.scope == 0 {
            return;
        }
        let mut g = GLOBAL.lock().unwrap_or_else(|e| e.into_inner());
        let s = g.get_or_insert_with(HashMap::new).entry(self.scope).or_default();
        s.evictions += self.evictions;
        s.flushes += self.flushes;
        for n in self.nodes.values_mut() {
            if n.lookups + n.unkeyed == 0 {
                continue;
            }
            let t = s.nodes.entry(n.label.clone()).or_default();
            t.lookups += n.lookups;
            t.hits += n.hits;
            t.unkeyed += n.unkeyed;
            t.inserts += n.inserts;
            t.miss_ns += n.miss_ns;
            t.key_ns += n.key_ns;
            t.disabled |= n.disabled;
            (n.lookups, n.hits, n.unkeyed, n.inserts, n.miss_ns, n.key_ns) = (0, 0, 0, 0, 0, 0);
        }
        (self.evictions, self.flushes) = (0, 0);
    }
}

impl Drop for Memo {
    fn drop(&mut self) {
        self.flush_stats();
    }
}

thread_local! {
    static MEMO: RefCell<Memo> = RefCell::new(Memo::new());
}

#[derive(Default)]
struct NodeTotals {
    lookups: u64,
    hits: u64,
    unkeyed: u64,
    inserts: u64,
    miss_ns: u64,
    key_ns: u64,
    disabled: bool,
}

#[derive(Default)]
struct ScopeTotals {
    nodes: HashMap<String, NodeTotals>,
    evictions: u64,
    flushes: u64,
}

/// Statistics flushed by the threads, by scope.
static GLOBAL: Mutex<Option<HashMap<u64, ScopeTotals>>> = Mutex::new(None);

/// The text of the memo section of `-stats`: the scopes reported so far.
static SECTION: Mutex<String> = Mutex::new(String::new());

/// Add the statistics of scope `id` to the memo section of `-stats`.
fn report(id: u64, label: &str) {
    let Some(s) = GLOBAL.lock().unwrap_or_else(|e| e.into_inner()).as_mut().and_then(|g| g.remove(&id)) else { return };
    let mut nodes: Vec<_> = s.nodes.into_iter().collect();
    nodes.sort_by_key(|(_, t)| std::cmp::Reverse(t.miss_ns));
    let (lookups, hits) = nodes.iter().fold((0, 0), |(l, h), (_, t)| (l + t.lookups, h + t.hits));
    let mut text = SECTION.lock().unwrap_or_else(|e| e.into_inner());
    text.push_str(&format!(
        "  {label}: {lookups} lookups, {hits} hits ({:.1}%), {} evictions, {} flushes\n",
        pct(hits, lookups),
        s.evictions,
        s.flushes
    ));
    for (name, t) in nodes {
        let per_miss = t.miss_ns as f64 / (t.lookups - t.hits).max(1) as f64;
        text.push_str(&format!(
            "    {name}: {} lookups, {} hits ({:.1}%), {} unkeyed, {} inserts, miss {:.1} us avg ({:.2} s), keys {:.2} s, est. saved {:.2} s{}\n",
            t.lookups,
            t.hits,
            pct(t.hits, t.lookups),
            t.unkeyed,
            t.inserts,
            per_miss / 1e3,
            t.miss_ns as f64 / 1e9,
            t.key_ns as f64 / 1e9,
            (t.hits as f64 * per_miss - t.key_ns as f64) / 1e9,
            if t.disabled { " [disabled: low hit rate]" } else { "" }
        ));
    }
    tlx_runtime::stats::set_section("memo tables (TLX_MEMO_STATS; all workers)", text.clone());
}

fn pct(a: u64, b: u64) -> f64 {
    100.0 * a as f64 / b.max(1) as f64
}

/// The memoization of one evaluation of an interpreter fallback node.
pub(crate) enum Probe {
    /// Not memoized: evaluate normally.
    Off,
    /// Memoized: the variables to key on.
    On(Rc<[u32]>),
}

/// Whether node `node` (an `Interp` of scope `scope`) is memoized;
/// `analyze` computes its dependencies on first use.
pub(crate) fn probe(scope: u64, node: usize, analyze: impl FnOnce() -> (Option<Deps>, String)) -> Probe {
    MEMO.with(|m| {
        let mut m = m.borrow_mut();
        m.enter(scope, config().slots);
        let n = m.nodes.entry(node).or_insert_with(|| {
            let (deps, label) = analyze();
            NodeInfo {
                vars: deps.map(|d| d.vars.into()),
                label,
                lookups: 0,
                hits: 0,
                unkeyed: 0,
                inserts: 0,
                miss_ns: 0,
                key_ns: 0,
                probation_lookups: 0,
                probation_hits: 0,
                probation_misses: 0,
                probation_ns: 0,
                disabled: false,
                skipped: 0,
                reprobe: REPROBE_FIRST,
            }
        });
        if n.disabled {
            n.skipped += 1;
            if n.skipped >= n.reprobe {
                // On probation again (see `REPROBE_FIRST`).
                n.disabled = false;
                n.skipped = 0;
                n.reprobe = (n.reprobe * 4).min(REPROBE_MAX);
                (n.probation_lookups, n.probation_hits, n.probation_misses, n.probation_ns) = (0, 0, 0, 0);
            }
        }
        match &n.vars {
            Some(vs) if !n.disabled => Probe::On(vs.clone()),
            _ => Probe::Off,
        }
    })
}

/// A key being built (reuses a per-thread buffer).
pub(crate) struct KeyBuf {
    pub words: Vec<u64>,
    start: Option<Instant>,
}

impl KeyBuf {
    pub(crate) fn new() -> KeyBuf {
        let words = MEMO.with(|m| std::mem::take(&mut m.borrow_mut().key));
        KeyBuf { words, start: config().stats.then(Instant::now) }
    }

    fn give_back(mut self) {
        self.words.clear();
        MEMO.with(|m| m.borrow_mut().key = std::mem::take(&mut self.words));
    }
}

/// Give back the key buffer of a hit.
pub(crate) fn release(key: KeyBuf) {
    key.give_back();
}

/// A description of an interpreted expression for the statistics: its
/// position and, for an operator application, the operator.
pub(crate) fn label(ip: &Interp, e: &hir::Expr) -> String {
    let file = ip.prog.file(e.span.file).path.file_stem().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
    let what = match &*e.kind {
        H::Apply { op: OpRef::Def(d), .. } => ip.prog.defs[d.idx()].name.to_string(),
        H::Builtin { op, .. } => op.name().to_string(),
        k => format!("{k:?}").split(|c: char| !c.is_alphanumeric()).next().unwrap_or_default().to_string(),
    };
    format!("{file}:{}:{} {what}", e.span.line, e.span.col)
}

/// A call whose inputs have no exact encoding.
pub(crate) fn unkeyed(node: usize, key: KeyBuf) {
    key.give_back();
    MEMO.with(|m| {
        if let Some(n) = m.borrow_mut().nodes.get_mut(&node) {
            n.unkeyed += 1;
        }
    });
}

/// The memoized value of `node` for `key`, if any. On a miss, the caller
/// evaluates and calls `fill`.
pub(crate) fn get(node: usize, key: &KeyBuf) -> Option<Value> {
    match get_cached(node, key)? {
        Cached::Val(v) => Some(v),
        Cached::Words(_) => unreachable!("an interpreted node memoizes values"),
    }
}

/// `get` of any memoized result.
pub(crate) fn get_cached(node: usize, key: &KeyBuf) -> Option<Cached> {
    let key_ns = key.start.map(|t| t.elapsed().as_nanos() as u64).unwrap_or(0);
    MEMO.with(|m| {
        let mut m = m.borrow_mut();
        let hash = hash_words(node, &key.words);
        let v = m.lookup(node, hash, &key.words);
        let n = m.nodes.get_mut(&node).expect("probed node");
        n.lookups += 1;
        n.probation_lookups = n.probation_lookups.saturating_add(1);
        n.key_ns += key_ns;
        if v.is_some() {
            n.hits += 1;
            n.probation_hits += 1;
        } else if n.probation_lookups == PROBATION {
            let cheap = n.probation_misses > 0 && n.probation_ns < n.probation_misses * MIN_MISS_NS;
            if cheap || n.probation_hits * 1000 < n.probation_lookups * MIN_HIT_PERMILLE {
                n.disabled = true;
            }
        }
        v
    })
}

/// Record the value of a miss (`r`, evaluated since `t0` if timed).
pub(crate) fn fill(node: usize, key: KeyBuf, r: Option<&Value>, t0: Option<Instant>) {
    fill_cached(node, key, r.map(|v| Cached::Val(v.clone())), t0)
}

/// `fill` with any result.
pub(crate) fn fill_cached(node: usize, key: KeyBuf, r: Option<Cached>, t0: Option<Instant>) {
    MEMO.with(|m| {
        let mut m = m.borrow_mut();
        let budget = thread_budget();
        let inserted = r.is_some();
        if let Some(v) = r {
            let hash = hash_words(node, &key.words);
            m.insert(node, hash, &key.words, v, budget);
        }
        let n = m.nodes.get_mut(&node).expect("probed node");
        n.inserts += inserted as u64;
        if let Some(t) = t0 {
            let ns = t.elapsed().as_nanos() as u64;
            n.miss_ns += ns;
            if n.probation_lookups <= PROBATION {
                n.probation_misses += 1;
                n.probation_ns += ns;
            }
        }
    });
    key.give_back();
}

/// Start timing a miss of `node` if it is on probation (or with
/// TLX_MEMO_STATS): its average miss time decides whether it stays
/// memoized (`MIN_MISS_NS`).
pub(crate) fn probation_timer(node: usize) -> Option<Instant> {
    let on = config().stats || MEMO.with(|m| m.borrow().nodes.get(&node).is_some_and(|n| n.probation_lookups <= PROBATION));
    on.then(Instant::now)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tlx_value::Sym;

    fn key(v: &Value) -> Vec<u64> {
        let mut out = Vec::new();
        assert!(push_value(v, &mut out));
        out
    }

    #[test]
    fn keys_are_exact() {
        let a = Value::Set(vec![Value::Int(1), Value::Int(2)].into());
        let b = Value::Tuple(vec![Value::Int(1), Value::Int(2)].into());
        let c = Value::Interval(1, 2);
        // Same elements, different representations: different keys.
        assert_ne!(key(&a), key(&b));
        assert_ne!(key(&a), key(&c));
        assert_eq!(key(&a), key(&Value::Set(vec![Value::Int(1), Value::Int(2)].into())));
        // Nesting is prefix-free: <<{1}, 2>> vs <<{1, 2}>>.
        let n1 = Value::Tuple(vec![Value::Set(vec![Value::Int(1)].into()), Value::Int(2)].into());
        let n2 = Value::Tuple(vec![Value::Set(vec![Value::Int(1), Value::Int(2)].into())].into());
        assert_ne!(key(&n1), key(&n2));
        let r = Value::Record(vec![(Sym::new("a"), Value::Bool(true))].into());
        let s = Value::Record(vec![(Sym::new("b"), Value::Bool(true))].into());
        assert_ne!(key(&r), key(&s));
        // An unboxed integer and a boxed one are kept apart.
        let (mut x, mut y) = (Vec::new(), Vec::new());
        push_int(3, &mut x);
        assert!(push_value(&Value::Int(3), &mut y));
        assert_ne!(x, y);
        let (mut e1, mut e2) = (Vec::new(), Vec::new());
        push_words(&[1, 2], &mut e1);
        push_words(&[1], &mut e2);
        assert_ne!(e1[..3], e2[..3]);
    }

    #[test]
    fn eviction_replaces_and_budget_clears() {
        let mut m = Memo::new();
        m.enter(7, 2);
        let budget = 1 << 20;
        // Slots 0 and 1 (by hash), then a collision on slot 0.
        m.insert(1, 0, &[10], Value::Int(1).into(), budget);
        m.insert(1, 1, &[11], Value::Int(2).into(), budget);
        assert_eq!(m.lookup(1, 0, &[10]), Some(Value::Int(1).into()));
        assert_eq!(m.lookup(1, 1, &[11]), Some(Value::Int(2).into()));
        m.insert(2, 2, &[12], Value::Int(3).into(), budget);
        assert_eq!(m.lookup(1, 0, &[10]), None);
        assert_eq!(m.lookup(2, 2, &[12]), Some(Value::Int(3).into()));
        assert_eq!(m.evictions, 1);
        // Same hash, different key or node: no hit.
        assert_eq!(m.lookup(2, 2, &[13]), None);
        assert_eq!(m.lookup(3, 2, &[12]), None);
        // A small budget clears the table instead of growing past it.
        // (An entry here is 104 bytes: at most budget / 16.)
        let small = 1700;
        let mut m = Memo::new();
        m.enter(8, 32);
        for i in 0..20u64 {
            m.insert(1, i, &[i], Value::Int(i as i64).into(), small);
            assert!(m.bytes <= small);
        }
        assert_eq!(m.flushes, 1);
        assert_eq!(m.lookup(1, 19, &[19]), Some(Value::Int(19).into()));
        assert_eq!(m.lookup(1, 0, &[0]), None);
        // Entries larger than budget / 16 are not kept.
        m.insert(1, 20, &[0; 200], Value::Int(0).into(), small);
        assert_eq!(m.lookup(1, 20, &[0; 200]), None);
        // A new scope drops everything.
        m.insert(1, 0, &[0], Value::Int(0).into(), small);
        m.enter(9, 32);
        assert_eq!(m.lookup(1, 0, &[0]), None);
    }

    #[test]
    fn table_grows_to_its_size() {
        let mut m = Memo::new();
        m.enter(7, 1 << 16);
        assert_eq!(m.slots.len(), START_SLOTS);
        let budget = 1 << 30;
        let n = 3 * START_SLOTS as u64;
        for i in 0..n {
            m.insert(1, i, &[i], Value::Int(i as i64).into(), budget);
        }
        // Distinct hashes below the table size never collide: all kept.
        assert_eq!(m.slots.len(), 8 * START_SLOTS);
        assert_eq!(m.evictions, 0);
        assert!((0..n).all(|i| m.lookup(1, i, &[i]) == Some(Value::Int(i as i64).into())));
        // It stops at the configured size.
        for i in n..(1 << 17) {
            m.insert(1, i, &[i], Value::Int(i as i64).into(), budget);
        }
        assert_eq!(m.slots.len(), 1 << 16);
        assert_eq!(m.used, 1 << 16);
    }

    #[test]
    fn function_keys_preserve_domain_witness_recursively() {
        use tlx_value::ops;

        let pairs = vec![(Value::Int(0), Value::Int(7))].into();
        let enumerated = Value::Fcn(std::sync::Arc::clone(&pairs), FcnDom::Enumerated);
        let interval = Value::Fcn(pairs, FcnDom::Interval);
        let absent = Value::model_value("absent");
        assert_eq!(ops::select(&enumerated, &absent).unwrap(), None);
        assert!(ops::select(&interval, &absent).is_err());
        // The witness changes the tag, without adding a word to the hot key.
        assert_eq!(key(&enumerated), [T_FCN, 1, T_VINT, 0, T_VINT, 7]);
        assert_eq!(key(&enumerated).len(), key(&interval).len());
        assert_ne!(key(&enumerated), key(&interval));
        for wrap in [
            Value::tuple as fn(Vec<Value>) -> Value,
            |vs| Value::Set(vs.into()),
            |vs| Value::record(vec![(tlx_value::Sym::new("f"), vs[0].clone())]),
            |vs| Value::fcn_rcd_from_pairs(vec![(vs[0].clone(), Value::TRUE)]).unwrap(),
            |vs| Value::fcn_rcd_from_pairs(vec![(Value::Int(0), vs[0].clone())]).unwrap(),
        ] {
            assert_ne!(key(&wrap(vec![enumerated.clone()])), key(&wrap(vec![interval.clone()])));
        }
    }

    #[test]
    fn keys_keep_other_semantic_representations_distinct() {
        let key = |v: Value| {
            let mut words = Vec::new();
            assert!(push_value(&v, &mut words));
            words
        };
        let tuple = Value::tuple(vec![Value::Int(7)]);
        let record = Value::record(vec![(tlx_value::Sym::new("a"), Value::Int(7))]);
        assert_ne!(key(tuple.clone()), key(tuple.into_fcn_rcd()));
        assert_ne!(key(record.clone()), key(record.into_fcn_rcd()));
        assert_ne!(key(Value::Interval(0, 0)), key(Value::Set(vec![Value::Int(0)].into())));
        assert_ne!(key(Value::str("m")), key(Value::model_value("m")));
        assert_ne!(key(Value::model_value("m")), key(Value::model_value("n")));
        assert_eq!(key(Value::Int(7)), [T_VINT, 7]);
        assert_eq!(key(Value::TRUE), [T_VBOOL, 1]);
    }

    #[test]
    fn lazy_inputs_have_no_key() {
        let lazy = Value::LazySet(std::sync::Arc::new(tlx_value::LazySet::Subset(Value::Interval(1, 3))));
        assert!(!push_value(&lazy, &mut Vec::new()));
        assert!(!push_value(&Value::Tuple(vec![Value::Int(1), lazy].into()), &mut Vec::new()));
    }
}

#[cfg(test)]
mod shared_facts {
    //! Facts the shared environment-aware walk (`crate::binding`) must keep
    //! for memo purity and read sets: through a `LET`, recursion, operator
    //! arguments (bound in an environment or carried by the node's
    //! `deferred` list) and a `CONSTANT` the cfg binds to a definition.
    use super::*;
    use std::sync::Arc;
    use tlx_eval::env::{Binding, OpVal, Thunk};
    use tlx_sema::hir::DefKind;

    const SPEC: &str = r#"
EXTENDS Naturals, TLC
VARIABLES x, y
CONSTANT C
RECURSIVE Rec(_)
Rec(n) == IF n = 0 THEN x ELSE Rec(n - 1)
Higher(Op(_)) == Op(42)
Override == y
LetConst == LET K == C IN K = x
Pure == x + 1
Impure == x' + 1
Unch == UNCHANGED x
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ y' = y
Enab == ENABLED Next
Vol == TLCGet("level")
Printing == PrintT(x)
"#;

    #[test]
    fn analyze_reaches_let_recursion_operator_arguments_and_overrides() {
        let source = tlx_testkit::module("ExecMemoShared", SPEC);
        let model = tlx_testkit::spec::load(&source, "CONSTANT C <- Override\nINIT Init\nNEXT Next\n");
        let ip = &model.ip;
        let def = |name: &str| ip.prog.defs.iter().find(|d| &*d.name == name).unwrap_or_else(|| panic!("{name}"));
        let body = |name: &str| {
            let DefKind::Op(e) = &def(name).kind else { panic!("{name}") };
            e.clone()
        };
        let facts = |name: &str, deferred: &[Deferred], env: &Env| analyze(ip, &body(name), &[], deferred, env);

        let empty = &Env::default();
        // A pure read, and the impurity sources that disable memoization.
        assert_eq!(facts("Pure", &[], empty), Some(Deps { vars: vec![0] }));
        for impure in ["Impure", "Unch", "Enab", "Vol", "Printing"] {
            assert_eq!(facts(impure, &[], empty), None, "{impure}");
        }
        // Recursion, and the `C <- Override` substitution under a `LET`.
        assert_eq!(facts("Rec", &[], empty), Some(Deps { vars: vec![0] }));
        assert_eq!(facts("Override", &[], empty), Some(Deps { vars: vec![1] }));
        assert_eq!(facts("LetConst", &[], empty), Some(Deps { vars: vec![0, 1] }));

        // An operator argument is inert while its parameter is unbound, and
        // followed to its reads through an environment binding: a `LAMBDA`,
        // an operator reference, a thunk or an arena expression (a value
        // binding reads nothing).
        assert_eq!(facts("Higher", &[], empty), Some(Deps { vars: vec![] }));
        let p = def("Higher").params[0];
        let rec = body("Rec");
        let rd = ip.prog.defs.iter().position(|d| &*d.name == "Rec").unwrap() as u32;
        let bound = |b: Binding| Env::default().bind(p, b);
        let lambda = OpVal::Lambda { params: Arc::from(Vec::new()), body: rec.clone(), env: Env::default() };
        for env in [
            bound(Binding::Op(lambda)),
            bound(Binding::Op(OpVal::Ref(OpRef::Def(DefId(rd))))),
            bound(Binding::Thunk(Arc::new(Thunk { expr: rec.clone(), env: Env::default(), memo: None }))),
            bound(Binding::Name(ip.prog.expr_id(&rec).unwrap(), Env::default())),
        ] {
            assert_eq!(facts("Higher", &[], &env), Some(Deps { vars: vec![0] }));
        }
        assert_eq!(facts("Higher", &[], &bound(Binding::Val(Value::Int(3)))), Some(Deps { vars: vec![] }));

        // The same operator argument carried by the node's `deferred` list,
        // including its impurity.
        assert_eq!(facts("Higher", &[Deferred::Thunk(p, rec.clone())], empty), Some(Deps { vars: vec![0] }));
        assert_eq!(facts("Higher", &[Deferred::Lambda(p, Arc::from(Vec::new()), rec.clone())], empty), Some(Deps { vars: vec![0] }));
        assert_eq!(facts("Higher", &[Deferred::OpRef(p, OpRef::Def(DefId(rd)))], empty), Some(Deps { vars: vec![0] }));
        assert_eq!(facts("Higher", &[Deferred::Thunk(p, body("Impure"))], empty), None);
    }
}
