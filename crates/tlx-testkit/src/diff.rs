//! Differential harness: lowered Init, actions, invariants and action
//! properties run in the IR executor (`tlx_compile::exec`) and as generated
//! C (`tlx_compile::cgen`, built synchronously) on the same encoded states,
//! with the interpreter as the reference.
//!
//! The IR executor is the closure-compiled `exec::fast`.
//!
//! Verdicts per (function, state):
//! - a compiled result (successor multiset / predicate verdict) must equal
//!   the interpreter's;
//! - where the interpreter fails, compiled code must fail too (it hands the
//!   pair to the interpreter, which reports the error);
//! - a compiled failure where the interpreter succeeds is a *bailout*
//!   (allowed: the interpreter re-runs the pair), e.g. a successor outside
//!   the layout;
//! - a panic in the IR executor is a failure.
//!
//! The IR executor and native code disagreeing only on whether to bail out
//! is recorded as an *asymmetry*: harmless for results but a sign that the
//! two implementations differ (`DiffReport::asymmetries`).
//!
//! The harness bypasses `EncModel` on purpose: it runs both compiled
//! implementations on every state, whereas `EncModel` runs only the best
//! available one (native, else IR) and never runs invariants in the IR
//! executor.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt::Write as _;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::Arc;

use tlx_compile::cgen::CGen;
use tlx_compile::enc::hints;
use tlx_compile::exec::fast;
use tlx_compile::ir::{ActionFn, Expr, ExprKind, PredFn, Stmt};
use tlx_compile::lower::Lowerer;
use tlx_compile::native_plan::NativeSet;
use tlx_compile::types::Typing;
use tlx_eval::model::State;
use tlx_eval::{EvalError, InterpModel};
use tlx_layout::infer::Observer;
use tlx_layout::{Layout, Shape};
use tlx_native::build::BuildOptions;
use tlx_native::native::{NativeLib, OK, UNSUPPORTED};
use tlx_runtime::Model;
use tlx_value::Value;

use crate::spec;
use crate::values::random_state;
use crate::Rng;

/// Result of running one function on one input.
#[derive(Clone, Debug, PartialEq)]
enum Res<T> {
    Ok(T),
    /// Runtime error / bailout (message).
    Err(String),
    /// Not implemented by this tier (not lowered / not native).
    Unsupported,
    /// The implementation panicked (always a failure).
    Panic(String),
}

/// Outcome counts of one tier for one function.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Tally {
    /// Compiled result equal to the interpreter's.
    pub agree: usize,
    /// Both the interpreter and compiled code failed.
    pub both_fail: usize,
    /// Compiled code failed (bailed out), the interpreter did not.
    pub bailout: usize,
    pub unsupported: usize,
    /// Wrong results, missing errors and panics.
    pub wrong: usize,
}

/// The results of a differential run.
#[derive(Debug, Default)]
pub struct DiffReport {
    /// Per function (`init`, `action A`, `invariant I`, `aprop P`): tallies
    /// of the IR executor and of native code.
    pub tallies: BTreeMap<String, (Tally, Tally)>,
    /// Descriptions of disagreements with the interpreter (first few).
    pub failures: Vec<String>,
    pub failure_count: usize,
    /// IR executor and native code disagreeing on whether to bail out
    /// (first few).
    pub asymmetries: Vec<String>,
    pub asymmetry_count: usize,
    /// States that did not fit the layout (not checked).
    pub skipped_states: usize,
}

const KEEP: usize = 8;

impl DiffReport {
    fn fail(&mut self, msg: String) {
        self.failure_count += 1;
        if self.failures.len() < KEEP {
            self.failures.push(msg);
        }
    }

    fn asym(&mut self, msg: String) {
        self.asymmetry_count += 1;
        if self.asymmetries.len() < KEEP {
            self.asymmetries.push(msg);
        }
    }

    /// Total tallies (IR executor, native).
    pub fn totals(&self) -> (Tally, Tally) {
        let add = |a: &mut Tally, b: &Tally| {
            a.agree += b.agree;
            a.both_fail += b.both_fail;
            a.bailout += b.bailout;
            a.unsupported += b.unsupported;
            a.wrong += b.wrong;
        };
        let (mut e, mut n) = (Tally::default(), Tally::default());
        for (x, y) in self.tallies.values() {
            add(&mut e, x);
            add(&mut n, y);
        }
        (e, n)
    }

    /// A readable summary (per-function tallies, failures, asymmetries).
    pub fn render(&self) -> String {
        let mut s = String::new();
        let t = |t: &Tally| {
            format!("agree {} both-fail {} bailout {} unsupported {} wrong {}", t.agree, t.both_fail, t.bailout, t.unsupported, t.wrong)
        };
        for (f, (e, n)) in &self.tallies {
            let _ = writeln!(s, "  {f}\n    exec:   {}\n    native: {}", t(e), t(n));
        }
        if self.skipped_states > 0 {
            let _ = writeln!(s, "  {} state(s) outside the layout skipped", self.skipped_states);
        }
        for f in &self.failures {
            let _ = writeln!(s, "FAILURE: {f}");
        }
        if self.failure_count > self.failures.len() {
            let _ = writeln!(s, "... {} failures in all", self.failure_count);
        }
        for a in &self.asymmetries {
            let _ = writeln!(s, "ASYMMETRY: {a}");
        }
        if self.asymmetry_count > self.asymmetries.len() {
            let _ = writeln!(s, "... {} asymmetries in all", self.asymmetry_count);
        }
        s
    }

    /// Panic (with the rendered report) if there were failures, or
    /// asymmetries when `TLX_DIFF_STRICT` is set.
    pub fn assert_ok(&self, what: &str) {
        let strict = std::env::var_os("TLX_DIFF_STRICT").is_some();
        if self.failure_count > 0 || (strict && self.asymmetry_count > 0) {
            panic!("{what}: IR executor / native code / interpreter disagree\n{}", self.render());
        }
    }
}

/// Which native backend a [`Harness`] built: the generated C library, or
/// the Cranelift JIT (`TLX_JIT=1` with the `jit` feature). The consumer
/// matrix needs this to tell a JIT cell from a C cell, since both leave the
/// generated C source in [`Harness::c_src`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Backend {
    C,
    Jit,
}

/// Host callbacks the generated C may call to run an operation it did not
/// inline (see `tlx-native`'s `tlx_abi.h`): `eval` runs a region in the
/// interpreter, `elems` enumerates a set the native tier cannot, and
/// `ref_op`/`ref_elems` are the value store's reference operations. The
/// generated C names them `h-><name>`; the string `host->` never appears in
/// generated C (only in doc comments and tests), so a guard that looks for
/// `host->` passes vacuously. A family that reaches one of these is
/// delegated, never executed natively.
pub const HOST_OPERATION_CALLBACKS: [&str; 4] = ["eval", "elems", "ref_op", "ref_elems"];

/// Host callbacks that manage the run instead of running an operation:
/// `emit` (the successor sink every model writes), `error` (the error sink),
/// `miss` (fall back to the interpreter for the whole call) and
/// `mark`/`release` (handle-lifetime watermarks). No operation family is
/// delegated through them. [`Harness::consumers`] asserts that every
/// `h-><name>` in the generated C is one of these or a
/// [`HOST_OPERATION_CALLBACKS`] entry, so a new delegation cannot be added
/// to the C tier and go unnoticed by the matrix.
pub const HOST_MACHINERY_CALLBACKS: [&str; 5] = ["emit", "error", "miss", "mark", "release"];

/// Lowered-IR kinds the interpreter's pre-resolved code tier
/// (`tlx-eval/src/code.rs`, `Interp::code_of`) turns into nodes of their
/// own; a lowered program with none of them is walked entirely by the tree
/// tier (`Node::Tree`) and its code cell is a gap.
pub const CODE_TIER_KINDS: [&str; 5] = ["Const", "ConstWords", "Let", "Temp", "Convert"];

/// The classification rule [`Harness::consumers`] applies to the host
/// callbacks the generated C names: every callback must be classified (a
/// [`HOST_OPERATION_CALLBACKS`] delegation or a [`HOST_MACHINERY_CALLBACKS`]
/// run-machinery entry), and a callback a family claims to delegate through
/// must be a real operation callback, never machinery. Split out from
/// `consumers` so the rule is unit-tested with hand-written callback sets
/// instead of only being exercised through a built model (CODE-19: a guard
/// that never fires on a bad input is no guard).
fn classify_host_callbacks<'a>(family: &str, callbacks: impl IntoIterator<Item = &'a str>, delegated: &[&str]) -> Result<(), String> {
    for cb in callbacks {
        if !HOST_OPERATION_CALLBACKS.contains(&cb) && !HOST_MACHINERY_CALLBACKS.contains(&cb) {
            return Err(format!("{family}: the generated C calls the unclassified host callback h->{cb}"));
        }
    }
    for d in delegated {
        let Some(name) = d.strip_prefix("h->") else {
            return Err(format!("{family}: delegated callback {d:?} is not named h-><name>"));
        };
        if !HOST_OPERATION_CALLBACKS.contains(&name) {
            return Err(format!("{family}: {d:?} is run machinery, not an operation delegation"));
        }
    }
    Ok(())
}

/// The host callbacks `c_src` names (`h-><name>`), deduplicated. A guard
/// that looks for the literal `host->` never matches generated C (which
/// spells the callbacks `h->…`), so it passes vacuously; a check for no host
/// delegation must instead ask whether this set is empty of
/// [`HOST_OPERATION_CALLBACKS`] entries (CODE-19).
pub fn host_callbacks(c_src: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let bytes = c_src.as_bytes();
    let mut i = 0;
    while let Some(pos) = c_src[i..].find("h->") {
        let start = i + pos + 3;
        let end = start + bytes[start..].iter().take_while(|b| b.is_ascii_alphanumeric() || **b == b'_').count();
        if end > start {
            out.insert(c_src[start..end].to_string());
        }
        i = end.max(start);
    }
    out
}

/// One execution consumer of the compiled pipeline, in the order a model
/// passes through it (docs/design.md): the lowered tree, the interpreter's
/// pre-resolved code, the closure executor, generated C, the JIT, the host
/// (the callbacks C delegates to, and the functions C does not compile), or
/// an explicit gap.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Consumer {
    Tree,
    Code,
    Closure,
    C,
    Jit,
    Host,
    Unsupported,
}

impl Consumer {
    /// Every consumer, in pipeline order.
    pub const ALL: [Consumer; 7] = [Self::Tree, Self::Code, Self::Closure, Self::C, Self::Jit, Self::Host, Self::Unsupported];

    pub fn name(self) -> &'static str {
        match self {
            Self::Tree => "tree",
            Self::Code => "code",
            Self::Closure => "closure",
            Self::C => "C",
            Self::Jit => "JIT",
            Self::Host => "host",
            Self::Unsupported => "unsupported",
        }
    }
}

/// What one consumer did with one operation family. Exactly one kind of
/// evidence is set: `ran` counts executions, `delegated` counts operations
/// the consumer handed to another consumer, `gap` names why the consumer
/// has no evidence at all (never a silent zero, CODE-19).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Cell {
    pub ran: usize,
    pub delegated: usize,
    pub gap: Option<String>,
}

impl Cell {
    fn ran(n: usize) -> Cell {
        Cell { ran: n, ..Cell::default() }
    }
    fn delegated(n: usize) -> Cell {
        Cell { delegated: n, ..Cell::default() }
    }
    fn gap(why: impl Into<String>) -> Cell {
        Cell { gap: Some(why.into()), ..Cell::default() }
    }
    /// The consumer executed the family.
    pub fn is_executed(&self) -> bool {
        self.ran > 0
    }
    /// The consumer handed the family to another consumer: not execution.
    pub fn is_delegated(&self) -> bool {
        self.ran == 0 && self.delegated > 0
    }
    /// The consumer neither ran nor delegated the family; `gap` says why.
    pub fn is_gap(&self) -> bool {
        self.ran == 0 && self.delegated == 0
    }
    fn kind(&self) -> u8 {
        (self.ran > 0) as u8 + (self.delegated > 0) as u8 + self.gap.is_some() as u8
    }
}

/// The consumers that run one operation family: the evidence
/// [`Harness::consumers`] collected (docs/development-standards.md CODE-19,
/// ARCH-06).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FamilyConsumers {
    pub family: String,
    pub cells: BTreeMap<Consumer, Cell>,
}

impl FamilyConsumers {
    pub fn cell(&self, consumer: Consumer) -> &Cell {
        self.cells.get(&consumer).expect("every consumer has a cell")
    }

    /// One line per consumer, for a test note.
    pub fn render(&self) -> String {
        let mut out = format!("family {}:", self.family);
        for c in Consumer::ALL {
            let cell = self.cell(c);
            let what = if cell.is_executed() {
                format!("ran {}", cell.ran)
            } else if cell.is_delegated() {
                format!("delegated {}", cell.delegated)
            } else {
                format!("gap ({})", cell.gap.as_deref().unwrap_or("?"))
            };
            let _ = write!(out, "\n  {:<11} {what}", c.name());
        }
        out
    }

    /// Fail unless every cell holds exactly one kind of evidence, a
    /// delegation is accounted for by the consumer that ran it, and no tier
    /// claims execution the backend did not do (CODE-19: no silent zero, and
    /// host delegation is never counted as a backend).
    pub fn assert_ok(&self) -> &Self {
        for c in Consumer::ALL {
            let cell = self.cell(c);
            assert_eq!(cell.kind(), 1, "{} / {}: ambiguous cell {cell:?}", self.family, c.name());
        }
        assert!(
            !(self.cell(Consumer::C).is_delegated() && self.cell(Consumer::Jit).is_executed()),
            "{}: the JIT claims execution while C delegates to the host",
            self.family
        );
        assert!(
            !self.cell(Consumer::C).is_delegated() || self.cell(Consumer::Host).is_executed(),
            "{}: C delegates to the host but the host shows no execution",
            self.family
        );
        self
    }

    /// Fail unless the interpreter tiers every lowered family runs (the tree
    /// and the pre-resolved code) executed the family.
    pub fn assert_lowered(&self) -> &Self {
        for c in [Consumer::Tree, Consumer::Code] {
            let cell = self.cell(c);
            assert!(cell.is_executed(), "{} / {}: the tier ran nothing ({cell:?})", self.family, c.name());
        }
        self
    }

    /// Fail unless `consumer` executed the family. Host delegation never
    /// satisfies this: a delegated operation did not run in that consumer.
    pub fn assert_executed(&self, consumer: Consumer) -> &Self {
        let cell = self.cell(consumer);
        assert!(
            cell.is_executed(),
            "{} / {}: expected execution, got {cell:?} (host delegation does not count)",
            self.family,
            consumer.name()
        );
        self
    }

    /// Fail unless `consumer` delegated the family to another consumer.
    pub fn assert_delegated(&self, consumer: Consumer) -> &Self {
        let cell = self.cell(consumer);
        assert!(cell.is_delegated(), "{} / {}: expected delegation, got {cell:?}", self.family, consumer.name());
        self
    }

    /// Fail unless `consumer` is an explicit gap.
    pub fn assert_gap(&self, consumer: Consumer) -> &Self {
        let cell = self.cell(consumer);
        assert!(cell.is_gap(), "{} / {}: expected a gap, got {cell:?}", self.family, consumer.name());
        self
    }
}

/// Fail unless the matrix attributes at least one operation family to the
/// host, by delegation or by a function the C and JIT tiers do not compile.
/// Without such a family the rules above (delegation is not execution; a
/// delegation is accounted for) are never exercised, so they would pass
/// vacuously (ARCH-06).
pub fn assert_host_classification_exercised(families: &[FamilyConsumers]) {
    assert!(
        families.iter().any(|f| f.cell(Consumer::Host).is_executed()),
        "no family in the matrix runs on the host: the delegation classification is untested"
    );
}

/// A spec lowered against a fixed layout, with its native library.
pub struct Harness {
    pub base: InterpModel,
    pub layout: Arc<Layout>,
    pub typing: Typing,
    pub init: Option<ActionFn>,
    pub actions: Vec<Option<ActionFn>>,
    pub invariants: Vec<PredFn>,
    pub aprops: Vec<PredFn>,
    /// Which functions are native.
    pub native: NativeSet,
    pub lib: Option<NativeLib>,
    /// Why functions were not lowered.
    pub notes: Vec<String>,
    /// The lowering's functions compiled for the closure executor.
    pub fast: fast::Program,
    /// The generated C source (empty when nothing was lowered to C). Used
    /// by the consumer matrix to see which operations the C tier delegates
    /// to the host (see [`HOST_OPERATION_CALLBACKS`]).
    pub c_src: String,
    /// The native backend behind `lib` ([`Backend::Jit`] under `TLX_JIT=1`).
    pub backend: Backend,
}

impl Harness {
    /// Load `src`/`cfg`, speculate the layout from the reachable states
    /// (at most `PRERUN_STATES`; unlike `prerun_shapes`, evaluation errors
    /// only prune the search, so that specs can exercise errors), lower and
    /// build native code.
    pub fn new(src: &str, cfg: &str) -> Harness {
        let base = spec::load(src, cfg);
        let (states, _) = reachable(&base, PRERUN_STATES);
        let mut obs = Observer::new(base.ip.prog.vars.len());
        for s in &states {
            obs.observe(s);
        }
        let shapes = obs.finalize(&hints(&base));
        Self::build(base, shapes, &mut |_, _| {})
    }

    /// As `new`, with the given variable shapes.
    pub fn with_shapes(src: &str, cfg: &str, shapes: Vec<Shape>) -> Harness {
        Self::build(spec::load(src, cfg), shapes, &mut |_, _| {})
    }

    /// As `with_shapes`, then `edit` may replace lowered actions by
    /// hand-written IR (registering the shapes it needs in the typing)
    /// before the native code is generated: for testing IR nodes in forms
    /// the lowering does not produce. A replaced action must still mean what
    /// the spec's action means (the interpreter runs the latter).
    pub fn with_ir(src: &str, cfg: &str, shapes: Vec<Shape>, edit: &mut dyn FnMut(&mut Typing, &mut [Option<ActionFn>])) -> Harness {
        Self::build(spec::load(src, cfg), shapes, edit)
    }

    /// Configure an experimental lowering without changing process-global
    /// environment variables shared by other tests.
    pub fn with_lowerer(src: &str, cfg: &str, shapes: Vec<Shape>, configure: &mut dyn FnMut(&mut Lowerer<'_>)) -> Harness {
        Self::build_configured(spec::load(src, cfg), shapes, configure, &mut |_, _| {})
    }

    fn build(base: InterpModel, shapes: Vec<Shape>, edit: &mut dyn FnMut(&mut Typing, &mut [Option<ActionFn>])) -> Harness {
        Self::build_configured(base, shapes, &mut |_| {}, edit)
    }

    fn build_configured(
        base: InterpModel,
        shapes: Vec<Shape>,
        configure: &mut dyn FnMut(&mut Lowerer<'_>),
        edit: &mut dyn FnMut(&mut Typing, &mut [Option<ActionFn>]),
    ) -> Harness {
        let layout = Arc::new(Layout::new(shapes));
        let ip = base.ip.clone();
        let mut lw = Lowerer::with_typing(&ip, Typing::new(layout.clone()));
        configure(&mut lw);
        let mut notes = Vec::new();
        let init = lw.lower_init(base.init_expr()).map_err(|e| notes.push(format!("Init not lowered: {}", e.0))).ok();
        let mut actions: Vec<Option<ActionFn>> = base
            .actions()
            .iter()
            .map(|a| lw.lower_action(a).map_err(|e| notes.push(format!("action {} not lowered: {}", a.name, e.0))).ok())
            .collect();
        let invariants: Vec<PredFn> = base.invariant_exprs().iter().zip(base.invariant_names()).map(|(e, n)| lw.lower_pred(n, e)).collect();
        let aprops: Vec<PredFn> =
            base.action_property_exprs().iter().zip(base.action_property_names()).map(|(e, n)| lw.lower_trans_pred(n, e)).collect();
        let mut typing = lw.into_typing();
        edit(&mut typing, &mut actions);
        let verified = tlx_compile::verify::Program::new(&typing, init.as_ref(), &actions, &invariants, &aprops).expect("valid lowered IR");
        let refops = tlx_compile::exec::refops::RefOpTable::of(&verified);
        let gen = CGen::new(&verified).with_refops(refops.clone()).library(base.action_names(), base.invariant_names());
        // `TLX_JIT` with the `jit` feature: the native tier is the Cranelift
        // prototype (same native functions as the C library).
        #[cfg(feature = "jit")]
        if tlx_compile::settings::Settings::global().jit == tlx_compile::settings::Jit::Only && gen.plan.native.any() {
            let j = tlx_compile::jit::library(&verified, None, refops.clone(), base.action_names(), base.invariant_names())
                .unwrap_or_else(|e| panic!("JIT failed: {e}"));
            let (a, b) = (&j.native, &gen.plan.native);
            assert_eq!(
                (a.init, &a.actions, &a.invariants, &a.action_properties),
                (b.init, &b.actions, &b.invariants, &b.action_properties),
                "JIT and C native sets differ"
            );
            let fast = fast::Program::new(&typing);
            return Harness {
                base,
                layout,
                typing,
                init,
                actions,
                invariants,
                aprops,
                native: gen.plan.native,
                lib: Some(j.lib),
                notes,
                fast,
                c_src: gen.src,
                backend: Backend::Jit,
            };
        }
        // Without the `jit` feature the branch above is not compiled, so
        // `TLX_JIT=1` would silently test the C tier. Refuse instead.
        #[cfg(not(feature = "jit"))]
        if tlx_compile::settings::Settings::global().jit == tlx_compile::settings::Jit::Only {
            panic!(
                "TLX_JIT selects the JIT tier but tlx-testkit was built without its `jit` feature: add --features tlx-testkit/jit (docs/testing.md)"
            );
        }
        let lib = gen.plan.native.any().then(|| {
            let path =
                tlx_native::build::build(&gen.src, &BuildOptions::default()).unwrap_or_else(|e| panic!("generated C does not build: {e}"));
            // SAFETY: gen is CGen output from verified IR with these refops
            // and no regions; the test compiler/cache are trusted.
            unsafe { NativeLib::load_with(&path, None, refops.map(|ops| ops as Arc<dyn tlx_native::mixed::RefOps>)) }
                .unwrap_or_else(|e| panic!("cannot load the generated library: {e}"))
        });
        let fast = fast::Program::new(&typing);
        Harness {
            base,
            layout,
            typing,
            init,
            actions,
            invariants,
            aprops,
            native: gen.plan.native,
            lib,
            notes,
            fast,
            c_src: gen.src,
            backend: Backend::C,
        }
    }

    /// Names of the functions that are not native (and why some were not
    /// lowered, in `notes`).
    pub fn not_native(&self) -> Vec<String> {
        let mut out = Vec::new();
        if !self.native.init {
            out.push("Init".to_string());
        }
        let names = |v: &[bool], ns: &[String], kind: &str, out: &mut Vec<String>| {
            for (b, n) in v.iter().zip(ns) {
                if !b {
                    out.push(format!("{kind} {n}"));
                }
            }
        };
        names(&self.native.actions, self.base.action_names(), "action", &mut out);
        names(&self.native.invariants, self.base.invariant_names(), "invariant", &mut out);
        names(&self.native.action_properties, self.base.action_property_names(), "aprop", &mut out);
        out
    }

    /// The IR kinds of the lowered functions the native plan marks (or does
    /// not mark) native. The consumer matrix attributes a family to the C and
    /// JIT tiers only where they compiled it, and to the host only where they
    /// did not.
    fn kinds_where(&self, native: bool) -> BTreeSet<&'static str> {
        let mut out = BTreeSet::new();
        if self.native.init == native {
            if let Some(f) = &self.init {
                stmt_kinds(&f.body, &mut out);
            }
        }
        for (i, f) in self.actions.iter().enumerate() {
            if self.native.actions.get(i).copied().unwrap_or(false) == native {
                if let Some(f) = f {
                    stmt_kinds(&f.body, &mut out);
                }
            }
        }
        for (i, p) in self.invariants.iter().enumerate() {
            if self.native.invariants.get(i).copied().unwrap_or(false) == native {
                expr_kinds(&p.body, &mut out);
            }
        }
        for (i, p) in self.aprops.iter().enumerate() {
            if self.native.action_properties.get(i).copied().unwrap_or(false) == native {
                expr_kinds(&p.body, &mut out);
            }
        }
        out
    }

    /// The family marker count in the lowered IR of the functions the
    /// closure executor (`exec::fast`) compiles, and the names of the
    /// functions it leaves to the interpreter. A function the closure
    /// compiler does not cover runs in the interpreter, not in the closure
    /// executor (docs/design.md "Fallback and executors").
    fn closure_evidence(&self, markers: &[&'static str]) -> (usize, Vec<String>) {
        let mut covered: BTreeSet<&'static str> = BTreeSet::new();
        let mut fell_back: Vec<String> = Vec::new();
        let mut visit = |name: &str, is_covered: bool, kinds: &BTreeSet<&'static str>| {
            if !markers.iter().any(|m| kinds.contains(*m)) {
                return;
            }
            if is_covered {
                covered.extend(markers.iter().filter(|m| kinds.contains(**m)).copied());
            } else {
                fell_back.push(name.to_string());
            }
        };
        let expr_kinds_of = |e: &Expr| {
            let mut k = BTreeSet::new();
            expr_kinds(e, &mut k);
            k
        };
        if let Some(f) = &self.init {
            let mut k = BTreeSet::new();
            stmt_kinds(&f.body, &mut k);
            visit("Init", self.fast.init(&self.typing, f).is_ok(), &k);
        }
        for f in self.actions.iter().flatten() {
            let mut k = BTreeSet::new();
            stmt_kinds(&f.body, &mut k);
            visit(&f.name, self.fast.action(&self.typing, f).is_ok(), &k);
        }
        for p in &self.invariants {
            visit(&p.name, self.fast.predicate(&self.typing, p).is_ok(), &expr_kinds_of(&p.body));
        }
        for p in &self.aprops {
            visit(&p.name, self.fast.transition(&self.typing, p).is_ok(), &expr_kinds_of(&p.body));
        }
        for (i, f) in self.typing.funcs.iter().enumerate() {
            visit(&f.name, self.fast.reason(i as u32).is_none(), &expr_kinds_of(&f.body));
        }
        (covered.len(), fell_back)
    }

    /// The consumer matrix row for one operation family: which consumers of
    /// the compiled pipeline ran, delegated or explicitly skipped it
    /// (docs/development-standards.md CODE-19, ARCH-06).
    ///
    /// `markers` names the lowered-IR kinds that identify the family
    /// (non-scalar kinds only: `IntBin`, `Var` and friends occur in every
    /// family). `delegated` names the generated-C host-operation callbacks
    /// the family uses (`h->ref_op`), empty when the family runs inline.
    /// Every cell is an execution, a delegation or a named gap - never a
    /// silent zero.
    pub fn consumers(&self, family: &str, markers: &[&'static str], delegated: &[&str]) -> FamilyConsumers {
        // Every host callback the generated C names is classified (a
        // delegation or run machinery), and a delegation must be a real
        // operation callback: a new delegation cannot reach the C tier
        // unnoticed (ARCH-06).
        let callbacks = host_callbacks(&self.c_src);
        if let Err(why) = classify_host_callbacks(family, callbacks.iter().map(String::as_str), delegated) {
            panic!("{why}");
        }
        let all = self.node_kinds();
        let native_kinds = self.kinds_where(true);
        let host_kinds = self.kinds_where(false);
        let hits = |set: &BTreeSet<&'static str>| markers.iter().filter(|m| set.contains(**m)).count();
        let evidence = |n: usize, why: String| if n > 0 { Cell::ran(n) } else { Cell::gap(why) };

        let mut cells = BTreeMap::new();
        cells.insert(Consumer::Tree, evidence(hits(&all), format!("{family}: no lowered-IR kind")));
        let code = CODE_TIER_KINDS.iter().filter(|k| all.contains(**k)).count();
        cells.insert(Consumer::Code, evidence(code, format!("{family}: the pre-resolved code tier was not reached")));

        // The closure executor compiles each lowered function; one it does
        // not cover is run by the interpreter instead, so it is no closure
        // evidence (docs/design.md "Fallback and executors").
        let (closure, closure_fell_back) = self.closure_evidence(markers);
        let closure_gap = if closure_fell_back.is_empty() {
            format!("{family}: no lowered function contains the family")
        } else {
            format!("{family}: the closure executor leaves {} to the interpreter", closure_fell_back.join(", "))
        };
        cells.insert(Consumer::Closure, evidence(closure, closure_gap));

        // C runs the family inline unless it hands the family's operations to
        // a host callback; the JIT follows the same native plan, so it either
        // runs the same native functions or delegates through the same
        // refops (docs/design.md "native plan").
        let delegated_hits: usize = delegated.iter().map(|cb| self.c_src.matches(cb).count()).sum();
        let native_ran = hits(&native_kinds);
        let c = if self.backend == Backend::Jit {
            Cell::gap("the JIT backend was selected, so no C library was built")
        } else if delegated_hits > 0 {
            Cell::delegated(delegated_hits)
        } else if self.lib.is_some() && native_ran > 0 {
            Cell::ran(native_ran)
        } else {
            Cell::gap(format!("{family}: nothing of the family was compiled to native C"))
        };
        cells.insert(Consumer::C, c);

        let jit = if self.backend != Backend::Jit {
            Cell::gap("the JIT backend is not built in this configuration")
        } else if delegated_hits > 0 {
            Cell::delegated(delegated_hits)
        } else if native_ran > 0 {
            Cell::ran(native_ran)
        } else {
            Cell::gap(format!("{family}: nothing of the family was compiled to the JIT"))
        };
        cells.insert(Consumer::Jit, jit);

        // The host runs the family through a callback C delegates to, or in
        // the functions the C and JIT tiers leave to the host executor.
        let host_ran = if delegated_hits > 0 { delegated_hits } else { hits(&host_kinds) };
        cells.insert(Consumer::Host, evidence(host_ran, format!("{family}: no host callback and no host-only function")));

        let unsupported = self.not_native();
        let unsup = if unsupported.is_empty() {
            Cell::gap(format!("{family}: every function lowered to native"))
        } else {
            Cell::ran(unsupported.len())
        };
        cells.insert(Consumer::Unsupported, unsup);

        FamilyConsumers { family: family.to_string(), cells }
    }

    /// The IR of the lowered functions named `name` (action, invariant or
    /// action property; `Init`), as text.
    pub fn dump(&self, name: &str) -> String {
        let mut out = String::new();
        let stmts = self.init.iter().chain(self.actions.iter().flatten());
        for f in stmts.filter(|f| &*f.name == name) {
            let _ = writeln!(out, "{}:", f.name);
            tlx_compile::ir_fmt::stmt(&f.body, 1, &mut out);
        }
        for p in self.invariants.iter().chain(&self.aprops).filter(|p| &*p.name == name) {
            let _ = writeln!(out, "{}:", p.name);
            tlx_compile::ir_fmt::expr(&p.body, 1, &mut out);
        }
        out
    }

    /// The IR node kinds (`ExprKind` / `Stmt` variant names) occurring in
    /// the lowered functions.
    pub fn node_kinds(&self) -> BTreeSet<&'static str> {
        let mut out = BTreeSet::new();
        let stmts = self.init.iter().chain(self.actions.iter().flatten()).map(|f| &f.body);
        for s in stmts {
            stmt_kinds(s, &mut out);
        }
        for p in self.invariants.iter().chain(&self.aprops) {
            expr_kinds(&p.body, &mut out);
        }
        out
    }

    /// Encode a state; None if it does not fit the layout.
    pub fn encode(&self, vals: &[Value]) -> Option<Box<[u64]>> {
        let mut w = vec![0u64; self.layout.words].into_boxed_slice();
        self.layout.encode_state(vals, &mut w).ok().map(|_| w)
    }

    fn state(vals: &[Value]) -> State {
        State::new(vals.into(), 1, 0)
    }

    fn show(&self, vals: &[Value]) -> String {
        let vars = &self.base.ip.prog.vars;
        vals.iter().zip(vars.iter()).map(|(v, d)| format!("{} = {v}", d.name)).collect::<Vec<_>>().join(", ")
    }

    // ------------------------------------------------------------------
    // running each tier

    /// `f` run on `s0` (None: Init) by the closure executor.
    fn exec_stmt(&self, f: &ActionFn, s0: Option<&[u64]>) -> Res<Vec<Vec<Value>>> {
        let compiled = if s0.is_some() { self.fast.action(&self.typing, f) } else { self.fast.init(&self.typing, f) };
        match compiled {
            Ok(action) => self.fast_stmt(&action, s0),
            Err(_) => Res::Unsupported,
        }
    }

    /// The compiled action `a` run on `s0` by the closure executor.
    fn fast_stmt(&self, a: &fast::ActionProg, s0: Option<&[u64]>) -> Res<Vec<Vec<Value>>> {
        let mut out: Vec<Box<[u64]>> = Vec::new();
        let r = catch_unwind(AssertUnwindSafe(|| {
            let decode = |w: &[u64]| -> Arc<[Value]> { self.layout.decode_state(w).into() };
            let mut emit = |w: &[u64]| -> Result<bool, EvalError> {
                out.push(w.into());
                Ok(true)
            };
            match s0 {
                Some(s0) =>
                // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
                unsafe {
                    fast::run_action_words(
                        &fast::Run::words(&self.base.ip, &self.typing, &self.fast, 1).with_decoder(&decode),
                        a,
                        s0,
                        &mut emit,
                    )
                },
                None => fast::run_init_words(&fast::Run::words(&self.base.ip, &self.typing, &self.fast, 0), a, &mut emit),
            }
        }));
        self.states_of(r, &out)
    }

    fn states_of(&self, r: std::thread::Result<Result<bool, EvalError>>, out: &[Box<[u64]>]) -> Res<Vec<Vec<Value>>> {
        match r {
            Ok(Ok(_)) => Res::Ok(self.decode_all(out)),
            Ok(Err(e)) => Res::Err(e.into_message()),
            Err(p) => Res::Panic(panic_msg(p)),
        }
    }

    fn decode_all(&self, ws: &[Box<[u64]>]) -> Vec<Vec<Value>> {
        let mut v: Vec<Vec<Value>> = ws.iter().map(|w| self.layout.decode_state(w)).collect();
        v.sort();
        v
    }

    /// A predicate run in the closure executor.
    fn exec_pred(&self, p: &PredFn, s: &[u64], t: Option<&[u64]>) -> Res<bool> {
        let compiled = if t.is_some() { self.fast.transition(&self.typing, p) } else { self.fast.predicate(&self.typing, p) };
        match compiled {
            Err(_) => Res::Unsupported,
            Ok(q) => {
                let r = catch_unwind(AssertUnwindSafe(|| {
                    let decode = |w: &[u64]| -> Arc<[Value]> { self.layout.decode_state(w).into() };
                    let run = fast::Run::words(&self.base.ip, &self.typing, &self.fast, 1).with_decoder(&decode);
                    match t {
                        Some(t) =>
                        // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
                        unsafe { fast::eval_trans_words(&run, &q, s, t) },
                        None =>
                        // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
                        unsafe { fast::eval_pred_words(&run, &q, s) },
                    }
                }));
                match r {
                    Ok(Ok(b)) => Res::Ok(b),
                    Ok(Err(e)) => Res::Err(e.into_message()),
                    Err(p) => Res::Panic(panic_msg(p)),
                }
            }
        }
    }

    fn native_states(&self, rc: i32, out: &[Box<[u64]>]) -> Res<Vec<Vec<Value>>> {
        match rc {
            OK => Res::Ok(self.decode_all(out)),
            UNSUPPORTED => Res::Unsupported,
            rc => Res::Err(format!("native rc {rc}")),
        }
    }

    fn native_verdict(rc: i32) -> Res<bool> {
        match rc {
            1 => Res::Ok(true),
            0 => Res::Ok(false),
            UNSUPPORTED => Res::Unsupported,
            rc => Res::Err(format!("native rc {rc}")),
        }
    }

    // ------------------------------------------------------------------
    // comparisons

    /// Record the results of the two compiled tiers against the
    /// interpreter's (`want`).
    fn judge<T: PartialEq + std::fmt::Debug>(
        &self,
        rep: &mut DiffReport,
        what: &str,
        input: &dyn Fn() -> String,
        want: Result<T, String>,
        exec: Res<T>,
        native: Res<T>,
    ) {
        let entry = rep.tallies.entry(what.to_string()).or_default();
        let (mut te, mut tn) = *entry;
        let mut fails = Vec::new();
        for (tier, r, t) in [("IR executor", &exec, &mut te), ("native code", &native, &mut tn)] {
            match (r, &want) {
                (Res::Unsupported, _) => t.unsupported += 1,
                (Res::Panic(p), _) => {
                    t.wrong += 1;
                    fails.push(format!("{tier} panicked: {p}"));
                }
                (Res::Ok(x), Ok(w)) if x == w => t.agree += 1,
                (Res::Ok(x), Ok(w)) => {
                    t.wrong += 1;
                    fails.push(format!("{tier} gives {x:?}, the interpreter {w:?}"));
                }
                (Res::Ok(x), Err(e)) => {
                    t.wrong += 1;
                    fails.push(format!("{tier} gives {x:?} where the interpreter fails ({e})"));
                }
                (Res::Err(_), Err(_)) => t.both_fail += 1,
                (Res::Err(_), Ok(_)) => t.bailout += 1,
            }
        }
        *rep.tallies.get_mut(what).unwrap() = (te, tn);
        for f in fails {
            rep.fail(format!("{what} on {}: {f}", input()));
        }
        if want.is_ok() {
            if let (Res::Ok(_), Res::Err(e)) | (Res::Err(e), Res::Ok(_)) = (&exec, &native) {
                let who = if matches!(exec, Res::Err(_)) { "IR executor" } else { "native code" };
                rep.asym(format!("{what} on {}: only {who} bails out ({e})", input()));
            }
        }
    }

    /// Compare Init in the three tiers.
    pub fn check_init(&self, rep: &mut DiffReport) {
        let mut want: Vec<Vec<Value>> = Vec::new();
        let r = self.base.ip.init_states(self.base.init_expr(), &mut |s1| {
            let vals = s1.iter().map(|v| -> Result<Value, EvalError> {
                Ok(v.as_ref().ok_or_else(|| EvalError::new("incomplete initial state"))?.normalize()?)
            });
            want.push(vals.collect::<Result<_, _>>()?);
            Ok(true)
        });
        want.sort();
        let want = r.map(|_| want).map_err(|e| e.into_message());
        let exec = match &self.init {
            Some(f) => self.exec_stmt(f, None),
            None => Res::Unsupported,
        };
        let native = match (&self.lib, self.native.init) {
            (Some(lib), true) => {
                let mut out = Vec::new();
                let rc = lib.init_into(&mut out);
                self.native_states(rc, &out)
            }
            _ => Res::Unsupported,
        };
        self.judge(rep, "init", &|| "the initial states".into(), want, exec, native);
    }

    /// Compare every action and invariant on the state `vals` (skipped if it
    /// does not fit the layout).
    pub fn check_state(&self, vals: &[Value], rep: &mut DiffReport) {
        let Some(w) = self.encode(vals) else {
            rep.skipped_states += 1;
            return;
        };
        let st = Self::state(vals);
        let input = || self.show(vals);
        let names = self.base.action_names();
        for (i, f) in self.actions.iter().enumerate() {
            let mut want: Vec<Vec<Value>> = Vec::new();
            let r = self.base.successor_values_of(&st, i, &mut |t| want.push(t.to_vec()));
            want.sort();
            let want = r.map(|_| want).map_err(|e| e.message);
            let exec = f.as_ref().map_or(Res::Unsupported, |f| self.exec_stmt(f, Some(&w)));
            let native = match (&self.lib, self.native.actions[i]) {
                (Some(lib), true) => {
                    let mut out = Vec::new();
                    let rc = lib.next_into(&w, i as u32, &mut out);
                    self.native_states(rc, &out)
                }
                _ => Res::Unsupported,
            };
            self.judge(rep, &format!("action {}", names[i]), &input, want, exec, native);
        }
        for (i, p) in self.invariants.iter().enumerate() {
            let want = self.base.check_invariant(&st, i).map(|r| r.is_none()).map_err(|e| e.message);
            let exec = self.exec_pred(p, &w, None);
            let native = match (&self.lib, self.native.invariants[i]) {
                (Some(lib), true) => Self::native_verdict(lib.invariant_raw(&w, i as u32)),
                _ => Res::Unsupported,
            };
            self.judge(rep, &format!("invariant {}", p.name), &input, want, exec, native);
        }
    }

    /// Compare every action property on the step `s -> t`.
    pub fn check_step(&self, s: &[Value], t: &[Value], rep: &mut DiffReport) {
        if self.aprops.is_empty() {
            return;
        }
        let (Some(ws), Some(wt)) = (self.encode(s), self.encode(t)) else {
            rep.skipped_states += 1;
            return;
        };
        let (ss, st) = (Self::state(s), Self::state(t));
        let input = || format!("{} -> {}", self.show(s), self.show(t));
        for (i, p) in self.aprops.iter().enumerate() {
            let want = self.base.check_action_property(&ss, &st, i).map_err(|e| e.message);
            let exec = self.exec_pred(p, &ws, Some(&wt));
            let native = match (&self.lib, self.native.action_properties[i]) {
                (Some(lib), true) => Self::native_verdict(lib.action_property_raw(&ws, &wt, i as u32)),
                _ => Res::Unsupported,
            };
            self.judge(rep, &format!("aprop {}", p.name), &input, want, exec, native);
        }
    }

    /// Up to `max` reachable states (interpreter BFS) and the steps between
    /// them.
    pub fn reachable(&self, max: usize) -> Reachable {
        reachable(&self.base, max)
    }

    /// Init, then every action and invariant on up to `max` reachable
    /// states, and the action properties on the steps between them.
    pub fn run_reachable(&self, max: usize) -> DiffReport {
        let mut rep = DiffReport::default();
        self.check_init(&mut rep);
        let (states, steps) = self.reachable(max);
        for s in &states {
            self.check_state(s, &mut rep);
        }
        for (i, j) in steps {
            self.check_step(&states[i], &states[j], &mut rep);
            // Stuttering steps too.
            self.check_step(&states[i], &states[i], &mut rep);
        }
        rep
    }

    /// `n` random states of the layout's shapes (and random steps between
    /// them) checked into `rep`, on a thread with `RANDOM_STACK_SIZE`: a
    /// recursive definition that terminates on the reachable states may
    /// recurse until the interpreter's depth guard on a random one (a
    /// cycle of pointers), far deeper than a test thread's stack allows.
    pub fn run_random(&self, rng: &mut Rng, n: usize, rep: &mut DiffReport) {
        tlx_base::stack::run_on_big_stack(RANDOM_STACK_SIZE, || self.run_random_here(rng, n, rep))
    }

    fn run_random_here(&self, rng: &mut Rng, n: usize, rep: &mut DiffReport) {
        let mut prev: Option<Vec<Value>> = None;
        for _ in 0..n {
            let s = random_state(&self.layout.vars, rng);
            self.check_state(&s, rep);
            if let Some(p) = &prev {
                self.check_step(p, &s, rep);
            }
            prev = Some(s);
        }
    }
}

/// Reachable states and the steps between them (indices into the states).
pub type Reachable = (Vec<Arc<[Value]>>, Vec<(usize, usize)>);

/// States of the speculation BFS of `Harness::new`.
const PRERUN_STATES: usize = 20_000;

/// Stack of `Harness::run_random`'s thread (virtual; only touched pages are
/// committed). The interpreter's depth guard (100 000 applications) took
/// 320–384 MiB on macOS and more than `tlx_base::stack::EVAL_STACK_SIZE`
/// (512 MiB) on Linux arm64 for a recursion through a function
/// application (exec_vs_native PointerCycles).
const RANDOM_STACK_SIZE: usize = 2 << 30;

/// Up to `max` states reachable in `m` (interpreter BFS; actions failing in
/// a state are skipped) and the steps between them (indices).
/// Enumeration stops at the admission cap; a single evaluation between
/// callbacks cannot be interrupted. Steps cover only the admitted prefix.
pub fn reachable(m: &InterpModel, max: usize) -> Reachable {
    let mut index: HashMap<Arc<[Value]>, usize> = HashMap::new();
    let mut states: Vec<Arc<[Value]>> = Vec::new();
    let mut steps = Vec::new();
    let mut queue = VecDeque::new();
    let add = |v: Arc<[Value]>,
               index: &mut HashMap<Arc<[Value]>, usize>,
               states: &mut Vec<Arc<[Value]>>,
               queue: &mut VecDeque<usize>|
     -> Option<usize> {
        if let Some(&i) = index.get(&v) {
            return Some(i);
        }
        if states.len() >= max {
            return None;
        }
        index.insert(v.clone(), states.len());
        states.push(v);
        queue.push_back(states.len() - 1);
        Some(states.len() - 1)
    };
    if max == 0 {
        return (states, steps);
    }
    let _ = m.init_states_until(&mut |s| {
        if states.len() >= max {
            return false;
        }
        add(s.vals, &mut index, &mut states, &mut queue);
        states.len() < max
    });
    let mut seen_steps = HashSet::new();
    while let Some(i) = queue.pop_front() {
        let st = Harness::state(&states[i]);
        for a in 0..m.actions().len() {
            if states.len() >= max {
                break;
            }
            // Stage only a bounded, structurally unique prefix: an action
            // that errors must still contribute no states or steps.
            let mut succ = Vec::new();
            let mut pending = HashSet::new();
            let mut new_states = 0;
            let result = m.ip.successors(&st.vals, st.level, &m.actions()[a], &mut |s1| {
                if states.len() + new_states >= max {
                    return Ok(false);
                }
                let t: Arc<[Value]> = s1
                    .iter()
                    .map(|v| v.as_ref().ok_or_else(|| EvalError::new("incomplete successor state"))?.normalize())
                    .collect::<Result<Vec<_>, _>>()?
                    .into();
                if pending.insert(t.clone()) {
                    new_states += usize::from(!index.contains_key(&t));
                    succ.push(t);
                }
                Ok(states.len() + new_states < max)
            });
            if result.is_err() {
                continue;
            }
            for t in succ {
                if let Some(j) = add(t, &mut index, &mut states, &mut queue) {
                    if seen_steps.insert((i, j)) {
                        steps.push((i, j));
                    }
                }
            }
        }
    }
    (states, steps)
}

fn panic_msg(p: Box<dyn std::any::Any + Send>) -> String {
    p.downcast_ref::<String>()
        .cloned()
        .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap_or_else(|| "(non-string panic)".into())
}

// ---------------------------------------------------------------------------
// IR node kinds

/// The names of the statement kinds of `s` and of all its expressions.
pub fn stmt_kinds(s: &Stmt, out: &mut BTreeSet<&'static str>) {
    out.insert(match s {
        Stmt::Stop => "Stop",
        Stmt::Emit => "Emit",
        Stmt::Branches(_) => "Branches",
        Stmt::Guard { .. } => "Guard",
        Stmt::If { .. } => "IfStmt",
        Stmt::Then { .. } => "Then",
        Stmt::Let { .. } => "LetStmt",
        Stmt::ForEach { .. } => "ForEach",
        Stmt::Assign { .. } => "Assign",
        Stmt::Error(_) => "Error",
        Stmt::Repeat { .. } => "Repeat",
        Stmt::Count(_) => "Count",
        Stmt::Compose { .. } => "Compose",
    });
    if let Some(e) = s.expr() {
        expr_kinds(e, out);
    }
    s.for_each_sub_stmt(&mut |b| stmt_kinds(b, out));
}

/// The names of the expression kinds of `e` and its sub-expressions
/// (including the statements of `ENABLED`).
pub fn expr_kinds(e: &Expr, out: &mut BTreeSet<&'static str>) {
    use ExprKind::*;
    let name = match &*e.kind {
        Const(_) => "Const",
        ConstWords(_) => "ConstWords",
        Var(_) => "Var",
        NextVar(_) => "NextVar",
        Temp(_) => "Temp",
        Not(_) => "Not",
        And(_) => "And",
        Or(_) => "Or",
        If(..) => "If",
        IntBin(..) => "IntBin",
        IntCmp(..) => "IntCmp",
        Neg(_) => "Neg",
        Eq(..) => "Eq",
        Convert(_) => "Convert",
        Exists { .. } => "Exists",
        Forall { .. } => "Forall",
        Choose { .. } => "Choose",
        Let { .. } => "Let",
        Apply(..) => "Apply",
        ValField(..) => "ValField",
        Slice { .. } => "Slice",
        Index { .. } => "Index",
        ExceptAt { .. } => "ExceptAt",
        ExceptIndex { .. } => "ExceptIndex",
        BitMember { .. } => "BitMember",
        BitSetOp(..) => "BitSetOp",
        BitCard(_) => "BitCard",
        Rank(_) => "Rank",
        Concat(_) => "Concat",
        Pack { .. } => "Pack",
        BitSet(_) => "BitSet",
        SeqLen(_) => "SeqLen",
        SeqIndex { .. } => "SeqIndex",
        SeqTail { .. } => "SeqTail",
        SeqAppend { .. } => "SeqAppend",
        SeqSub { .. } => "SeqSub",
        SortedOp { .. } => "SortedOp",
        SeqFilter { .. } => "SeqFilter",
        SeqConcat { .. } => "SeqConcat",
        UnionField { .. } => "UnionField",
        UnionFieldInt { .. } => "UnionFieldInt",
        OrderedSet { .. } => "OrderedSet",
        ConstElems { .. } => "ConstElems",
        IntRange(..) => "IntRange",
        Subsets(_) => "Subsets",
        Fail(_) => "Fail",
        Filter { .. } => "Filter",
        MapSet { .. } => "MapSet",
        Collect { .. } => "Collect",
        Fold { .. } => "Fold",
        UnionFold { .. } => "UnionFold",
        Call { .. } => "Call",
        RankFlat { .. } => "RankFlat",
        Recode { .. } => "Recode",
        RankUnion { .. } => "RankUnion",
        Lookup { .. } => "Lookup",
        SortedMember { .. } => "SortedMember",
        SortedInsert { .. } => "SortedInsert",
        MapGet { .. } => "MapGet",
        MapPut { .. } => "MapPut",
        MapBuild { .. } => "MapBuild",
        MapMerge(..) => "MapMerge",
        Enabled(s) => {
            stmt_kinds(s, out);
            "Enabled"
        }
        Tuple(_) => "Tuple",
        ValOp { .. } => "ValOp",
        RefOp { .. } => "RefOp",
        RefElems(_) => "RefElems",
        Interp { .. } => "Interp",
    };
    out.insert(name);
    e.for_each_child(&mut |c| expr_kinds(c, out));
}

#[cfg(test)]
mod sampling_tests {
    use super::*;

    #[test]
    fn flood_admission_stops_enumeration() {
        for (init, next, count) in [("\\E n \\in 1..100: Tick /\\ x = n", "x' = x", 3), ("x = 0", "\\E n \\in 1..100: Tick /\\ x' = n", 2)]
        {
            let m = spec::load(
                &crate::module("Flood", &format!("EXTENDS Naturals, TLC\nVARIABLE x\nASSUME TLCSet(0, 0)\nTick == TLCSet(0, TLCGet(0) + 1)\nCount == TLCGet(0)\nInit == {init}\nNext == {next}")),
                "INIT Init\nNEXT Next\n",
            );
            m.check_assumes().unwrap();
            let (states, _) = reachable(&m, 3);
            assert_eq!(states.len(), 3);
            assert_eq!(
                states.iter().map(|s| s[0].clone()).collect::<Vec<_>>(),
                if count == 3 {
                    vec![Value::Int(1), Value::Int(2), Value::Int(3)]
                } else {
                    vec![Value::Int(0), Value::Int(1), Value::Int(2)]
                }
            );
            let d = m.ip.prog.defs.iter().position(|d| &*d.name == "Count").unwrap();
            assert_eq!(m.ip.eval_def_in_state(tlx_sema::hir::DefId(d as u32), &states[0]).unwrap(), Value::Int(count));
        }
    }

    #[test]
    fn sampling_keeps_structural_identity_and_skips_failed_actions() {
        let m = spec::load(
            &crate::module("Prune", "EXTENDS Naturals\nVARIABLE x\nInit == x = 0\nBad == \\E n \\in x..(x + 1): x' = IF n = x THEN 1 ELSE 1 \\div 0\nGood == x' = 8\nNext == Bad \\/ Good\nV == x - x\nC == x = 0"),
            "INIT Init\nNEXT Next\nVIEW V\nCONSTRAINT C\n",
        );
        let (states, steps) = reachable(&m, 10);
        assert_eq!(states, vec![Arc::from([Value::Int(0)]), Arc::from([Value::Int(8)])]);
        assert_eq!(steps, vec![(0, 1), (1, 1)]);
        assert!(reachable(&m, 0).0.is_empty());
    }
}

#[cfg(test)]
mod consumer_matrix_tests {
    use super::*;

    #[test]
    fn host_callbacks_are_classified_or_rejected() {
        // Machinery and operation callbacks are accepted.
        classify_host_callbacks("f", ["emit", "mark", "release", "ref_op"], &[]).unwrap();
        // The callbacks that actually appear in generated C, from a C build.
        classify_host_callbacks("f", ["ref_op", "ref_elems", "release", "mark", "eval", "emit", "elems"], &["h->ref_op"]).unwrap();
    }

    #[test]
    fn an_unclassified_host_callback_is_rejected() {
        let err = classify_host_callbacks("f", ["ref_op", "grade"], &[]).unwrap_err();
        assert!(err.contains("unclassified host callback h->grade"), "{err}");
    }

    #[test]
    fn run_machinery_is_not_an_operation_delegation() {
        let err = classify_host_callbacks("f", ["emit"], &["h->emit"]).unwrap_err();
        assert!(err.contains("run machinery, not an operation delegation"), "{err}");
        let err = classify_host_callbacks("f", ["mark"], &["h->mark"]).unwrap_err();
        assert!(err.contains("run machinery"), "{err}");
    }

    #[test]
    fn a_delegation_must_name_a_generated_callback() {
        let err = classify_host_callbacks("f", [], &["ref_op"]).unwrap_err();
        assert!(err.contains("not named h-><name>"), "{err}");
    }

    #[test]
    fn host_callbacks_scans_generated_c_names() {
        let src = "x = h->ref_op(a); if (h->miss(h)) return; h->emit(b); h->ref_op(c);";
        assert_eq!(host_callbacks(src), BTreeSet::from(["ref_op".to_string(), "miss".to_string(), "emit".to_string()]));
        assert!(host_callbacks("no callbacks here").is_empty());
    }

    /// A cell that claims both an execution and a gap is neither: `assert_ok`
    /// must refuse it so a stale row cannot hide behind a `ran 1` count. The
    /// panic message names the ambiguous cell (CODE-19: no silent zero).
    #[test]
    #[should_panic(expected = "ambiguous cell")]
    fn an_ambiguous_cell_is_rejected() {
        let mut cells = BTreeMap::new();
        for c in Consumer::ALL {
            cells.insert(c, Cell::ran(1));
        }
        cells.insert(Consumer::Tree, Cell { ran: 1, delegated: 0, gap: Some("both".into()) });
        FamilyConsumers { family: "f".into(), cells }.assert_ok();
    }
}
