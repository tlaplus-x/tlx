//! Interpreter setup: binds `.cfg` constants and overrides to a resolved
//! program, and precomputes how definitions may be evaluated (constant-level
//! and cached, action-level and called by name, memoizable per state). The
//! state of a run and the `Interp` methods that read and maintain it live in
//! `run`; the thread-local register, dry-evaluation and output-hold scopes
//! those methods use are declared here.

mod analysis;
pub(crate) use analysis::constant_level_builtin;
mod cfg;
pub(crate) mod effects;
pub(crate) mod local;
mod run;

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};

use tlx_front::cfg::Config;
use tlx_sema::builtins::Builtin;
use tlx_sema::hir::*;
use tlx_sema::Program;
use tlx_value::Value;

use crate::env::Env;
use crate::error::{EResult, EvalError};
use crate::eval::Ctx;
use effects::Registers;

pub use cfg::{cfg_names, cfg_value};

/// Value bound to a CONSTANT.
#[derive(Clone)]
pub enum ConstVal {
    Value(Value),
    /// `C <- Def` for a 0-ary constant (evaluated and cached on use).
    Def(DefId),
    /// `F <- G` for an operator constant.
    Op(OpRef),
    /// `F(1) = a  F(2) = b`: an operator constant given by its values at
    /// some arguments (TLC's OpRcdValue).
    Table(Arc<Vec<(Vec<Value>, Value)>>),
}

pub struct Interp {
    pub prog: Program,
    pub(crate) symmetry_guards: OnceLock<crate::model::autosym::guard::Guards>,
    /// Unique id (key of the per-thread constant copies, `local`).
    pub(crate) uid: u64,
    /// Symbols of the strings in the program.
    pub(crate) syms: local::SymTable,
    pub cfg: Config,
    pub(crate) consts: Vec<Option<ConstVal>>,
    /// `Def = value` overrides from the cfg.
    pub(crate) def_value: DefTable<Value>,
    /// `Def <- Other` overrides from the cfg.
    pub(crate) def_redirect: DefTable<DefId>,
    /// 0-ary, non-LET constant-level definitions (cached in `const_cache`).
    pub(crate) def_const: Vec<bool>,
    /// Function definitions `f[x \in S] == e` whose body refers to `f`.
    def_recursive_fn: Vec<bool>,
    /// Definitions that can call themselves (on a cycle of the static call
    /// graph): the ones the recursion-depth guard is applied to.
    def_recursive: Vec<bool>,
    /// Definitions whose body can observe the next state (`'`, UNCHANGED,
    /// ENABLED, `[A]_v`, or calls such a definition / an operator argument):
    /// their arguments must be passed by name in action contexts.
    pub(crate) def_by_name: Vec<bool>,
    /// Some definition applies `TLCExt!Trace` (`Interp::uses_trace`).
    pub(crate) uses_trace: bool,
    /// Definitions whose arguments TLC passes unevaluated (all but those
    /// TLC overrides by Java methods): an argument whose evaluation fails is
    /// bound by name, so that the error happens only if the body uses it.
    pub(crate) def_defer_errors: Vec<bool>,
    /// The same for LAMBDA operators, by the file they are written in
    /// (computed once: a LAMBDA is applied in hot loops).
    pub(crate) file_lazy_args: Vec<bool>,
    /// `scan_action` of the bodies of applied LAMBDAs (and LET operators
    /// passed as arguments), by arena expression (0: not computed yet,
    /// 1: no, 2: yes): `apply_opval` needs it at every application in an
    /// action context, and the scan only depends on the body.
    lambda_action: Box<[std::sync::atomic::AtomicU8]>,
    /// Constant-level definitions of any arity.
    pub(crate) def_pure: Vec<bool>,
    /// Definitions that (transitively) use a nondeterministic or
    /// side-effecting builtin (`Builtin::is_volatile`), not counting
    /// applications of operator parameters (`def_effectful`).
    pub(crate) def_effectful: Vec<bool>,
    /// Constant-level, non-LET operators with (value) parameters: their
    /// applications in constant contexts are memoized (`memo`).
    pub(crate) def_memo: Vec<bool>,
    /// 0-ary, non-LET, state-level (not action-level, not constant),
    /// deterministic definitions: memoizable per state context.
    pub(crate) def_state_cacheable: Vec<bool>,
    /// States TLC counts as generated that do not reach the explorer:
    /// intermediate states of action compositions enumerated so far, and
    /// successors that could not be completed (incomplete, or VIEW failed).
    pub composed_states: std::sync::atomic::AtomicU64,
    /// The complete assignments of the variables that the last enumeration
    /// of the initial states rejected (a conjunct after the last assignment
    /// was false): TLC counts them in the coverage of the initial predicate.
    pub init_rejected: std::sync::atomic::AtomicU64,
    /// 0-ary LET definitions whose value is cached per LET evaluation.
    pub(crate) let_cacheable: Vec<bool>,
    /// Values of the `def_const` definitions, computed on first use.
    pub(crate) const_cache: Vec<OnceLock<EResult<Value>>>,
    /// Domains of bound variables that are closed constant expressions
    /// (`is_closed_constant`), keyed by the address of their `ExprKind`:
    /// their slot in the per-thread tables (`local::Slot::Bound`, filled by
    /// `Interp::bound_elems`).
    pub(crate) closed_bounds: local::AddrMap<u32>,
    /// What TLC evaluates at startup, in its order (`eval_constant_defns`).
    constant_defns: Vec<RootSymbol>,
    constant_defns_done: std::sync::Once,
    /// Evaluating the definitions the cfg substitutes for constants before
    /// the model exists (`check_constant_substitutions`): TLC's statistics
    /// are undefined then.
    pub(crate) before_model: std::sync::atomic::AtomicBool,
    /// TLC binds `\div` per module: floor division only if Integers is loaded.
    pub(crate) div_floor: bool,
    /// Standard-module operators overridden by the cfg (`Seq <- LimitedSeq`):
    /// uses of the native builtin are routed to the overridden definition.
    /// Few entries, looked up on every builtin application: a linear scan
    /// (a SipHash map lookup there cost 10% of MCReachabilityTestAllGraphs).
    builtin_override: Vec<(Builtin, DefId)>,
    /// The state of the current run (configuration, registers, exit request,
    /// side effects, statistics), as opposed to the program and what is
    /// derived from it.
    run: run::RunState,
    /// The generators behind RandomElement and the Randomization module.
    pub(crate) random: Mutex<crate::random::Randomness>,
    /// `TLCCache(expression, closure)`: by the location of the expression,
    /// None if it is not constant-level, else the values it was evaluated
    /// to, by closure value (see `Interp::tlc_cache`).
    pub(crate) tlc_cache: Mutex<HashMap<Span, Option<Vec<(Value, Value)>>>>,
    /// The code of the program's expressions (`ExprId` index), compiled on
    /// first evaluation (`Interp::code_of`).
    pub(crate) codes: Box<[OnceLock<crate::code::Code>]>,
    /// Hoisting slots handed out (`code::Node::Hoist`, `code::Node::Shared`).
    pub(crate) hoist_slots: std::sync::atomic::AtomicUsize,
}

/// What `TLCGet("spec")` and `TLCGet("action")` report (built by
/// `InterpModel::new`).
#[derive(Clone, Debug)]
pub struct SpecInfo {
    /// The `TLCGet("spec")` record.
    pub spec: Value,
    /// `TLCGet("action")` for an initial state, and for a state produced by
    /// each action (in simulation).
    pub init_action: Value,
    pub actions: Vec<Value>,
}

/// Registers serialized (`tlx_value::ser`): count, then (index, value) by
/// index. The effect replay journal is process-local and is not part of these
/// bytes. A change to this payload requires a checkpoint manifest VERSION
/// bump (`tlx-runtime/src/explore/checkpoint/manifest.rs`); changing the
/// process-local replay keys does not.
fn write_registers(regs: &Registers) -> Result<Vec<u8>, String> {
    let mut keys: Vec<i64> = regs.keys().copied().collect();
    keys.sort_unstable();
    let mut w = tlx_value::ser::Writer::new();
    w.usize(keys.len());
    for k in keys {
        w.ivar(k);
        w.value(&regs[&k]).map_err(|e| format!("cannot write the TLCSet register {k} to a checkpoint: {e}"))?;
    }
    Ok(w.into_bytes())
}

/// Registers written by `write_registers`.
pub(crate) fn read_registers(b: &[u8]) -> Result<Registers, String> {
    let mut r = tlx_value::ser::Reader::new(b);
    let e = |e: tlx_value::ser::DecodeError| format!("corrupt TLCSet registers in the checkpoint: {e}");
    let n = r.count(2).map_err(e)?;
    let mut regs = Registers::with_capacity_and_hasher(n, Default::default());
    for _ in 0..n {
        let k = r.ivar().map_err(e)?;
        regs.insert(k, r.value().map_err(e)?);
    }
    r.finish().map_err(e)?;
    Ok(regs)
}

/// A copy of the main thread's TLCGet/TLCSet registers.
#[derive(Clone, Debug, Default)]
pub struct SavedRegisters(Registers);

/// A simulation run, as reported by `TLCGet("config")`.
#[derive(Clone, Copy, Debug, Default)]
pub struct SimConfig {
    /// `-generate` rather than `-simulate`.
    pub generate: bool,
    /// The number of behaviors (TLC: workers times `num`, as a Java int).
    pub traces: i64,
    /// The maximum length of a behavior; -1 if unbounded.
    pub depth: i64,
    pub seed: i64,
}

/// Statistics of a finished run, as reported by `TLCGet("stats")`.
#[derive(Clone, Copy, Debug, Default)]
pub struct RunStats {
    pub distinct: u64,
    pub generated: u64,
    pub queue: u64,
    pub diameter: u64,
    pub duration_secs: u64,
    pub initial: u64,
    /// Behaviors generated (simulation only).
    pub traces: Option<u64>,
    /// Mean and variance of the behavior lengths (simulation only).
    pub level_mean: u64,
    pub level_variance: i64,
}

/// A map keyed by definition, stored densely (looked up on hot paths).
pub(crate) struct DefTable<T>(Vec<Option<T>>);

impl<T> DefTable<T> {
    fn new(n: usize, m: HashMap<DefId, T>) -> DefTable<T> {
        let mut v: Vec<Option<T>> = (0..n).map(|_| None).collect();
        for (d, x) in m {
            v[d.idx()] = Some(x);
        }
        DefTable(v)
    }

    #[inline]
    pub(crate) fn get(&self, d: &DefId) -> Option<&T> {
        self.0.get(d.idx()).and_then(Option::as_ref)
    }

    #[inline]
    pub(crate) fn contains_key(&self, d: &DefId) -> bool {
        self.get(d).is_some()
    }

    pub(crate) fn values(&self) -> impl Iterator<Item = &T> {
        self.0.iter().flatten()
    }
}

/// Where output started being held back (`Interp::hold_begin`).
#[must_use]
pub struct HoldMark {
    was: bool,
    start: usize,
}

impl Drop for HoldMark {
    fn drop(&mut self) {
        HOLDING.set(self.was);
        HELD.with(|h| h.borrow_mut().truncate(self.start));
    }
}

thread_local! {
    /// Per-thread registers, keyed by interpreter uid (not address: a later
    /// interpreter at the address of a dropped one must not see its
    /// registers), and which worker of the search this thread is (if one).
    static REGISTERS: RefCell<tlx_base::hash::FxMap<u64, (Registers, Option<usize>)>> = RefCell::new(Default::default());
    /// Evaluations on this thread have no lasting side effects (see
    /// `Interp::without_effects`).
    static DRY: Cell<bool> = const { Cell::new(false) };
    /// Print/PrintT output of this thread is held back (see
    /// `Interp::hold_output`), and the lines held.
    static HOLDING: Cell<bool> = const { Cell::new(false) };
    static HELD: RefCell<Vec<String>> = const { RefCell::new(Vec::new()) };
}

impl Interp {
    pub fn new(mut prog: Program, cfg: Config) -> EResult<Arc<Interp>> {
        cfg::intern_cfg(&cfg);
        cfg::intern_sources(&mut prog);
        let constant_defns = prog.tlc_constant_defn_order();
        let cfg::CfgBindings { consts, def_value, def_redirect } = cfg::bind_cfg(&mut prog, &cfg)?;
        if let Some(e) = prog.take_errors().first() {
            return Err(EvalError::at(e.message.clone(), e.span));
        }
        let div_floor = prog.has_module("Integers");
        let builtin_override =
            def_value.keys().chain(def_redirect.keys()).filter_map(|d| prog.defs[d.idx()].builtin.map(|b| (b, *d))).collect();
        let def_value = DefTable::new(prog.defs.len(), def_value);
        let def_redirect = DefTable::new(prog.defs.len(), def_redirect);
        let mut ip = Interp {
            uid: local::fresh_uid(),
            symmetry_guards: OnceLock::new(),
            syms: local::SymTable::new(&prog),
            builtin_override,
            run: run::RunState::new(),
            random: Mutex::new(crate::random::Randomness::new(0)),
            tlc_cache: Default::default(),
            consts,
            def_value,
            def_redirect,
            def_const: Vec::new(),
            def_recursive_fn: Vec::new(),
            def_recursive: Vec::new(),
            def_by_name: Vec::new(),
            uses_trace: false,
            def_defer_errors: Vec::new(),
            file_lazy_args: Vec::new(),
            lambda_action: Box::default(),
            def_state_cacheable: Vec::new(),
            let_cacheable: Vec::new(),
            composed_states: Default::default(),
            init_rejected: Default::default(),
            def_pure: Vec::new(),
            def_effectful: Vec::new(),
            def_memo: Vec::new(),
            const_cache: Vec::new(),
            closed_bounds: Default::default(),
            constant_defns,
            constant_defns_done: std::sync::Once::new(),
            before_model: Default::default(),
            div_floor,
            codes: (0..prog.arena_len()).map(|_| OnceLock::new()).collect(),
            hoist_slots: Default::default(),
            prog,
            cfg,
        };
        ip.analyze_defs();
        Ok(Arc::new(ip))
    }

    // --- queries (also used by the compiler, tlx-compile) ---

    /// The root-visible definition named `name`. The program is shared and
    /// cannot be resolved further here; everything the cfg names was
    /// resolved in `new`.
    pub fn root_def(&self, name: &str) -> Option<DefId> {
        (0..self.prog.defs.len()).map(|i| DefId(i as u32)).find(|d| {
            let def = &self.prog.defs[d.idx()];
            &*def.name == name && !self.prog.def_is_let(*d) && !matches!(def.kind, DefKind::Pending)
        })
    }

    /// The environment a definition's body is evaluated in: LET definitions
    /// close over the environment of their use, others see no locals.
    pub(crate) fn def_env(&self, d: DefId, env: &Env) -> Env {
        if self.prog.def_is_let(d) {
            env.clone()
        } else {
            Env::default()
        }
    }

    /// The body of `d` (after cfg redirection) if it is an ordinary,
    /// user-defined operator; `None` for built-ins and function definitions.
    pub(crate) fn plain_op_body(&self, d: DefId) -> Option<(DefId, &Expr)> {
        let d = self.redirect_def(d);
        let def = &self.prog.defs[d.idx()];
        match &def.kind {
            DefKind::Op(body) if def.builtin.is_none() => Some((d, body)),
            _ => None,
        }
    }

    /// Values bound to CONSTANTs and to definitions by the cfg (hints for
    /// shape inference).
    pub fn cfg_values(&self) -> Vec<Value> {
        let consts = self.consts.iter().filter_map(|c| match c {
            Some(ConstVal::Value(v)) => Some(v.clone()),
            _ => None,
        });
        consts.chain(self.def_value.values().cloned()).collect()
    }

    /// Follow cfg `Def <- Other` redirections.
    pub fn redirect_def(&self, d: DefId) -> DefId {
        let mut d = d;
        while let Some(&t) = self.def_redirect.get(&d) {
            d = t;
        }
        d
    }

    /// Whether the cfg assigns a value to definition `d` (`Def = v`).
    pub fn has_def_value(&self, d: DefId) -> bool {
        self.def_value.contains_key(&d)
    }

    /// 0-ary constant-level (cached) definition.
    pub fn is_const_def(&self, d: DefId) -> bool {
        self.def_const[d.idx()]
    }

    /// 0-ary constant-level definition whose value is already computed (and
    /// cached): using it creates no strings.
    pub fn const_def_evaluated(&self, d: DefId) -> bool {
        self.def_const[d.idx()] && self.const_cache[d.idx()].get().is_some()
    }

    /// Constant-level definition of any arity (its result depends only on its arguments).
    pub fn is_pure_def(&self, d: DefId) -> bool {
        self.def_pure[d.idx()]
    }

    /// Whether definition `d` (after redirection by a cfg override)
    /// transitively uses a nondeterministic or side-effecting builtin
    /// (`Builtin::is_volatile`: Print, TLCSet, RandomElement, ...) or is
    /// still pending: its applications must be evaluated every time. An
    /// application of an operator parameter does not count (the operator it
    /// ends up applying is scanned where it is written). Independent of
    /// constness: a volatile constant definition is still evaluated once
    /// (`is_const_def`).
    pub fn def_effectful(&self, d: DefId) -> bool {
        self.def_effectful[self.redirect_def(d).idx()]
    }

    /// Function definition `f[x \in S] == e` whose body refers to `f`.
    pub fn is_recursive_fn(&self, d: DefId) -> bool {
        self.def_recursive_fn[d.idx()]
    }

    /// Definition that can call itself (on a cycle of the static call graph):
    /// applications of it take the recursion-depth guard.
    pub fn is_recursive(&self, d: DefId) -> bool {
        self.def_recursive[d.idx()]
    }

    /// Evaluate (and cache) the constant-level definitions TLC evaluates at
    /// startup, in its order (`Program::tlc_constant_defn_order`), ignoring
    /// errors as TLC does, where it shows: those that may create strings,
    /// which fixes the order of their strings (TLC's `UniqueString` tokens
    /// are assigned on creation, so this is their order in sets), and those
    /// making random choices or printing (after the seed is set: TLC
    /// evaluates them with the seeded random stream). The others are
    /// evaluated on first use: the value is the same, and an unused one may
    /// be expensive or diverge (TLC survives a stack overflow there; tlx
    /// would not). Runs once, before anything else is evaluated.
    pub fn eval_constant_defns(self: &Arc<Self>) {
        self.constant_defns_done.call_once(|| {
            // (Type-aware: `Tail`, `SubSeq` and `\o` count only where
            // their operand may be a string.)
            let strings = crate::strings::StringMakers::typed(self);
            for s in &self.constant_defns {
                let d = match *s {
                    RootSymbol::Const(c) => match &self.consts[c.idx()] {
                        Some(ConstVal::Def(t)) => *t,
                        _ => continue,
                    },
                    RootSymbol::Def(d) if !self.def_value.contains_key(&d) => self.redirect_def(d),
                    _ => continue,
                };
                let def = &self.prog.defs[d.idx()];
                if self.def_const[d.idx()]
                    && def.builtin.is_none()
                    && !self.def_value.contains_key(&d)
                    && (!self.def_pure[d.idx()] || strings.applied(d))
                {
                    let _ = self.call_def(d, &Env::default(), &Ctx::NONE, def.span);
                }
            }
        });
    }

    /// TLC evaluates the definition substituted for each constant (`C <-
    /// D`) at startup, before the model exists
    /// (SpecProcessor.processConstantDefns); one that fails and is not
    /// constant-level (it refers to variables, or TLCGet) is a
    /// configuration error (EC.TLC_CONFIG_SUBSTITUTION_NON_CONSTANT): the
    /// error's constant, definition and message.
    pub fn check_constant_substitutions(self: &Arc<Self>) -> Result<(), (String, String, String)> {
        for (i, c) in self.consts.iter().enumerate() {
            let Some(ConstVal::Def(d)) = c else { continue };
            let d = self.redirect_def(*d);
            let def = &self.prog.defs[d.idx()];
            if self.def_const[d.idx()] || !def.params.is_empty() || def.builtin.is_some() || self.def_value.contains_key(&d) {
                continue;
            }
            self.before_model.store(true, std::sync::atomic::Ordering::Relaxed);
            let r = self.call_def(d, &Env::default(), &Ctx::NONE, def.span);
            self.before_model.store(false, std::sync::atomic::Ordering::Relaxed);
            if let Err(e) = r {
                return Err((self.prog.consts[i].name.to_string(), def.name.to_string(), e.message.to_string()));
            }
        }
        Ok(())
    }

    /// Whether the definition's body can observe the next state, so that its
    /// arguments are passed by name in action contexts (`def_by_name`).
    pub fn is_action_level(&self, d: DefId) -> bool {
        self.def_by_name[d.idx()]
    }

    /// Whether an argument of `d` that fails to evaluate is an error only
    /// where the body uses it (TLC passes arguments lazily). False for the
    /// standard- and community-module definitions TLC overrides by Java
    /// methods: those evaluate every argument.
    pub fn defers_arg_errors(&self, d: DefId) -> bool {
        self.def_defer_errors[d.idx()]
    }

    /// `defers_arg_errors` for a LAMBDA written in `file`.
    pub fn lambda_defers_arg_errors(&self, file: tlx_front::ast::FileId) -> bool {
        self.lambda_lazy_args(file)
    }

    /// 0-ary LET definition whose value may be computed once per LET.
    pub fn is_let_cacheable(&self, d: DefId) -> bool {
        self.let_cacheable[d.idx()]
    }

    /// 0-ary, deterministic, state-level (non-constant, non-action) definition.
    pub fn is_state_cacheable(&self, d: DefId) -> bool {
        self.def_state_cacheable[d.idx()]
    }

    /// Value of 0-ary definition `d` in state `s0`.
    pub fn eval_def_in_state(self: &Arc<Self>, d: DefId, s0: &[Value]) -> EResult<Value> {
        self.call_def(d, &Env::default(), &Ctx::state(s0, 0), Default::default())
    }

    /// Whether the cfg overrides this standard-module operator.
    pub fn is_builtin_overridden(&self, b: Builtin) -> bool {
        self.builtin_override(b).is_some()
    }

    /// The definition overriding standard-module operator `b`, if any.
    #[inline]
    pub(crate) fn builtin_override(&self, b: Builtin) -> Option<DefId> {
        if self.builtin_override.is_empty() {
            return None;
        }
        self.builtin_override.iter().find(|(x, _)| *x == b).map(|(_, d)| *d)
    }

    /// `\div` is floor division (Integers loaded) rather than TLC's Naturals quirk.
    pub fn div_is_floor(&self) -> bool {
        self.div_floor
    }

    /// The operator an operator constant is bound to by the cfg.
    pub fn const_op_ref(&self, c: ConstId) -> Option<OpRef> {
        match &self.consts[c.idx()] {
            Some(ConstVal::Op(r)) => Some(*r),
            _ => None,
        }
    }

    /// The definition a 0-ary constant is bound to by the cfg (`C <- Def`).
    pub fn const_def(&self, c: ConstId) -> Option<DefId> {
        match &self.consts[c.idx()] {
            Some(ConstVal::Def(d)) => Some(*d),
            _ => None,
        }
    }
}

#[cfg(test)]
mod scope_tests {
    use super::*;
    use std::panic::{catch_unwind, AssertUnwindSafe};
    use std::sync::atomic::Ordering;

    fn interp() -> Arc<Interp> {
        let dir = tlx_testkit::TempDir::new("interp-scopes");
        let path = dir.write(
            "Scopes.tla",
            &tlx_testkit::module(
                "Scopes",
                "EXTENDS Integers, TLC\nPut == TLCSet(0, 2)\nRead == TLCGet(0)\nSay(s) == PrintT(s)\nFail == 1 \\div 0\n",
            ),
        );
        Interp::new(Program::load(&path, &[]).unwrap(), Config::default()).unwrap()
    }

    fn eval(ip: &Arc<Interp>, name: &str) -> EResult<Value> {
        // A 0-ary constant-level PrintT definition is cached after its first use.
        let args = if name == "Say" { vec![Expr::new(ExprKind::Str("line".into()), Span::default())] } else { vec![] };
        let expr = Expr::new(ExprKind::Apply { op: OpRef::Def(ip.root_def(name).unwrap()), args }, Span::default());
        ip.eval(&expr, &Env::default(), &Ctx::NONE)
    }

    #[test]
    fn output_scope_restores_after_unwind_and_result_error() {
        let ip = interp();
        assert!(catch_unwind(AssertUnwindSafe(|| {
            Interp::hold_output(|| {
                eval(&ip, "Say").unwrap();
                panic!("abort capture");
            });
        }))
        .is_err());
        assert!(!HOLDING.get());
        HELD.with(|h| assert!(h.borrow().is_empty()));
        let expected = eval(&ip, "Fail").unwrap_err().to_string();
        let (result, lines) = Interp::hold_output(|| {
            eval(&ip, "Say")?;
            eval(&ip, "Fail")
        });
        assert_eq!(result.unwrap_err().to_string(), expected);
        assert_eq!(lines, ["\"line\""]);
        assert!(!HOLDING.get());
    }

    #[test]
    fn nested_output_scopes_preserve_the_outer_prefix() {
        let ip = interp();
        let (_, outer) = Interp::hold_output(|| {
            ip.print_line("before");
            assert!(catch_unwind(AssertUnwindSafe(|| {
                Interp::hold_output(|| {
                    ip.print_line("discarded");
                    panic!("abort nested capture");
                });
            }))
            .is_err());
            let (_, inner) = Interp::hold_output(|| ip.print_line("inner"));
            assert_eq!(inner, ["inner"]);
            ip.print_line("after");
        });
        assert_eq!(outer, ["before", "after"]);
        assert!(!HOLDING.get());
        HELD.with(|h| assert!(h.borrow().is_empty()));
    }

    #[test]
    fn dropped_two_step_output_mark_discards_only_its_scope() {
        let ip = interp();
        let (_, lines) = Interp::hold_output(|| {
            ip.print_line("before");
            let mark = Interp::hold_begin();
            ip.print_line("discarded");
            drop(mark);
            ip.print_line("after");
        });
        assert_eq!(lines, ["before", "after"]);
        assert!(!HOLDING.get());
    }

    fn check_dry_scope(ip: &Arc<Interp>) {
        ip.set_register(0, Value::Int(1));
        let before = ip.with_registers(|r, _| r.clone());
        let copies = ip.copies_of_registers(true, std::thread::current().id());
        assert!(catch_unwind(AssertUnwindSafe(|| {
            ip.without_effects(|| {
                eval(ip, "Put").unwrap();
                ip.count_composed_states(7);
                panic!("abort dry evaluation");
            });
        }))
        .is_err());
        assert!(!DRY.get());
        assert_eq!(ip.with_registers(|r, _| r.clone()), before);
        assert_eq!(ip.copies_of_registers(true, std::thread::current().id()), copies);
        assert_eq!(eval(ip, "Read").unwrap(), Value::Int(1));
        let expected = eval(ip, "Fail").unwrap_err().to_string();
        let result = ip.without_effects(|| {
            eval(ip, "Put").unwrap();
            assert!(catch_unwind(AssertUnwindSafe(|| {
                ip.without_effects(|| {
                    ip.set_register(0, Value::Int(9));
                    panic!("abort nested dry evaluation");
                });
            }))
            .is_err());
            assert!(DRY.get());
            assert_eq!(eval(ip, "Read").unwrap(), Value::Int(2));
            let result = ip.without_effects(|| eval(ip, "Fail"));
            assert!(DRY.get());
            assert_eq!(eval(ip, "Read").unwrap(), Value::Int(2));
            result
        });
        assert_eq!(result.unwrap_err().to_string(), expected);
        assert!(!DRY.get());
        assert_eq!(ip.with_registers(|r, _| r.clone()), before);
        assert_eq!(ip.copies_of_registers(true, std::thread::current().id()), copies);
        eval(ip, "Put").unwrap();
        assert_eq!(eval(ip, "Read").unwrap(), Value::Int(2));
        ip.count_composed_states(3);
        assert_eq!(ip.composed_states.load(Ordering::Relaxed), 3);
    }

    #[test]
    fn dry_scope_restores_main_and_worker_copies() {
        let ip = interp();
        ip.run.worker_regs.lock().unwrap().push(Some((std::thread::current().id(), Registers::default())));
        check_dry_scope(&ip);
    }

    #[test]
    fn dry_scope_restores_worker_thread_registers() {
        let ip = interp();
        std::thread::spawn(move || {
            REGISTERS.with(|r| r.borrow_mut().insert(ip.uid, (Registers::default(), Some(0))));
            ip.run.worker_regs.lock().unwrap().push(Some((std::thread::current().id(), Registers::default())));
            check_dry_scope(&ip);
        })
        .join()
        .unwrap();
    }
}

#[cfg(test)]
mod checkpoint_tests {
    use super::*;

    #[test]
    fn register_checkpoint_manifest_v3_bytes_are_unchanged_by_replay_keys() {
        // Independent manifest-v3 register payload fixture: sorted indices 1, 2, 3; Int(7), TRUE,
        // and an interval-domain function 0 |-> 1 (tag 15).
        const V3: &[u8] = &[3, 2, 2, 14, 4, 1, 6, 15, 1, 2, 0, 2, 2];
        let f = Value::Fcn(Arc::from([(Value::Int(0), Value::Int(1))]), tlx_value::FcnDom::Interval);
        let regs = Registers::from_iter([(3, f), (2, Value::TRUE), (1, Value::Int(7))]);
        assert_eq!(write_registers(&regs).unwrap(), V3);
        let decoded = read_registers(V3).unwrap();
        assert_eq!(decoded, regs);
        assert!(matches!(&decoded[&3], Value::Fcn(_, tlx_value::FcnDom::Interval)));
        let recovered = effects::Effects::default();
        recovered.set_resume(vec![Some(decoded)]);
        assert_eq!(recovered.take_resume_registers(0), Some(regs));
        assert_eq!(recovered.take_resume_registers(0), None);
        for cut in 0..V3.len() {
            assert!(read_registers(&V3[..cut]).is_err());
        }
        let mut trailing = V3.to_vec();
        trailing.push(0);
        assert!(read_registers(&trailing).is_err());
    }
}
