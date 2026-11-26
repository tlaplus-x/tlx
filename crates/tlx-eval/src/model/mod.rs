//! The interpreted model: `InterpModel`, its construction from the
//! configuration and the specification, and the evaluator-based state
//! enumeration.
//!
//! The layers that face the outside world live in their own modules so that
//! construction, execution, persistence and reporting stay at separate
//! responsibility boundaries (CODE-03): `runtime_adapter.rs` holds the
//! `tlx_runtime::Model` implementation, `report.rs` the TLC-shaped
//! locations, coverage labels, ALIAS rendering and evaluation errors, and
//! `checkpoint.rs` the checkpoint persistence. Their public paths are
//! re-exported here, so the extraction does not move any API (`ARCH-10`).

pub mod autosym;
mod checkpoint;
pub mod liveness;
mod optimization;
mod ordered;
mod print_order;
mod report;
mod runtime_adapter;
mod spec;
pub mod spec_info;
mod startup;
pub mod symcheck;
mod symmetry;

use std::rc::Rc;
use std::sync::Arc;

use tlx_front::cfg::Config;
use tlx_runtime::{stats, Model, ModelError};
use tlx_sema::hir::*;
use tlx_sema::source::EndTrim;
use tlx_value::{Sym, Value};

use crate::enumerate::Action;
use crate::env::Env;
use crate::error::{EResult, EvalError};
use crate::eval::{same_rep, Ctx, DefCache, StateMemo};
use crate::interp::Interp;
pub use checkpoint::{restore_strings, strings_snapshot, STRINGS_FILE};
pub(crate) use report::fmt_state;
pub use report::{location_record, ActionInfo};
use spec::PropPart;
pub use spec::TAUTOLOGY;
pub use symmetry::StateVals;
use symmetry::{ChosenPerm, Group, Perm};

/// States whose definition memos a thread keeps (the state being expanded
/// and its latest successors).
const MEMO_STATES: usize = 4;

thread_local! {
    /// Memos of state-level definitions of recently used states, keyed by
    /// interpreter and state (the state is kept alive, so its address is not
    /// reused while it is a key).
    static MEMOS: std::cell::RefCell<Vec<(u64, Arc<[Value]>, Rc<StateMemo>)>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// An interpreted state: variable values (in `VarId` order) plus the BFS level
/// at which it was found (for `TLCGet("level")`; not part of its identity).
#[derive(Clone, Debug)]
pub struct State {
    pub vals: Arc<[Value]>,
    pub level: u32,
    /// Fingerprint (computed once; accounts for VIEW and SYMMETRY).
    pub fp: u64,
    /// The fingerprints of the variable values, if known (a successor
    /// made without VIEW and SYMMETRY): its own successors take those of the
    /// values they share with it from here instead of fingerprinting them
    /// again.
    pub var_fps: Option<Arc<[u64]>>,
}

impl State {
    /// A state without known variable fingerprints.
    pub fn new(vals: Arc<[Value]>, level: u32, fp: u64) -> State {
        State { vals, level, fp, var_fps: None }
    }
}

/// A source location as TLC reports it (the end is the last non-blank
/// character, see `Model::location_parts`).
pub use tlx_sema::source::SourceRange as Location;

/// A warning about the specification or configuration (TLC prints it
/// before the search, with a message code of its kind).
#[derive(Clone, Debug)]
pub struct Warning {
    pub kind: WarningKind,
    pub text: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WarningKind {
    /// A variable missing from the subscript of `[][Next]_vars`
    /// (TLC_SUBSCRIPT_CONTAIN_NO_STATE_VAR).
    SubscriptWithoutVariable,
    /// SYMMETRY with temporal properties
    /// (TLC_FEATURE_UNSUPPORTED_LIVENESS_SYMMETRY).
    LivenessSymmetry,
}

/// The fingerprints an `InterpModel` gives its states (`with_fp_mode`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FpMode {
    /// Reduced by the VIEW and SYMMETRY of the cfg: TLC's fingerprints.
    Reduced,
    /// Of the variable values alone, for a caller that does not need the
    /// reduction (a shape pre-run) or fingerprints the states itself (the
    /// compiled tier, on encodings).
    Plain,
}

/// The interpreted model. (`Clone` is for `with_fp_mode`.)
#[derive(Clone)]
pub struct InterpModel {
    pub ip: Arc<Interp>,
    /// False when the cfg has no behavior spec (only ASSUMEs are checked).
    pub has_behavior: bool,
    /// True when the cfg has an INIT but no next-state action: the initial
    /// states are computed, then there is nothing to expand (TLC 2115).
    pub no_next: bool,
    init: Expr,
    /// The INSTANCE statement each conjunct of `init` from the
    /// SPECIFICATION is under, if any (see `spec::split_spec`; empty: none).
    init_within: Vec<Option<Span>>,
    actions: Vec<Action>,
    action_names: Vec<String>,
    invariants: Vec<Expr>,
    invariant_names: Vec<String>,
    constraints: Vec<Expr>,
    action_constraints: Vec<Expr>,
    /// Safety parts of PROPERTY of the form `[][A]_v`.
    action_props: Vec<Expr>,
    action_prop_names: Vec<String>,
    /// PROPERTY parts that are state predicates (checked on initial states).
    init_props: Vec<(String, Expr)>,
    pub check_deadlock: bool,
    /// SYMMETRY group (factorized for disjoint symmetric-group products, or
    /// explicit fallback for arbitrary subgroups).
    group: Group,
    /// How states are fingerprinted (fixed: see `with_fp_mode`).
    fp_mode: FpMode,
    /// Liveness obligations (empty: none).
    pub live: liveness::LiveSpec,
    /// `-coverage`: the initial states are enumerated by the interpreter
    /// in every tier (which counts the assignments Init rejects, see
    /// `Interp::init_rejected`). Set by the caller.
    pub coverage: bool,
    /// VIEW: states are fingerprinted by the value of this expression.
    view: Option<Expr>,
    /// A proved state projection is canonicalized before symmetry.
    state_projection: bool,
    ordered_projection: Option<Arc<tlx_sema::optimize::OrderedPlan>>,
    /// Optional Lean certificate emitted with the accepted projection.
    projection_certificate: Option<Arc<str>>,
    /// ALIAS: error-trace states are displayed as this record.
    alias: Option<Expr>,
    /// POSTCONDITIONs (name, definition), checked after model checking.
    postconditions: Vec<(String, DefId)>,
    /// `_POSSIBLE` predicates and whether each was witnessed, shared by the
    /// copies of the model (the workers).
    possible: Arc<Vec<Possible>>,
    /// The POSTCONDITION checked last (its index), for its label.
    post_at: Arc<std::sync::atomic::AtomicUsize>,
    /// Warnings about the specification and configuration, printed before
    /// the search.
    pub warnings: Vec<Warning>,
    /// The order in which TLC prints the variables (computed when first
    /// needed).
    var_order: std::sync::OnceLock<Vec<usize>>,
    /// A symmetry tlx applies on its own (`apply_symmetry`), checked at
    /// sampled expanded states under `TLX_SYMMETRY_PARANOID`.
    claim: Option<Arc<Claim>>,
}

/// A symmetry applied without a declaration, and how often it is checked.
struct Claim {
    /// The unreduced model.
    plain: InterpModel,
    /// Generators of the group.
    gens: Vec<Perm>,
    /// One expanded state in `every` is checked.
    every: u64,
    seen: std::sync::atomic::AtomicU64,
}

/// A `_POSSIBLE` predicate: TLC (SpecProcessor.processConfigPossible) tracks
/// it as the last CONSTRAINT (state level) or ACTION_CONSTRAINT (action
/// level) and checks before the POSTCONDITIONs that it held somewhere.
struct Possible {
    name: String,
    def: DefId,
    /// Action level (evaluated on steps; otherwise on states).
    action: bool,
    witnessed: std::sync::atomic::AtomicBool,
}

/// The `_POSSIBLE` predicates of the cfg (0-ary definitions that are not
/// temporal formulas, as TLC requires).
fn possible_preds(ip: &Interp, cfg: &Config) -> EResult<Vec<Possible>> {
    let mut out = Vec::new();
    for name in &cfg.possible {
        let target = subst_target(ip, name).unwrap_or(name);
        let d = ip.root_def(target).ok_or_else(|| {
            EvalError::new(format!("The possible {name} specified in the configuration file is not defined in the specification."))
        })?;
        let def = &ip.prog.defs[ip.redirect_def(d).idx()];
        if !def.params.is_empty() {
            return Err(EvalError::new(format!("TLC requires {name} not to take any argument, but it does.")));
        }
        // (TLC has the value of a constant-level definition instead.)
        if spec::tlc_has_value(ip, d) {
            return Err(EvalError::new(format!("The possible {name} cannot be a constant.")));
        }
        let e = Expr::new(ExprKind::Apply { op: OpRef::Def(d), args: Vec::new() }, def.span);
        if spec::is_temporal_expr(ip, &e) {
            return Err(EvalError::new(format!(
                "The possible {name} is a temporal formula; only state- and action-level predicates are supported."
            )));
        }
        let action = !spec::is_action_free(ip, &e);
        out.push(Possible { name: name.clone(), def: d, action, witnessed: Default::default() });
    }
    Ok(out)
}

/// The plain `<-` substitution `name` denotes, if any: TLC's `defns` holds the
/// right-hand side's definition under the left-hand side's name.
fn subst_target<'a>(ip: &'a Interp, name: &str) -> Option<&'a str> {
    ip.cfg.last_constant_subst(name)
}

/// A 0-ary use of the root definition `name` named by the cfg (after applying
/// a `<-` substitution, if any).
fn def_ref(ip: &Interp, name: &str) -> EResult<Expr> {
    let target = subst_target(ip, name).unwrap_or(name);
    let d = ip
        .root_def(target)
        .ok_or_else(|| EvalError::new(format!("The configuration refers to `{name}`, which is not defined by the spec")))?;
    let span = ip.prog.defs[d.idx()].span;
    Ok(Expr::new(ExprKind::Apply { op: OpRef::Def(d), args: Vec::new() }, span))
}

fn def_refs(ip: &Interp, names: &[String]) -> EResult<Vec<Expr>> {
    names.iter().map(|n| def_ref(ip, n)).collect()
}

/// True when `name` denotes the value `TRUE`: a root constant the
/// configuration values `TRUE`, or a constant substituted for by one. TLC
/// looks such a name up in `defns` as a boolean value, so an INVARIANT,
/// PROPERTY or CONSTRAINT naming it is accepted (with a warning) and then
/// dropped.
fn cfg_true_const(ip: &Interp, name: &str) -> bool {
    let valued_true = |n: &str| matches!(ip.cfg.last_constant_value(n), Some(tlx_front::cfg::CfgValue::Bool(true)));
    valued_true(name) || subst_target(ip, name).is_some_and(valued_true)
}

/// The behavior spec the configuration gives (TLC's Init/Next, from INIT and
/// NEXT or from a SPECIFICATION).
pub enum Behavior {
    /// INIT and NEXT, or the `Init` and `[][Next]_vars` conjuncts of a
    /// SPECIFICATION.
    Full {
        init: Expr,
        next: Expr,
        /// The temporal conjuncts of the SPECIFICATION.
        temporal: Vec<Expr>,
        /// The subscript of `[][Next]_vars`.
        sub: Option<Expr>,
        /// `[][Next]_vars` is under the substitutions of the INSTANCE
        /// statement here (see `spec::split_spec`).
        within: Option<Span>,
        /// The same for each conjunct of `init` (empty: none is).
        init_within: Vec<Option<Span>>,
    },
    /// An INIT but no next-state action: TLC computes the initial states and,
    /// unless there are none, reports that there is no next-state action
    /// (EC.TLC_STATES_AND_NO_NEXT_ACTION).
    InitOnly { init: Expr },
    /// Neither: TLC only checks the ASSUMEs.
    None,
}

/// Init and Next from INIT/NEXT or SPECIFICATION; `None` when the cfg has no
/// behavior spec.
/// The behavior spec: Init, Next, the other temporal conjuncts of a
/// SPECIFICATION, and the subscript of its `[][Next]_vars`.
fn behavior(ip: &Arc<Interp>, cfg: &Config) -> EResult<Behavior> {
    match (&cfg.init, &cfg.next, &cfg.specification) {
        (Some(i), Some(n), _) => Ok(Behavior::Full {
            init: def_ref(ip, i)?,
            next: def_ref(ip, n)?,
            temporal: Vec::new(),
            sub: None,
            within: None,
            init_within: Vec::new(),
        }),
        (Some(i), None, None) => Ok(Behavior::InitOnly { init: def_ref(ip, i)? }),
        (_, _, Some(spec)) => {
            let body = def_ref(ip, spec)?;
            let mut inits = Vec::new();
            let mut next = None;
            let mut temporal = Vec::new();
            spec::split_spec(ip, &body, None, &mut inits, &mut next, &mut temporal);
            // A conjunct naming a constant-level definition: TLC has its value
            // already and rejects the spec if it is FALSE
            // (SpecProcessor.processConfigSpec, TLC_CONFIG_SPEC_IS_TRIVIAL).
            for (e, _) in &inits {
                if let ExprKind::Apply { op: OpRef::Def(d), args } = &*e.kind {
                    let d = ip.redirect_def(*d);
                    if args.is_empty() && spec::tlc_has_value(ip, d) && matches!(ip.eval_bool(e, &Env::default(), &Ctx::NONE), Ok(false)) {
                        return Err(EvalError::new(format!(
                            "The spec is trivially false because {} is false.",
                            ip.prog.defs[d.idx()].name
                        )));
                    }
                }
            }
            let (next, sub, within) =
                next.ok_or_else(|| EvalError::new(format!("Cannot find the next-state relation `[][Next]_vars` in {spec}")))?;
            let (mut inits, init_within): (Vec<Expr>, Vec<Option<Span>>) = inits.into_iter().unzip();
            let init = if inits.len() == 1 { inits.pop().unwrap() } else { Expr::new(ExprKind::And(inits), body.span) };
            Ok(Behavior::Full { init, next, temporal, sub: Some(sub), within, init_within })
        }
        (None, None, None) => Ok(Behavior::None),
        _ => Err(EvalError::new("The configuration must specify INIT and NEXT, or SPECIFICATION")),
    }
}

/// The initial predicate of a SPECIFICATION as TLC takes it
/// (`InterpModel::spec_init`).
pub enum SpecInit {
    /// Something to evaluate is left (or the cfg has an INIT).
    Some,
    /// Every conjunct is a definition valued TRUE (or there is none).
    Empty,
    /// The conjunct with this name is a definition valued FALSE.
    TriviallyFalse(String),
}

/// The parts of the behavior spec and of the PROPERTYs (`InterpModel::spec_parts`).
pub struct SpecParts {
    /// The temporal (fairness) conjuncts of the SPECIFICATION.
    pub temporals: Vec<Expr>,
    /// State predicates, checked on the initial states.
    pub implied_inits: Vec<(String, Expr)>,
    /// `[]P` parts (checked as invariants).
    pub implied_invariants: Vec<(String, Expr)>,
    /// `[][A]_v` parts.
    pub implied_actions: Vec<(String, Expr)>,
    /// Liveness parts.
    pub implied_temporals: Vec<(String, Expr)>,
}

/// The parts of the cfg PROPERTYs checked during BFS.
#[derive(Default)]
struct Properties {
    /// `[]P` parts, with the name of their property.
    invariants: Vec<(String, Expr)>,
    actions: Vec<(String, Expr)>,
    init: Vec<(String, Expr)>,
    /// Temporal (liveness) parts, with the name of their property.
    liveness: Vec<(String, Expr)>,
}

fn properties(ip: &Arc<Interp>, cfg: &Config) -> EResult<Properties> {
    let mut props = Properties::default();
    for name in &cfg.properties {
        if cfg_true_const(ip, name) {
            continue;
        }
        let mut parts = Vec::new();
        spec::classify_property(ip, &def_ref(ip, name)?, name, &mut parts)?;
        for p in parts {
            match p {
                PropPart::Invariant(part, e) => props.invariants.push((part, e)),
                PropPart::Action(part, e) => props.actions.push((part, e)),
                PropPart::Init(part, e) => props.init.push((part, e)),
                PropPart::Liveness(e) => props.liveness.push((name.clone(), e)),
            }
        }
    }
    Ok(props)
}

/// TLC's source location of `sp` (see `InterpModel::location`).
fn span_location(ip: &Interp, sp: Span) -> String {
    Location::of(ip.prog.file(sp.file), sp, EndTrim::BlankAndComments, module_name(ip, sp)).to_string()
}

/// The name of the module containing `sp` (its file stem).
fn module_name(ip: &Interp, sp: Span) -> String {
    let path = &ip.prog.file(sp.file).path;
    path.file_stem().map(|s| s.to_string_lossy().to_string()).unwrap_or_default()
}

impl InterpModel {
    pub fn new(ip: Arc<Interp>) -> EResult<InterpModel> {
        Self::new_with_reduction(ip, true)
    }

    /// Build without evaluating or closing the declared symmetry group.
    /// The soundness checker evaluates generators separately.
    pub fn new_unreduced(ip: Arc<Interp>) -> EResult<InterpModel> {
        Self::new_with_reduction(ip, false)
    }

    fn new_with_reduction(ip: Arc<Interp>, reduce: bool) -> EResult<InterpModel> {
        ip.eval_constant_defns();
        startup::check(&ip)?;
        let cfg = &ip.cfg;
        let mut warnings = Vec::new();
        let (has_behavior, no_next, init, next, spec_temporal, (within, init_within)) = match behavior(&ip, cfg)? {
            Behavior::Full { init, next, temporal, sub, within, init_within } => {
                let mut missing = sub.map(|sub| spec::vars_not_in_subscript(&ip, &sub)).unwrap_or_default();
                if !missing.is_empty() {
                    // (In the order TLC prints the variables.)
                    if let Some(order) = print_order::tlc_var_order(&ip.prog) {
                        missing.sort_by_key(|v| order.iter().position(|&i| i == v.idx()));
                    }
                }
                for v in missing {
                    let name = &ip.prog.vars[v.idx()].name;
                    let text = format!("The subscript of the next-state relation specified by the specification\ndoes not seem to contain the state variable {name}");
                    warnings.push(Warning { kind: WarningKind::SubscriptWithoutVariable, text });
                }
                (true, false, init, next, temporal, (within, init_within))
            }
            Behavior::InitOnly { init } => {
                // No next-state action: TLC computes the initial states, then
                // reports EC.TLC_STATES_AND_NO_NEXT_ACTION unless there are
                // none (ModelChecker).
                let f = Expr::new(ExprKind::Bool(false), Default::default());
                (true, true, init, f, Vec::new(), Default::default())
            }
            Behavior::None => {
                // No behavior spec: TLC only checks the assumptions.
                let f = Expr::new(ExprKind::Bool(false), Default::default());
                (false, false, f.clone(), f, Vec::new(), Default::default())
            }
        };
        // (`[][Next]_vars` of a SPECIFICATION under the substitutions of an
        // INSTANCE: TLC does not split Next.)
        let actions = if no_next { Vec::new() } else { ip.split_actions(&next, within) };
        let action_names = actions.iter().map(|a| a.name.to_string()).collect();
        let cfg_invariants: Vec<String> = cfg.invariants.iter().filter(|n| !cfg_true_const(&ip, n)).cloned().collect();
        let mut invariants = def_refs(&ip, &cfg_invariants)?;
        let mut invariant_names = cfg_invariants;
        let props = properties(&ip, cfg)?;
        for (name, e) in props.invariants {
            invariants.push(e);
            invariant_names.push(name);
        }
        let (action_prop_names, action_props) = props.actions.into_iter().unzip();
        let constraints = def_refs(&ip, &cfg.constraints.iter().filter(|n| !cfg_true_const(&ip, n)).cloned().collect::<Vec<_>>())?;
        let action_constraints =
            def_refs(&ip, &cfg.action_constraints.iter().filter(|n| !cfg_true_const(&ip, n)).cloned().collect::<Vec<_>>())?;
        let mut live = liveness::live_spec(&ip, &props.liveness, &spec_temporal, &next)?;

        let group = match &cfg.symmetry {
            Some(name) if reduce => symmetry::symmetry_group(&ip, &def_ref(&ip, name)?)?,
            _ => Group::default(),
        };
        if !group.is_empty() && !live.is_empty() {
            let text = "Declaring symmetry during liveness checking is dangerous. It might cause TLC to miss violations of the stated liveness properties. Please check liveness without symmetry defined.".into();
            warnings.push(Warning { kind: WarningKind::LivenessSymmetry, text });
        }
        let view = cfg.view.as_ref().map(|n| def_ref(&ip, n)).transpose()?;
        if !group.is_empty() || view.is_some() {
            live.next_steps.clear();
        } else if !live.is_empty() {
            live.label_actions(&ip, &actions);
        }
        let alias = cfg.alias.as_ref().map(|n| def_ref(&ip, n)).transpose()?;
        let postconditions = cfg
            .postconditions
            .iter()
            .map(|n| {
                let target = subst_target(&ip, n).unwrap_or(n);
                let d = ip
                    .root_def(target)
                    .ok_or_else(|| EvalError::new(format!("The configuration refers to `{n}`, which is not defined by the spec")))?;
                let def = &ip.prog.defs[ip.redirect_def(d).idx()];
                if !def.params.is_empty() {
                    return Err(EvalError::new(format!("The postcondition {n} specified in the configuration file requires arguments.")));
                }
                Ok((n.clone(), d))
            })
            .collect::<EResult<Vec<_>>>()?;
        let possible = Arc::new(possible_preds(&ip, cfg)?);
        let model = InterpModel {
            coverage: false,
            has_behavior,
            no_next,
            check_deadlock: cfg.check_deadlock.unwrap_or(true),
            invariant_names,
            action_props,
            action_prop_names,
            init_props: props.init,
            init,
            init_within,
            actions,
            action_names,
            invariants,
            constraints,
            action_constraints,
            group,
            fp_mode: if reduce { FpMode::Reduced } else { FpMode::Plain },
            view,
            state_projection: false,
            ordered_projection: None,
            projection_certificate: None,
            alias,
            postconditions,
            possible,
            post_at: Default::default(),
            live,
            warnings,
            var_order: Default::default(),
            claim: None,
            ip,
        };
        // What `TLCGet("spec")` and `TLCGet("action")` report.
        model.ip.set_spec_info(spec_info::spec_info(&model));
        Ok(model)
    }

    /// The parts of the behavior spec and of the PROPERTYs, as TLC lists
    /// them in `TLCGet("spec")`.
    pub fn spec_parts(&self) -> SpecParts {
        let temporals = match behavior(&self.ip, &self.ip.cfg) {
            Ok(Behavior::Full { temporal, .. }) => temporal,
            _ => Vec::new(),
        };
        let p = properties(&self.ip, &self.ip.cfg).unwrap_or_default();
        SpecParts {
            temporals,
            implied_inits: p.init,
            implied_invariants: p.invariants,
            implied_actions: p.actions,
            implied_temporals: p.liveness,
        }
    }

    // --- accessors (also used by the compiler, tlx-compile) ---

    pub fn has_constraints(&self) -> bool {
        !self.constraints.is_empty()
    }

    pub fn has_action_constraints(&self) -> bool {
        !self.action_constraints.is_empty()
    }

    pub fn has_init_properties(&self) -> bool {
        !self.init_props.is_empty()
    }

    /// Whether fingerprints depend on VIEW or SYMMETRY (not just the values).
    /// The SYMMETRY group (without the identity): each element maps the
    /// model values it moves to their images (materialized on demand for
    /// factorized groups up to order 720).
    pub fn symmetry_maps(&self) -> &[std::collections::HashMap<tlx_value::Sym, Value>] {
        self.group.symmetry_maps()
    }

    /// Indices into `symmetry_maps()` in the order the interpreter visits the
    /// non-identity permutations when a TLC comparison may fail; a compiled
    /// encodings-based path must follow it so both tiers hit the same
    /// incomparable-value error. `None` when the group has no explicit maps.
    pub fn symmetry_maps_tlc_order(&self) -> Option<Vec<usize>> {
        self.group.symmetry_maps_tlc_order()
    }

    pub fn has_view(&self) -> bool {
        self.view.is_some()
    }

    pub fn has_symmetry(&self) -> bool {
        !self.group.is_empty()
    }

    /// Reduce the search by the group the permutations `gens` generate, as
    /// by a declared SYMMETRY (the representative of each orbit is chosen
    /// in the same way). For a symmetry tlx applies without a declaration
    /// (`autosym`); the model must not have a declared SYMMETRY. Under
    /// `TLX_SYMMETRY_PARANOID=N` one expanded state in N is checked against
    /// it (`check_symmetry_claim`).
    pub fn apply_symmetry(&mut self, gens: Vec<std::collections::HashMap<Sym, Value>>) -> EResult<()> {
        assert!(self.group.is_empty(), "apply_symmetry with a declared SYMMETRY");
        let every = tlx_base::knobs::Env::process().opt_num("TLX_SYMMETRY_PARANOID").ok().flatten();
        let claim = every.filter(|n| *n > 0).map(|every| {
            let plain = InterpModel { claim: None, ..self.with_fp_mode(FpMode::Plain) };
            Arc::new(Claim { plain, gens: gens.clone(), every, seen: Default::default() })
        });
        self.group = Group::from_generators(gens)?;
        self.claim = claim;
        self.fp_mode = FpMode::Reduced;
        Ok(())
    }

    /// Whether the state being expanded is to be checked against the
    /// symmetry `apply_symmetry` applied (`TLX_SYMMETRY_PARANOID`).
    #[inline]
    pub fn symmetry_check_due(&self) -> bool {
        match &self.claim {
            None => false,
            Some(c) => c.seen.fetch_add(1, std::sync::atomic::Ordering::Relaxed) % c.every == 0,
        }
    }

    /// Check that every generator of the applied symmetry maps state `s`
    /// (its Init membership, invariants, constraints, successors, and the
    /// action constraints and properties of its edges) to its image. A
    /// mismatch means the symmetry does not hold: an internal error of tlx
    /// (exit 101), like a `TLX_PARANOID` mismatch.
    pub fn check_symmetry_claim(&self, s: &State) {
        let Some(c) = &self.claim else { return };
        // (An evaluation error is the search's to report.)
        if let Ok(Some((perm, d))) = symcheck::compare_state(&c.plain, s, &c.gens, usize::MAX) {
            let edge = match &d.edge {
                Some(symcheck::Edge::Images { original, image }) => {
                    format!("\nsuccessor t:\n{}\np(t):\n{}", c.plain.render(original), c.plain.render(image))
                }
                Some(symcheck::Edge::ExtraSuccessor(u)) => format!("\nsuccessor of p(s):\n{}", c.plain.render(u)),
                None => String::new(),
            };
            panic!(
                "TLX_SYMMETRY_PARANOID: the symmetry applied without a declaration does not hold: {} under the permutation {perm} at state s\n{}\np(s):\n{}{edge}",
                d.part,
                c.plain.render(s),
                c.plain.render(&d.image)
            );
        }
    }

    /// The VIEW expression (a reference to the cfg's VIEW definition).
    pub fn view_expr(&self) -> Option<&Expr> {
        self.view.as_ref()
    }

    pub fn has_view_or_symmetry(&self) -> bool {
        self.view.is_some() || !self.group.is_empty()
    }

    /// Whether a search of a model of this spec records the liveness
    /// behavior graph (design.md §7.4): with temporal properties to check,
    /// and without VIEW or SYMMETRY (whose liveness checking follows TLC's
    /// algorithm on concrete states).
    pub fn records_live_edges(&self) -> bool {
        !self.live.is_empty() && !self.has_view_or_symmetry()
    }

    /// Invariant expressions (cfg INVARIANTs and `[]P` parts of PROPERTYs).
    pub fn invariant_exprs(&self) -> &[Expr] {
        &self.invariants
    }

    /// CONSTRAINT expressions, in order.
    pub fn constraint_exprs(&self) -> &[Expr] {
        &self.constraints
    }

    /// ACTION_CONSTRAINT expressions, in order.
    pub fn action_constraint_exprs(&self) -> &[Expr] {
        &self.action_constraints
    }

    /// Whether CONSTRAINT `i` holds in `s`.
    pub fn check_constraint(&self, s: &State, i: usize) -> Result<bool, ModelError> {
        self.all_hold(&self.constraints[i..=i], &Ctx::state(&s.vals, s.level))
    }

    /// Whether ACTION_CONSTRAINT `i` holds on `s -> t`. (As in every action
    /// context, `TLCGet("level")` is the level of `s`, TLC's
    /// `s0.getLevel()`, and one more primed.)
    pub fn check_action_constraint(&self, s: &State, t: &State, i: usize) -> Result<bool, ModelError> {
        let t1: Vec<Option<Value>> = t.vals.iter().cloned().map(Some).collect();
        self.all_hold(&self.action_constraints[i..=i], &Ctx::action(&s.vals, &t1, s.level))
    }

    /// Action property expressions (`[A]_v` / `<A>_v`), in order.
    pub fn action_property_exprs(&self) -> &[Expr] {
        &self.action_props
    }

    /// The initial predicate.
    pub fn init_expr(&self) -> &Expr {
        &self.init
    }

    /// What is left of the initial predicate of a SPECIFICATION (without
    /// INIT) once TLC drops the conjuncts that are 0-ary constant-level
    /// definitions valued TRUE: SpecProcessor.processConfigSpec looks such
    /// a name up as its value (evaluated at startup); one valued FALSE makes
    /// the spec trivially false (EC.TLC_CONFIG_SPEC_IS_TRIVIAL).
    pub fn spec_init(&self) -> SpecInit {
        let cfg = &self.ip.cfg;
        if cfg.specification.is_none() || cfg.init.is_some() || !self.has_behavior {
            return SpecInit::Some;
        }
        let conjuncts = match &*self.init.kind {
            ExprKind::And(es) => es.as_slice(),
            _ => std::slice::from_ref(&self.init),
        };
        let mut left = false;
        for c in conjuncts {
            match self.const_def_value(c) {
                Some(Value::Bool(true)) => {}
                Some(Value::Bool(false)) => {
                    let ExprKind::Apply { op: OpRef::Def(d), .. } = &*c.kind else { unreachable!() };
                    return SpecInit::TriviallyFalse(self.ip.prog.defs[d.idx()].name.to_string());
                }
                _ => left = true,
            }
        }
        if left {
            SpecInit::Some
        } else {
            SpecInit::Empty
        }
    }

    /// Whether the model checks anything but the assumptions: TLC's
    /// condition for requiring an initial predicate
    /// (SpecProcessor.processSpec: variables, invariants, or implied
    /// initial, action or temporal properties).
    /// (TLC drops an invariant or a property part that is a definition
    /// valued TRUE, see `spec_init`.)
    pub fn checks_states(&self) -> bool {
        let checked = |e: &Expr| !matches!(self.const_def_value(e), Some(Value::Bool(true)));
        !self.ip.prog.vars.is_empty()
            || self.invariants.iter().any(checked)
            || self.init_props.iter().any(|(_, e)| checked(e))
            || !self.action_props.is_empty()
            || !self.live.is_empty()
    }

    /// The value of `e` if it names a 0-ary constant-level definition that
    /// evaluates (TLC evaluates these at startup and looks the name up as
    /// the value).
    fn const_def_value(&self, e: &Expr) -> Option<Value> {
        match &*e.kind {
            ExprKind::Apply { op: OpRef::Def(d), args } if args.is_empty() && self.ip.is_const_def(self.ip.redirect_def(*d)) => {
                self.ip.eval(e, &Env::default(), &Ctx::NONE).ok()
            }
            _ => None,
        }
    }

    /// The action instances (Next split like TLC's getActions).
    pub fn actions(&self) -> &[Action] {
        &self.actions
    }

    // --- states ---

    /// Build a state from a complete assignment (normalizes values and
    /// computes the fingerprint); `what` names the state in errors.
    pub fn make_state(&self, s1: &[Option<Value>], level: u32, what: &str) -> EResult<State> {
        self.make_state_with(s1, level, || what.to_string())
    }

    /// `make_state` of a generated state (an initial state or a successor):
    /// one that fails (e.g. its VIEW) still counts as generated, as in TLC
    /// (`count_generated`). (Not for re-encoding states already counted.)
    pub fn make_state_counted(&self, s1: &[Option<Value>], level: u32, what: &str) -> EResult<State> {
        self.make_state(s1, level, what).inspect_err(|_| self.count_generated())
    }

    /// Count a generated state that the search does not see: TLC counts a
    /// state as generated before it checks it (Worker.addElement), so one
    /// that is incomplete or whose fingerprint (VIEW) fails counts too.
    pub fn count_generated(&self) {
        self.ip.composed_states.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    /// `make_state` with the state's description built only on error.
    fn make_state_with(&self, s1: &[Option<Value>], level: u32, what: impl FnOnce() -> String) -> EResult<State> {
        self.make_successor(s1, level, None, what)
    }

    /// `make_state_with` for a successor of `base`: values it shares with
    /// `base` (unchanged variables) are neither normalized nor fingerprinted
    /// again.
    fn make_successor(&self, s1: &[Option<Value>], level: u32, base: Option<&State>, what: impl FnOnce() -> String) -> EResult<State> {
        self.make_successor_in(s1, level, base, None, what)
    }

    /// `make_successor`, with the memo of `base` if the caller has it.
    fn make_successor_in(
        &self,
        s1: &[Option<Value>],
        level: u32,
        base: Option<&State>,
        memo: Option<&StateMemo>,
        what: impl FnOnce() -> String,
    ) -> EResult<State> {
        if let Some(b) = base {
            if let Some(st) = self.make_successor_plain(s1, level, b, memo) {
                return Ok(st);
            }
        }
        let vals = self.to_state(s1, base, what)?;
        let span = stats::span();
        let fp = self.compute_fp_and_var_fps(&vals, level, base);
        span.end(stats::T::Fingerprint);
        let (fp, var_fps) = fp?;
        Ok(State { vals, level, fp, var_fps })
    }

    /// `make_successor` of a complete successor of `base` whose fingerprint
    /// is that of its variable values (neither VIEW nor SYMMETRY): each new
    /// value is normalized and fingerprinted in one walk. `None` when that
    /// does not apply or fails (`make_successor` then reports the error).
    fn make_successor_plain(&self, s1: &[Option<Value>], level: u32, base: &State, memo: Option<&StateMemo>) -> Option<State> {
        let plain = self.fp_mode == FpMode::Plain;
        if !plain && (self.view.is_some() || !self.group.is_empty()) {
            return None;
        }
        let span = stats::span();
        if let Some(fps) = &base.var_fps {
            return self.make_successor_from(s1, level, base, fps, span);
        }
        let owned;
        let memo = match memo {
            Some(m) => m,
            None => {
                owned = self.memo(base);
                &owned
            }
        };
        if memo.var_fps.get().is_none() {
            let fps = base.vals.iter().map(tlx_value::fingerprint::fingerprint).collect::<Result<Vec<u64>, _>>().ok()?;
            let _ = memo.var_fps.set(fps);
        }
        self.make_successor_from(s1, level, base, memo.var_fps.get().unwrap(), span)
    }

    /// `make_successor_plain` with the fingerprints of `base`'s values.
    fn make_successor_from(&self, s1: &[Option<Value>], level: u32, base: &State, base_fps: &[u64], span: stats::Span) -> Option<State> {
        let mut vals = Vec::with_capacity(s1.len());
        let mut fps = Vec::with_capacity(s1.len());
        for ((v, b), &f) in s1.iter().zip(base.vals.iter()).zip(base_fps) {
            let v = v.as_ref()?;
            if same_rep(v, b) {
                vals.push(v.clone());
                fps.push(f);
                continue;
            }
            let (fp, normal) = tlx_value::fingerprint::fingerprint_and_normal(v).ok()?;
            vals.push(if normal { v.clone() } else { v.normalize().ok()? });
            fps.push(fp);
        }
        let fp = symmetry::combine_fps(&fps).ok()?;
        span.end(stats::T::Fingerprint);
        Some(State { vals: vals.into(), level, fp, var_fps: Some(fps.into()) })
    }

    fn to_state(&self, s1: &[Option<Value>], base: Option<&State>, what: impl FnOnce() -> String) -> EResult<Arc<[Value]>> {
        let mut out = Vec::with_capacity(s1.len());
        let mut missing = Vec::new();
        for (i, v) in s1.iter().enumerate() {
            match v {
                Some(v) if base.is_some_and(|b| same_rep(v, &b.vals[i])) => out.push(v.clone()),
                Some(v) => out.push(v.normalize()?),
                None => missing.push(self.ip.prog.vars[i].name.to_string()),
            }
        }
        if !missing.is_empty() {
            return Err(EvalError::new(format!(
                "{} is not completely specified. The following variable(s) are not defined: {}.",
                what(),
                missing.join(", ")
            )));
        }
        Ok(out.into())
    }

    /// This model with fingerprints `mode` (the interpreter, and with it
    /// the side effects, registers and generated-states count, is shared).
    pub fn with_fp_mode(&self, mode: FpMode) -> InterpModel {
        InterpModel { fp_mode: mode, ..self.clone() }
    }

    /// Fingerprint of a state: of its VIEW value if there is one, otherwise
    /// of the fingerprints of its variable values; with SYMMETRY, like TLC,
    /// of the least state of the orbit in TLC's value order (with a VIEW:
    /// the VIEW of that state, see `least_in_orbit`). Proved projections
    /// instead canonicalize the projected value. `base` is
    /// a state that `vals` may share values with (whose fingerprints are
    /// reused). (`FpMode::Plain`: neither VIEW nor SYMMETRY.)
    fn compute_fp(&self, vals: &Arc<[Value]>, level: u32, base: Option<&State>) -> EResult<u64> {
        Ok(self.compute_fp_and_var_fps(vals, level, base)?.0)
    }

    /// `compute_fp`, and the fingerprints of the variable values when they
    /// were computed (no VIEW).
    fn compute_fp_and_var_fps(&self, vals: &Arc<[Value]>, level: u32, base: Option<&State>) -> EResult<(u64, Option<Arc<[u64]>>)> {
        let plain = self.fp_mode == FpMode::Plain;
        if let (Some(v), false) = (&self.view, plain) {
            if self.has_projected_symmetry() {
                return Ok((self.projected_orbit_fp(v, vals, level)?, None));
            }
            let least = self.least_in_orbit(vals)?;
            let state: &[Value] = least.as_deref().unwrap_or(vals);
            let viewed = self.projected_value(v, state, level)?;
            return Ok((tlx_value::fingerprint::fingerprint(&viewed)?, None));
        }
        let fps = self.var_fps(vals, base)?;
        if self.group.is_empty() || plain {
            return Ok((symmetry::combine_fps(&fps)?, Some(fps.into())));
        }
        let var_fps: Arc<[u64]> = fps.as_slice().into();
        // The fingerprint of a canonical member of the orbit (the counts
        // only depend on the orbits): the least state in TLC's value order,
        // comparing the variables from the smallest (sizes are the same in
        // the whole orbit, and small variables are cheap to compare and
        // usually decide).
        let order = symmetry::size_order(vals);
        let Some(p) = self.group.least_perm(&mut StateVals::Given(vals), &order)? else {
            return Ok((symmetry::combine_fps(&fps)?, Some(var_fps)));
        };
        let mut least = fps;
        for (v, f) in vals.iter().zip(least.iter_mut()) {
            if let Some(x) = p.apply(v)? {
                *f = tlx_value::fingerprint::fingerprint(&x)?;
            }
        }
        Ok((symmetry::combine_fps(&least)?, Some(var_fps)))
    }

    /// The least state (in TLC's value order, variable by variable) of the
    /// SYMMETRY orbit of `vals`, or `None` when that is `vals` itself (or
    /// there is no SYMMETRY). The variables are compared in TLC's order of
    /// the state's values (`TLCStateMut.fingerPrint` compares `values[j]`
    /// by variable location, the order TLC prints them in), which with a
    /// VIEW decides which state's VIEW is fingerprinted.
    fn least_in_orbit(&self, vals: &[Value]) -> EResult<Option<Vec<Value>>> {
        let Some(p) = self.least_perm_chosen(&mut StateVals::Given(vals))? else {
            return Ok(None);
        };
        vals.iter().map(|v| Ok(p.apply(v)?.unwrap_or_else(|| v.clone()))).collect::<EResult<Vec<_>>>().map(Some)
    }

    fn least_perm_chosen(&self, vals: &mut StateVals) -> EResult<Option<ChosenPerm<'_>>> {
        if self.group.is_empty() {
            return Ok(None);
        }
        let order = self.var_order(vals.len());
        if self.view.is_some() {
            self.group.least_view_perm(vals, order)
        } else {
            self.group.least_perm(vals, order)
        }
    }

    /// The index (in `symmetry_maps`) of the permutation that maps `vals`
    /// to the least state of its SYMMETRY orbit (see `least_in_orbit`), or
    /// `None` when that is `vals` itself (or there is no SYMMETRY).
    fn least_perm_of(&self, vals: &mut StateVals) -> EResult<Option<usize>> {
        if self.group.is_empty() {
            return Ok(None);
        }
        let order = self.var_order(vals.len());
        self.group.least_perm_index(vals, order, self.view.is_some())
    }

    /// `least_perm_of` for the compiled tier (whose VIEW fingerprints
    /// permute encodings; it decodes the variables as they are compared).
    pub fn least_perm(&self, vals: &mut StateVals) -> Result<Option<usize>, ModelError> {
        self.least_perm_of(vals).map_err(|e| self.error(e))
    }

    /// The fingerprints of the values of `vals`; those of values shared with
    /// `base` are taken from its memo.
    fn var_fps(&self, vals: &[Value], base: Option<&State>) -> EResult<Vec<u64>> {
        let fresh = |v: &Value| -> EResult<u64> { Ok(tlx_value::fingerprint::fingerprint(v)?) };
        let Some(base) = base else {
            return vals.iter().map(fresh).collect();
        };
        if let Some(base_fps) = &base.var_fps {
            return vals
                .iter()
                .zip(base.vals.iter())
                .zip(base_fps.iter())
                .map(|((v, b), &f)| if same_rep(v, b) { Ok(f) } else { fresh(v) })
                .collect();
        }
        let memo = self.memo(base);
        if memo.var_fps.get().is_none() {
            let fps = base.vals.iter().map(fresh).collect::<EResult<Vec<u64>>>()?;
            let _ = memo.var_fps.set(fps);
        }
        let base_fps = memo.var_fps.get().unwrap();
        vals.iter().zip(base.vals.iter()).zip(base_fps).map(|((v, b), &f)| if same_rep(v, b) { Ok(f) } else { fresh(v) }).collect()
    }

    // --- enumeration ---

    /// Initial states until `out` returns false (for bounded pre-runs).
    pub fn init_states_until(&self, out: &mut dyn FnMut(State) -> bool) -> Result<(), ModelError> {
        let mut emit = |s1: &[Option<Value>]| {
            let st = self.make_state(s1, 1, "The initial state")?;
            Ok(out(st))
        };
        self.ip.init_states(&self.init, &mut emit).map_err(|e| self.error(e))
    }

    /// Successors of `s` under action instance `i` only (interpreted).
    /// Returns false when `out` stopped the enumeration. (Not
    /// `TLCSet("exit", TRUE)`: TLC generates all successors of the state
    /// being expanded, the search stops before the next one.)
    pub fn successors_of(&self, s: &State, i: usize, out: &mut dyn FnMut(State, u32) -> bool) -> Result<bool, ModelError> {
        let a = &self.actions[i];
        let mut stop = false;
        let mut incomplete = None;
        let memo = self.memo(s);
        let mut emit = |s1: &[Option<Value>]| {
            if let Some(e) = self.incomplete(s1, Some(i as u32)) {
                self.count_generated();
                let msg = e.message.clone();
                incomplete = Some(e);
                return Err(EvalError::new(msg));
            }
            let t = self
                .make_successor_in(s1, s.level + 1, Some(s), Some(&memo), || format!("Successor state generated by action {}", a.name))
                .inspect_err(|_| self.count_generated())?;
            let go_on = out(t, i as u32);
            stop = !go_on;
            Ok(go_on)
        };
        let r = self.ip.successors_memo(&s.vals, s.level, a, memo.clone(), &mut emit);
        if let Some(e) = incomplete {
            return Err(e);
        }
        r.map_err(|e| self.error(e))?;
        Ok(!stop)
    }

    /// `successors`: `successors_of` of each action until `out` stops, with
    /// the state's memo and enumerator set up once.
    fn successors_all(&self, s: &State, out: &mut dyn FnMut(State, u32) -> bool) -> Result<(), ModelError> {
        let memo = self.memo(s);
        let current = std::cell::Cell::new(0usize);
        let stop = std::cell::Cell::new(false);
        let incomplete = std::cell::RefCell::new(None);
        let mut emit = |s1: &[Option<Value>]| {
            let i = current.get();
            if let Some(e) = self.incomplete(s1, Some(i as u32)) {
                self.count_generated();
                let msg = e.message.clone();
                *incomplete.borrow_mut() = Some(e);
                return Err(EvalError::new(msg));
            }
            let a = &self.actions[i];
            let t = self
                .make_successor_in(s1, s.level + 1, Some(s), Some(&memo), || format!("Successor state generated by action {}", a.name))
                .inspect_err(|_| self.count_generated())?;
            let go_on = out(t, i as u32);
            stop.set(!go_on);
            Ok(go_on)
        };
        let mut runner = self.ip.action_runner(&s.vals, s.level, memo.clone(), &mut emit);
        for (i, a) in self.actions.iter().enumerate() {
            current.set(i);
            let r = runner.run(a);
            if let Some(e) = incomplete.borrow_mut().take() {
                return Err(e);
            }
            r.map_err(|e| self.error(e))?;
            if stop.get() {
                break;
            }
        }
        Ok(())
    }

    /// The error for state `s1` (an initial state, or a successor by action
    /// `action`) if some variable has no value in it.
    fn incomplete(&self, s1: &[Option<Value>], action: Option<u32>) -> Option<ModelError> {
        if s1.iter().all(Option::is_some) {
            return None;
        }
        let missing: Vec<String> =
            s1.iter().zip(&self.ip.prog.vars).filter(|(v, _)| v.is_none()).map(|(_, d)| d.name.to_string()).collect();
        let what = match action {
            None => "The initial state".to_string(),
            Some(i) => format!("Successor state generated by action {}", self.actions[i as usize].name),
        };
        let msg = format!("{what} is not completely specified. The following variable(s) are not defined: {}.", missing.join(", "));
        let state = self.render_partial(s1);
        Some(ModelError::new(msg).within(tlx_runtime::ErrorContext::IncompleteState { action, state, missing }))
    }

    /// A state as TLC shows it (see `Model::render`), with `null` for the
    /// variables without a value.
    pub fn render_partial(&self, s1: &[Option<Value>]) -> String {
        let show = |v: &Option<Value>| v.as_ref().map_or_else(|| "null".to_string(), |v| v.to_string());
        fmt_state(self.var_order(s1.len()).iter().map(|&i| (&*self.ip.prog.vars[i].name, show(&s1[i]))), false)
    }

    /// The variables in the order TLC shows them (`len`: their number).
    pub fn var_order(&self, len: usize) -> &[usize] {
        self.var_order.get_or_init(|| print_order::tlc_var_order(&self.ip.prog).unwrap_or_else(|| (0..len).collect()))
    }

    /// The successor values of `s` under action instance `i` (normalized,
    /// without fingerprints, VIEW or the generated-states count): for
    /// cross-checking compiled actions against the interpreter.
    pub fn successor_values_of(&self, s: &State, i: usize, out: &mut dyn FnMut(Arc<[Value]>)) -> Result<(), ModelError> {
        let a = &self.actions[i];
        let mut emit = |s1: &[Option<Value>]| {
            out(self.to_state(s1, Some(s), || format!("Successor state generated by action {}", a.name))?);
            Ok(true)
        };
        self.ip.successors(&s.vals, s.level, a, &mut emit).map(|_| ()).map_err(|e| self.error(e))
    }

    /// This thread's memo of the state-level definitions of `s`.
    fn memo(&self, s: &State) -> Rc<StateMemo> {
        MEMOS.with(|m| {
            let mut m = m.borrow_mut();
            let uid = self.ip.uid;
            if let Some(i) = m.iter().position(|(u, v, _)| *u == uid && Arc::ptr_eq(v, &s.vals)) {
                // Most recently used last.
                let e = m.remove(i);
                let memo = e.2.clone();
                m.push(e);
                return memo;
            }
            if m.len() == MEMO_STATES {
                m.remove(0);
            }
            let memo = Rc::new(StateMemo::default());
            m.push((uid, s.vals.clone(), memo.clone()));
            memo
        })
    }

    // --- checks ---

    /// Whether every expression of `es` holds in context `cx`.
    fn all_hold(&self, es: &[Expr], cx: &Ctx) -> Result<bool, ModelError> {
        for e in es {
            if !self.ip.eval_bool(e, &Env::default(), cx).map_err(|e| self.error(e))? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Check invariant `i` only (an evaluation error is reported as TLC's
    /// "Evaluating invariant ... failed", whatever the tier).
    pub fn check_invariant(&self, s: &State, i: usize) -> Result<Option<usize>, ModelError> {
        let cache = DefCache::over(self.memo(s), None);
        let cx = Ctx::state(&s.vals, s.level).with_cache(&cache);
        Ok((!self.invariant_holds(i, &cx)?).then_some(i))
    }

    /// Whether invariant `i` holds in context `cx`.
    fn invariant_holds(&self, i: usize, cx: &Ctx) -> Result<bool, ModelError> {
        self.ip
            .eval_bool(&self.invariants[i], &Env::default(), cx)
            .map_err(|e| self.error(e).within(tlx_runtime::ErrorContext::Invariant(self.invariant_names[i].clone())))
    }

    /// The PROPERTY parts that are state predicates, on initial state `s`:
    /// TLC's name of the first false one (see `spec::classify_property`).
    pub fn check_init_properties(&self, s: &State) -> Result<Option<String>, ModelError> {
        for (n, p) in &self.init_props {
            if !self.ip.eval_bool(p, &Env::default(), &Ctx::state(&s.vals, s.level)).map_err(|e| self.error(e))? {
                return Ok(Some(n.clone()));
            }
        }
        Ok(None)
    }

    /// Whether action property `i` holds on the transition `s -> t`.
    pub fn check_action_property(&self, s: &State, t: &State, i: usize) -> Result<bool, ModelError> {
        let t1: Vec<Option<Value>> = t.vals.iter().cloned().map(Some).collect();
        let cache = DefCache::over(self.memo(s), Some(self.memo(t)));
        let cx = Ctx::action(&s.vals, &t1, s.level).with_cache(&cache);
        self.ip
            .eval_bool(&self.action_props[i], &Env::default(), &cx)
            .map_err(|e| self.error(e).within(tlx_runtime::ErrorContext::ActionProperty(self.action_prop_names[i].clone())))
    }

    /// Evaluate the ASSUME declarations (TLC does this before model checking).
    pub fn check_assumes(&self) -> Result<(), ModelError> {
        for a in &self.ip.prog.assumes {
            match self.ip.eval_bool(a, &Env::default(), &Ctx::NONE) {
                Ok(true) => {}
                Ok(false) => {
                    return Err(ModelError::new(format!("Assumption {} is false.", self.location(a.span))));
                }
                Err(e) => return Err(self.error(e).within(tlx_runtime::ErrorContext::Assumption(self.location(a.span)))),
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::fmt_state;

    #[test]
    fn fmt_state_bullets() {
        assert_eq!(fmt_state([("x", 1)], false), "x = 1");
        assert_eq!(fmt_state([("x", 1)], true), "/\\ x = 1");
        assert_eq!(fmt_state([("x", 1), ("y", 2)], false), "/\\ x = 1\n/\\ y = 2");
        assert_eq!(fmt_state(Vec::<(&str, i32)>::new(), true), "");
    }
}
