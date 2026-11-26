//! Liveness obligations of a model (design.md §7.4): the temporal parts of
//! the PROPERTYs and the fairness of the SPECIFICATION, translated into
//! formulas over *atoms* — state predicates evaluated on states and action
//! predicates evaluated on steps — that the liveness checker (tlx-live)
//! decides on the behavior graph.

use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hash, Hasher};
use std::sync::Arc;
use tlx_base::hash::{FxHasher, IdHasher};

use tlx_live::Ltl;
use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::*;
use tlx_value::Value;

use super::spec::{is_action_free, temporal_body};
use crate::enumerate::partial_successors_at_most;
use crate::env::Env;
use crate::error::{EResult, EvalError};
use crate::eval::Ctx;
use crate::interp::Interp;

/// A predicate in the environment of its (possibly quantified) occurrence.
#[derive(Clone)]
pub struct Atom {
    pub expr: Expr,
    pub env: Env,
}

/// How a state atom is computed.
#[derive(Clone)]
pub enum StateAtom {
    /// A state predicate, evaluated on the state.
    Pred(Atom),
    /// `ENABLED <<A>>_v` of a fairness condition where every `<<A>>_v`
    /// step is a step of the next-state relation (A is the next-state
    /// relation or a disjunct of it, see `Builder::covered`): whether some
    /// step of the behavior graph from the state (stuttering included,
    /// steps leaving the constraints too) is an `<<A>>_v` step, i.e. action
    /// atom `.0` holds on an outgoing edge. `.1` is the predicate itself
    /// (`ENABLED <<A>>_v`), for evaluating it directly as TLC does (see
    /// `LiveSpec::eval_state_atom`). Fairness of other actions (outside the
    /// next-state relation, or subactions with fewer constraints) is a
    /// `Pred` atom: TLC evaluates ENABLED on the state (LNStateEnabled),
    /// whatever the next-state relation allows.
    EnabledVia(u32, Atom),
}

/// `WF_v(A)` / `SF_v(A)` of the SPECIFICATION: `enabled` is the state atom
/// `ENABLED <<A>>_v`, `taken` the action atom `<<A>>_v`.
#[derive(Clone, Copy, Debug)]
pub struct Fair {
    pub strong: bool,
    pub enabled: u32,
    pub taken: u32,
}

/// A liveness vector whose mutable access starts a new cache generation.
/// Keeping mutation behind `DerefMut` covers element replacement as well as
/// Vec operations. A cached generation retains its allocation, so a later
/// vector cannot acquire the same identity even after its owner is dropped.
pub struct LiveCacheVec<T> {
    values: Vec<T>,
    generation: Arc<()>,
}

impl<T> Default for LiveCacheVec<T> {
    fn default() -> Self {
        Self { values: Vec::new(), generation: Arc::new(()) }
    }
}

impl<T: Clone> Clone for LiveCacheVec<T> {
    fn clone(&self) -> Self {
        Self { values: self.values.clone(), generation: Arc::new(()) }
    }
}

impl<T> std::ops::Deref for LiveCacheVec<T> {
    type Target = Vec<T>;

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

impl<T> std::ops::DerefMut for LiveCacheVec<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.generation = Arc::new(());
        &mut self.values
    }
}

/// Everything the liveness checker needs.
#[derive(Clone, Default)]
pub struct LiveSpec {
    pub state_atoms: Vec<StateAtom>,
    pub action_atoms: LiveCacheVec<Atom>,
    /// One formula per temporal PROPERTY part (with its property's name),
    /// under the non-fairness temporal conjuncts of the SPECIFICATION.
    pub props: Vec<(String, Ltl)>,
    /// The formula of each part of `props` alone (TLC evaluates these on a
    /// counterexample to name the properties it violates).
    pub alone: Vec<Ltl>,
    pub fairness: Vec<Fair>,
    /// The state atoms of the tableaux TLC builds for the properties (set
    /// by the caller, see `tlx_live::tableau_state_atoms`): TLC evaluates
    /// them on the successors of each state it expands.
    pub tableau: Vec<u32>,
    /// Ordered consistency checks, needed only when locating a liveness
    /// evaluation error. Building particles eagerly at startup bypasses
    /// the memory budget of the regular liveness checker.
    initial_checks: std::sync::OnceLock<Vec<Vec<(u32, bool)>>>,
    /// Per action atom (missing: `FromSteps::No`): whether it is an
    /// `<<A>>_v` evaluated from the enumeration of A's steps (see `Steps`).
    pub from_steps: LiveCacheVec<FromSteps>,
    /// Per action atom (missing: false): an `<<A>>_v` such that every step
    /// of the next-state relation is an A-step (see `Builder::covers_next`,
    /// e.g. the `<<Next>>_vars` of `WF_vars(Next)`). The atoms are only
    /// evaluated on steps of the behavior graph, which are steps of the
    /// next-state relation (or stuttering steps), so there it is whether
    /// `v` changes (`step_atom`). The model clears it with VIEW or
    /// SYMMETRY, where a counterexample's cycle may close on a state that is
    /// not a successor of its last state.
    pub next_steps: Vec<bool>,
    /// Per state atom (missing: None): for an `ENABLED <<A>>_v` `Pred`
    /// atom of a fairness condition, the action atom `<<A>>_v` (a
    /// `from_steps` one) whose enumeration of A's steps decides it in
    /// `state_bits` (see `Steps::enabled`); otherwise, and where that
    /// fails, the predicate is evaluated.
    pub enabled_steps: Vec<Option<u32>>,
    /// The `<<A>>_v` atoms decided by the actions of the model that
    /// generate a step (see `label_actions`, `tlx_runtime::ActionMasks`).
    pub action_masks: Option<tlx_runtime::ActionMasks>,
}

/// How an action atom `<<A>>_v` is evaluated on the steps from a state
/// (see `Steps`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum FromSteps {
    /// On each step.
    #[default]
    No,
    /// From the enumeration of A: every step of A is a step of the
    /// next-state relation (see `Builder::covered`), so enumerating A costs
    /// at most as much as generating the successors.
    Covered,
    /// From the enumeration of A while it has at most `STEPS_BOUND` steps
    /// from the state (A is not part of the next-state relation: it may
    /// have many more steps than the state has successors).
    Bounded,
}

/// The most A-steps from a state enumerated for a `FromSteps::Bounded`
/// atom; after `STEPS_OVER` states with more, the atom is evaluated on each
/// step.
const STEPS_BOUND: usize = 64;
const STEPS_OVER: u32 = 8;

impl LiveSpec {
    pub fn is_empty(&self) -> bool {
        self.props.is_empty()
    }

    /// Evaluate the atoms of the tableaux on `s` (see `tableau`), a state
    /// at `level` (`TLCGet("level")`, as TLC's `s0.getLevel()`).
    pub fn eval_tableau(&self, ip: &Arc<Interp>, s: &[Value], level: u32) -> EResult<()> {
        for &i in &self.tableau {
            self.eval_state_atom(ip, i as usize, s, level)?;
        }
        Ok(())
    }

    /// The bits of the state atoms on state `s` (at `level`) whose outgoing
    /// steps have the action-atom bits `out`.
    pub fn state_bits(&self, ip: &Arc<Interp>, s: &[Value], level: u32, out: &[&[u64]]) -> EResult<Vec<u64>> {
        let cx = Ctx::state(s, level);
        STEPS.with(|steps| {
            let mut steps = steps.borrow_mut();
            bits(self.state_atoms.len(), |i| match &self.state_atoms[i] {
                StateAtom::Pred(a) => {
                    if let Some(t) = self.enabled_steps.get(i).copied().flatten() {
                        steps.from(self, ip, s, level);
                        if let Some(b) = steps.enabled(self, ip, t as usize, s, level) {
                            return Ok(b);
                        }
                    }
                    ip.eval_bool(&a.expr, &a.env, &cx)
                }
                StateAtom::EnabledVia(t, _) => Ok(out.iter().any(|b| b[*t as usize / 64] >> (t % 64) & 1 == 1)),
            })
        })
    }

    /// The bits of the state atoms of the tableaux on `s` (the others 0;
    /// `EnabledVia` atoms false, as in `state_bits` without outgoing steps).
    pub fn tableau_bits(&self, ip: &Arc<Interp>, s: &[Value], level: u32) -> EResult<Vec<u64>> {
        let cx = Ctx::state(s, level);
        let mut out = vec![0u64; self.state_atoms.len().div_ceil(64)];
        for &i in &self.tableau {
            if let StateAtom::Pred(a) = &self.state_atoms[i as usize] {
                if ip.eval_bool(&a.expr, &a.env, &cx)? {
                    out[i as usize / 64] |= 1 << (i % 64);
                }
            }
        }
        Ok(out)
    }

    /// State atom `i` on `s` (at `level`), evaluated directly (an
    /// `EnabledVia` atom as its predicate `ENABLED <<A>>_v`).
    pub fn eval_state_atom(&self, ip: &Arc<Interp>, i: usize, s: &[Value], level: u32) -> EResult<bool> {
        let (StateAtom::Pred(a) | StateAtom::EnabledVia(_, a)) = &self.state_atoms[i];
        ip.eval_bool(&a.expr, &a.env, &Ctx::state(s, level))
    }

    /// Action atom `i` on the step `s -> t` of the behavior graph, if it is
    /// a `next_steps` atom and its `v` evaluates on both states.
    pub fn step_atom(&self, ip: &Arc<Interp>, i: usize, s: &[Value], t: &[Value], level: u32) -> Option<bool> {
        if !self.next_steps.get(i).is_some_and(|&b| b) {
            return None;
        }
        let a = &self.action_atoms[i];
        let ExprKind::AngleAction { sub, .. } = &*a.expr.kind else { return None };
        let vs = ip.eval(sub, &a.env, &Ctx::state(s, level)).ok()?;
        let vt = ip.eval(sub, &a.env, &Ctx::state(t, level + 1)).ok()?;
        Some(!tlx_value::order::eq_tlc(&vs, &vt).ok()?)
    }

    /// The `<<A>>_v` atoms whose A is a union of the model's `actions`
    /// (each of A's disjuncts is an action: the same expression in an
    /// environment with the same bindings, see `leaves`): A's steps from a
    /// state are the successors these actions generate, so on a step
    /// generated by another action the atom holds only if one of them
    /// generates the same successor (`action_masks`). Not with VIEW or
    /// SYMMETRY (the caller does not set it then: steps to states with the
    /// same fingerprint need not be steps to the same state).
    pub fn label_actions(&mut self, ip: &Arc<Interp>, actions: &[crate::enumerate::Action]) {
        let mut by_expr: HashMap<*const ExprKind, Vec<usize>> = HashMap::new();
        for (j, a) in actions.iter().enumerate() {
            by_expr.entry(Arc::as_ptr(&a.expr.kind)).or_default().push(j);
        }
        let words = self.action_atoms.len().div_ceil(64);
        let mut decided = vec![0u64; words];
        let mut per_action = vec![vec![0u64; words]; actions.len()];
        for (i, atom) in self.action_atoms.iter().enumerate() {
            let ExprKind::AngleAction { action, .. } = &*atom.expr.kind else { continue };
            let mut mine = Vec::new();
            leaves(ip, action, &atom.env, &mut mine);
            let mut of = Vec::new();
            let all = !mine.is_empty()
                && mine.iter().all(|(e, env)| {
                    let before = of.len();
                    for &j in by_expr.get(&Arc::as_ptr(&e.kind)).into_iter().flatten() {
                        if env.same_bindings(&actions[j].env, &ip.prog) {
                            of.push(j);
                        }
                    }
                    of.len() > before
                });
            if all {
                decided[i / 64] |= 1 << (i % 64);
                for j in of {
                    per_action[j][i / 64] |= 1 << (i % 64);
                }
            }
        }
        let masks = tlx_runtime::ActionMasks::new(decided, per_action);
        self.action_masks = masks.any().then_some(masks);
    }

    /// Action atom `i` on the step `s -> t` (`s` at `level`).
    pub fn eval_action_atom(&self, ip: &Arc<Interp>, i: usize, s: &[Value], t: &[Value], level: u32) -> EResult<bool> {
        let t1: Vec<Option<Value>> = t.iter().cloned().map(Some).collect();
        let a = &self.action_atoms[i];
        ip.eval_bool(&a.expr, &a.env, &Ctx::action(s, &t1, level))
    }

    /// The bits of the action atoms on the step `s -> t` (`s` at `level`).
    pub fn action_bits(&self, ip: &Arc<Interp>, s: &[Value], t: &[Value], level: u32) -> EResult<Vec<u64>> {
        self.action_bits_only(ip, s, t, level, None)
    }

    /// The bits of the action atoms on the step `s -> t` (`s` at `level`), with
    /// `mask` only those of the atoms in it (the others 0).
    pub fn action_bits_only(&self, ip: &Arc<Interp>, s: &[Value], t: &[Value], level: u32, mask: Option<&[u64]>) -> EResult<Vec<u64>> {
        let mut t1: Option<Vec<Option<Value>>> = None;
        STEPS.with(|steps| {
            let mut steps = steps.borrow_mut();
            steps.from(self, ip, s, level);
            let th = std::cell::OnceCell::new();
            let skip = |i: usize| mask.is_some_and(|m| m[i / 64] >> (i % 64) & 1 == 0);
            bits(self.action_atoms.len(), |i| {
                match skip(i)
                    .then_some(false)
                    .or_else(|| self.step_atom(ip, i, s, t, level))
                    .or_else(|| steps.angle(self, ip, i, s, t, level, &th))
                {
                    Some(b) => Ok(b),
                    None => {
                        let t1 = t1.get_or_insert_with(|| t.iter().cloned().map(Some).collect());
                        ip.eval_bool(&self.action_atoms[i].expr, &self.action_atoms[i].env, &Ctx::action(s, t1, level))
                    }
                }
            })
        })
    }
}

thread_local! {
    static STEPS: std::cell::RefCell<Steps> = std::cell::RefCell::new(Steps::default());
}

/// The steps of the `<<A>>_v` action atoms from one state, for all the
/// steps from it: the atoms are evaluated on every step of the
/// behavior graph, and evaluating A on a step costs about as much as
/// enumerating all A-steps from its first state, which is done once here
/// instead. `<<A>>_v` holds on `s -> t` iff the enumeration of A from `s`
/// yields `t` (on the variables A determines: A does not mention the others
/// primed, so it holds whatever their values) and `v` differs on `s` and
/// `t`. For the `<<A>>_v` atoms of `LiveSpec::from_steps`: where A's steps
/// are steps of the next-state relation, enumerating A costs at most as
/// much as generating the successors; other actions are enumerated up to
/// `STEPS_BOUND` steps. Where A cannot be enumerated (an evaluation fails,
/// e.g. on a primed variable A has not determined yet) or `v` fails, the
/// atom is evaluated on the step, as before (so errors are those of that
/// evaluation).
#[derive(Default)]
struct Steps {
    /// The generations of the action atoms and their enumeration policies.
    /// Retaining the tokens prevents address reuse; mutations and clones
    /// get new tokens. The interpreter allocation is retained weakly for
    /// the same reason, without keeping a finished model alive.
    spec: Option<(Arc<()>, Arc<()>)>,
    ip: std::sync::Weak<Interp>,
    src: Vec<Value>,
    /// BFS level of `src` (`TLCGet("level")`).
    level: u32,
    /// Per action atom.
    atoms: Vec<AngleSteps>,
    /// Per action atom: its enumeration failed once (do not try again).
    off: Vec<bool>,
    /// Per action atom: the states from which it had more than
    /// `STEPS_BOUND` steps (`FromSteps::Bounded`).
    over: Vec<u32>,
}

#[derive(Clone)]
enum AngleSteps {
    /// Not enumerated yet from `src`.
    Unknown,
    /// Evaluated on each step.
    Eval,
    /// No A-step from `src` (`v` is not needed then).
    None,
    /// The A-steps from `src` and `v` at `src`.
    Steps(Arc<StepSet>, Value),
}

/// The A-steps from a state, grouped by the variables they determine.
struct StepSet {
    /// Per set of determined variables (None: all of them), the values of
    /// those variables in the steps' successor states, by `state_hash`.
    groups: Vec<(Option<Vec<usize>>, HashMap<u64, Vec<Vec<Value>>, BuildHasherDefault<IdHasher>>)>,
}

impl StepSet {
    fn new(succ: Vec<Vec<Option<Value>>>) -> Self {
        let mut set = StepSet { groups: Vec::new() };
        for u in succ {
            let vars = (!u.iter().all(Option::is_some))
                .then(|| u.iter().enumerate().filter(|(_, v)| v.is_some()).map(|(k, _)| k).collect::<Vec<_>>());
            let vals: Vec<Value> = u.into_iter().flatten().collect();
            let g = match set.groups.iter().position(|(v, _)| *v == vars) {
                Some(g) => g,
                None => {
                    set.groups.push((vars, HashMap::default()));
                    set.groups.len() - 1
                }
            };
            set.groups[g].1.entry(state_hash(&vals)).or_default().push(vals);
        }
        set
    }

    /// Whether `t` is the successor state of a step (`th`: the hash of
    /// `t`, once computed).
    fn contains(&self, t: &[Value], th: &std::cell::OnceCell<u64>) -> bool {
        self.groups.iter().any(|(vars, steps)| match vars {
            None => steps.get(th.get_or_init(|| state_hash(t))).is_some_and(|us| us.iter().any(|u| u[..] == *t)),
            Some(vars) => {
                let p: Vec<Value> = vars.iter().map(|&k| t[k].clone()).collect();
                steps.get(&state_hash(&p)).is_some_and(|us| us.contains(&p))
            }
        })
    }
}

/// A hash of a state's values (consistent with their equality).
fn state_hash(vals: &[Value]) -> u64 {
    let mut h: FxHasher = Default::default();
    vals.hash(&mut h);
    h.finish()
}

impl Steps {
    /// Steps from `s` (at BFS `level`) next (of the atoms of `spec`).
    fn from(&mut self, spec: &LiveSpec, ip: &Arc<Interp>, s: &[Value], level: u32) {
        let same = self.spec.as_ref().is_some_and(|(atoms, policies)| {
            Arc::ptr_eq(atoms, &spec.action_atoms.generation) && Arc::ptr_eq(policies, &spec.from_steps.generation)
        }) && self.ip.as_ptr() == Arc::as_ptr(ip);
        if !same {
            self.spec = Some((spec.action_atoms.generation.clone(), spec.from_steps.generation.clone()));
            self.ip = Arc::downgrade(ip);
            self.off = vec![false; spec.action_atoms.len()];
            self.over = vec![0; spec.action_atoms.len()];
        } else if self.level == level && self.src[..] == *s {
            return;
        }
        self.src = s.to_vec();
        self.level = level;
        self.atoms = vec![AngleSteps::Unknown; spec.action_atoms.len()];
    }

    /// Atom `i` on the step `s -> t` (`s` the state of `from`, at `level`),
    /// if it is an `<<A>>_v` atom whose A-steps from `s` are known.
    /// `th`: the hash of `t`, once computed.
    #[allow(clippy::too_many_arguments, reason = "threads BFS level into cached step lookup")]
    fn angle(
        &mut self,
        spec: &LiveSpec,
        ip: &Arc<Interp>,
        i: usize,
        s: &[Value],
        t: &[Value],
        level: u32,
        th: &std::cell::OnceCell<u64>,
    ) -> Option<bool> {
        let atom = &spec.action_atoms[i];
        let ExprKind::AngleAction { sub, .. } = &*atom.expr.kind else { return None };
        if spec.from_steps.get(i).copied().unwrap_or_default() == FromSteps::No {
            return None;
        }
        self.enumerate(spec, ip, i, s, level);
        match &self.atoms[i] {
            AngleSteps::None => Some(false),
            AngleSteps::Steps(succ, _) if !succ.contains(t, th) => Some(false),
            AngleSteps::Steps(_, v) => {
                let vt = ip.eval(sub, &atom.env, &Ctx::state(t, level + 1)).ok()?;
                Some(!tlx_value::order::eq_tlc(v, &vt).ok()?)
            }
            _ => None,
        }
    }

    /// Enumerate the A-steps from `s` (the state of `from`, at `level`) of the
    /// `<<A>>_v` atom `i` (a `from_steps` one), unless done.
    fn enumerate(&mut self, spec: &LiveSpec, ip: &Arc<Interp>, i: usize, s: &[Value], level: u32) {
        if !matches!(self.atoms[i], AngleSteps::Unknown) {
            return;
        }
        let atom = &spec.action_atoms[i];
        let ExprKind::AngleAction { action, sub } = &*atom.expr.kind else {
            self.atoms[i] = AngleSteps::Eval;
            return;
        };
        let how = spec.from_steps.get(i).copied().unwrap_or_default();
        let bound = if how == FromSteps::Bounded { STEPS_BOUND } else { usize::MAX };
        let steps = if self.off[i] {
            None
        } else {
            match partial_successors_at_most(ip, s, level, action, &atom.env, bound) {
                // (Often: A is not enabled.)
                Ok(Some(succ)) if succ.is_empty() => {
                    self.atoms[i] = AngleSteps::None;
                    return;
                }
                Ok(Some(succ)) => ip.eval(sub, &atom.env, &Ctx::state(s, level)).ok().map(|v| (succ, v)),
                Ok(None) => {
                    // Too many steps from this state: on each step.
                    self.over[i] += 1;
                    self.off[i] = self.over[i] >= STEPS_OVER;
                    self.atoms[i] = AngleSteps::Eval;
                    return;
                }
                Err(_) => None,
            }
        };
        self.atoms[i] = match steps {
            Some((succ, v)) => AngleSteps::Steps(Arc::new(StepSet::new(succ)), v),
            None => {
                self.off[i] = true;
                AngleSteps::Eval
            }
        };
    }

    /// `ENABLED <<A>>_v` on `s` (the state of `from`, at `level`), for the
    /// `<<A>>_v` atom `i` (a `from_steps` one), from the enumeration of A's
    /// steps: whether one of them changes `v`. None where that is not
    /// known: A could not be enumerated, a step leaves a variable
    /// undetermined, or `v` fails on a step; the predicate is then
    /// evaluated (TLC's ENABLED, with its errors).
    fn enabled(&mut self, spec: &LiveSpec, ip: &Arc<Interp>, i: usize, s: &[Value], level: u32) -> Option<bool> {
        self.enumerate(spec, ip, i, s, level);
        let (set, v) = match &self.atoms[i] {
            AngleSteps::None => return Some(false),
            AngleSteps::Steps(set, v) => (set, v),
            _ => return None,
        };
        let ExprKind::AngleAction { sub, .. } = &*spec.action_atoms[i].expr.kind else { return None };
        let env = &spec.action_atoms[i].env;
        if set.groups.iter().any(|(vars, _)| vars.is_some()) {
            return None;
        }
        for t in set.groups.iter().flat_map(|(_, steps)| steps.values().flatten()) {
            let vt = ip.eval(sub, env, &Ctx::state(t, level + 1)).ok()?;
            if !tlx_value::order::eq_tlc(v, &vt).ok()? {
                return Some(true);
            }
        }
        Some(false)
    }
}

fn bits(n: usize, mut f: impl FnMut(usize) -> EResult<bool>) -> EResult<Vec<u64>> {
    let mut out = vec![0u64; n.div_ceil(64)];
    for i in 0..n {
        if f(i)? {
            out[i / 64] |= 1 << (i % 64);
        }
    }
    Ok(out)
}

/// Translate the temporal property parts (with names) under the temporal
/// conjuncts of the SPECIFICATION (fairness and other assumptions).
/// `next` is the next-state relation.
pub(super) fn live_spec(ip: &Arc<Interp>, props: &[(String, Expr)], spec_temporal: &[Expr], next: &Expr) -> EResult<LiveSpec> {
    let mut next_leaves = Vec::new();
    if !props.is_empty() {
        leaves(ip, next, &Env::default(), &mut next_leaves);
    }
    let mut b = Builder { ip, next_leaves, spec: LiveSpec::default(), expanding: 0 };
    if props.is_empty() {
        return Ok(b.spec);
    }
    let mut assumptions = Vec::new();
    for e in spec_temporal {
        b.assumption(e, &Env::default(), &mut assumptions)?;
    }
    for (name, e) in props {
        let f = b.formula(e, &Env::default())?;
        b.spec.alone.push(f.clone());
        // Non-fairness temporal conjuncts of the spec become antecedents.
        let f = if assumptions.is_empty() { f } else { Ltl::Or(vec![Ltl::Not(Box::new(Ltl::And(assumptions.clone()))), f]) };
        b.spec.props.push((name.clone(), f));
    }
    let fairness: Vec<tlx_live::Fairness> =
        b.spec.fairness.iter().map(|f| tlx_live::Fairness { strong: f.strong, enabled: f.enabled, taken: f.taken }).collect();
    for (_, f) in &b.spec.props {
        tlx_live::check_size(f, &fairness).map_err(EvalError::new)?;
    }
    b.spec.next_steps = b
        .spec
        .action_atoms
        .iter()
        .map(|a| matches!(&*a.expr.kind, ExprKind::AngleAction { action, .. } if b.covers_next(action, &a.env)))
        .collect();
    Ok(b.spec)
}

struct Builder<'a> {
    ip: &'a Arc<Interp>,
    /// The disjuncts of the next-state relation (see `leaves`).
    next_leaves: Vec<(Expr, Env)>,
    spec: LiveSpec,
    /// Nesting of the operator applications being expanded.
    expanding: u32,
}

/// Nesting of operator expansions in a temporal formula at which it counts
/// as a recursion that does not end.
const MAX_EXPANSION_DEPTH: u32 = 2000;

impl Builder<'_> {
    fn state_atom(&mut self, expr: Expr, env: &Env) -> Ltl {
        self.spec.state_atoms.push(StateAtom::Pred(Atom { expr, env: env.clone() }));
        Ltl::State(self.spec.state_atoms.len() as u32 - 1)
    }

    fn action_atom(&mut self, expr: Expr, env: &Env) -> Ltl {
        let i = self.spec.action_atoms.len();
        if let ExprKind::AngleAction { action, .. } = &*expr.kind {
            self.spec.from_steps.resize(i + 1, FromSteps::No);
            self.spec.from_steps[i] = if self.covered(action, env) { FromSteps::Covered } else { FromSteps::Bounded };
        }
        self.spec.action_atoms.push(Atom { expr, env: env.clone() });
        Ltl::Action(i as u32)
    }

    /// The atoms `ENABLED <<A>>_v` and `<<A>>_v`. `fresh`: the argument of
    /// the ENABLED where it is not `<<A>>_v` (in an instance, see
    /// `ExprKind::Fairness`): it is evaluated as is, not decided from the
    /// steps of the behavior graph (an A step of the instantiated module
    /// need not be a step of the spec).
    fn fairness_atoms(&mut self, sub: &Expr, action: &Expr, fresh: Option<&Expr>, span: Span, env: &Env) -> (u32, u32) {
        let angle = Expr::new(ExprKind::AngleAction { action: action.clone(), sub: sub.clone() }, span);
        let enabled_arg = fresh.cloned().unwrap_or_else(|| angle.clone());
        let enabled = Atom { expr: Expr::new(ExprKind::Builtin { op: B::Enabled, args: vec![enabled_arg] }, span), env: env.clone() };
        let Ltl::Action(t) = self.action_atom(angle, env) else { unreachable!() };
        if fresh.is_some() {
            self.spec.state_atoms.push(StateAtom::Pred(enabled));
            return (self.spec.state_atoms.len() as u32 - 1, t);
        }
        let covered = matches!(self.spec.from_steps.get(t as usize), Some(FromSteps::Covered));
        let atom = if covered { StateAtom::EnabledVia(t, enabled) } else { StateAtom::Pred(enabled) };
        if !covered {
            // (Decided by the enumeration of A's steps where it can be.)
            let k = self.spec.state_atoms.len();
            self.spec.enabled_steps.resize(k + 1, None);
            self.spec.enabled_steps[k] = Some(t);
        }
        self.spec.state_atoms.push(atom);
        (self.spec.state_atoms.len() as u32 - 1, t)
    }

    /// Whether every step of `action` (in `env`) is certainly a step of
    /// the next-state relation: each of its disjuncts is one of the
    /// next-state relation (the same expression in an environment with the
    /// same bindings; see `leaves`). Then `ENABLED <<A>>_v` is whether some
    /// successor of the state is an `<<A>>_v` step.
    fn covered(&self, action: &Expr, env: &Env) -> bool {
        let mut mine = Vec::new();
        leaves(self.ip, action, env, &mut mine);
        mine.iter().all(|(e, env)| {
            self.next_leaves.iter().any(|(n, nenv)| Arc::ptr_eq(&e.kind, &n.kind) && env.same_bindings(nenv, &self.ip.prog))
        })
    }

    /// Whether every step of the next-state relation is a step of `action`
    /// (in `env`): each disjunct of the next-state relation is one of
    /// `action`'s (the converse of `covered`).
    fn covers_next(&self, action: &Expr, env: &Env) -> bool {
        if self.next_leaves.is_empty() {
            return false;
        }
        let mut mine = Vec::new();
        leaves(self.ip, action, env, &mut mine);
        self.next_leaves
            .iter()
            .all(|(n, nenv)| mine.iter().any(|(e, env)| Arc::ptr_eq(&e.kind, &n.kind) && env.same_bindings(nenv, &self.ip.prog)))
    }

    /// A temporal conjunct of the SPECIFICATION: fairness becomes a
    /// constraint of the checker; anything else an assumption formula.
    fn assumption(&mut self, e: &Expr, env: &Env, out: &mut Vec<Ltl>) -> EResult<()> {
        match &*e.kind {
            ExprKind::And(es) => es.iter().try_for_each(|c| self.assumption(c, env, out)),
            ExprKind::Let { body, .. } => self.assumption(body, env, out),
            ExprKind::Quant { kind: QuantKind::Forall, bounds, body } => {
                let ip = self.ip.clone();
                let mut envs = Vec::new();
                ip.for_each_binding(bounds, env, &Ctx::NONE, &mut |env2| {
                    envs.push(env2.clone());
                    Ok(true)
                })?;
                envs.iter().try_for_each(|env2| self.assumption(body, env2, out))
            }
            ExprKind::Fairness { kind, sub, action, enabled } => {
                let (enabled, taken) = self.fairness_atoms(sub, action, enabled.as_ref(), e.span, env);
                self.spec.fairness.push(Fair { strong: matches!(kind, FairnessKind::Strong), enabled, taken });
                Ok(())
            }
            // The conditional fairness of the examples of the TLA+ book,
            // `(guard) => WF_v(A)`: with a constant `guard` the conjunct is
            // the fairness condition (guard TRUE) or TRUE (guard FALSE), not
            // an assumption formula. (TLC folds the constant too. Keeping the
            // implication as an antecedent would leave the `[]<>`s of its
            // consequent to the tableau of the property, which unfolds the
            // `2k` of `k` guarded `WF`s into `2^(2k)` automaton states instead
            // of the checker taking them as cycle conditions.)
            ExprKind::Builtin { op: B::Implies, args } if args.len() == 2 && self.foldable(&args[0], env) => {
                if self.ip.eval_bool(&args[0], env, &Ctx::NONE)? {
                    self.assumption(&args[1], env, out)
                } else {
                    Ok(())
                }
            }
            ExprKind::Apply { op: OpRef::Def(d), args } => match self.expand(*d, args, env)? {
                Some((body, env2)) => self.assumption(&body, &env2, out),
                None => {
                    out.push(self.formula(e, env)?);
                    Ok(())
                }
            },
            _ => {
                out.push(self.formula(e, env)?);
                Ok(())
            }
        }
    }

    /// Whether `e` is a state predicate whose value does not depend on the
    /// state (as `formula`: a constant subformula, evaluated now).
    fn foldable(&self, e: &Expr, env: &Env) -> bool {
        is_action_free(self.ip, e) && !super::spec::is_temporal_expr(self.ip, e) && self.ip.is_constant_in(e, env)
    }

    /// The body of a temporal definition applied to `args` (bound by value
    /// in a constant context), or None for a non-temporal definition.
    fn expand(&self, d: DefId, args: &[Expr], env: &Env) -> EResult<Option<(Expr, Env)>> {
        let d = self.ip.redirect_def(d);
        let Some(body) = temporal_body(self.ip, d) else { return Ok(None) };
        let def = &self.ip.prog.defs[d.idx()];
        if def.params.len() != args.len() {
            return Err(EvalError::new(format!("wrong number of arguments for {}", def.name)));
        }
        // Operator parameters get the operator value; other arguments are
        // bound by name, as a thunk over the caller's environment, so that a
        // state expression (a subscript, say) is read where the body uses it.
        let mut env2 = self.ip.def_env(d, env);
        for (p, a) in def.params.iter().zip(args) {
            if self.ip.prog.locals[p.idx()].arity > 0 {
                env2 = env2.bind(*p, crate::env::Binding::Op(self.ip.op_val(a, env)?));
                continue;
            }
            env2 = env2.bind(*p, crate::env::Binding::Thunk(Arc::new(crate::env::Thunk { expr: a.clone(), env: env.clone(), memo: None })));
        }
        Ok(Some((body.clone(), env2)))
    }

    /// A temporal formula.
    fn formula(&mut self, e: &Expr, env: &Env) -> EResult<Ltl> {
        Ok(match &*e.kind {
            // A state predicate is one atom, also when it is a conjunction or
            // disjunction; a constant one is TRUE or FALSE, as for TLC
            // (Liveness.astToLive), which counts the branches of the
            // negated property after folding it.
            _ if is_action_free(self.ip, e) && !super::spec::is_temporal_expr(self.ip, e) => {
                if self.ip.is_constant_in(e, env) {
                    if self.ip.eval_bool(e, env, &Ctx::NONE)? {
                        Ltl::True
                    } else {
                        Ltl::False
                    }
                } else {
                    self.check_constant_subformulas(e, env)?;
                    self.state_atom(e.clone(), env)
                }
            }
            ExprKind::And(es) => Ltl::And(es.iter().map(|c| self.formula(c, env)).collect::<EResult<_>>()?),
            ExprKind::Or(es) => Ltl::Or(es.iter().map(|c| self.formula(c, env)).collect::<EResult<_>>()?),
            ExprKind::Let { body, .. } => self.formula(body, env)?,
            ExprKind::If { cond, then, els }
                if super::spec::is_temporal_expr(self.ip, then) || super::spec::is_temporal_expr(self.ip, els) =>
            {
                // A constant guard selects one branch, so that a recursive
                // operator whose recursion ends at such a guard expands to
                // a finite formula (TLC, tlaplus/tlaplus#1389).
                if is_action_free(self.ip, cond) && self.ip.is_constant_in(cond, env) {
                    let branch = if self.ip.eval_bool(cond, env, &Ctx::NONE)? { then } else { els };
                    return self.formula(branch, env);
                }
                let c = self.formula(cond, env)?;
                let (t, f) = (self.formula(then, env)?, self.formula(els, env)?);
                Ltl::Or(vec![Ltl::And(vec![c.clone(), t]), Ltl::And(vec![neg(c), f])])
            }
            ExprKind::Builtin { op: B::Not, args } => Ltl::Not(Box::new(self.formula(&args[0], env)?)),
            ExprKind::Builtin { op: B::Implies, args } => {
                Ltl::Or(vec![Ltl::Not(Box::new(self.formula(&args[0], env)?)), self.formula(&args[1], env)?])
            }
            ExprKind::Builtin { op: B::Equiv, args } => {
                let (a, b) = (self.formula(&args[0], env)?, self.formula(&args[1], env)?);
                Ltl::Or(vec![Ltl::And(vec![a.clone(), b.clone()]), Ltl::And(vec![neg(a), neg(b)])])
            }
            ExprKind::Builtin { op: B::Always, args } => Ltl::Always(Box::new(self.formula(&args[0], env)?)),
            ExprKind::Builtin { op: B::Eventually, args } => Ltl::Eventually(Box::new(self.formula(&args[0], env)?)),
            ExprKind::Builtin { op: B::LeadsTo, args } => {
                let (p, q) = (self.formula(&args[0], env)?, self.formula(&args[1], env)?);
                Ltl::Always(Box::new(Ltl::Or(vec![neg(p), Ltl::Eventually(Box::new(q))])))
            }
            ExprKind::Fairness { kind, sub, action, enabled } => {
                // WF: []<>~ENABLED <<A>>_v \/ []<><<A>>_v; SF: <>[]~ENABLED \/ []<><<A>>_v.
                let (enabled, taken) = self.fairness_atoms(sub, action, enabled.as_ref(), e.span, env);
                let not_enabled = neg(Ltl::State(enabled));
                let disabled = match kind {
                    FairnessKind::Weak => always(eventually(not_enabled)),
                    FairnessKind::Strong => eventually(always(not_enabled)),
                };
                Ltl::Or(vec![disabled, always(eventually(Ltl::Action(taken)))])
            }
            ExprKind::Quant { kind, bounds, body } => {
                let ip = self.ip.clone();
                let mut envs = Vec::new();
                ip.for_each_binding(bounds, env, &Ctx::NONE, &mut |env2| {
                    envs.push(env2.clone());
                    Ok(true)
                })?;
                let parts = envs.iter().map(|env2| self.formula(body, env2)).collect::<EResult<Vec<_>>>()?;
                match kind {
                    QuantKind::Forall => Ltl::And(parts),
                    QuantKind::Exists => Ltl::Or(parts),
                }
            }
            ExprKind::Apply { op: OpRef::Def(d), args } => match self.expand(*d, args, env)? {
                Some((body, env2)) => {
                    // A recursive operator whose expansion does not end fails
                    // as an evaluation that recurses forever (TLC: a stack
                    // overflow). Each level may inspect the arguments of all
                    // levels above it (`is_constant_in`): the bound is far
                    // below the evaluation's.
                    if self.expanding >= MAX_EXPANSION_DEPTH || tlx_base::stack::low() {
                        return Err(crate::depth::error(e.span));
                    }
                    self.expanding += 1;
                    let r = self.formula(&body, &env2);
                    self.expanding -= 1;
                    r?
                }
                None => self.action_atom(e.clone(), env),
            },
            // `[A]_v`, `<<A>>_v` and other action-level predicates: on the
            // step from the current state.
            _ => self.action_atom(e.clone(), env),
        })
    }

    /// Liveness.astToLiveAppl visits propositional children before collapsing
    /// a state-level formula into one LNStateAST. Thus a constant boolean
    /// child can fail at startup even when no initial state exists. Do not
    /// descend into arbitrary value expressions: their evaluation is lazy.
    fn check_constant_subformulas(&self, e: &Expr, env: &Env) -> EResult<()> {
        if self.ip.is_constant_in(e, env) {
            self.ip.eval_bool(e, env, &Ctx::NONE)?;
            return Ok(());
        }
        match &*e.kind {
            ExprKind::And(xs) | ExprKind::Or(xs) | ExprKind::Builtin { op: B::Not | B::Implies | B::Equiv, args: xs } => {
                for x in xs {
                    self.check_constant_subformulas(x, env)?;
                }
            }
            ExprKind::Let { body, .. } => self.check_constant_subformulas(body, env)?,
            ExprKind::If { cond, then, els } => {
                if self.ip.is_constant_in(cond, env) {
                    let branch = if self.ip.eval_bool(cond, env, &Ctx::NONE)? { then } else { els };
                    self.check_constant_subformulas(branch, env)?;
                } else {
                    for x in [cond, then, els] {
                        self.check_constant_subformulas(x, env)?;
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }
}

/// The disjuncts of action `e` in `env`, the way the next-state relation is
/// split into actions (disjunctions, `\E` over constant sets, operators
/// with constant arguments; see `Interp::split_actions`), also through
/// one-conjunct conjunctions.
fn leaves(ip: &Arc<Interp>, e: &Expr, env: &Env, out: &mut Vec<(Expr, Env)>) {
    match &*e.kind {
        ExprKind::Or(es) => es.iter().for_each(|c| leaves(ip, c, env, out)),
        ExprKind::And(es) if es.len() == 1 => leaves(ip, &es[0], env, out),
        ExprKind::Let { body, .. } => leaves(ip, body, env, out),
        ExprKind::Quant { kind: QuantKind::Exists, bounds, body } => match ip.collect_split_bindings(bounds, env) {
            Some(envs) => envs.iter().for_each(|env2| leaves(ip, body, env2, out)),
            None => out.push((e.clone(), env.clone())),
        },
        ExprKind::Apply { op: OpRef::Def(d), args } => match ip.expand_for_split(*d, args, env) {
            Some((_, body, env2)) => leaves(ip, body, &env2, out),
            None => out.push((e.clone(), env.clone())),
        },
        _ => out.push((e.clone(), env.clone())),
    }
}

fn neg(f: Ltl) -> Ltl {
    Ltl::Not(Box::new(f))
}

fn always(f: Ltl) -> Ltl {
    Ltl::Always(Box::new(f))
}

fn eventually(f: Ltl) -> Ltl {
    Ltl::Eventually(Box::new(f))
}

/// Evaluation of the atoms of a `LiveSpec` on the states of some model
/// (`EnabledVia` atoms from the action-atom bits of the outgoing steps).
pub use tlx_runtime::AtomBits;

/// The interpreter's atoms on its own states.
impl AtomBits<super::State> for super::InterpModel {
    fn state(&self, s: &super::State, out: &[&[u64]]) -> Result<Vec<u64>, tlx_runtime::ModelError> {
        self.live.state_bits(&self.ip, &s.vals, s.level, out).map_err(|e| self.error(e))
    }
    fn action(&self, s: &super::State, t: &super::State) -> Result<Vec<u64>, tlx_runtime::ModelError> {
        self.live.action_bits(&self.ip, &s.vals, &t.vals, s.level).map_err(|e| self.error(e))
    }
    fn action_masks(&self) -> Option<&tlx_runtime::ActionMasks> {
        self.live.action_masks.as_ref()
    }
    fn action_only(&self, s: &super::State, t: &super::State, mask: &[u64]) -> Result<Vec<u64>, tlx_runtime::ModelError> {
        self.live.action_bits_only(&self.ip, &s.vals, &t.vals, s.level, Some(mask)).map_err(|e| self.error(e))
    }
    fn tableau(&self, t: &super::State) -> Result<(), tlx_runtime::ModelError> {
        self.live.eval_tableau(&self.ip, &t.vals, t.level).map_err(|e| self.error(e))
    }
    fn tableau_bits(&self, t: &super::State) -> Result<Vec<u64>, tlx_runtime::ModelError> {
        self.live.tableau_bits(&self.ip, &t.vals, t.level).map_err(|e| self.error(e))
    }
    fn has_action_atoms(&self) -> bool {
        !self.live.action_atoms.is_empty()
    }
}

/// The liveness predicates evaluated by the interpreter on the variable
/// values of a state, where TLC evaluates them during its search
/// (`tlx_runtime::liveness::find_error`).
pub struct InterpSearchAtoms<'a, S> {
    pub base: &'a super::InterpModel,
    pub values: &'a (dyn Fn(&S) -> Arc<[Value]> + Sync),
    /// The level of a state (`TLCGet("level")`).
    pub level: &'a (dyn Fn(&S) -> u32 + Sync),
}

impl<S> tlx_runtime::liveness::SearchAtoms<S> for InterpSearchAtoms<'_, S> {
    fn init(&self, s: &S) -> Result<(), tlx_runtime::ModelError> {
        let (live, ip) = (&self.base.live, &self.base.ip);
        let vs = (self.values)(s);
        let checks = live.initial_checks.get_or_init(|| {
            let fairness = live
                .fairness
                .iter()
                .map(|f| tlx_live::Fairness { strong: f.strong, enabled: f.enabled, taken: f.taken })
                .collect::<Vec<_>>();
            live.props.iter().flat_map(|(_, f)| tlx_live::tableau_initial_checks(f, &fairness)).collect()
        });
        for node in checks {
            for &(i, positive) in node {
                if i == u32::MAX || live.eval_state_atom(ip, i as usize, &vs, (self.level)(s)).map_err(|e| self.base.error(e))? != positive
                {
                    break;
                }
            }
        }
        Ok(())
    }

    fn expanded(&self, s: &S, succ: &[S]) -> Result<(), tlx_runtime::ModelError> {
        let (live, ip) = (&self.base.live, &self.base.ip);
        let (vs, ls) = ((self.values)(s), (self.level)(s));
        let vts: Vec<_> = succ.iter().map(|t| ((self.values)(t), (self.level)(t))).collect();
        for vt in std::iter::once(&vs).chain(vts.iter().map(|(v, _)| v)) {
            live.action_bits(ip, &vs, vt, ls).map_err(|e| self.base.error(e))?;
        }
        for i in 0..live.state_atoms.len() {
            live.eval_state_atom(ip, i, &vs, ls).map_err(|e| self.base.error(e))?;
        }
        for (vt, lt) in &vts {
            for &i in &live.tableau {
                live.eval_state_atom(ip, i as usize, vt, *lt).map_err(|e| self.base.error(e))?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture(action: &str) -> (Arc<Interp>, LiveSpec) {
        let dir = tlx_testkit::TempDir::new("live-cache");
        let body = format!("EXTENDS Naturals\nVARIABLE x\nA == {action}\nAtom == <<A>>_x\nOther == <<x' = 2>>_x\n");
        let path = dir.write("M.tla", &tlx_testkit::module("M", &body));
        let mut prog = tlx_sema::Program::load(&path, &[]).unwrap();
        let Some(RootSymbol::Def(d)) = prog.lookup_root("Atom") else { panic!("missing Atom") };
        let DefKind::Op(expr) = &prog.defs[d.idx()].kind else { panic!("not an operator") };
        let atom = Atom { expr: expr.clone(), env: Env::default() };
        let ip = Interp::new(prog, Default::default()).unwrap();
        let mut live = LiveSpec::default();
        live.action_atoms.push(atom);
        live.from_steps.push(FromSteps::Bounded);
        (ip, live)
    }

    fn other(ip: &Interp) -> Expr {
        let def = ip.prog.defs.iter().find(|d| d.name.as_ref() == "Other").unwrap();
        let DefKind::Op(expr) = &def.kind else { panic!("not an operator") };
        expr.clone()
    }

    fn edge(live: &LiveSpec, ip: &Arc<Interp>, s: i64, t: i64) -> Vec<u64> {
        live.action_bits(ip, &[Value::Int(s)], &[Value::Int(t)], 1).unwrap()
    }

    #[test]
    fn steps_same_address_replacement() {
        let (ip, mut live) = fixture("x' = 1");
        assert_eq!(edge(&live, &ip, 0, 1), [1]);
        let address = &live as *const LiveSpec;
        let mut replacement = LiveSpec::default();
        replacement.action_atoms.push(Atom { expr: other(&ip), env: Env::default() });
        replacement.from_steps.push(FromSteps::Bounded);
        live = replacement;
        assert_eq!(&live as *const LiveSpec, address);
        assert_eq!(edge(&live, &ip, 0, 1), [0]);
        assert_eq!(edge(&live, &ip, 0, 2), [1]);
    }

    #[test]
    fn steps_changed_atom_count() {
        let (ip, mut live) = fixture("x' = 1");
        assert_eq!(edge(&live, &ip, 0, 1), [1]);
        let atom = live.action_atoms[0].clone();
        live.action_atoms.push(atom);
        live.from_steps.push(FromSteps::Bounded);
        assert_eq!(edge(&live, &ip, 0, 1), [3]);
        live.action_atoms.truncate(1);
        assert_eq!(edge(&live, &ip, 0, 1), [1]);
    }

    #[test]
    fn steps_replaced_atom_same_count() {
        let (ip, mut live) = fixture("x' = 1");
        assert_eq!(edge(&live, &ip, 0, 1), [1]);
        live.action_atoms[0].expr = other(&ip);
        assert_eq!(edge(&live, &ip, 0, 1), [0]);
        assert_eq!(edge(&live, &ip, 0, 2), [1]);
    }

    #[test]
    fn steps_repeated_spec_hits_cache_and_clone_resets_it() {
        let (ip, mut live) = fixture("x' = 1");
        assert_eq!(edge(&live, &ip, 0, 1), [1]);
        let cached = STEPS.with(|steps| match &steps.borrow().atoms[0] {
            AngleSteps::Steps(set, _) => set.clone(),
            _ => panic!("not enumerated"),
        });
        assert_eq!(edge(&live, &ip, 0, 2), [0]);
        STEPS.with(|steps| {
            let steps = steps.borrow();
            let AngleSteps::Steps(set, _) = &steps.atoms[0] else { panic!("not enumerated") };
            assert!(Arc::ptr_eq(set, &cached));
        });
        live = live.clone();
        assert_eq!(edge(&live, &ip, 0, 1), [1]);
        STEPS.with(|steps| {
            let steps = steps.borrow();
            let AngleSteps::Steps(set, _) = &steps.atoms[0] else { panic!("not enumerated") };
            assert!(!Arc::ptr_eq(set, &cached));
        });
    }

    #[test]
    fn steps_bounded_fallback_and_policy_mutation() {
        let (ip, mut live) = fixture(r"x' \in 1..65");
        for s in 0..i64::from(STEPS_OVER) {
            assert_eq!(edge(&live, &ip, s, 65), [1]);
            assert_eq!(edge(&live, &ip, s, 66), [0]);
        }
        STEPS.with(|steps| {
            let steps = steps.borrow();
            assert_eq!(steps.over, [STEPS_OVER]);
            assert_eq!(steps.off, [true]);
        });
        live.from_steps[0] = FromSteps::Covered;
        assert_eq!(edge(&live, &ip, 7, 65), [1]);
        STEPS.with(|steps| {
            let steps = steps.borrow();
            assert_eq!(steps.over, [0]);
            assert_eq!(steps.off, [false]);
            assert!(matches!(steps.atoms[0], AngleSteps::Steps(..)));
        });
    }

    #[test]
    fn steps_failed_enumeration_preserves_direct_evaluation() {
        let (ip, live) = fixture("x' = x'");
        assert_eq!(edge(&live, &ip, 0, 1), [1]);
        assert_eq!(edge(&live, &ip, 0, 0), [0]);
        assert_eq!(edge(&live, &ip, 1, 2), [1]);
        STEPS.with(|steps| {
            let steps = steps.borrow();
            assert_eq!(steps.off, [true]);
            assert!(matches!(steps.atoms[0], AngleSteps::Eval));
        });
    }

    #[test]
    fn steps_sequential_models_clear_failed_enumeration() {
        let mut model = fixture("x' = x'");
        assert_eq!(edge(&model.1, &model.0, 0, 1), [1]);
        model = fixture("x' = 2");
        assert_eq!(edge(&model.1, &model.0, 0, 1), [0]);
        assert_eq!(edge(&model.1, &model.0, 0, 2), [1]);
        STEPS.with(|steps| assert_eq!(steps.borrow().off, [false]));
    }

    #[test]
    fn steps_state_enabled_observes_atom_mutation() {
        let (ip, mut live) = fixture("x' = 1");
        let enabled = Expr::new(ExprKind::Builtin { op: B::Enabled, args: vec![live.action_atoms[0].expr.clone()] }, Span::default());
        live.state_atoms.push(StateAtom::Pred(Atom { expr: enabled, env: Env::default() }));
        live.enabled_steps.push(Some(0));
        assert_eq!(live.state_bits(&ip, &[Value::Int(2)], 1, &[]).unwrap(), [1]);
        live.action_atoms[0].expr = other(&ip);
        assert_eq!(live.state_bits(&ip, &[Value::Int(2)], 1, &[]).unwrap(), [0]);
    }
    #[test]
    fn steps_changed_interpreter_invalidates_same_spec() {
        let (ip, live) = fixture("x' = 1");
        assert_eq!(edge(&live, &ip, 0, 1), [1]);
        let (ip2, _) = fixture("x' = 2");
        assert_eq!(edge(&live, &ip2, 0, 1), [0]);
        assert_eq!(edge(&live, &ip2, 0, 2), [1]);
    }

    #[test]
    fn steps_cache_tracks_bfs_level() {
        let dir = tlx_testkit::TempDir::new("live-level");
        let body = "EXTENDS Naturals, TLC\nVARIABLE x\nA == x' = TLCGet(\"level\")\nAtom == <<A>>_x\n";
        let path = dir.write("M.tla", &tlx_testkit::module("M", body));
        let mut prog = tlx_sema::Program::load(&path, &[]).unwrap();
        let Some(RootSymbol::Def(d)) = prog.lookup_root("Atom") else { panic!("missing Atom") };
        let DefKind::Op(expr) = &prog.defs[d.idx()].kind else { panic!("not an operator") };
        let atom = Atom { expr: expr.clone(), env: Env::default() };
        let ip = Interp::new(prog, Default::default()).unwrap();
        let mut live = LiveSpec::default();
        live.action_atoms.push(atom.clone());
        live.from_steps.push(FromSteps::Bounded);
        let enabled = Expr::new(ExprKind::Builtin { op: B::Enabled, args: vec![atom.expr] }, Span::default());
        live.state_atoms.push(StateAtom::Pred(Atom { expr: enabled, env: Env::default() }));
        live.enabled_steps.push(Some(0));

        // Same state `x = 1`, different BFS levels: at level 1, A steps to x' = 1 (no change);
        // at level 2, A steps to x' = 2 (changes x).
        assert_eq!(live.action_bits(&ip, &[Value::Int(1)], &[Value::Int(2)], 1).unwrap(), [0]);
        assert_eq!(live.state_bits(&ip, &[Value::Int(1)], 1, &[]).unwrap(), [0]);
        assert_eq!(live.action_bits(&ip, &[Value::Int(1)], &[Value::Int(2)], 2).unwrap(), [1]);
        assert_eq!(live.state_bits(&ip, &[Value::Int(1)], 2, &[]).unwrap(), [1]);
    }
}
