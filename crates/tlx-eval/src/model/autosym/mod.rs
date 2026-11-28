//! Automatic symmetry (docs/reductions.md §2.2): the sets of model
//! values the cfg binds to constants (candidates), a static proof of which
//! permutations of them are automorphisms of the checked state graph
//! (`analyze`: a scalarset analysis), and the resulting group.
//!
//! A candidate is a constant whose cfg value is a set of at least two
//! model values (`RM = {r1, r2, r3}`, or `RM <- Def` with a constant
//! definition of such a set). A transposition of two of its elements is
//! admitted when it maps every constant value the checked parts read to
//! itself (`Leader = r1` pins r1); the admitted transpositions generate
//! the group, a product of the full permutation groups of classes of
//! elements. A candidate is proven when no breaker applies to its
//! elements. The proof covers safety checking only: initial states,
//! successors, invariants, constraints, action constraints, action
//! properties and deadlock.

mod analyze;
mod shape;

use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt::Write as _;
use std::sync::Arc;
use std::time::{Duration, Instant};

use tlx_front::cfg::ConstBinding;
use tlx_sema::hir::*;
use tlx_sema::optimize::{SymGroup, SymGroupKind};
use tlx_value::{ops, SymAtom, Value};

use super::{behavior, Behavior, InterpModel};
use crate::env::Env;
use crate::eval::Ctx;
use crate::interp::{ConstVal, Interp};
use shape::Mask;

/// A constant bound to a set of model values.
#[derive(Clone, Debug)]
pub struct Candidate {
    /// The constant's name.
    pub name: String,
    /// Its elements, in TLC's value order.
    pub elems: Vec<Value>,
}

/// What the analysis concluded about a candidate.
#[derive(Clone, Debug)]
pub enum Verdict {
    /// The cfg's SYMMETRY already permutes its elements.
    Declared,
    /// Its elements never occur in a state (nothing to reduce).
    Unused,
    /// Not provable: `what` at `at` may depend on which element a value
    /// contains.
    Rejected { what: String, at: String },
    /// Provable: every permutation of each class (of at least two
    /// elements) is an automorphism. Fewer classes than the whole set when
    /// constants (`pinned_by`) single out elements.
    Proven { classes: Vec<Vec<Value>>, pinned_by: Vec<String> },
    /// Provable only for the identity: constants (`pinned_by`) single out
    /// every element.
    Pinned { pinned_by: Vec<String> },
}

#[derive(Clone, Debug)]
pub struct SetResult {
    pub candidate: Candidate,
    pub verdict: Verdict,
    /// When `verdict` is `Rejected { what: "CHOOSE", .. }` and no other
    /// breaker applied to this candidate, the verdict that atom partitioning
    /// produces if the `CHOOSE` expressions are separately certified.
    pub choose_verdict: Option<Verdict>,
}

/// The result of the analysis.
#[derive(Clone, Debug, Default)]
pub struct Analysis {
    pub sets: Vec<SetResult>,
    /// Builtins whose results or side effects depend on the states explored
    /// (`Print at Spec.tla:10:3`): no count-changing reduction applies.
    pub effects: Vec<String>,
    /// The analysis gave up (the spec is too large for it): nothing is
    /// proven.
    pub incomplete: bool,
    /// The candidates treated as proven by `force`.
    pub forced: Vec<String>,
    pub elapsed: Duration,
}

/// `file:line:col` of `sp`.
fn location(ip: &Interp, sp: Span) -> String {
    let path = &ip.prog.file(sp.file).path;
    let file = path.file_name().map_or_else(|| path.display().to_string(), |f| f.to_string_lossy().to_string());
    format!("{file}:{}:{}", sp.line, sp.col)
}

/// The elements of `v` if it is a homogeneous set of at least two model values
/// of the same model-value type, or at least two strings.
fn scalarset_elems(v: &Value) -> Option<Vec<Value>> {
    let Value::Set(es) = v else { return None };
    if es.len() < 2 {
        return None;
    }
    match &es[0] {
        Value::ModelValue(first) => {
            let ty = first.model_value_type();
            es.iter().all(|e| matches!(e, Value::ModelValue(m) if m.model_value_type() == ty)).then(|| es.to_vec())
        }
        Value::Str(_) => es.iter().all(|e| matches!(e, Value::Str(_))).then(|| es.to_vec()),
        _ => None,
    }
}

/// Convert a non-empty homogeneous slice of `SymAtom` keys to a typed `SymGroup`.
pub fn sym_group_from_atoms(keys: &[SymAtom]) -> Option<SymGroup> {
    let first = *keys.first()?;
    let kind = match first {
        SymAtom::Model(_) => SymGroupKind::Model,
        SymAtom::Str(_) => SymGroupKind::Str,
    };
    if !keys.iter().all(|k| matches!((first, *k), (SymAtom::Model(_), SymAtom::Model(_)) | (SymAtom::Str(_), SymAtom::Str(_)))) {
        return None;
    }
    Some(SymGroup { kind, keys: keys.iter().map(|m| m.sym().as_str().to_owned()).collect() })
}

/// The value the cfg gives the root constant or definition `name`.
fn cfg_bound_value(ip: &Arc<Interp>, name: &str) -> Option<Value> {
    if let Some(c) = ip.prog.consts.iter().position(|c| &*c.name == name && c.arity == 0) {
        return match &ip.consts[c] {
            Some(ConstVal::Value(v)) => Some(v.clone()),
            Some(ConstVal::Def(d)) => {
                let d = ip.redirect_def(*d);
                if let Some(v) = ip.def_value.get(&d) {
                    return Some(v.clone());
                }
                if !ip.is_const_def(d) {
                    return None;
                }
                let span = ip.prog.defs[d.idx()].span;
                let e = Expr::new(ExprKind::Apply { op: OpRef::Def(d), args: Vec::new() }, span);
                ip.eval(&e, &Env::default(), &Ctx::NONE).ok()
            }
            _ => None,
        };
    }
    let d = ip.root_def(name)?;
    ip.def_value.get(&d).cloned()
}

/// The candidates, in the order the cfg binds them.
pub fn candidates(ip: &Arc<Interp>) -> Vec<Candidate> {
    let mut out: Vec<Candidate> = Vec::new();
    for b in &ip.cfg.constants {
        let name = match b {
            ConstBinding::Value { name, module: None, .. } | ConstBinding::Subst { name, module: None, .. } => name,
            _ => continue,
        };
        if out.iter().any(|c| &c.name == name) {
            continue;
        }
        if let Some(elems) = cfg_bound_value(ip, name).as_ref().and_then(scalarset_elems) {
            out.push(Candidate { name: name.clone(), elems });
        }
    }
    out
}

/// The model values the declared SYMMETRY moves.
fn declared_support(model: &InterpModel) -> HashSet<SymAtom> {
    let mut out = model.group.moved_syms();
    if !out.is_empty() {
        return out;
    }
    let Some(name) = &model.ip.cfg.symmetry else { return out };
    let Ok(e) = super::def_ref(&model.ip, name) else { return out };
    let Ok(set) = model.ip.eval(&e, &Env::default(), &Ctx::NONE) else { return out };
    let _ = ops::for_each_element(&set, &mut |f| {
        if let Ok(keys) = ops::enumerate_normalized(&ops::domain(&f)?) {
            for k in keys {
                if let (Some(atom), Ok(img)) = (SymAtom::from_value(&k), ops::apply(&f, &k)) {
                    if img != k {
                        out.insert(atom);
                    }
                }
            }
        }
        Ok(out.len() < 100_000)
    });
    out
}

/// The expressions the safety checks evaluate.
fn checked_parts(model: &InterpModel) -> Vec<Expr> {
    let ip = &model.ip;
    let mut out = vec![model.init.clone()];
    if let Ok(Behavior::Full { next, .. }) = behavior(ip, &ip.cfg) {
        out.push(next);
    }
    out.extend(model.invariants.iter().cloned());
    out.extend(model.constraints.iter().cloned());
    out.extend(model.action_constraints.iter().cloned());
    out.extend(model.action_props.iter().cloned());
    out.extend(model.init_props.iter().map(|(_, e)| e.clone()));
    let refer = |d: DefId| Expr::new(ExprKind::Apply { op: OpRef::Def(d), args: Vec::new() }, ip.prog.defs[d.idx()].span);
    out.extend(model.possible.iter().map(|p| refer(p.def)));
    out.extend(model.postconditions.iter().map(|(_, d)| refer(*d)));
    out
}

/// Reuse the interprocedural effect analysis only after a coarse trace fails.
/// Trace itself has a reconstructed path; other effects can change generation,
/// admission or the terminal predicate when the stopped search is replayed.
pub(super) fn trace_replay_limit(model: &InterpModel) -> Option<&'static str> {
    let impure = |entries: &[Expr]| {
        let mask_of = |_: SymAtom| 0;
        let mut an = analyze::Analyzer::new(&model.ip, &mask_of, 0);
        an.run(entries);
        (an.effects.iter().any(|e| e.what != "Trace"), an.overflow)
    };
    let view = model.view.is_some();
    let note = |part, entries: &[Expr]| {
        let (effects, overflow) = impure(entries);
        if overflow {
            Some("trace cannot be reconstructed: effect analysis of replayed predicates was incomplete")
        } else if effects {
            Some(match (view, part) {
                (true, 0) => "trace cannot be reconstructed: Next depends on run-time counters (TLCGet/TLCSet/Random) under VIEW",
                (false, 0) => "trace cannot be reconstructed: Next depends on run-time counters (TLCGet/TLCSet/Random) under SYMMETRY",
                (true, 1) => "trace cannot be reconstructed: Init depends on run-time counters (TLCGet/TLCSet/Random) under VIEW",
                (false, 1) => "trace cannot be reconstructed: Init depends on run-time counters (TLCGet/TLCSet/Random) under SYMMETRY",
                (true, _) => "trace cannot be reconstructed: a replayed predicate depends on run-time counters, registers, randomness or I/O under VIEW",
                (false, _) => "trace cannot be reconstructed: a replayed predicate depends on run-time counters, registers, randomness or I/O under SYMMETRY",
            })
        } else {
            None
        }
    };
    if let Ok(Behavior::Full { next, .. }) = behavior(&model.ip, &model.ip.cfg) {
        if let Some(reason) = note(0, &[next]) {
            return Some(reason);
        }
    }
    if let Some(reason) = note(1, std::slice::from_ref(&model.init)) {
        return Some(reason);
    }
    let mut parts = checked_parts(model);
    parts.extend(model.view.iter().cloned());
    note(2, &parts)
}

/// Analyze the candidates of `model`.
pub fn analyze(model: &InterpModel) -> Analysis {
    let started = Instant::now();
    let ip = &model.ip;
    let cands = candidates(ip);
    let declared = declared_support(model);
    // (At most 64 candidates are analyzed: one bit each.)
    let analyzed: Vec<usize> = (0..cands.len()).filter(|&i| !cands[i].elems.iter().all(|e| is_declared(e, &declared))).take(64).collect();
    let mut masks: HashMap<SymAtom, Mask> = HashMap::new();
    let mut string_mask: Mask = 0;
    for (bit, &i) in analyzed.iter().enumerate() {
        for e in &cands[i].elems {
            if let Some(atom) = SymAtom::from_value(e) {
                *masks.entry(atom).or_default() |= 1 << bit;
                if matches!(atom, SymAtom::Str(_)) {
                    string_mask |= 1 << bit;
                }
            }
        }
    }
    let mask_of = |a: SymAtom| masks.get(&a).copied().unwrap_or(0);
    let mut an = analyze::Analyzer::new(ip, &mask_of, string_mask);
    if !analyzed.is_empty() && model.has_behavior {
        // The declared `VIEW` shapes the reduced fingerprint, so its own
        // effects and (non-)equivariance are part of the reduction: a view that
        // reads run-time counters or breaks the group makes the orbit quotient
        // unsound and must refuse automatic symmetry.
        let mut parts = checked_parts(model);
        parts.extend(model.view.iter().cloned());
        an.run(&parts);
    }
    let state_mask = an.vars.iter().fold(0, |a, s| a | s.mask());
    let mut sets = Vec::new();
    for (i, c) in cands.iter().enumerate() {
        let (verdict, choose_verdict) = match analyzed.iter().position(|&j| j == i) {
            None if c.elems.iter().all(|e| is_declared(e, &declared)) => (Verdict::Declared, None),
            None => (Verdict::Rejected { what: "too many candidate sets".into(), at: String::new() }, None),
            Some(bit) => {
                let bit: Mask = 1 << bit;
                if an.overflow {
                    (Verdict::Rejected { what: "the analysis (the spec is too large for it)".into(), at: String::new() }, None)
                } else if let Some(b) =
                    an.breakers.iter().filter(|b| b.mask & bit != 0).min_by_key(|b| (b.what == "CHOOSE", b.span.file.0, b.span.start))
                {
                    let choose_verdict = if b.what == "CHOOSE" {
                        if state_mask & bit == 0 || !model.has_behavior {
                            Some(Verdict::Unused)
                        } else {
                            Some(classes(ip, c, &an.atoms))
                        }
                    } else {
                        None
                    };
                    (Verdict::Rejected { what: b.what.clone(), at: location(ip, b.span) }, choose_verdict)
                } else if state_mask & bit == 0 || !model.has_behavior {
                    (Verdict::Unused, None)
                } else {
                    (classes(ip, c, &an.atoms), None)
                }
            }
        };
        sets.push(SetResult { candidate: c.clone(), verdict, choose_verdict });
    }
    let mut effects: Vec<String> = an.effects.iter().map(|e| format!("{} at {}", e.what, location(ip, e.span))).collect();
    effects.dedup();
    Analysis { sets, effects, incomplete: an.overflow, forced: Vec::new(), elapsed: started.elapsed() }
}

fn is_declared(e: &Value, declared: &HashSet<SymAtom>) -> bool {
    SymAtom::from_value(e).is_some_and(|a| declared.contains(&a))
}

/// The classes of the elements of `c` that transpositions fixing every
/// atom connect.
fn classes(ip: &Interp, c: &Candidate, atoms: &[analyze::Atom]) -> Verdict {
    let n = c.elems.len();
    let mut parent: Vec<usize> = (0..n).collect();
    fn root(p: &mut [usize], mut x: usize) -> usize {
        while p[x] != x {
            p[x] = p[p[x]];
            x = p[x];
        }
        x
    }
    let mut pinned_by = BTreeSet::new();
    for x in 0..n {
        for y in x + 1..n {
            let (Some(a), Some(b)) = (SymAtom::from_value(&c.elems[x]), SymAtom::from_value(&c.elems[y])) else { continue };
            match atoms.iter().find(|at| shape::fixed_by(&at.value, a, b) != Some(true)) {
                None => {
                    let (rx, ry) = (root(&mut parent, x), root(&mut parent, y));
                    parent[rx] = ry;
                }
                Some(at) => {
                    let place = at.at.map_or_else(|| "the cfg".to_string(), |sp| location(ip, sp));
                    pinned_by.insert(format!("{} ({place})", at.name));
                }
            }
        }
    }
    let mut groups: HashMap<usize, Vec<Value>> = HashMap::new();
    for x in 0..n {
        let r = root(&mut parent, x);
        groups.entry(r).or_default().push(c.elems[x].clone());
    }
    let mut classes: Vec<Vec<Value>> = groups.into_values().filter(|g| g.len() >= 2).collect();
    classes.sort_by(|a, b| tlx_value::order::cmp_tlc(&a[0], &b[0]).unwrap_or(std::cmp::Ordering::Equal));
    let pinned_by: Vec<String> = if classes.len() == 1 && classes[0].len() == n { Vec::new() } else { pinned_by.into_iter().collect() };
    if classes.is_empty() {
        Verdict::Pinned { pinned_by }
    } else {
        Verdict::Proven { classes, pinned_by }
    }
}

impl SetResult {
    /// Whether every permutation of the whole set is proven.
    pub fn full(&self) -> bool {
        matches!(&self.verdict, Verdict::Proven { classes, .. } if classes.len() == 1 && classes[0].len() == self.candidate.elems.len())
    }

    /// The proven group of this set, as TLA+ text (`Permutations(RM)`, or
    /// `Permutations(RM \ {r1})` and products), `None` if nothing is proven.
    pub fn group_text(&self) -> Option<String> {
        let Verdict::Proven { classes, .. } = &self.verdict else { return None };
        let name = &self.candidate.name;
        if self.full() {
            return Some(format!("Permutations({name})"));
        }
        let parts: Vec<String> = classes
            .iter()
            .map(|cl| {
                let rest: Vec<String> = self.candidate.elems.iter().filter(|e| !cl.contains(e)).map(|e| e.to_string()).collect();
                if rest.len() < cl.len() {
                    format!("Permutations({name} \\ {{{}}})", rest.join(", "))
                } else {
                    format!("Permutations({{{}}})", cl.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(", "))
                }
            })
            .collect();
        Some(parts.join(" x "))
    }

    /// The order of the proven group.
    pub fn group_order(&self) -> u128 {
        match &self.verdict {
            Verdict::Proven { classes, .. } => classes.iter().map(|c| factorial(c.len())).product(),
            _ => 1,
        }
    }

    /// Generators of the proven group: adjacent transpositions of each class.
    pub fn generators(&self) -> Vec<HashMap<SymAtom, Value>> {
        let Verdict::Proven { classes, .. } = &self.verdict else { return Vec::new() };
        classes.iter().flat_map(|cl| transpositions(cl)).collect()
    }

    /// Why it is not proven (for `-stats`), `None` if it is.
    pub fn reason(&self) -> Option<String> {
        Some(match &self.verdict {
            Verdict::Declared => "covered by the declared SYMMETRY".into(),
            Verdict::Unused => "its elements never occur in a state".into(),
            Verdict::Rejected { what, at } if at.is_empty() => format!("not provable ({what})"),
            Verdict::Rejected { what, at } => format!("not provable ({what} at {at})"),
            Verdict::Pinned { pinned_by } => format!("not provable (every element is singled out by {})", pinned_by.join(", ")),
            Verdict::Proven { .. } => return None,
        })
    }
}

/// Adjacent transpositions of `elems`: generators of all their permutations.
pub fn transpositions(elems: &[Value]) -> Vec<HashMap<SymAtom, Value>> {
    let mut out = Vec::new();
    for pair in elems.windows(2) {
        let (Some(a), Some(b)) = (SymAtom::from_value(&pair[0]), SymAtom::from_value(&pair[1])) else { continue };
        if !matches!((a, b), (SymAtom::Model(_), SymAtom::Model(_)) | (SymAtom::Str(_), SymAtom::Str(_))) {
            continue;
        }
        out.push(HashMap::from([(a, pair[1].clone()), (b, pair[0].clone())]));
    }
    out
}

fn factorial(n: usize) -> u128 {
    (1..=n as u128).fold(1u128, |a, k| a.saturating_mul(k))
}

impl Analysis {
    /// The sets with a proven group.
    pub fn proven(&self) -> impl Iterator<Item = &SetResult> {
        self.sets.iter().filter(|s| matches!(s.verdict, Verdict::Proven { .. }))
    }

    /// The proven group as text (`Permutations(RM) x Permutations(Acceptor)`).
    pub fn group_text(&self) -> String {
        self.proven().filter_map(|s| s.group_text()).collect::<Vec<_>>().join(" x ")
    }

    /// A SYMMETRY definition of the proven group, to paste into the spec
    /// (`Permutations(RM) \cup Permutations(Acceptor)`), `None` when a
    /// class cannot be named in TLA+ (it leaves out elements no constant
    /// names) or when any proven set contains `Value::Str` elements (which
    /// manual `.cfg` `SYMMETRY` cannot permute).
    pub fn symmetry_definition(&self) -> Option<String> {
        let mut parts = Vec::new();
        for s in self.proven() {
            if !s.full() || s.candidate.elems.iter().any(|e| matches!(e, Value::Str(_))) {
                return None;
            }
            parts.push(format!("Permutations({})", s.candidate.name));
        }
        (!parts.is_empty()).then(|| parts.join(" \\cup "))
    }

    /// The order of the proven group.
    pub fn group_order(&self) -> u128 {
        self.proven().map(|s| s.group_order()).fold(1u128, |a, b| a.saturating_mul(b))
    }

    /// The suggestion line: the proven group, if any. `advice` says how to
    /// use it: `Some(true)` by running without `-tlc` (or declaring it),
    /// `Some(false)` by declaring it, `None` not at all (the run checks
    /// temporal properties, which a reduction can falsify).
    pub fn suggestion(&self, advice: Option<bool>) -> Option<String> {
        let g = self.group_text();
        if g.is_empty() {
            return None;
        }
        self.suggestion_for(advice.map(|ok| ok.then_some(g.as_str())))
    }

    /// Like [`Self::suggestion`], naming the exact `certified` group text when
    /// default mode certifies a proper subset of `self.group_text()`.
    pub fn suggestion_for(&self, certified: Option<Option<&str>>) -> Option<String> {
        let g = self.group_text();
        if g.is_empty() {
            return None;
        }
        let mut s = format!("Symmetry: {g} is provable for safety checking and not declared");
        let declare = self.symmetry_definition().map(|d| format!("define Perms == {d} and add \"SYMMETRY Perms\" to the cfg"));
        match (certified, declare) {
            (Some(Some(cg)), Some(d)) if cg == g => {
                let _ = write!(s, "; to use it, run without -tlc, or {d}.");
            }
            (Some(Some(cg)), Some(d)) => {
                let _ = write!(s, "; run without -tlc to use {cg}, or {d} for the full group.");
            }
            (Some(Some(cg)), None) if cg == g => s.push_str("; to use it, run without -tlc."),
            (Some(Some(cg)), None) => {
                let _ = write!(s, "; run without -tlc to use {cg}.");
            }
            (Some(None), Some(d)) => {
                let _ = write!(s, "; to use it, {d}.");
            }
            (None, _) => {
                s.push_str(" (not for the temporal properties this run checks: under SYMMETRY, TLC can miss or invent their violations).")
            }
            (Some(None), None) => s.push('.'),
        }
        Some(s)
    }

    /// Treat the candidates named in `names` as proven for all their
    /// permutations, whatever the analysis found: a deliberately wrong
    /// proof, to test the checks of an applied symmetry
    /// (`TLX_AUTOSYM_FORCE`).
    pub fn force(&mut self, names: &[&str]) {
        for s in &mut self.sets {
            if names.contains(&s.candidate.name.as_str()) && !matches!(s.verdict, Verdict::Declared) {
                s.verdict = Verdict::Proven { classes: vec![s.candidate.elems.clone()], pinned_by: Vec::new() };
                self.forced.push(s.candidate.name.clone());
            }
        }
    }

    /// The proven sets to apply: by group order, largest first, as long as
    /// the order of the product stays at most `max_order` (the search
    /// tries every element of the group on each state); and the proven
    /// sets left out.
    pub fn select(&self, max_order: u128) -> (Vec<&SetResult>, Vec<&SetResult>) {
        let mut sets: Vec<&SetResult> = self.proven().collect();
        sets.sort_by_key(|s| std::cmp::Reverse(s.group_order()));
        let (mut chosen, mut skipped, mut order) = (Vec::new(), Vec::new(), 1u128);
        for s in sets {
            let o = order.saturating_mul(s.group_order());
            if o <= max_order {
                order = o;
                chosen.push(s);
            } else {
                skipped.push(s);
            }
        }
        // (In the order the cfg binds them.)
        let at = |x: &&SetResult| self.sets.iter().position(|y| std::ptr::eq(y, *x));
        chosen.sort_by_key(at);
        skipped.sort_by_key(at);
        (chosen, skipped)
    }

    /// A line per candidate that is not proven, with the reason.
    pub fn rejections(&self) -> Vec<String> {
        self.sets.iter().filter_map(|s| s.reason().map(|r| format!("{}: {r}", s.candidate.name))).collect()
    }
}
