//! Bounded equivariance checks on the unreduced transition system.
//! A successful bounded run is evidence, not a proof of symmetry.

use std::collections::{HashMap, HashSet};

use tlx_sema::builtins::Builtin;
use tlx_value::ops;

use super::*;

#[derive(Clone, Debug)]
pub struct Bounds {
    pub states: usize,
    /// Maximum number of transitions from an initial state.
    pub depth: u32,
    pub permutations: usize,
    /// Maximum generated successors of either side of a comparison.
    pub edges: usize,
    /// Stop (as at the state bound) after this time.
    pub time: Option<std::time::Duration>,
}

impl Default for Bounds {
    fn default() -> Self {
        Self { states: 1000, depth: 10, permutations: 100, edges: 10000, time: None }
    }
}

pub struct Witness {
    pub part: String,
    pub permutation: String,
    pub trace: Vec<(State, Option<u32>)>,
    pub image: State,
    /// An edge involved in the mismatch, and its image.
    pub edge: Option<Edge>,
}

pub enum Edge {
    Images { original: State, image: State },
    ExtraSuccessor(State),
}

pub struct Report {
    pub checked: usize,
    pub permutations: usize,
    pub depth: u32,
    pub limited: bool,
    pub witness: Option<Witness>,
}

/// Recognize Permutations(S), aliases and unions without expanding n!.
/// Adjacent transpositions generate each full symmetric group; the union
/// of generating sets generates the group TLC takes from a union.
fn generators(ip: &Arc<Interp>, e: &Expr, out: &mut Vec<Perm>, limit: usize, nesting: usize) -> EResult<bool> {
    if nesting > 100 {
        return Err(EvalError::new("SYMMETRY definition nesting exceeds 100"));
    }
    let (op, args) = match &*e.kind {
        ExprKind::Builtin { op, args } => (*op, args),
        ExprKind::Apply { op: OpRef::Def(d), args } => {
            let d = ip.redirect_def(*d);
            if ip.def_value.contains_key(&d) {
                return Ok(false);
            }
            let def = &ip.prog.defs[d.idx()];
            if let Some(op) = def.builtin {
                (op, args)
            } else if args.is_empty() && def.params.is_empty() {
                match &def.kind {
                    DefKind::Op(body) => return generators(ip, body, out, limit, nesting + 1),
                    _ => return Ok(false),
                }
            } else {
                return Ok(false);
            }
        }
        _ => return Ok(false),
    };
    // Native operators may be replaced in the cfg. Syntax alone must not
    // bypass the same override dispatch that evaluation uses.
    if ip.is_builtin_overridden(op) {
        return Ok(false);
    }
    match (op, &args[..]) {
        (Builtin::Cup, [a, b]) => Ok(generators(ip, a, out, limit, nesting + 1)? && generators(ip, b, out, limit, nesting + 1)?),
        (Builtin::Permutations, [set]) => {
            let set = ip.eval(set, &Env::default(), &Ctx::NONE)?;
            let mut values = Vec::new();
            ops::for_each_element(&set, &mut |v| {
                values.push(v);
                Ok(values.len() <= limit.saturating_add(1))
            })?;
            if values.len() > limit.saturating_add(1) {
                return Err(EvalError::new("SYMMETRY generator limit exceeded; increase -symmetryperms"));
            }
            let values = ops::enumerate_normalized(&Value::set_from(values)?)?;
            for v in &values {
                if !matches!(v, Value::ModelValue(_)) {
                    return Err(EvalError::new(format!("SYMMETRY permutations must map model values, found {v}")));
                }
            }
            for pair in values.windows(2) {
                let (Value::ModelValue(a), Value::ModelValue(b)) = (&pair[0], &pair[1]) else { unreachable!() };
                let p = HashMap::from([(*a, pair[1].clone()), (*b, pair[0].clone())]);
                if !out.contains(&p) {
                    out.push(p);
                }
                if out.len() > limit {
                    return Err(EvalError::new("SYMMETRY generator limit exceeded; increase -symmetryperms"));
                }
            }
            Ok(true)
        }
        _ => Ok(false),
    }
}

fn permutations(m: &InterpModel, limit: usize) -> EResult<Vec<Perm>> {
    let name = m.ip.cfg.symmetry.as_ref().ok_or_else(|| EvalError::new("-checksymmetry requires a SYMMETRY declaration"))?;
    let e = def_ref(&m.ip, name)?;
    let mut out = Vec::new();
    if generators(&m.ip, &e, &mut out, limit, 0)? {
        return Ok(out);
    }
    // Arbitrary finite sets are generators too: checking every declared
    // element avoids closing them under composition (potentially n!).
    out.clear();
    let set = m.ip.eval(&e, &Env::default(), &Ctx::NONE)?;
    let mut fs = Vec::new();
    ops::for_each_element(&set, &mut |v| {
        fs.push(v);
        Ok(fs.len() <= limit)
    })?;
    if fs.len() > limit {
        return Err(EvalError::new("SYMMETRY element limit exceeded; increase -symmetryperms"));
    }
    for f in fs {
        let keys = ops::enumerate_normalized(&ops::domain(&f)?)?;
        let mut images = Vec::new();
        let mut p = Perm::new();
        for k in &keys {
            let Value::ModelValue(s) = k else { return Err(EvalError::new("SYMMETRY domain must contain model values")) };
            let v = ops::apply(&f, k)?;
            if !keys.contains(&v) || images.contains(&v) {
                return Err(EvalError::new("SYMMETRY element is not a bijection on its domain"));
            }
            images.push(v.clone());
            if v != *k {
                p.insert(*s, v);
            }
        }
        if !p.is_empty() && !out.contains(&p) {
            out.push(p);
        }
    }
    Ok(out)
}

fn image(m: &InterpModel, s: &State, p: &symmetry::FastPerm) -> Result<State, ModelError> {
    let vals: Arc<[Value]> = s
        .vals
        .iter()
        .map(|v| p.apply(v).map(|x| x.unwrap_or_else(|| v.clone())))
        .collect::<tlx_value::Result<Vec<_>>>()
        .map_err(|e| ModelError::new(e.to_string()))?
        .into();
    let fp = m.compute_fp(&vals, s.level, None).map_err(|e| m.error(e))?;
    Ok(State::new(vals, s.level, fp))
}

fn label(p: &Perm) -> String {
    let mut pairs: Vec<_> = p.iter().map(|(k, v)| format!("{} -> {v}", Value::ModelValue(*k))).collect();
    pairs.sort();
    pairs.join(", ")
}

struct Node {
    state: State,
    parent: Option<usize>,
    action: Option<u32>,
}

fn witness(nodes: &[Node], at: usize, p: &Perm, image: State, part: String, edge: Option<Edge>) -> Witness {
    let mut trace = Vec::new();
    let mut i = Some(at);
    while let Some(j) = i {
        trace.push((nodes[j].state.clone(), nodes[j].action));
        i = nodes[j].parent;
    }
    trace.reverse();
    Witness { part, permutation: label(p), trace, image, edge }
}

fn successors(m: &InterpModel, s: &State, limit: usize) -> Result<Vec<(State, u32)>, ModelError> {
    let mut out = Vec::new();
    m.successors(s, &mut |t, a| {
        out.push((t, a));
        out.len() <= limit
    })?;
    if out.len() > limit {
        return Err(ModelError::new("successor limit exceeded; increase -symmetryedges"));
    }
    Ok(out)
}

fn state_difference(m: &InterpModel, s: &State, ps: &State, p: &symmetry::FastPerm, initial: bool) -> Result<Option<String>, ModelError> {
    let eval = |e: &Expr, s: &State| {
        m.ip.eval(e, &Env::default(), &Ctx::state(&s.vals, s.level)).and_then(|v| Ok(v.normalize()?)).map_err(|e| m.error(e))
    };
    if initial && eval(&m.init, s)? != eval(&m.init, ps)? {
        return Ok(Some("Init differs on the permuted initial state".into()));
    }
    for (i, name) in m.invariant_names.iter().enumerate() {
        if m.check_invariant(s, i)? != m.check_invariant(ps, i)? {
            return Ok(Some(format!("invariant {name} differs")));
        }
    }
    if let Some(v) = &m.view {
        let view = m.projected_value(v, &s.vals, s.level).map_err(|e| m.error(e))?;
        let image = p.apply(&view).map_err(|e| ModelError::new(e.to_string()))?.unwrap_or(view);
        if image != m.projected_value(v, &ps.vals, ps.level).map_err(|e| m.error(e))? {
            return Ok(Some("VIEW does not commute with the permutation: V(p(s)) != p(V(s))".into()));
        }
    }
    for (i, e) in m.constraints.iter().enumerate() {
        if m.check_constraint(s, i)? != m.check_constraint(ps, i)? {
            return Ok(Some(format!("state constraint {} differs", expr_name(m, e))));
        }
    }
    Ok(None)
}

fn expr_name(m: &InterpModel, e: &Expr) -> String {
    match &*e.kind {
        ExprKind::Apply { op: OpRef::Def(d), .. } => m.ip.prog.defs[d.idx()].name.to_string(),
        _ => "predicate".into(),
    }
}

/// How a state and its image under a permutation differ.
pub struct Mismatch {
    pub part: String,
    /// The image of the state.
    pub image: State,
    pub edge: Option<Edge>,
}

/// Compare state `s` of the unreduced model `m`, whose successors are
/// `ts`, with its image under `f`: membership in Init (`initial`), the
/// invariants, VIEW and state constraints, the successors (the image of
/// each successor of `s` must be a successor of the image, and the other
/// way round), and the action constraints and action properties of each
/// edge.
fn compare(
    m: &InterpModel,
    s: &State,
    ts: &[(State, u32)],
    f: &symmetry::FastPerm,
    initial: bool,
    edges: usize,
) -> Result<Option<Mismatch>, ModelError> {
    let ps = image(m, s, f)?;
    if let Some(part) = state_difference(m, s, &ps, f, initial)? {
        return Ok(Some(Mismatch { part, image: ps, edge: None }));
    }
    let pts = ts.iter().map(|(t, a)| Ok((image(m, t, f)?, *a))).collect::<Result<Vec<_>, ModelError>>()?;
    let us = successors(m, &ps, edges)?;
    let actual: HashSet<_> = us.iter().map(|(u, _)| u.fp).collect();
    let expected: HashSet<_> = pts.iter().map(|(u, _)| u.fp).collect();
    let at_edge = |part: String, t: &State, pt: &State| Mismatch {
        part,
        image: ps.clone(),
        edge: Some(Edge::Images { original: t.clone(), image: pt.clone() }),
    };
    for ((t, a), (pt, _)) in ts.iter().zip(&pts) {
        let action = &m.action_names[*a as usize];
        // Check constraints on raw edges, including edges that the
        // constrained search will not admit.
        if let Some(part) = state_difference(m, t, pt, f, false)? {
            return Ok(Some(at_edge(format!("{part} at successor (action {action})"), t, pt)));
        }
        for (i, e) in m.action_constraints.iter().enumerate() {
            if m.check_action_constraint(s, t, i)? != m.check_action_constraint(&ps, pt, i)? {
                return Ok(Some(at_edge(format!("action constraint {} differs ({action})", expr_name(m, e)), t, pt)));
            }
        }
        for (i, name) in m.action_prop_names.iter().enumerate() {
            if m.check_action_property(s, t, i)? != m.check_action_property(&ps, pt, i)? {
                return Ok(Some(at_edge(format!("action property {name} differs ({action})"), t, pt)));
            }
        }
        if !actual.contains(&pt.fp) {
            return Ok(Some(at_edge(format!("successor of s has no permuted counterpart (action {action})"), t, pt)));
        }
    }
    if let Some((u, a)) = us.iter().find(|(u, _)| !expected.contains(&u.fp)) {
        let part = format!("successor of p(s) has no counterpart in p(Next(s)) (action {})", m.action_names[*a as usize]);
        // Only an actual successor of the image exists.
        return Ok(Some(Mismatch { part, image: ps, edge: Some(Edge::ExtraSuccessor(u.clone())) }));
    }
    Ok(None)
}

/// `compare` of state `s` with its image under each permutation of `perms`
/// (`m` unreduced): the label of the first permutation that differs, and how.
pub(super) fn compare_state(m: &InterpModel, s: &State, perms: &[Perm], edges: usize) -> Result<Option<(String, Mismatch)>, ModelError> {
    let ts = successors(m, s, edges)?;
    for p in perms {
        if let Some(d) = compare(m, s, &ts, &symmetry::FastPerm::new(p), s.level <= 1, edges)? {
            return Ok(Some((label(p), d)));
        }
    }
    Ok(None)
}

/// Explore at most `states` unreduced states, checking every selected
/// permutation at each state. Successor comparisons always use complete
/// sets; an edge cap stops the check with an explicit incomplete error.
pub fn check(model: &InterpModel, bounds: &Bounds) -> Result<Report, ModelError> {
    if bounds.states == 0 || bounds.permutations == 0 || bounds.edges == 0 {
        return Err(ModelError::new("symmetry limits must be positive"));
    }
    let perms = permutations(model, bounds.permutations).map_err(|e| model.error(e))?;
    check_perms(model, perms, bounds)
}

/// `check` of the given permutations (generators of a group) instead of
/// the declared SYMMETRY.
pub fn check_perms(model: &InterpModel, perms: Vec<HashMap<Sym, Value>>, bounds: &Bounds) -> Result<Report, ModelError> {
    if bounds.states == 0 || bounds.edges == 0 {
        return Err(ModelError::new("symmetry limits must be positive"));
    }
    let started = std::time::Instant::now();
    let m = model.with_fp_mode(FpMode::Plain);
    let fast: Vec<_> = perms.iter().map(symmetry::FastPerm::new).collect();
    let mut report = Report { checked: 0, permutations: perms.len(), depth: 0, limited: false, witness: None };
    let mut nodes = Vec::new();
    let mut seen = HashSet::new();
    m.init_states_while(&mut |s| {
        if seen.insert(s.fp) {
            if nodes.len() == bounds.states {
                report.limited = true;
                return false;
            }
            nodes.push(Node { state: s, parent: None, action: None });
        }
        true
    })?;
    let mut at = 0;
    while at < nodes.len() {
        let s = nodes[at].state.clone();
        report.checked += 1;
        report.depth = report.depth.max(s.level - 1);
        if bounds.time.is_some_and(|t| started.elapsed() >= t) {
            report.limited = true;
            break;
        }
        let ts = successors(&m, &s, bounds.edges)?;
        for (p, f) in perms.iter().zip(&fast) {
            if let Some(d) = compare(&m, &s, &ts, f, nodes[at].parent.is_none(), bounds.edges)? {
                report.witness = Some(witness(&nodes, at, p, d.image, d.part, d.edge));
                return Ok(report);
            }
        }
        if m.constraint(&s)? {
            for (t, a) in ts {
                if !m.constraint(&t)? || !m.action_constraint(&s, &t)? || seen.contains(&t.fp) {
                    continue;
                }
                if s.level > bounds.depth || nodes.len() >= bounds.states {
                    report.limited = true;
                    continue;
                }
                seen.insert(t.fp);
                nodes.push(Node { state: t, parent: Some(at), action: Some(a) });
            }
        }
        at += 1;
    }
    Ok(report)
}
