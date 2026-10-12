//! Full symmetry of fixed-domain maps with key-free payloads.
//! Key operations are explicit rule IR; leaves never receive renamed keys.
mod expressions;
mod output;

use super::{
    binding, branches,
    domain::{self, Atom, Domain, Domains, Locals},
    normalize::Normalizer,
    variable, Branch,
};
use crate::{builtins::Builtin as B, hir::*, Program};
use std::collections::BTreeSet;
use tlx_front::cfg::Config;

/// Generate a connected certificate for the full permutation group of `keys`.
/// Unsupported state shapes or key operations fail closed. No verifier is run.
pub fn symmetry_certificate(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    observations: &[Expr],
    keys: &[String],
) -> Option<String> {
    if !(2..=6).contains(&keys.len()) {
        return None;
    }
    let keys: BTreeSet<_> = keys.iter().map(|k| Atom::Model(k.as_str().into())).collect();
    let mut normalize = Normalizer::new(program);
    let initial = normalize.root(init)?;
    let steps = branches(&normalize.root(next)?)?;
    let observations = observations.iter().map(|o| normalize.root(o)).collect::<Option<Vec<_>>>()?;
    let domains = Domains::infer(program, cfg, &branches(&initial)?, &steps)?;
    let mut maps = vec![];
    for (i, d) in domains.vars.iter().enumerate() {
        if let Domain::Function(ks, payload) = d {
            if *ks == keys && independent(payload, &keys) && comparable(payload) {
                maps.push(VarId(i as u32));
                continue;
            }
        }
        if !independent(d, &keys) {
            return None;
        }
    }
    if maps.is_empty() || steps.is_empty() {
        return None;
    }
    let mut e = Emitter { domains: &domains, keys: &keys, maps, atoms: vec![] };
    let cases = steps.iter().map(|b| e.case(b)).collect::<Option<Vec<_>>>()?;
    let observation = e.tests(&observations, &[])?;
    Some(e.output(&initial, &cases, &observation))
}

struct Emitter<'a> {
    domains: &'a Domains,
    keys: &'a BTreeSet<Atom>,
    maps: Vec<VarId>,
    atoms: Vec<String>,
}
struct Case {
    guard: String,
    writes: Vec<String>,
    keys: Vec<LocalId>,
}

// Domain inference is a trusted lowering layer, not an invariant assumption.
fn independent(d: &Domain, keys: &BTreeSet<Atom>) -> bool {
    match d {
        Domain::Bottom | Domain::Integer(_) => true,
        Domain::Top | Domain::Mapping(_) => false,
        Domain::Atoms(a) => a.is_disjoint(keys),
        Domain::Set(d) | Domain::Seq(d) => independent(d, keys),
        Domain::Record(fs) => fs.values().all(|d| independent(d, keys)),
        Domain::Records(rs) => rs.iter().all(|fs| fs.values().all(|d| independent(d, keys))),
        Domain::Function(ks, d) => ks.is_disjoint(keys) && independent(d, keys),
    }
}

// Runtime symmetry uses TLC's partial comparison to select a representative.
// Values at each permuted map slot must be mutually comparable.
fn comparable(d: &Domain) -> bool {
    match d {
        Domain::Bottom | Domain::Integer(_) => true,
        Domain::Top | Domain::Mapping(_) | Domain::Records(_) => false,
        Domain::Atoms(a) => domain::compatible(a),
        Domain::Set(d) | Domain::Seq(d) => comparable(d),
        Domain::Record(fs) => fs.values().all(comparable),
        Domain::Function(ks, d) => domain::compatible(ks) && comparable(d),
    }
}

impl Emitter<'_> {
    fn case(&mut self, b: &Branch) -> Option<Case> {
        let locals = self.domains.locals(&b.bounds);
        let mut keys = vec![];
        let mut guards = vec![];
        for bound in &b.bounds {
            let BoundVars::Many(ids) = &bound.vars else { return None };
            if self.domains.exact_set(&bound.set).as_ref() == Some(self.keys) {
                keys.extend(ids);
            } else {
                for id in ids {
                    if !independent(locals.get(id)?, self.keys) {
                        return None;
                    }
                    guards.push(Expr::new(
                        ExprKind::Builtin { op: B::In, args: vec![Expr::new(ExprKind::Local(*id), bound.set.span), bound.set.clone()] },
                        bound.set.span,
                    ));
                }
            }
        }
        let mut writes = vec![];
        for slot in 0..self.maps.len() {
            let var = self.maps[slot];
            let rhs = binding(b, var, true)?;
            if variable(&rhs, false) == Some(var) {
                continue;
            }
            let ExprKind::Except { base, updates } = &*rhs.kind else { return None };
            if variable(base, false) != Some(var) || updates.is_empty() {
                return None;
            }
            let mut actor = None;
            let mut payload = None;
            for (path, value) in updates {
                let (ExceptKey::Index(args), rest) = path.split_first()? else { return None };
                let [arg] = args.as_slice() else { return None };
                let ExprKind::Local(id) = &*arg.kind else { return None };
                let index = keys.iter().position(|k| k == id)?;
                if actor.is_some_and(|a| a != index) {
                    return None;
                }
                actor = Some(index);
                let previous = payload.unwrap_or_else(|| Expr::new(ExprKind::FnApp { func: base.clone(), args: args.clone() }, rhs.span));
                payload = Some(if rest.is_empty() {
                    value.clone()
                } else {
                    Expr::new(ExprKind::Except { base: previous, updates: vec![(rest.to_vec(), value.clone())] }, rhs.span)
                });
            }
            let value = self.value(&payload?, &keys)?;
            writes.push(format!("⟨⟨{slot}, by decide⟩, {}, {value}⟩", actor?));
        }
        for term in &b.terms {
            if matches!(&*term.kind, ExprKind::Builtin { op: B::Eq, args } if args.len()==2 && variable(&args[0],true).is_some_and(|v| self.maps.contains(&v)))
            {
                continue;
            }
            let term = if let ExprKind::Builtin { op: B::Unchanged, args } = &*term.kind {
                let [arg] = args.as_slice() else { return None };
                Expr::new(ExprKind::Builtin { op: B::Unchanged, args: vec![self.frames(arg)?] }, term.span)
            } else {
                term.clone()
            };
            guards.push(term);
        }
        Some(Case { guard: self.tests(&guards, &keys)?, writes, keys })
    }

    fn frames(&self, e: &Expr) -> Option<Expr> {
        Some(Expr::new(
            match &*e.kind {
                ExprKind::Var(v) if self.maps.contains(v) => ExprKind::Tuple(vec![]),
                ExprKind::Var(_) => return Some(e.clone()),
                ExprKind::Tuple(es) => ExprKind::Tuple(es.iter().map(|e| self.frames(e)).collect::<Option<_>>()?),
                _ => return None,
            },
            e.span,
        ))
    }
}
