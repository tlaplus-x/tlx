//! Independent certificates for cleanup passes. These checks do not call the
//! candidate generators or consume their cached analyses.

use super::ir::{Domain, Model, Predicate as P, Update};
use super::Diagnostic;

fn invalid(rule: &str) -> Diagnostic {
    Diagnostic::new(format!("invalid {rule} evidence or rewrite"))
}

pub(super) fn constant(before: &Model, after: &Model, variables: &[usize]) -> Result<(), Diagnostic> {
    let fail = || invalid("constant-state-propagation");
    if before.variables.len() != after.variables.len()
        || before.initial != after.initial
        || before.actions.len() != after.actions.len()
        || before.properties.len() != after.properties.len()
        || variables.windows(2).any(|w| w[0] >= w[1])
    {
        return Err(fail());
    }
    let mut fixed = vec![false; before.variables.len()];
    for &i in variables {
        if i >= fixed.len() || matches!(before.variables[i].domain, Domain::Interval(_)) {
            return Err(fail());
        }
        // Init establishes x=initial[x]. Every action must preserve it;
        // guards and target properties are never assumed to establish it.
        if !before.actions.iter().all(|a| matches!(a.updates[i], Update::Keep) || a.updates[i] == Update::Reset && before.initial[i] == 0) {
            return Err(fail());
        }
        fixed[i] = true;
    }
    for (i, (a, b)) in before.variables.iter().zip(&after.variables).enumerate() {
        let domain = if fixed[i] { Domain::Constant(before.initial[i]) } else { a.domain.clone() };
        if a.name != b.name || a.span != b.span || b.domain != domain {
            return Err(fail());
        }
    }
    for (a, b) in before.actions.iter().zip(&after.actions) {
        if a.span != b.span || !substituted(&a.guard, &b.guard, &fixed, &before.initial) {
            return Err(fail());
        }
        for (i, (x, y)) in a.updates.iter().zip(&b.updates).enumerate() {
            if *y != if fixed[i] { Update::Keep } else { *x } {
                return Err(fail());
            }
        }
    }
    for (a, b) in before.properties.iter().zip(&after.properties) {
        if a.name != b.name || a.span != b.span || !substituted(&a.predicate, &b.predicate, &fixed, &before.initial) {
            return Err(fail());
        }
    }
    Ok(())
}

fn substituted(a: &P, b: &P, fixed: &[bool], initial: &[u32]) -> bool {
    match (a, b) {
        (P::Compare { var, op, value }, _) if fixed[*var] => *b == P::Bool(op.test(initial[*var].into(), (*value).into())),
        (P::Bool(_), _) | (P::Compare { .. }, _) => a == b,
        (P::Not(a), P::Not(b)) => substituted(a, b, fixed, initial),
        (P::And(a), P::And(b)) | (P::Or(a), P::Or(b)) => {
            a.len() == b.len() && a.iter().zip(b).all(|(a, b)| substituted(a, b, fixed, initial))
        }
        _ => false,
    }
}

pub(super) fn simplify(before: &Model, after: &Model) -> Result<(), Diagnostic> {
    let fail = || invalid("predicate-simplification");
    if before.variables != after.variables
        || before.initial != after.initial
        || before.actions.len() != after.actions.len()
        || before.properties.len() != after.properties.len()
    {
        return Err(fail());
    }
    for (a, b) in before.actions.iter().zip(&after.actions) {
        if a.span != b.span || a.updates != b.updates || !equivalent(&a.guard, &b.guard, before) {
            return Err(fail());
        }
    }
    for (a, b) in before.properties.iter().zip(&after.properties) {
        if a.name != b.name || a.span != b.span || !equivalent(&a.predicate, &b.predicate, before) {
            return Err(fail());
        }
    }
    Ok(())
}

fn equivalent(a: &P, b: &P, model: &Model) -> bool {
    if a == b {
        return true;
    }
    if let P::Bool(value) = b {
        return truth(a, model) == Some(*value);
    }
    match (a, b) {
        (P::Not(a), P::Not(b)) => equivalent(a, b, model),
        (P::And(children), _) | (P::Or(children), _) => {
            let and = matches!(a, P::And(_));
            let live: Vec<_> = children.iter().filter(|p| truth(p, model) != Some(and)).collect();
            // A singleton conjunction/disjunction can disappear completely,
            // even when its child is itself the same connective.
            if live.len() == 1 && equivalent(live[0], b, model) {
                return true;
            }
            let target = match b {
                P::And(ps) if and => ps,
                P::Or(ps) if !and => ps,
                _ => return false,
            };
            live.len() == target.len() && live.iter().zip(target).all(|(a, b)| equivalent(a, b, model))
        }
        _ => false,
    }
}

fn truth(p: &P, model: &Model) -> Option<bool> {
    match p {
        P::Bool(b) => Some(*b),
        P::Compare { var, op, value } => {
            let (lo, hi) = match model.variables[*var].domain {
                Domain::Natural => (0, u64::MAX),
                Domain::Constant(n) => (u64::from(n), u64::from(n)),
                Domain::Interval(n) => (0, u64::from(n)),
            };
            let boundary = u64::from(*value);
            let expected = op.test(lo, boundary);
            // A scalar comparison changes truth only at value and value+1.
            // These partition representatives cover every natural in the
            // domain, including the unbounded tail; this is not sampling.
            [boundary, boundary + 1]
                .into_iter()
                .filter(|&n| lo <= n && n <= hi)
                .all(|n| op.test(n, boundary) == expected)
                .then_some(expected)
        }
        P::Not(p) => truth(p, model).map(|b| !b),
        P::And(ps) | P::Or(ps) => {
            let identity = matches!(p, P::And(_));
            let mut unknown = false;
            for p in ps {
                match truth(p, model) {
                    Some(b) if b != identity => return Some(b),
                    None => unknown = true,
                    _ => {}
                }
            }
            (!unknown).then_some(identity)
        }
    }
}

pub(super) fn dead(before: &Model, after: &Model, retained: &[usize]) -> Result<(), Diagnostic> {
    let fail = || invalid("dead-action-elimination");
    if before.variables != after.variables
        || before.initial != after.initial
        || before.properties != after.properties
        || retained.len() != after.actions.len()
        || retained.windows(2).any(|w| w[0] >= w[1])
    {
        return Err(fail());
    }
    let mut next = 0;
    for (i, action) in before.actions.iter().enumerate() {
        if retained.get(next) == Some(&i) {
            if action != &after.actions[next] {
                return Err(fail());
            }
            next += 1;
        } else if action.guard != P::Bool(false) {
            return Err(fail());
        }
    }
    if next != retained.len() {
        return Err(fail());
    }
    Ok(())
}
