//! The negation of a property as a disjunction of checks, as TLC splits it
//! (its `OrderOfSolution`s with their `[]<>` and `<>[]` conditions): each
//! disjunct is a conjunction of recurrence conditions (`[]<>x`: `x` at some
//! position of the cycle), persistence conditions (`<>[]x`: `x` at every
//! position of the cycle) and a rest, which needs a tableau. The conditions
//! need no tableau states: a conjunction of `k` of them in a tableau has up
//! to 2^k states (e.g. the `<>[][A]_v` assumptions of a specification, one
//! per process). Bodies `x` are propositional and may mix state and action
//! atoms, evaluated at the same position (a state and the step leaving it).
//!
//! Suffix-invariant ("tail") subformulas — `[]<>` and `<>[]` obligations and
//! boolean combinations of them — hold at a position of a behavior iff they
//! hold at position 0, so `<>(P /\ T)` is equivalent to `(<>P) /\ T` and
//! `[](P \/ T)` to `([]P) \/ T`. Hoisting them out of `<>` and `[]` turns
//! nested patterns such as `[]( \E k : S_k => <>[]R_k )` (whose negation is
//! `<>( /\ (S_k /\ []<>~R_k) )`, as in `bcastFolklore`'s `ReliableChan`) into
//! top-level cycle conditions plus a two-state reachability automaton instead
//! of an exponential GPVW tableau. Propositional `[]<>A \/ []<>B` disjuncts
//! merge into `[]<>(A \/ B)` as in TLC's `toDNF`.

use crate::{Bits, Ltl};

#[derive(Clone, Debug)]
pub(crate) struct Condition(Ltl);

impl Condition {
    pub fn holds(&self, state: &Bits, step: &Bits) -> bool {
        fn eval(f: &Ltl, state: &Bits, step: &Bits) -> bool {
            match f {
                Ltl::True => true,
                Ltl::False => false,
                Ltl::State(i) => state.get(*i),
                Ltl::Action(i) => step.get(*i),
                Ltl::Not(x) => !eval(x, state, step),
                Ltl::And(xs) => xs.iter().all(|x| eval(x, state, step)),
                Ltl::Or(xs) => xs.iter().any(|x| eval(x, state, step)),
                Ltl::Always(_) | Ltl::Eventually(_) => unreachable!("propositional condition"),
            }
        }
        eval(&self.0, state, step)
    }
}

/// One disjunct of the negation of a property (see the module doc).
#[derive(Debug, Default)]
pub(crate) struct Disjunct {
    pub recur: Vec<Condition>,
    pub persist: Vec<Condition>,
    /// The other conjuncts, if any: their conjunction (not negated).
    pub rest: Option<Ltl>,
}

/// The most disjuncts the negation of a property is split into; a negation
/// with more (distributing conjunctions over disjunctions) is one disjunct
/// of its top-level conjuncts.
const MAX_DISJUNCTS: usize = 64;

/// The disjuncts of the negation of `prop`, normalized in negation normal
/// form with suffix-invariant tail formulas hoisted to the top level and at
/// most `MAX_DISJUNCTS` disjuncts.
pub(crate) fn split_negation(prop: &Ltl) -> Vec<Disjunct> {
    let neg = norm(prop, true);
    let conjunctions = dnf(&neg).filter(|d| d.len() <= MAX_DISJUNCTS).unwrap_or_else(|| {
        let mut c = Vec::new();
        conjuncts(&neg, &mut c);
        vec![c]
    });
    conjunctions.into_iter().map(|c| disjunct(&c)).collect()
}

fn propositional(f: &Ltl) -> bool {
    match f {
        Ltl::Always(_) | Ltl::Eventually(_) => false,
        Ltl::Not(x) => propositional(x),
        Ltl::And(xs) | Ltl::Or(xs) => xs.iter().all(propositional),
        _ => true,
    }
}

/// Whether `f` is suffix-invariant: its truth at any position of an infinite
/// behavior equals its truth at position 0.
fn is_tail(f: &Ltl) -> bool {
    match f {
        Ltl::True | Ltl::False => true,
        Ltl::Always(x) => matches!(&**x, Ltl::Eventually(_)) || is_tail(x),
        Ltl::Eventually(x) => matches!(&**x, Ltl::Always(_)) || is_tail(x),
        Ltl::Not(x) => is_tail(x),
        Ltl::And(xs) | Ltl::Or(xs) => xs.iter().all(is_tail),
        Ltl::State(_) | Ltl::Action(_) => false,
    }
}

/// Propositional body `x` if `f` is `[]<>x`.
fn ae_prop_body(f: &Ltl) -> Option<&Ltl> {
    match f {
        Ltl::Always(x) => match &**x {
            Ltl::Eventually(y) if propositional(y) => Some(y),
            _ => None,
        },
        _ => None,
    }
}

fn make_and(xs: Vec<Ltl>) -> Ltl {
    let mut flat = Vec::new();
    for x in xs {
        match x {
            Ltl::True => {}
            Ltl::False => return Ltl::False,
            Ltl::And(ys) => flat.extend(ys),
            y => flat.push(y),
        }
    }
    match flat.len() {
        0 => Ltl::True,
        1 => flat.pop().unwrap(),
        _ => Ltl::And(flat),
    }
}

fn make_or(xs: Vec<Ltl>) -> Ltl {
    let (mut flat, mut ae, mut ae_pos) = (Vec::new(), Vec::new(), None);
    let mut add = |x: Ltl| match x {
        Ltl::False => {}
        Ltl::True => flat.push(Ltl::True),
        y => match ae_prop_body(&y) {
            Some(b) => {
                if ae_pos.is_none() {
                    ae_pos = Some(flat.len());
                    flat.push(Ltl::False);
                }
                ae.push(b.clone());
            }
            None => flat.push(y),
        },
    };
    for x in xs {
        match x {
            Ltl::Or(ys) => ys.into_iter().for_each(&mut add),
            y => add(y),
        }
    }
    if flat.iter().any(|x| matches!(x, Ltl::True)) {
        return Ltl::True;
    }
    if let Some(pos) = ae_pos {
        let body = if ae.len() == 1 { ae.pop().unwrap() } else { Ltl::Or(ae) };
        flat[pos] = Ltl::Always(Box::new(Ltl::Eventually(Box::new(body))));
    }
    match flat.len() {
        0 => Ltl::False,
        1 => flat.pop().unwrap(),
        _ => Ltl::Or(flat),
    }
}

fn make_eventually(inner: Ltl) -> Ltl {
    if is_tail(&inner) {
        return inner;
    }
    match inner {
        Ltl::Eventually(y) => Ltl::Eventually(y),
        Ltl::And(xs) if xs.iter().any(is_tail) => {
            let (tails, rest): (Vec<_>, Vec<_>) = xs.into_iter().partition(is_tail);
            let mut out = Vec::with_capacity(tails.len() + 1);
            if !rest.is_empty() {
                out.push(make_eventually(make_and(rest)));
            }
            out.extend(tails);
            make_and(out)
        }
        Ltl::Or(xs) if xs.iter().any(|x| is_tail(x) || matches!(x, Ltl::And(ys) if ys.iter().any(is_tail))) => {
            let (mut hoisted, mut plain) = (Vec::new(), Vec::new());
            for x in xs {
                if is_tail(&x) || matches!(&x, Ltl::And(ys) if ys.iter().any(is_tail)) {
                    hoisted.push(make_eventually(x));
                } else {
                    plain.push(x);
                }
            }
            if !plain.is_empty() {
                hoisted.push(Ltl::Eventually(Box::new(make_or(plain))));
            }
            make_or(hoisted)
        }
        y => Ltl::Eventually(Box::new(y)),
    }
}

fn make_always(inner: Ltl) -> Ltl {
    if is_tail(&inner) {
        return inner;
    }
    match inner {
        Ltl::Always(y) => Ltl::Always(y),
        Ltl::Or(xs) if xs.iter().any(is_tail) => {
            let (tails, rest): (Vec<_>, Vec<_>) = xs.into_iter().partition(is_tail);
            let mut out = Vec::with_capacity(tails.len() + 1);
            if !rest.is_empty() {
                out.push(make_always(make_or(rest)));
            }
            out.extend(tails);
            make_or(out)
        }
        Ltl::And(xs) if xs.iter().any(|x| is_tail(x) || matches!(x, Ltl::Or(ys) if ys.iter().any(is_tail))) => {
            let (mut hoisted, mut plain) = (Vec::new(), Vec::new());
            for x in xs {
                if is_tail(&x) || matches!(&x, Ltl::Or(ys) if ys.iter().any(is_tail)) {
                    hoisted.push(make_always(x));
                } else {
                    plain.push(x);
                }
            }
            if !plain.is_empty() {
                hoisted.push(Ltl::Always(Box::new(make_and(plain))));
            }
            make_and(hoisted)
        }
        y => Ltl::Always(Box::new(y)),
    }
}

/// Negation normal form of `f` (negated if `neg`), hoisting suffix-invariant
/// subformulas out of `[]` and `<>` and merging propositional `[]<>`
/// disjunctions.
fn norm(f: &Ltl, neg: bool) -> Ltl {
    match f {
        Ltl::Not(x) => norm(x, !neg),
        Ltl::True | Ltl::False => {
            if matches!(f, Ltl::True) != neg {
                Ltl::True
            } else {
                Ltl::False
            }
        }
        Ltl::State(_) | Ltl::Action(_) => {
            if neg {
                Ltl::Not(Box::new(f.clone()))
            } else {
                f.clone()
            }
        }
        Ltl::And(xs) | Ltl::Or(xs) => {
            let conj = matches!(f, Ltl::And(_)) != neg;
            let ys: Vec<Ltl> = xs.iter().map(|x| norm(x, neg)).collect();
            if conj {
                make_and(ys)
            } else {
                make_or(ys)
            }
        }
        Ltl::Always(x) | Ltl::Eventually(x) => {
            let always = matches!(f, Ltl::Always(_)) != neg;
            let y = norm(x, neg);
            if always {
                make_always(y)
            } else {
                make_eventually(y)
            }
        }
    }
}

/// `f` (already in NNF) in disjunctive normal form over its temporal
/// subformulas and atoms, if it has at most `MAX_DISJUNCTS` disjuncts
/// (each a list of conjuncts; no disjunct: FALSE, an empty one: TRUE).
fn dnf(f: &Ltl) -> Option<Vec<Vec<&Ltl>>> {
    match f {
        Ltl::True => Some(vec![Vec::new()]),
        Ltl::False => Some(Vec::new()),
        Ltl::And(xs) => {
            let mut out = vec![Vec::new()];
            for x in xs {
                let d = dnf(x)?;
                if out.len().saturating_mul(d.len()) > MAX_DISJUNCTS {
                    return None;
                }
                out = out.iter().flat_map(|a| d.iter().map(move |b| a.iter().chain(b).copied().collect())).collect();
            }
            Some(out)
        }
        Ltl::Or(xs) => {
            let mut out = Vec::new();
            for x in xs {
                out.extend(dnf(x)?);
                if out.len() > MAX_DISJUNCTS {
                    return None;
                }
            }
            Some(out)
        }
        _ => Some(vec![vec![f]]),
    }
}

/// The top-level conjuncts of `f` (in NNF), into `out`.
fn conjuncts<'a>(f: &'a Ltl, out: &mut Vec<&'a Ltl>) {
    match f {
        Ltl::And(xs) => xs.iter().for_each(|x| conjuncts(x, out)),
        Ltl::True => {}
        _ => out.push(f),
    }
}

/// The conditions and the rest of the conjunction `c`.
fn disjunct(c: &[&Ltl]) -> Disjunct {
    let mut d = Disjunct::default();
    let mut rest = Vec::new();
    for &f in c {
        match condition(f) {
            Some((true, cond)) => d.recur.push(cond),
            Some((false, cond)) => d.persist.push(cond),
            None => rest.push(f.clone()),
        }
    }
    d.rest = match rest.len() {
        0 => None,
        1 => rest.pop(),
        _ => Some(Ltl::And(rest)),
    };
    d
}

/// `f` (in NNF) as a recurrence (`(true, x)` for `[]<>x`) or persistence
/// condition (`(false, x)` for `<>[]x`), if `x` is propositional.
fn condition(f: &Ltl) -> Option<(bool, Condition)> {
    match f {
        Ltl::Always(y) => match &**y {
            Ltl::Eventually(x) if propositional(x) => Some((true, Condition((**x).clone()))),
            _ => None,
        },
        Ltl::Eventually(y) => match &**y {
            Ltl::Always(x) if propositional(x) => Some((false, Condition((**x).clone()))),
            _ => None,
        },
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn st(i: u32) -> Ltl {
        Ltl::State(i)
    }
    fn al(f: Ltl) -> Ltl {
        Ltl::Always(Box::new(f))
    }
    fn ev(f: Ltl) -> Ltl {
        Ltl::Eventually(Box::new(f))
    }
    fn not(f: Ltl) -> Ltl {
        Ltl::Not(Box::new(f))
    }

    #[test]
    fn conditions_and_rest() {
        // ¬(<>[]a /\ <>[]b => []<>c) = <>[]a /\ <>[]b /\ <>[]¬c.
        let prop = Ltl::Or(vec![not(Ltl::And(vec![ev(al(st(0))), ev(al(st(1)))])), al(ev(st(2)))]);
        let d = split_negation(&prop);
        assert_eq!(d.len(), 1);
        assert_eq!((d[0].recur.len(), d[0].persist.len()), (0, 3));
        assert!(d[0].rest.is_none());
        let (s, e) = (Bits::from_u64(0b011), Bits::new());
        assert!(d[0].persist[0].holds(&s, &e) && d[0].persist[1].holds(&s, &e) && d[0].persist[2].holds(&s, &e));
        // ¬([]<>a \/ (b ~> c)) = <>[]¬a /\ <>(b /\ []¬c): a persistence and
        // a rest; ¬(<>[]a /\ <>b) = []<>¬a \/ []¬b: two disjuncts.
        let leads = al(Ltl::Or(vec![not(st(1)), ev(st(2))]));
        let prop = Ltl::Or(vec![al(ev(st(0))), leads]);
        let d = split_negation(&prop);
        assert_eq!(d.len(), 1);
        assert_eq!((d[0].recur.len(), d[0].persist.len()), (0, 1));
        assert!(d[0].rest.is_some());
        let prop = Ltl::And(vec![ev(al(st(0))), ev(st(1))]);
        let d = split_negation(&prop);
        assert_eq!(d.len(), 2);
        assert_eq!((d[0].recur.len(), d[0].persist.len(), d[0].rest.is_none()), (1, 0, true));
        assert_eq!((d[1].recur.len(), d[1].persist.len(), d[1].rest.is_some()), (0, 0, true));
        // ¬TRUE: no disjunct; ¬FALSE: one without conditions or rest.
        assert!(split_negation(&Ltl::True).is_empty());
        let d = split_negation(&Ltl::False);
        assert!(d.len() == 1 && d[0].recur.is_empty() && d[0].persist.is_empty() && d[0].rest.is_none());
    }

    #[test]
    fn too_many_disjuncts_are_not_distributed() {
        // The negation of a disjunction of 7 conjunctions of two is a
        // conjunction of 7 disjunctions of two: 2^7 disjuncts if
        // distributed; one disjunct of 7 conjuncts instead.
        let prop = Ltl::Or((0..7).map(|i| Ltl::And(vec![ev(st(2 * i)), ev(st(2 * i + 1))])).collect());
        let d = split_negation(&prop);
        assert_eq!(d.len(), 1);
        assert!(d[0].rest.is_some());
    }

    #[test]
    fn tail_conditions_hoist_out_of_eventually_and_merge_in_or() {
        // `[]( \E k \in 0..7 : s_k => <>[]r_k )` (`bcastFolklore` ReliableChan):
        // negation `<>( /\ (s_k /\ []<>~r_k) )` hoists all 8 `[]<>~r_k` to top-level
        // recurrence conditions, leaving only `<>(s_0 /\ ... /\ s_7)` in `rest`.
        let prop = al(Ltl::Or((0..8).map(|k| Ltl::Or(vec![not(st(2 * k)), ev(al(st(2 * k + 1)))])).collect()));
        let d = split_negation(&prop);
        assert_eq!(d.len(), 1);
        assert_eq!((d[0].recur.len(), d[0].persist.len()), (8, 0));
        assert_eq!(d[0].rest, Some(ev(Ltl::And((0..8).map(|k| st(2 * k)).collect()))));

        // `\E k \in 0..11 : (<>[]a_k /\ <>[]b_k)`: negation is a 12-way conjunction
        // of `([]<>~a_k \/ []<>~b_k)`, each merged to `[]<>(~a_k \/ ~b_k)` so it
        // produces 1 disjunct of 12 recurrence conditions and no tableau.
        let prop = Ltl::Or((0..12).map(|k| Ltl::And(vec![ev(al(st(2 * k))), ev(al(st(2 * k + 1)))])).collect());
        let d = split_negation(&prop);
        assert_eq!(d.len(), 1);
        assert_eq!(d[0].recur.len(), 12);
        assert!(d[0].rest.is_none());
    }
}
