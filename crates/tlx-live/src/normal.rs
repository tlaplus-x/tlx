//! Normal forms of temporal formulas and what TLC derives from them before
//! its search: the number of its "branches" and whether a property takes
//! cycle conditions (`tlc2.tool.liveness.Liveness`, `OrderOfSolution`).
//!
//! The top-level DNF is a traversal, not a value: [`each_disjunct`] emits one
//! disjunct (its conjuncts) at a time and reuses one accumulator, so neither
//! metadata consumer below materializes the exponential Cartesian
//! intermediate the negation produces. The number of disjuncts itself still
//! grows exponentially in the top-level conjunctions - TLC counts the same
//! disjuncts - but the traversal holds at most one disjunct's conjuncts, and
//! it stops at the first witness when the caller asks for one.

use crate::Ltl;

/// Whether checking `prop` takes cycle conditions, which is when TLC warns
/// that a stuttering counterexample may be caused by missing fairness
/// (`OrderOfSolution.hasEmptyPEMAndBoxFreePromises` is false): some
/// disjunct of the negated property has a conjunct `[]<>P` or `<>[]P` (P
/// without temporal operators), or a `<>` whose body has a `[]`.
pub fn needs_cycle_conditions(prop: &Ltl) -> bool {
    let neg = nnf(prop, true);
    let mut found = false;
    each_cartesian_row(&neg, classify_ltl, &mut |c| {
        found = c.iter().any(|x| pem(x) || box_in_promise(x));
        !found
    });
    found
}

/// Whether TLC finds the temporal properties `props` (each under the
/// non-fairness temporal conjuncts of the spec) to be a tautology: the
/// negation of their conjunction folds to FALSE when constants are folded
/// through conjunction, disjunction and negation only
/// (`Liveness.processLiveness`: `pushNeg(false).simplify().toDNF()`, which
/// does not look through `[]` and `<>`; e.g. `<>[]TRUE => TRUE`, but not
/// `<>TRUE`). TLC then reports EC.TLC_LIVE_FORMULA_TAUTOLOGY instead of
/// checking the model.
pub fn is_tautology<'a>(props: impl IntoIterator<Item = &'a Ltl>) -> bool {
    fn fold(f: &Ltl) -> Option<bool> {
        match f {
            Ltl::True => Some(true),
            Ltl::False => Some(false),
            Ltl::Not(x) => fold(x).map(|b| !b),
            // (LNConj.simplify / LNDisj.simplify.)
            Ltl::And(xs) | Ltl::Or(xs) => {
                let unit = matches!(f, Ltl::And(_));
                let mut all = true;
                for x in xs {
                    match fold(x) {
                        Some(b) if b != unit => return Some(b),
                        Some(_) => {}
                        None => all = false,
                    }
                }
                all.then_some(unit)
            }
            _ => None,
        }
    }
    let mut any = false;
    for p in props {
        any = true;
        if fold(p) != Some(true) {
            return false;
        }
    }
    any
}

/// The number of TLC's "branches" of the temporal properties `props`
/// (`Liveness.processLiveness`: its `OrderOfSolution`s): the disjuncts of
/// the DNF of their negation, grouped by the conjunction of their conjuncts
/// other than `[]<>P` and `<>[]P` (the formula that takes a tableau). The
/// fairness conjuncts never take one, so they do not matter. (TLC also
/// folds constant-level predicates to TRUE / FALSE first; here they are
/// atoms, so e.g. `C => <>[]P` counts one branch too many.)
pub fn branches<'a>(props: impl IntoIterator<Item = &'a Ltl>) -> usize {
    let neg = collapse_pem_only(Ltl::Or(props.into_iter().map(|p| nnf(p, true)).collect()));
    // The tableau key is the ordered conjuncts that take one; comparing the
    // conjuncts themselves keeps identity structural and preserves both the
    // order and the multiplicity TLC distinguishes (CODE-13).
    let mut tableaux: std::collections::HashSet<Vec<&Ltl>> = std::collections::HashSet::new();
    each_cartesian_row(&neg, classify_ltl, &mut |c| {
        if c.iter().any(|x| matches!(x, Ltl::False)) {
            return true;
        }
        let key: Vec<&Ltl> = c.iter().copied().filter(|x| !pem(x) && !matches!(x, Ltl::True)).collect();
        tableaux.insert(key);
        true
    });
    tableaux.len().max(1)
}

/// Fold pure-PEM boolean subtrees bottom-up in one linear pass: PEM leaves
/// (`[]<>P` / `<>[]P`) become `TRUE` (an empty tableau contribution), and a
/// junction whose transformed children are all `TRUE` / `FALSE` folds to a
/// single constant (`TRUE` if satisfiable, `FALSE` otherwise), while mixed
/// junctions preserve their exact structure and child order (including
/// `TRUE \/ ordinary_atom`, which represents two distinct tableau keys).
fn collapse_pem_only(f: Ltl) -> Ltl {
    match f {
        c if pem(&c) => Ltl::True,
        Ltl::And(xs) => {
            let ys: Vec<Ltl> = xs.into_iter().map(collapse_pem_only).collect();
            if ys.iter().all(|y| matches!(y, Ltl::True | Ltl::False)) {
                if ys.iter().all(|y| matches!(y, Ltl::True)) {
                    Ltl::True
                } else {
                    Ltl::False
                }
            } else {
                Ltl::And(ys)
            }
        }
        Ltl::Or(xs) => {
            let ys: Vec<Ltl> = xs.into_iter().map(collapse_pem_only).collect();
            if ys.iter().all(|y| matches!(y, Ltl::True | Ltl::False)) {
                if ys.iter().any(|y| matches!(y, Ltl::True)) {
                    Ltl::True
                } else {
                    Ltl::False
                }
            } else {
                Ltl::Or(ys)
            }
        }
        other => other,
    }
}

/// Negation normal form of `f`, negated if `neg`.
fn nnf(f: &Ltl, neg: bool) -> Ltl {
    match (f, neg) {
        (Ltl::Not(x), _) => nnf(x, !neg),
        (Ltl::True, true) => Ltl::False,
        (Ltl::False, true) => Ltl::True,
        (Ltl::State(_) | Ltl::Action(_), true) => Ltl::Not(Box::new(f.clone())),
        (Ltl::And(xs), true) => Ltl::Or(xs.iter().map(|x| nnf(x, true)).collect()),
        (Ltl::Or(xs), true) => Ltl::And(xs.iter().map(|x| nnf(x, true)).collect()),
        (Ltl::And(xs), false) => Ltl::And(xs.iter().map(|x| nnf(x, false)).collect()),
        (Ltl::Or(xs), false) => Ltl::Or(xs.iter().map(|x| nnf(x, false)).collect()),
        (Ltl::Always(x), _) => {
            let x = Box::new(nnf(x, neg));
            if neg {
                Ltl::Eventually(x)
            } else {
                Ltl::Always(x)
            }
        }
        (Ltl::Eventually(x), _) => {
            let x = Box::new(nnf(x, neg));
            if neg {
                Ltl::Always(x)
            } else {
                Ltl::Eventually(x)
            }
        }
        _ => f.clone(),
    }
}

fn temporal(f: &Ltl) -> bool {
    match f {
        Ltl::Always(_) | Ltl::Eventually(_) => true,
        Ltl::Not(x) => temporal(x),
        Ltl::And(xs) | Ltl::Or(xs) => xs.iter().any(temporal),
        _ => false,
    }
}

/// Formula node classification for [`each_cartesian_row`].
pub(crate) enum Node<'a, T> {
    And(&'a [T]),
    Or(&'a [T]),
    Leaf,
}

fn classify_ltl(f: &Ltl) -> Node<'_, Ltl> {
    match f {
        Ltl::And(xs) => Node::And(xs),
        Ltl::Or(xs) => Node::Or(xs),
        _ => Node::Leaf,
    }
}

/// Iteratively enumerate the top-level Cartesian DNF rows of `f` in TLC's
/// `LNConj.toDNF` order (first `Or` varies slowest, last `Or` varies fastest;
/// conjuncts within a row appear in `And` order), using an explicit heap work
/// stack so wide flat conjunctions take `O(1)` call-stack depth. `visit`
/// returning `false` stops early and returns `false`; otherwise returns `true`.
pub(crate) fn each_cartesian_row<'a, T>(
    f: &'a T,
    classify: impl Fn(&'a T) -> Node<'a, T>,
    visit: &mut dyn FnMut(&[&'a T]) -> bool,
) -> bool {
    struct Choice<'a, T> {
        rest: &'a [T],
        conj_len: usize,
        todo: Vec<&'a [T]>,
    }
    let mut conj: Vec<&'a T> = Vec::new();
    let mut todo: Vec<&'a [T]> = vec![std::slice::from_ref(f)];
    let mut choices: Vec<Choice<'a, T>> = Vec::new();
    loop {
        while let Some(top) = todo.last_mut() {
            let head = &top[0];
            *top = &top[1..];
            if top.is_empty() {
                todo.pop();
            }
            match classify(head) {
                Node::And(xs) => {
                    if !xs.is_empty() {
                        todo.push(xs);
                    }
                }
                Node::Or(xs) => {
                    if xs.is_empty() {
                        todo.clear();
                        if let Some(mut ch) = choices.pop() {
                            conj.truncate(ch.conj_len);
                            todo = ch.todo;
                            let next = &ch.rest[0];
                            if ch.rest.len() > 1 {
                                ch.rest = &ch.rest[1..];
                                choices.push(Choice { rest: ch.rest, conj_len: ch.conj_len, todo: todo.clone() });
                            }
                            todo.push(std::slice::from_ref(next));
                        } else {
                            return true;
                        }
                        continue;
                    }
                    if xs.len() > 1 {
                        choices.push(Choice { rest: &xs[1..], conj_len: conj.len(), todo: todo.clone() });
                    }
                    todo.push(std::slice::from_ref(&xs[0]));
                }
                Node::Leaf => conj.push(head),
            }
        }
        if !visit(conj.as_slice()) {
            return false;
        }
        let Some(mut ch) = choices.pop() else {
            return true;
        };
        conj.truncate(ch.conj_len);
        todo = ch.todo;
        let next = &ch.rest[0];
        if ch.rest.len() > 1 {
            ch.rest = &ch.rest[1..];
            choices.push(Choice { rest: ch.rest, conj_len: ch.conj_len, todo: todo.clone() });
        }
        todo.push(std::slice::from_ref(next));
    }
}

/// Whether `f` has a `[]` at its top level or under `<>`, `!`, `/\` or `\/`.
fn has_always(f: &Ltl) -> bool {
    match f {
        Ltl::Always(_) => true,
        Ltl::Eventually(x) | Ltl::Not(x) => has_always(x),
        Ltl::And(xs) | Ltl::Or(xs) => xs.iter().any(has_always),
        _ => false,
    }
}

/// A promise (`<>` subformula) whose body has a `[]`.
fn box_in_promise(f: &Ltl) -> bool {
    match f {
        Ltl::Eventually(x) => has_always(x) || box_in_promise(x),
        Ltl::Always(x) | Ltl::Not(x) => box_in_promise(x),
        Ltl::And(xs) | Ltl::Or(xs) => xs.iter().any(box_in_promise),
        _ => false,
    }
}

/// A conjunct `[]<>P` or `<>[]P` (P without temporal operators): checked
/// on the state graph, without a tableau (TLC: a possible error model).
fn pem(c: &Ltl) -> bool {
    match c {
        Ltl::Always(x) => matches!(&**x, Ltl::Eventually(y) if !temporal(y)),
        Ltl::Eventually(x) => matches!(&**x, Ltl::Always(y) if !temporal(y)),
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(i: u32) -> Ltl {
        Ltl::State(i)
    }
    fn always(f: Ltl) -> Ltl {
        Ltl::Always(Box::new(f))
    }
    fn eventually(f: Ltl) -> Ltl {
        Ltl::Eventually(Box::new(f))
    }

    /// The pre-refactor eager DNF, kept here as the differential oracle for
    /// the streaming traversal: the exhaustive tests below compare the two
    /// on every small formula, so the refactor cannot silently change the
    /// disjunct order or multiplicity the metadata consumers see.
    fn dnf_eager(f: &Ltl) -> Vec<Vec<Ltl>> {
        match f {
            Ltl::Or(xs) => xs.iter().flat_map(dnf_eager).collect(),
            Ltl::And(xs) => xs.iter().fold(vec![Vec::new()], |acc, x| {
                let d = dnf_eager(x);
                acc.iter().flat_map(|c| d.iter().map(move |e| c.iter().chain(e).cloned().collect())).collect()
            }),
            _ => vec![vec![f.clone()]],
        }
    }

    fn each_disjunct_collect(f: &Ltl) -> Vec<Vec<Ltl>> {
        let mut rows = Vec::new();
        let mut visit = |c: &[&Ltl]| -> bool {
            rows.push(c.iter().copied().cloned().collect());
            true
        };
        assert!(each_cartesian_row(f, classify_ltl, &mut visit));
        rows
    }

    fn branches_one_eager(f: &Ltl) -> usize {
        let mut tableaux: Vec<Vec<Ltl>> = Vec::new();
        for conj in dnf_eager(&nnf(f, true)) {
            if conj.iter().any(|c| matches!(c, Ltl::False)) {
                continue;
            }
            let key: Vec<Ltl> = conj.iter().filter(|c| !pem(c) && !matches!(c, Ltl::True)).cloned().collect();
            if !tableaux.contains(&key) {
                tableaux.push(key);
            }
        }
        tableaux.len().max(1)
    }

    fn needs_cycle_conditions_eager(f: &Ltl) -> bool {
        dnf_eager(&nnf(f, true)).iter().flatten().any(|c| pem(c) || box_in_promise(c))
    }

    /// Every small formula over two state atoms and one action atom (plus
    /// `TRUE`, `FALSE` and the empty conjunction / disjunction), built from
    /// the constructors up to two combination layers.
    fn small_formulas() -> Vec<Ltl> {
        let base = [Ltl::True, Ltl::False, p(0), p(1), Ltl::Action(0), Ltl::And(Vec::new()), Ltl::Or(Vec::new())];
        let mut out: Vec<Ltl> = base.to_vec();
        let mut layer: Vec<Ltl> = base.to_vec();
        // Miri checks one combination layer (126 formulas) to stay fast; the
        // two-layer 28,805-formula corpus runs natively.
        for _ in 0..if cfg!(miri) { 1 } else { 2 } {
            let mut next = Vec::new();
            for a in &layer {
                next.push(Ltl::Not(Box::new(a.clone())));
                next.push(always(a.clone()));
                next.push(eventually(a.clone()));
            }
            for a in &layer {
                for b in &layer {
                    next.push(Ltl::And(vec![a.clone(), b.clone()]));
                    next.push(Ltl::Or(vec![a.clone(), b.clone()]));
                }
            }
            out.extend(next.iter().cloned());
            layer = next;
        }
        // 7 + 119 = 126 with one layer; 7 + 119 + (119 * 3 + 119 * 119 * 2) =
        // 28_805 natively. Pinned so a change to the corpus shows up in the
        // test instead of shrinking coverage silently (HARNESS-21).
        assert_eq!(out.len(), if cfg!(miri) { 126 } else { 28_805 });
        out
    }

    #[test]
    fn streaming_dnf_matches_eager_dnf_exhaustively() {
        let fs = small_formulas();
        for f in &fs {
            assert_eq!(each_disjunct_collect(f), dnf_eager(f), "disjuncts of {f:?}");
        }
    }

    #[test]
    fn metadata_matches_the_eager_reference_exhaustively() {
        let fs = small_formulas();
        for f in &fs {
            assert_eq!(branches([f]), branches_one_eager(f), "branches of {f:?}");
            assert_eq!(needs_cycle_conditions(f), needs_cycle_conditions_eager(f), "cycle conditions of {f:?}");
        }
    }

    #[test]
    fn streaming_traversal_holds_one_disjunct_and_stops_when_asked() {
        // /\_{i<n} (p2i \/ p2i+1) has 2^n disjuncts of n conjuncts each. The
        // eager DNF built all 2^n rows; the traversal sees the same 2^n
        // disjuncts but never holds more than n conjuncts at once (CODE-15).
        let product = |n: usize| -> Ltl { Ltl::And((0..n).map(|i| Ltl::Or(vec![p(2 * i as u32), p(2 * i as u32 + 1)])).collect()) };
        // Miri's interpreter cannot afford the 2^12..2^16 row products.
        for n in if cfg!(miri) { 6..=8usize } else { 12..=16usize } {
            let f = product(n);
            let (mut visits, mut max_len, mut min_len) = (0usize, 0usize, usize::MAX);
            let mut visit = |c: &[&Ltl]| -> bool {
                visits += 1;
                max_len = max_len.max(c.len());
                min_len = min_len.min(c.len());
                true
            };
            assert!(each_cartesian_row(&f, classify_ltl, &mut visit));
            assert_eq!(visits, 1 << n, "disjuncts of the {n}-way product");
            assert_eq!((min_len, max_len), (n, n), "each disjunct has exactly the {n} conjuncts");

            // A visit that returns false stops immediately, which is what
            // `needs_cycle_conditions` relies on to stop at the first witness.
            let mut early = 0usize;
            let mut visit = |_: &[&Ltl]| -> bool {
                early += 1;
                early < 3
            };
            assert!(!each_cartesian_row(&f, classify_ltl, &mut visit));
            assert_eq!(early, 3);

            // The eager DNF the refactor removed materialized all 2^n rows,
            // n * 2^n conjunct clones; the traversal above kept at most one
            // disjunct's n conjuncts (CODE-15).
            let eager = dnf_eager(&f);
            assert_eq!(eager.len(), 1 << n, "rows the eager DNF materialized");
            assert_eq!(eager.iter().map(Vec::len).sum::<usize>(), n << n, "conjunct clones the eager DNF materialized");
        }
    }

    #[test]
    fn branches_group_disjuncts_by_their_tableau() {
        // ~<>[]P is []<>~P: one disjunct without a tableau.
        assert_eq!(branches([&eventually(always(p(0)))]), 1);
        // ~(<>P \/ <>Q) is []~P /\ []~Q: one disjunct.
        assert_eq!(branches([&Ltl::Or(vec![eventually(p(0)), eventually(p(1))])]), 1);
        // ~(<>P /\ <>Q) is []~P \/ []~Q: two disjuncts, two tableaux.
        assert_eq!(branches([&Ltl::And(vec![eventually(p(0)), eventually(p(1))])]), 2);
        // The same formula twice takes one tableau.
        let f = eventually(p(0));
        assert_eq!(branches([&f, &f]), 1);
        // Two identical disjuncts take one tableau.
        let dup = Ltl::And(vec![Ltl::Or(vec![p(0), p(1)]), Ltl::Or(vec![p(0), p(1)])]);
        assert_eq!(branches([&dup]), 1);
        // Conjunct order and multiplicity are structural: the four rows of
        // /\ (¬p0 \/ ¬p1) x (¬p1 \/ ¬p0) stay distinct.
        let swapped = Ltl::Or(vec![Ltl::And(vec![p(0), p(1)]), Ltl::And(vec![p(1), p(0)])]);
        assert_eq!(branches([&swapped]), 4);
        // Mixed `pem \/ ordinary_atom` keeps both the empty tableau key and
        // the atom's tableau key, matching the eager oracle.
        let mixed = Ltl::Or(vec![Ltl::And(vec![eventually(always(p(0))), p(1)]), eventually(p(2))]);
        assert_eq!(branches([&mixed]), branches_one_eager(&mixed));
        assert_eq!(branches([&mixed]), 2);
        // Deep mixed chain with PEM siblings at every layer and one ordinary
        // atom at the bottom runs in linear time without quadratic re-scans.
        // Miri keeps far more per layer, so it checks a shorter chain of the
        // same shape.
        let mut chain = p(0);
        let depth = if cfg!(miri) { 200u32 } else { 2_000 };
        for i in 0..depth {
            chain = Ltl::Or(vec![eventually(always(p(i % 8))), chain]);
        }
        assert_eq!(branches([&chain]), 1);
        // No properties: the folded conjunction is TRUE, one branch.
        assert_eq!(branches([]), 1);
    }

    #[test]
    fn cycle_conditions() {
        // ~<>P is []~P: no promise, no []<> / <>[] conjunct.
        assert!(!needs_cycle_conditions(&eventually(p(0))));
        // ~[]<>P is <>[]~P.
        assert!(needs_cycle_conditions(&always(eventually(p(0)))));
        // ~[](P => <>Q) has the promise <>(P /\ []~Q), whose body has a [].
        let leads_to = always(Ltl::Or(vec![Ltl::Not(Box::new(p(0))), eventually(p(1))]));
        assert!(needs_cycle_conditions(&leads_to));
        // ~(P /\ []<>Q) is ~P \/ <>[]~Q: the first disjunct has no witness,
        // the second one does, so the traversal must reach it.
        let late = Ltl::And(vec![p(0), always(eventually(p(1)))]);
        assert!(needs_cycle_conditions(&late));
    }
}
