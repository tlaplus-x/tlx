use crate::{Bits, Fairness, Ltl};

// ---------------------------------------------------------------------------
// Formulas (TLC's LiveExprNode) and their decomposition.

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum F {
    Bool(bool),
    Lit { action: bool, atom: u32, pos: bool },
    And(Vec<F>),
    Or(Vec<F>),
    All(Box<F>),
    Even(Box<F>),
}

const STATE_LEVEL: u8 = 1;
const ACTION_LEVEL: u8 = 2;
const TEMPORAL_LEVEL: u8 = 3;

impl F {
    fn level(&self) -> u8 {
        match self {
            F::Bool(_) => 0,
            F::Lit { action, .. } => {
                if *action {
                    ACTION_LEVEL
                } else {
                    STATE_LEVEL
                }
            }
            F::And(xs) | F::Or(xs) => xs.iter().map(F::level).max().unwrap_or(0),
            F::All(_) | F::Even(_) => TEMPORAL_LEVEL,
        }
    }

    /// A conjunction (`conj`) or disjunction, flattening nested ones (TLC's
    /// `addConj`/`addDisj`).
    pub(super) fn junction(conj: bool, xs: impl IntoIterator<Item = F>) -> F {
        let mut out = Vec::new();
        for x in xs {
            match x {
                F::And(ys) if conj => out.extend(ys),
                F::Or(ys) if !conj => out.extend(ys),
                x => out.push(x),
            }
        }
        if conj {
            F::And(out)
        } else {
            F::Or(out)
        }
    }

    /// Negation normal form of `f` (negated if `neg`): TLC's `pushNeg`.
    fn nnf(f: &Ltl, neg: bool) -> F {
        match f {
            Ltl::True => F::Bool(!neg),
            Ltl::False => F::Bool(neg),
            Ltl::State(a) => F::Lit { action: false, atom: *a, pos: !neg },
            Ltl::Action(a) => F::Lit { action: true, atom: *a, pos: !neg },
            Ltl::Not(g) => F::nnf(g, !neg),
            Ltl::And(gs) => F::junction(!neg, gs.iter().map(|g| F::nnf(g, neg))),
            Ltl::Or(gs) => F::junction(neg, gs.iter().map(|g| F::nnf(g, neg))),
            Ltl::Always(g) => {
                let b = Box::new(F::nnf(g, neg));
                if neg {
                    F::Even(b)
                } else {
                    F::All(b)
                }
            }
            Ltl::Eventually(g) => {
                let b = Box::new(F::nnf(g, neg));
                if neg {
                    F::All(b)
                } else {
                    F::Even(b)
                }
            }
        }
    }

    /// TLC's `simplify`.
    fn simplify(self) -> F {
        match self {
            F::And(xs) | F::Or(xs) if xs.is_empty() => F::Bool(true),
            F::And(xs) => {
                let mut out = Vec::new();
                for x in xs {
                    match x.simplify() {
                        F::Bool(false) => return F::Bool(false),
                        F::Bool(true) => {}
                        y => out.push(y),
                    }
                }
                match out.len() {
                    0 => F::Bool(true),
                    1 => out.pop().unwrap(),
                    _ => F::junction(true, out),
                }
            }
            F::Or(xs) => {
                let mut out = Vec::new();
                for x in xs {
                    match x.simplify() {
                        F::Bool(true) => return F::Bool(true),
                        F::Bool(false) => {}
                        y => out.push(y),
                    }
                }
                match out.len() {
                    0 => F::Bool(false),
                    1 => out.pop().unwrap(),
                    _ => F::junction(false, out),
                }
            }
            F::All(x) => match x.simplify() {
                F::All(y) => F::All(y),
                y => F::All(Box::new(y)),
            },
            F::Even(x) => match x.simplify() {
                F::Even(y) => F::Even(y),
                y => F::Even(Box::new(y)),
            },
            f => f,
        }
    }

    /// Whether this is `[]<>A`.
    fn is_ae(&self) -> bool {
        matches!(self, F::All(x) if matches!(&**x, F::Even(_)))
    }

    /// Take `A` out of `[]<>A`, or return `self` on `Err`.
    fn into_ae_body(self) -> Result<F, F> {
        match self {
            F::All(x) => match *x {
                F::Even(y) => Ok(*y),
                other => Err(F::All(Box::new(other))),
            },
            other => Err(other),
        }
    }

    /// TLC's `toDNF` (which does not look below temporal operators and
    /// merges `[]<>A \/ []<>B` into `[]<>(A \/ B)`). Err when a
    /// conjunction has more disjuncts than TLC's `int` can count
    /// (`LNConj.toDNF`'s `Math.multiplyExact`).
    fn into_dnf(self) -> Result<F, DnfTooLarge> {
        Ok(match self {
            F::And(xs) => {
                let mut nes = Vec::new();
                let mut total = 1usize;
                for x in xs {
                    match x.into_dnf()? {
                        F::Or(ds) => {
                            total = total.checked_mul(ds.len()).filter(|&t| t <= i32::MAX as usize).ok_or(DnfTooLarge)?;
                            nes.push(F::Or(ds));
                        }
                        F::And(cs) => nes.extend(cs),
                        y => nes.push(y),
                    }
                }
                if total == 1 {
                    return Ok(F::And(nes));
                }
                let mut res: Vec<Vec<F>> = vec![Vec::new(); total];
                let add = |c: &mut Vec<F>, e: &F| match e {
                    F::And(ys) => c.extend(ys.iter().cloned()),
                    e => c.push(e.clone()),
                };
                let (mut num, mut rcount) = (1, total);
                for ln in &nes {
                    if let F::Or(ds) = ln {
                        rcount /= ds.len();
                        let mut idx = 0;
                        for _ in 0..num {
                            for e in ds {
                                for _ in 0..rcount {
                                    add(&mut res[idx], e);
                                    idx += 1;
                                }
                            }
                        }
                        num *= ds.len();
                    } else {
                        for c in res.iter_mut() {
                            add(c, ln);
                        }
                    }
                }
                F::Or(res.into_iter().map(F::And).collect())
            }
            F::Or(xs) => {
                let transformed = xs.into_iter().map(F::into_dnf).collect::<Result<Vec<_>, _>>()?;
                F::junction(false, merge_ae_disjuncts(transformed))
            }
            f => f,
        })
    }

    /// TLC's `flattenSingleJunctions`.
    fn flatten_single(self) -> F {
        match self {
            F::And(mut xs) | F::Or(mut xs) if xs.len() == 1 => xs.pop().unwrap().flatten_single(),
            F::And(xs) => F::And(xs.into_iter().map(F::flatten_single).collect()),
            F::Or(xs) => F::Or(xs.into_iter().map(F::flatten_single).collect()),
            F::All(x) => F::All(Box::new(x.flatten_single())),
            F::Even(x) => F::Even(Box::new(x.flatten_single())),
            f => f,
        }
    }

    /// Truth on a step from a state with state-atom bits `s` and
    /// action-atom bits `a` (no temporal operators).
    pub(super) fn eval(&self, s: &Bits, a: &Bits) -> bool {
        match self {
            F::Bool(b) => *b,
            &F::Lit { action, atom, pos } => (if action { a.get(atom) } else { s.get(atom) }) == pos,
            F::And(xs) => xs.iter().all(|x| x.eval(s, a)),
            F::Or(xs) => xs.iter().any(|x| x.eval(s, a)),
            F::All(_) | F::Even(_) => unreachable!("temporal formula in a cycle condition"),
        }
    }
}

/// A possible error model: conditions on a cycle.
#[derive(Debug, Default)]
pub(super) struct Pem {
    /// `[]<>A`, A a state predicate: some state of the cycle satisfies A.
    pub(super) ae_state: Vec<F>,
    /// `[]<>A`, A an action: some step of the cycle satisfies A.
    pub(super) ae_action: Vec<F>,
    /// `<>[]A`: every step of the cycle satisfies A.
    pub(super) ea: Vec<F>,
}

impl Pem {
    /// No condition on cycles: a disjunct of the negated property that a
    /// finite behavior (stuttering at its end) can satisfy.
    pub(super) fn is_empty(&self) -> bool {
        self.ae_state.is_empty() && self.ae_action.is_empty() && self.ea.is_empty()
    }
}

/// TLC's `OrderOfSolution`: a tableau formula (None: no tableau) and the
/// error models checked with it.
#[derive(Debug)]
pub(super) struct Solution {
    pub(super) tf: Option<F>,
    pub(super) pems: Vec<Pem>,
}

/// Whether a simplified top-level conjunct `c` is a cycle condition (`<>[]A`
/// or `[]<>A` with `A` free of temporal operators) rather than a tableau
/// formula (`solutions`).
pub(super) fn is_pem(c: &F) -> bool {
    match c {
        F::Even(x) => matches!(&**x, F::All(y) if y.level() < TEMPORAL_LEVEL),
        F::All(x) => matches!(&**x, F::Even(y) if y.level() <= ACTION_LEVEL),
        _ => false,
    }
}

/// Flatten `Or` children, collect `[]<>A` disjuncts by moving their boxed
/// bodies, and append the merged `[]<>(A_1 \/ ... \/ A_k)` at the end as
/// TLC's `LNDisj.toDNF` does.
fn merge_ae_disjuncts(xs: impl IntoIterator<Item = F>) -> Vec<F> {
    let (mut res, mut ae) = (Vec::new(), Vec::new());
    let mut add = |e: F| match e.into_ae_body() {
        Ok(b) => ae.push(b),
        Err(e) => res.push(e),
    };
    for x in xs {
        match x {
            F::Or(ds) => ds.into_iter().for_each(&mut add),
            y => add(y),
        }
    }
    match ae.len() {
        0 => {}
        1 => res.push(F::All(Box::new(F::Even(Box::new(ae.pop().unwrap()))))),
        _ => res.push(F::All(Box::new(F::Even(Box::new(F::junction(false, ae)))))),
    }
    res
}

/// Merge direct `[]<>A \/ []<>B` siblings inside `F::Or` into `[]<>(A \/ B)`
/// as `into_dnf` does, without distributing `F::And` over `F::Or`.
pub(super) fn merge_ae_or(f: F) -> F {
    match f {
        F::And(xs) => F::junction(true, xs.into_iter().map(merge_ae_or)),
        F::Or(xs) => {
            let mut res = merge_ae_disjuncts(xs.into_iter().map(merge_ae_or));
            match res.len() {
                0 => F::Bool(false),
                1 => res.pop().unwrap(),
                _ => F::junction(false, res),
            }
        }
        f => f,
    }
}

/// Replace every top-level cycle condition (`is_pem`) with `FALSE` and fold
/// the enclosing boolean (`And`/`Or`) junctions without descending into
/// retained temporal leaves (matching TLC's `toDNF`, which does not re-run
/// `simplify` inside merged `[]<>` bodies).
pub(super) fn without_pems(f: F) -> F {
    match f {
        F::And(xs) => {
            let mut out = Vec::new();
            for x in xs {
                match without_pems(x) {
                    F::Bool(false) => return F::Bool(false),
                    F::Bool(true) => {}
                    F::And(ys) => out.extend(ys),
                    y => out.push(y),
                }
            }
            match out.len() {
                0 => F::Bool(true),
                1 => out.pop().unwrap(),
                _ => F::And(out),
            }
        }
        F::Or(xs) => {
            let mut out = Vec::new();
            for x in xs {
                match without_pems(x) {
                    F::Bool(true) => return F::Bool(true),
                    F::Bool(false) => {}
                    F::Or(ys) => out.extend(ys),
                    y => out.push(y),
                }
            }
            match out.len() {
                0 => F::Bool(false),
                1 => out.pop().unwrap(),
                _ => F::Or(out),
            }
        }
        c => {
            let c = c.flatten_single();
            if is_pem(&c) {
                F::Bool(false)
            } else {
                c
            }
        }
    }
}

/// Fold top-level cycle conditions (`is_pem`) into `F::Bool(true)` (standing
/// for an empty tableau contribution) in one bottom-up pass on a simplified,
/// `merge_ae_or`-normalized formula that is neither `Bool(true)` nor
/// `Bool(false)`. Pure-PEM conjunctions and disjunctions collapse to a single
/// `F::Bool(true)`, while mixed disjunctions keep the first `F::Bool(true)` in
/// place so the distinct `Solution::tf`s and their first-occurrence order
/// equal those of `solutions`.
fn fold_tableau_pems(f: F) -> F {
    match f {
        F::And(xs) => {
            let mut out = Vec::new();
            for x in xs {
                match fold_tableau_pems(x) {
                    F::Bool(true) => {}
                    F::And(ys) => out.extend(ys),
                    y => out.push(y),
                }
            }
            match out.len() {
                0 => F::Bool(true),
                1 => out.pop().unwrap(),
                _ => F::And(out),
            }
        }
        F::Or(xs) => {
            let mut out = Vec::new();
            let mut seen_empty = false;
            let mut push = |y: F| {
                if y == F::Bool(true) {
                    if seen_empty {
                        return;
                    }
                    seen_empty = true;
                }
                out.push(y);
            };
            for x in xs {
                match fold_tableau_pems(x) {
                    F::Or(ys) => ys.into_iter().for_each(&mut push),
                    y => push(y),
                }
            }
            match out.len() {
                0 => F::Bool(false),
                1 => out.pop().unwrap(),
                _ => F::Or(out),
            }
        }
        c => {
            let c = c.flatten_single();
            if is_pem(&c) {
                F::Bool(true)
            } else {
                c
            }
        }
    }
}

fn classify_f(f: &F) -> crate::normal::Node<'_, F> {
    match f {
        F::And(xs) => crate::normal::Node::And(xs),
        F::Or(xs) => crate::normal::Node::Or(xs),
        _ => crate::normal::Node::Leaf,
    }
}

/// Visit each distinct non-empty ordered conjunct row of a prepared (PEM-folded
/// or PEM-pruned) formula `h` once in TLC's first-occurrence order, using a
/// hash set over borrowed leaf keys. Returning `false` from `visit` stops early.
fn visit_unique_tableau_rows<'a>(h: &'a F, mut visit: impl FnMut(&[&'a F]) -> bool) {
    let mut seen: std::collections::HashSet<Vec<&'a F>> = std::collections::HashSet::new();
    crate::normal::each_cartesian_row(h, classify_f, &mut |row| {
        let key: Vec<&'a F> = row.iter().copied().filter(|c| !matches!(c, F::Bool(true))).collect();
        if key.is_empty() || seen.contains(&key) {
            return true;
        }
        let more = visit(&key);
        seen.insert(key);
        more
    });
}

/// Assemble a prepared non-empty row of leaf conjuncts into a single `F`.
fn row_to_formula<'a>(row: &[&'a F]) -> std::borrow::Cow<'a, F> {
    if row.len() == 1 {
        std::borrow::Cow::Borrowed(row[0])
    } else {
        std::borrow::Cow::Owned(F::And(row.iter().map(|&f| f.clone()).collect()))
    }
}

/// Prepare `prop` under `fairness` for first-occurrence tableau row traversal.
/// Returns `None` when no tableau formulas exist (`Bool(false)` or pure PEMs).
fn prepare_tableau_rows(prop: &Ltl, fairness: &[Fairness]) -> Option<F> {
    let g = F::nnf(prop, true).simplify();
    if g == F::Bool(false) {
        return None;
    }
    if g == F::Bool(true) {
        return fairness.is_empty().then_some(F::Bool(true));
    }
    let h = fold_tableau_pems(merge_ae_or(g));
    (h != F::Bool(true)).then_some(h)
}

/// The state atoms of the tableau formulas TLC builds for `prop` under
/// `fairness`: TLC evaluates them on the successors of each state it
/// expands (tableau node consistency, `LiveCheck.addNextState`) and on the
/// initial states; the other atoms only on the state expanded and its steps.
pub fn tableau_state_atoms(prop: &Ltl, fairness: &[Fairness]) -> Vec<u32> {
    fn collect_atoms(f: &F, seen: &mut std::collections::HashSet<u32>, out: &mut Vec<u32>) {
        match f {
            F::Bool(_) => {}
            F::Lit { action, atom, .. } => {
                if !*action && seen.insert(*atom) {
                    out.push(*atom);
                }
            }
            F::And(xs) | F::Or(xs) => xs.iter().for_each(|x| collect_atoms(x, seen, out)),
            F::All(x) | F::Even(x) => collect_atoms(x, seen, out),
        }
    }
    let Some(h) = prepare_tableau_rows(prop, fairness) else {
        return Vec::new();
    };
    if h == F::Bool(true) {
        return Vec::new();
    }
    let mut seen = std::collections::HashSet::new();
    let mut out = Vec::new();
    visit_unique_tableau_rows(&h, |row| {
        for f in row {
            collect_atoms(f, &mut seen, &mut out);
        }
        true
    });
    out
}

/// State literals checked, in order, for each initial tableau node.
/// TLC's TBGraphNode.isConsistent short-circuits each node at its first
/// false literal; flattening these lists evaluates predicates TLC skips.
pub fn tableau_initial_checks(prop: &Ltl, fairness: &[Fairness]) -> Vec<Vec<(u32, bool)>> {
    let Some(h) = prepare_tableau_rows(prop, fairness) else {
        return Vec::new();
    };
    if h == F::Bool(true) {
        return super::tableau::initial_checks(&F::Bool(true));
    }
    let mut checks = Vec::new();
    visit_unique_tableau_rows(&h, |row| {
        let tf = row_to_formula(row);
        checks.extend(super::tableau::initial_checks(&tf));
        true
    });
    checks
}

/// A temporal formula whose disjunctive normal form is too large for TLC.
#[derive(Debug)]
pub(super) struct DnfTooLarge;

/// Negation of `prop` conjoined with `fairness`, simplified before DNF.
fn negated_simplified(prop: &Ltl, fairness: &[Fairness]) -> F {
    let ev = |f: F| F::Even(Box::new(f));
    let al = |f: F| F::All(Box::new(f));
    let mut conj: Vec<F> = fairness
        .iter()
        .map(|f| {
            let disabled = F::Lit { action: false, atom: f.enabled, pos: false };
            let taken = al(ev(F::Lit { action: true, atom: f.taken, pos: true }));
            F::Or(vec![if f.strong { ev(al(disabled)) } else { al(ev(disabled)) }, taken])
        })
        .collect();
    conj.push(F::nnf(prop, true));
    F::junction(true, conj).simplify()
}

/// The disjunctive normal form of the negation of `prop` under `fairness`
/// (see `solutions`).
fn negated_dnf(prop: &Ltl, fairness: &[Fairness]) -> Result<F, DnfTooLarge> {
    negated_simplified(prop, fairness).into_dnf()
}

/// Shape of `f.into_dnf()` without allocating the expanded disjunct vectors.
enum DnfShape {
    /// `into_dnf` returns `F::Or(ds)` with `non_ae` non-`[]<>` elements and
    /// `usize::from(has_ae)` merged `[]<>` element.
    Or { non_ae: usize, has_ae: bool },
    /// `into_dnf` returns a non-`F::Or` node (`is_ae`: `ae_body().is_some()`).
    Single { is_ae: bool },
}

fn check_dnf_size(f: &F) -> Result<DnfShape, DnfTooLarge> {
    Ok(match f {
        F::And(xs) => {
            let mut total = 1usize;
            for x in xs {
                if let DnfShape::Or { non_ae, has_ae } = check_dnf_size(x)? {
                    let len = non_ae.checked_add(usize::from(has_ae)).ok_or(DnfTooLarge)?;
                    total = total.checked_mul(len).filter(|&t| t <= i32::MAX as usize).ok_or(DnfTooLarge)?;
                }
            }
            if total == 1 {
                DnfShape::Single { is_ae: false }
            } else {
                DnfShape::Or { non_ae: total, has_ae: false }
            }
        }
        F::Or(xs) => {
            let (mut non_ae, mut has_ae) = (0usize, false);
            for x in xs {
                match check_dnf_size(x)? {
                    DnfShape::Or { non_ae: n, has_ae: a } => {
                        non_ae = non_ae.checked_add(n).ok_or(DnfTooLarge)?;
                        has_ae |= a;
                    }
                    DnfShape::Single { is_ae } => {
                        if is_ae {
                            has_ae = true;
                        } else {
                            non_ae = non_ae.checked_add(1).ok_or(DnfTooLarge)?;
                        }
                    }
                }
            }
            DnfShape::Or { non_ae, has_ae }
        }
        _ => DnfShape::Single { is_ae: f.is_ae() },
    })
}

/// TLC's error for a property whose negation under `fairness` has a
/// disjunctive normal form TLC cannot represent (EC.TLC_LIVE_CANNOT_HANDLE_FORMULA
/// from `LNConj.toDNF`), checked before anything else uses the property.
pub fn check_size(prop: &Ltl, fairness: &[Fairness]) -> Result<(), String> {
    check_dnf_size(&negated_simplified(prop, fairness)).map(|_| ()).map_err(|_| {
        "TLC cannot handle the temporal formula because it exceeds the maximum supported size in disjunctive normal form.".to_string()
    })
}

/// Decompose an already-computed DNF formula into `OrderOfSolution`s.
pub(super) fn solutions_of_dnf(dnf: F) -> Vec<Solution> {
    if dnf == F::Bool(false) {
        return Vec::new();
    }
    let disjuncts = match dnf {
        F::Or(ds) => ds,
        d => vec![d],
    };
    let mut sols: Vec<Solution> = Vec::new();
    for d in disjuncts {
        let mut pem = Pem::default();
        let mut tfs = Vec::new();
        let conjuncts = match d.flatten_single() {
            F::And(cs) => cs,
            c => vec![c],
        };
        for c in conjuncts {
            match &c {
                F::Even(x) if matches!(&**x, F::All(y) if y.level() < TEMPORAL_LEVEL) => {
                    let F::All(y) = &**x else { unreachable!() };
                    pem.ea.push((**y).clone());
                    continue;
                }
                F::All(x) => {
                    if let F::Even(y) = &**x {
                        match y.level() {
                            l if l <= STATE_LEVEL => {
                                pem.ae_state.push((**y).clone());
                                continue;
                            }
                            ACTION_LEVEL => {
                                pem.ae_action.push((**y).clone());
                                continue;
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
            tfs.push(c);
        }
        let tf = match tfs.len() {
            0 => None,
            1 => tfs.pop(),
            _ => Some(F::junction(true, tfs)),
        };
        match sols.iter_mut().find(|s| s.tf == tf) {
            Some(s) => s.pems.push(pem),
            None => sols.push(Solution { tf, pems: vec![pem] }),
        }
    }
    sols
}

/// The decomposition of the negation of `prop` under `fairness`
/// (`Liveness.processLiveness`). As TLC, fairness is part of the formula:
/// `WF_v(A)` is `[]<>~ENABLED <<A>>_v \/ []<><<A>>_v` (merged into one
/// `[]<>` condition on steps, `ENABLED` evaluated on their first state),
/// `SF_v(A)` is `<>[]~ENABLED <<A>>_v \/ []<><<A>>_v`.
pub(super) fn solutions(prop: &Ltl, fairness: &[Fairness]) -> Vec<Solution> {
    let dnf = negated_dnf(prop, fairness).expect("the size of the formula is checked by check_size");
    solutions_of_dnf(dnf)
}

pub(super) fn has_pem_free_accepting_sink(prop: &Ltl) -> bool {
    let g = F::nnf(prop, true).simplify();
    if let F::Bool(b) = g {
        return b;
    }
    let h = without_pems(merge_ae_or(g));
    if let F::Bool(b) = h {
        return b;
    }
    let mut found = false;
    visit_unique_tableau_rows(&h, |row| {
        let tf = row_to_formula(row);
        if super::tableau::particle_tableau(&tf).1.iter().any(|&b| b) {
            found = true;
            return false;
        }
        true
    });
    found
}
