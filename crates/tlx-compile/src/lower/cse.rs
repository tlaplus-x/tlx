//! Local common subexpressions.
//!
//! The rank of an encoded element (`RankFlat`, `RankUnion`: a switch over
//! the union arm and a mixed-radix sum) is computed for each set operation
//! on the element: `F(S \cup {x}) \cup {x}` or `x \in T /\ T \cup {x}` rank
//! `x` two or three times. A rank whose operand is read without
//! computation (a temp, a variable, a part of one) that occurs more than
//! once in an expression is computed once, bound to a temp before the
//! smallest subexpression containing all its occurrences. Ranks cannot
//! fail, so computing one earlier (even where an occurrence would not have
//! been evaluated) changes nothing but the time.

use super::*;

impl Lowerer<'_> {
    /// Share the repeated ranks of `e` (typed lowering).
    pub(super) fn share_ranks(&mut self, e: &mut Expr) {
        let mut groups = repeated_ranks(e);
        // Innermost first; binding a node moves the paths below it into
        // the body of the new `Let` (its second child).
        groups.sort_by_key(|(lca, _)| std::cmp::Reverse(lca.len()));
        for k in 0..groups.len() {
            let (lca, occs) = groups[k].clone();
            let t = self.temp(Ty::Int);
            let mut value = None;
            for p in &occs {
                at_path(e, p, &mut |x| value = Some(std::mem::replace(x, temp_ref(Ty::Int, t))));
            }
            let mut value = value;
            at_path(e, &lca, &mut |node| {
                let body = std::mem::replace(node, bool_lit(false));
                *node = Expr::new(body.ty, ExprKind::Let { temp: t, value: value.take().expect("one node"), body });
            });
            let moved = |p: &mut Vec<usize>| {
                if p.starts_with(&lca) {
                    p.insert(lca.len(), 1);
                }
            };
            for (l, ps) in &mut groups[k + 1..] {
                moved(l);
                ps.iter_mut().for_each(moved);
            }
        }
    }
}

/// An occurrence of a rank: its path (child indices in `for_each_child`
/// order), the rank, and the temps bound on the way (at the depth of the
/// binding node).
struct Occ {
    path: Vec<usize>,
    rank: Expr,
    binders: Vec<(usize, Temp)>,
}

/// A rank of an operand that is read without computation or failure.
fn candidate(e: &Expr) -> bool {
    matches!(&*e.kind, ExprKind::RankFlat { x, .. } | ExprKind::RankUnion { x, .. } if plain(x))
}

fn plain(e: &Expr) -> bool {
    match &*e.kind {
        ExprKind::Temp(_) | ExprKind::Var(_) | ExprKind::NextVar(_) | ExprKind::ConstWords(_) => true,
        ExprKind::Slice { base, .. } => plain(base),
        _ => false,
    }
}

/// Structural equality of two `plain` operands.
fn same_plain(a: &Expr, b: &Expr) -> bool {
    a.ty == b.ty
        && match (&*a.kind, &*b.kind) {
            (ExprKind::Temp(x), ExprKind::Temp(y)) => x == y,
            (ExprKind::Var(x), ExprKind::Var(y)) | (ExprKind::NextVar(x), ExprKind::NextVar(y)) => x == y,
            (ExprKind::ConstWords(x), ExprKind::ConstWords(y)) => x == y,
            (ExprKind::Slice { base: x, loc: i }, ExprKind::Slice { base: y, loc: j }) => i == j && same_plain(x, y),
            _ => false,
        }
}

fn same_rank(a: &Expr, b: &Expr) -> bool {
    match (&*a.kind, &*b.kind) {
        (ExprKind::RankFlat { x, radices: r }, ExprKind::RankFlat { x: y, radices: s }) => r == s && same_plain(x, y),
        (ExprKind::RankUnion { x, arms: r }, ExprKind::RankUnion { x: y, arms: s }) => r == s && same_plain(x, y),
        _ => false,
    }
}

/// The temp a `plain` operand (or the rank of one) reads, if any.
fn operand_temp(e: &Expr) -> Option<Temp> {
    match &*e.kind {
        ExprKind::RankFlat { x, .. } | ExprKind::RankUnion { x, .. } => operand_temp(x),
        ExprKind::Temp(t) => Some(*t),
        ExprKind::Slice { base, .. } => operand_temp(base),
        _ => None,
    }
}

/// The ranks occurring more than once that can be shared: the path of the
/// smallest subexpression containing a rank's occurrences, and their
/// paths.
fn repeated_ranks(e: &Expr) -> Vec<(Vec<usize>, Vec<Vec<usize>>)> {
    let mut occs = Vec::new();
    collect(e, &mut Vec::new(), &mut Vec::new(), &mut occs);
    let mut out = Vec::new();
    let mut used = vec![false; occs.len()];
    for i in 0..occs.len() {
        if used[i] {
            continue;
        }
        let group: Vec<usize> = (i..occs.len()).filter(|&j| !used[j] && same_rank(&occs[i].rank, &occs[j].rank)).collect();
        for &j in &group {
            used[j] = true;
        }
        if group.len() < 2 {
            continue;
        }
        let mut lca = occs[group[0]].path.clone();
        for &j in &group[1..] {
            let n = lca.iter().zip(&occs[j].path).take_while(|(a, b)| a == b).count();
            lca.truncate(n);
        }
        // The operand's temp must be the same binding at every occurrence:
        // bound above the common subexpression, not by it or below it.
        if let Some(t) = operand_temp(&occs[i].rank) {
            if group.iter().any(|&j| occs[j].binders.iter().any(|&(d, b)| b == t && d >= lca.len())) {
                continue;
            }
        }
        out.push((lca, group.iter().map(|&j| occs[j].path.clone()).collect()));
    }
    out
}

/// The ranks of `e` that are candidates; not inside `ENABLED` (its next
/// state is its own) or an interpreter fallback.
fn collect(e: &Expr, path: &mut Vec<usize>, binders: &mut Vec<(usize, Temp)>, out: &mut Vec<Occ>) {
    if candidate(e) {
        out.push(Occ { path: path.clone(), rank: e.clone(), binders: binders.clone() });
        return;
    }
    if matches!(&*e.kind, ExprKind::Enabled(_) | ExprKind::Interp { .. }) {
        return;
    }
    let bound = binder(e);
    if let Some(t) = bound {
        binders.push((path.len(), t));
    }
    let mut i = 0;
    e.for_each_child(&mut |c| {
        path.push(i);
        collect(c, path, binders, out);
        path.pop();
        i += 1;
    });
    if bound.is_some() {
        binders.pop();
    }
}

/// The temp `e` binds for (some of) its children.
fn binder(e: &Expr) -> Option<Temp> {
    use ExprKind as K;
    match &*e.kind {
        K::Let { temp, .. } => Some(*temp),
        K::Exists { bind, .. }
        | K::Forall { bind, .. }
        | K::Choose { bind, .. }
        | K::Filter { bind, .. }
        | K::SeqFilter { bind, .. }
        | K::MapSet { bind, .. }
        | K::MapBuild { bind, .. }
        | K::Collect { bind, .. }
        | K::Fold { bind, .. } => Some(*bind),
        _ => None,
    }
}

/// Call `f` on the node of `e` at `path`.
fn at_path(e: &mut Expr, path: &[usize], f: &mut dyn FnMut(&mut Expr)) {
    let Some((&first, rest)) = path.split_first() else { return f(e) };
    let mut i = 0;
    e.for_each_child_mut(&mut |c| {
        if i == first {
            at_path(c, rest, f);
        }
        i += 1;
    });
}
