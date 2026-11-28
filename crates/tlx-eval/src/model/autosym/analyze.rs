//! The scalarset analysis: an abstract interpretation of the checked parts
//! of a spec over shapes (`shape.rs`). It records
//!
//! - every *breaker*: an operation whose result may depend on which
//!   element of a candidate set a value contains (its value order or its
//!   name), applied to a value that may contain such an element;
//! - every *atom*: a constant value read by the checked parts (a CONSTANT,
//!   a definition the cfg assigns a value, a constant-level 0-ary
//!   definition), with its value, so that only permutations fixing it are
//!   admitted;
//! - every *effect*: a builtin whose result or side effect depends on
//!   which states are explored (output, registers, statistics, IO,
//!   randomness), which rules out any count-changing reduction.
//!
//! Every other operation commutes with a permutation of model values
//! (renaming elements does not change the structure of sets, functions,
//! records and sequences, nor equality or membership), so if no breaker
//! applies to the elements of a set S, and every atom is fixed by a
//! permutation p of S, then each checked expression e satisfies
//! e(p(s)) = p(e(s)) for every state (and pair of states) s: p is an
//! automorphism of the state graph, of its initial states, and of the
//! truth of the invariants, constraints and action properties.
//!
//! The analysis is flow-insensitive for the variables: the shape of a
//! variable is the join of everything assigned to it anywhere (`x' = e`,
//! `x' \in S`, `x' \subseteq S`, and `x = e`, `x \in S`, `x \subseteq S` of
//! the initial predicate), computed
//! as a fixpoint over passes. Operator applications are analyzed per
//! shape of their arguments (memoized; recursion by a fixpoint).

mod builtins;
mod choices;
mod defs;
mod expr;
mod folds;

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::*;
use tlx_value::{Sym, SymAtom, Value};

use super::shape::{Mask, Sh, ALL};
use crate::interp::Interp;
use choices::fold_chooses;

/// An operation that breaks the symmetry of the candidate sets in `mask`.
#[derive(Clone, Debug)]
pub(super) struct Breaker {
    pub mask: Mask,
    pub what: String,
    pub span: Span,
}

/// A builtin whose result or side effect depends on the states explored.
#[derive(Clone, Debug)]
pub(super) struct Effect {
    pub what: String,
    pub span: Span,
}

/// A constant value the checked parts read.
#[derive(Clone, Debug)]
pub(super) struct Atom {
    pub value: Value,
    pub name: String,
    /// The definition computing the value (`None`: the cfg gives it).
    pub at: Option<Span>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum AtomKey {
    Const(ConstId),
    Def(DefId),
    StrLit(Sym),
}

/// An argument of an operator: its shape, and the variable it is (primed
/// or not), since a parameter bound to a variable can be assigned
/// (`Op(v) == v' = 1` applied to `x` assigns `x`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct Arg {
    sh: Sh,
    var: Option<VarId>,
}

impl Arg {
    fn of(sh: Sh) -> Arg {
        Arg { sh, var: None }
    }
}

type Key = (DefId, Vec<Arg>);

/// An operator application being analyzed.
struct Frame {
    key: Key,
    /// The result assumed for recursive applications.
    approx: Sh,
    /// Whether a recursive application used `approx`.
    used: bool,
}

/// Shapes are cut at this depth.
const DEPTH: usize = 6;
/// Nesting of operator applications analyzed.
const MAX_FRAMES: usize = 256;
/// Expressions visited, in all passes, before the analysis gives up.
const MAX_STEPS: usize = 4_000_000;
/// Passes over the spec before the variables are widened to "any value".
const MAX_PASSES: usize = 12;

pub(super) struct Analyzer<'a> {
    ip: &'a Arc<Interp>,
    mask_of: &'a dyn Fn(SymAtom) -> Mask,
    /// Bitmask of all analyzed `Value::Str` scalarset candidates.
    string_mask: Mask,
    /// The shapes of the variables (fixed during a pass).
    pub vars: Vec<Sh>,
    /// The shapes assigned to the variables in this pass.
    next_vars: Vec<Sh>,
    memo: HashMap<Key, Sh>,
    stack: Vec<Frame>,
    /// The lowest frame whose approximation the current application used.
    used_below: usize,
    locals: Vec<(LocalId, Arg)>,
    /// The values `@` stands for in EXCEPT.
    at: Vec<Sh>,
    pub breakers: Vec<Breaker>,
    pub effects: Vec<Effect>,
    pub atoms: Vec<Atom>,
    atom_keys: HashSet<AtomKey>,
    const_defs: HashMap<DefId, (Option<Sh>, Mask)>,
    /// The CHOOSE expressions of recursive folds over sets (`fold_chooses`).
    folds: HashSet<usize>,
    steps: usize,
    /// The analysis gave up (too large): its result is not a proof.
    pub overflow: bool,
}

impl<'a> Analyzer<'a> {
    pub(super) fn new(ip: &'a Arc<Interp>, mask_of: &'a dyn Fn(SymAtom) -> Mask, string_mask: Mask) -> Analyzer<'a> {
        let n = ip.prog.vars.len();
        Analyzer {
            ip,
            mask_of,
            string_mask,
            vars: vec![Sh::default(); n],
            next_vars: vec![Sh::default(); n],
            memo: HashMap::new(),
            stack: Vec::new(),
            used_below: usize::MAX,
            locals: Vec::new(),
            at: Vec::new(),
            breakers: Vec::new(),
            effects: Vec::new(),
            atoms: Vec::new(),
            atom_keys: HashSet::new(),
            const_defs: HashMap::new(),
            folds: fold_chooses(ip),
            steps: 0,
            overflow: false,
        }
    }

    /// Analyze `entries` (the initial predicate, the next-state relation,
    /// the invariants, ...) until the shapes of the variables are stable.
    pub(super) fn run(&mut self, entries: &[Expr]) {
        for pass in 0.. {
            self.memo.clear();
            self.breakers.clear();
            self.effects.clear();
            self.next_vars = self.vars.clone();
            for e in entries {
                self.expr(e);
            }
            if self.overflow {
                return;
            }
            let next: Vec<Sh> = self.next_vars.iter().map(|s| s.limit(DEPTH)).collect();
            if next.iter().zip(&self.vars).all(|(n, v)| n.le(v)) {
                return;
            }
            self.vars = if pass >= MAX_PASSES {
                // Not stable: every variable may hold anything (the top
                // shape, so the next pass is the last).
                vec![Sh::any(ALL); next.len()]
            } else {
                self.vars.iter().zip(&next).map(|(v, n)| v.join(n)).collect()
            };
        }
    }

    fn breaker(&mut self, mask: Mask, what: impl Into<String>, span: Span) {
        if mask != 0 {
            self.breakers.push(Breaker { mask, what: what.into(), span });
        }
    }

    fn effect(&mut self, what: impl Into<String>, span: Span) {
        self.effects.push(Effect { what: what.into(), span });
    }

    fn local(&self, l: LocalId) -> Option<&Arg> {
        self.locals.iter().rev().find(|(id, _)| *id == l).map(|(_, a)| a)
    }

    /// The variable `e` denotes (primed or not), directly or through an
    /// operator parameter.
    fn target(&self, e: &Expr) -> Option<VarId> {
        match &*e.kind {
            ExprKind::Var(v) => Some(*v),
            ExprKind::Builtin { op: B::Prime, args } if args.len() == 1 => self.target(&args[0]),
            ExprKind::Local(l) => self.local(*l).and_then(|a| a.var),
            ExprKind::InstVar { subst, .. } => self.target(subst),
            _ => None,
        }
    }

    fn assign(&mut self, v: VarId, sh: &Sh) {
        let s = &mut self.next_vars[v.idx()];
        *s = s.join(sh);
    }
}
