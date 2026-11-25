//! Level checking, as SANY does it (`OpApplNode.levelCheck` and friends),
//! on the resolved HIR.
//!
//! Levels: 0 constant, 1 state, 2 action, 3 temporal. Every expression gets
//! a level computed with the parameters of the enclosing definitions taken as
//! constants, plus the set of parameters its level depends on. A definition
//! is summarized SANY-style by its level, a weight per parameter (whether
//! the level of an application depends on the argument's level), the
//! maximum level allowed for each argument (from uses like `p'`), and for
//! operator parameters the minimum level their arguments must accept.
//!
//! Instantiated definitions have their substitutions applied in the HIR, so
//! they are checked like any other definition; the substitutions themselves
//! are checked against the declarations they replace (`check_levels`).

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use tlx_front::ast::Span;

use super::{err, Program, SemaError, Sym};
use crate::builtins::Builtin;
use crate::hir::*;

const CONSTANT: u8 = 0;
pub(super) const ACTION: u8 = 2;
pub(super) const TEMPORAL: u8 = 3;

/// The level of an expression and what it depends on.
#[derive(Clone, Default)]
pub(super) struct Info {
    level: u8,
    /// Parameters (locals) the level depends on.
    params: BTreeSet<LocalId>,
    /// Maximum levels allowed for parameters.
    cons: BTreeMap<LocalId, u8>,
    /// For operator parameters `F` and argument positions `j`: the minimum
    /// level that the operator substituted for `F` must accept for argument j.
    arg_cons: BTreeMap<(LocalId, usize), u8>,
    /// `(F, j, p)`: parameter `p` occurs in argument j of an application of
    /// operator parameter `F` (SANY's ArgLevelParams).
    arg_params: BTreeSet<(LocalId, usize, LocalId)>,
    /// Parameters occurring in arguments of non-Leibniz operators (`'`,
    /// ENABLED, ...).
    nonleibniz: BTreeSet<LocalId>,
    /// A level error was found in the expression (SANY then reports no
    /// argument level errors for enclosing operators).
    bad: bool,
}

impl Info {
    pub(super) fn at(level: u8) -> Info {
        Info { level, ..Info::default() }
    }

    /// Merge `o`'s constraints into `self`.
    pub(super) fn constraints(&mut self, o: &Info) {
        self.bad |= o.bad;
        for (&p, &m) in &o.cons {
            constrain(&mut self.cons, p, m);
        }
        for (&k, &m) in &o.arg_cons {
            let e = self.arg_cons.entry(k).or_insert(m);
            *e = (*e).max(m);
        }
        self.arg_params.extend(o.arg_params.iter().copied());
        self.nonleibniz.extend(o.nonleibniz.iter().copied());
    }

    /// Merge `o` as an operand of weight 1.
    fn absorb(&mut self, o: &Info) {
        self.level = self.level.max(o.level);
        self.params.extend(o.params.iter().copied());
        self.constraints(o);
    }
}

fn constrain(cons: &mut BTreeMap<LocalId, u8>, p: LocalId, max: u8) {
    let e = cons.entry(p).or_insert(max);
    *e = (*e).min(max);
}

/// SANY's view of an operator: level, and per argument the maximum level
/// and the weight.
#[derive(Clone)]
pub(super) struct Summary {
    level: u8,
    weights: Vec<bool>,
    max: Vec<u8>,
    /// Per (operator) parameter: per argument, the minimum level the operator
    /// passed for it must accept.
    min_max: Vec<Vec<u8>>,
    /// `(f, j, p)`: the argument at position p is passed to argument j of
    /// the operator argument at position f.
    arg_params: Vec<(usize, usize, usize)>,
    /// `(f, j, p)`: the argument at position p is passed to argument j of
    /// captured (free) operator parameter `f` (e.g. `LET Apply(a) == F(a)`).
    free_arg_params: Vec<(LocalId, usize, usize)>,
    /// `(f, j, p)`: captured (free) parameter `p` is passed to argument j of
    /// the operator argument at position `f` (e.g. `LET Apply(F(_)) == F(s)`).
    bound_arg_free: Vec<(usize, usize, LocalId)>,
    /// Per parameter: whether the operator is non-Leibniz in it.
    nonleibniz: Vec<bool>,
    /// Dependencies on the enclosing definitions' parameters (LET definitions,
    /// LAMBDAs); `free.bad`: the definition has level errors.
    free: Info,
}

impl Summary {
    /// What nothing is known about: accepts anything, propagates everything.
    fn lenient(n: usize) -> Summary {
        Summary {
            level: CONSTANT,
            weights: vec![true; n],
            max: vec![TEMPORAL; n],
            min_max: vec![Vec::new(); n],
            arg_params: Vec::new(),
            free_arg_params: Vec::new(),
            bound_arg_free: Vec::new(),
            nonleibniz: vec![false; n],
            free: Info::default(),
        }
    }

    fn weight(&self, i: usize) -> bool {
        self.weights.get(i).copied().unwrap_or(true)
    }

    fn max(&self, i: usize) -> u8 {
        self.max.get(i).copied().unwrap_or(TEMPORAL)
    }
}

/// SANY's name, level, argument maximum level and weight of a built-in.
fn builtin_spec(b: Builtin) -> (&'static str, u8, u8, bool) {
    use Builtin as B;
    match b {
        B::Eq => ("=", 0, 2, true),
        B::Neq => ("/=", 0, 2, true),
        B::In => ("\\in", 0, 2, true),
        B::NotIn => ("\\notin", 0, 2, true),
        B::Subset => ("SUBSET", 0, 2, true),
        B::Union => ("UNION", 0, 2, true),
        B::Domain => ("DOMAIN", 0, 2, true),
        B::Cup => ("\\union", 0, 2, true),
        B::Cap => ("\\intersect", 0, 2, true),
        B::SetMinus => ("\\", 0, 2, true),
        B::SubsetEq => ("\\subseteq", 0, 2, true),
        B::Times => ("$CartesianProd", 0, 2, true),
        B::Not => ("\\lnot", 0, 3, true),
        B::Implies => ("=>", 0, 3, true),
        B::Equiv => ("\\equiv", 0, 3, true),
        B::Prime => ("'", 2, 1, false),
        B::Unchanged => ("UNCHANGED", 2, 1, false),
        B::Enabled => ("ENABLED", 1, 2, false),
        B::Always => ("[]", 3, 3, false),
        B::Eventually => ("<>", 3, 3, false),
        B::LeadsTo => ("~>", 3, 3, false),
        B::WhilePlus => ("-+->", 3, 3, false),
        B::Compose => ("\\cdot", 2, 2, false),
        // Standard-module operators: their TLA+ definitions (constant level).
        other => (other.name(), 0, 3, true),
    }
}

/// SANY's `arg_params` `(op_pos, op_arg_pos, param_pos)` for operator-taking
/// standard and community module built-ins, matching their TLA+ definitions.
fn builtin_arg_params(b: Builtin) -> Vec<(usize, usize, usize)> {
    use Builtin as B;
    match b {
        B::SelectSeq => vec![(1, 0, 0)],
        B::SortSeq => vec![(1, 0, 0), (1, 1, 0)],
        B::SelectInSubSeq | B::SelectLastInSubSeq => vec![(3, 0, 0), (3, 0, 1), (3, 0, 2)],
        B::FoldFunction | B::FoldFunctionOnSet | B::FoldSeq => vec![(0, 0, 2)],
        B::FoldBag => vec![(0, 0, 1), (0, 0, 2)],
        B::FoldRight | B::FoldRightDomain => vec![(0, 0, 1)],
        B::MapThenFoldSet => vec![(0, 0, 2), (0, 0, 3), (2, 0, 3)],
        _ => Vec::new(),
    }
}

fn builtin_summary(b: Builtin, n: usize) -> Summary {
    let (_, level, max, w) = builtin_spec(b);
    Summary {
        level,
        weights: vec![w; n],
        max: vec![max; n],
        min_max: vec![Vec::new(); n],
        arg_params: builtin_arg_params(b),
        free_arg_params: Vec::new(),
        bound_arg_free: Vec::new(),
        nonleibniz: vec![!w; n],
        free: Info::default(),
    }
}

pub(super) struct Checker<'p> {
    p: &'p Program,
    memo: Vec<Option<Arc<Summary>>>,
    in_progress: Vec<bool>,
    errors: Vec<SemaError>,
    /// Levels of the EXCEPT bases (for `@`).
    at: Vec<Info>,
    /// Definitions being summarized (innermost last).
    stack: Vec<DefId>,
    /// Instance contexts with level errors in their substitutions: errors
    /// in their (substituted) definitions are consequences, not reported.
    muted: Vec<bool>,
}

impl Checker<'_> {
    fn error(&mut self, span: Span, msg: String) {
        if let Some(d) = self.stack.last() {
            if self.muted.get(self.p.def_src[d.idx()].ctx).copied().unwrap_or(false) {
                return;
            }
        }
        self.errors.push(err(span, msg));
    }

    fn arg_error(&mut self, span: Span, op: &str, i: usize) {
        self.error(
            span,
            format!("Level error in applying operator {op}:\nThe level of argument {i} exceeds the maximum level allowed by the operator."),
        );
    }

    pub(super) fn summary(&mut self, d: DefId) -> Arc<Summary> {
        if let Some(s) = &self.memo[d.idx()] {
            return s.clone();
        }
        let def = &self.p.defs[d.idx()];
        if self.in_progress[d.idx()] || def.builtin.is_some() {
            // Recursion: assume nothing (SANY checks recursive definitions
            // with similar leniency).
            return Arc::new(Summary::lenient(def.params.len()));
        }
        self.in_progress[d.idx()] = true;
        self.stack.push(d);
        let mut info = match &def.kind {
            DefKind::Pending => Info::default(),
            DefKind::Op(e) => self.expr(e),
            DefKind::Fn { bounds, body } => self.binder("$RecursiveFcnSpec", bounds, body, TEMPORAL, true, def.span),
        };
        for (se, max) in &self.p.def_subst_bounds[d.idx()] {
            let saved_errors = self.errors.len();
            let si = self.expr(se);
            self.errors.truncate(saved_errors);
            for &p in &si.params {
                constrain(&mut info.cons, p, *max);
            }
        }
        let s = Arc::new(self.summarize(&def.params, info));
        self.stack.pop();
        self.in_progress[d.idx()] = false;
        self.memo[d.idx()] = Some(s.clone());
        s
    }

    /// Summary of an operator with parameters `params` whose body has `info`.
    fn summarize(&self, params: &[LocalId], info: Info) -> Summary {
        let weights = params.iter().map(|p| info.params.contains(p)).collect();
        let max = params.iter().map(|p| info.cons.get(p).copied().unwrap_or(TEMPORAL)).collect();
        let min_max = params
            .iter()
            .map(|p| {
                let arity = self.p.locals[p.idx()].arity;
                (0..arity).map(|j| info.arg_cons.get(&(*p, j)).copied().unwrap_or(CONSTANT)).collect()
            })
            .collect();
        let pos = |l: &LocalId| params.iter().position(|p| p == l);
        let arg_params = info.arg_params.iter().filter_map(|(f, j, p)| Some((pos(f)?, *j, pos(p)?))).collect();
        let free_arg_params =
            info.arg_params.iter().filter_map(|(f, j, p)| if pos(f).is_none() { Some((*f, *j, pos(p)?)) } else { None }).collect();
        let bound_arg_free =
            info.arg_params.iter().filter_map(|(f, j, p)| if pos(p).is_none() { Some((pos(f)?, *j, *p)) } else { None }).collect();
        let nonleibniz = params.iter().map(|p| info.nonleibniz.contains(p)).collect();
        let level = info.level;
        let mut free = info;
        free.level = CONSTANT;
        free.nonleibniz.retain(|p| !params.contains(p));
        for p in params {
            free.params.remove(p);
            free.cons.remove(p);
        }
        free.arg_cons.retain(|(p, _), _| !params.contains(p));
        free.arg_params.retain(|(f, _, p)| !params.contains(f) && !params.contains(p));
        Summary { level, weights, max, min_max, arg_params, free_arg_params, bound_arg_free, nonleibniz, free }
    }

    /// The summary of an operator argument (`OpArg` / `LAMBDA`), if known.
    fn op_summary(&mut self, e: &Expr) -> Option<Arc<Summary>> {
        match &*e.kind {
            ExprKind::OpArg(OpRef::Def(d)) => Some(self.summary(*d)),
            ExprKind::OpArg(OpRef::Builtin(b)) => Some(Arc::new(builtin_summary(*b, b.arity().max(0) as usize))),
            ExprKind::Lambda { params, body } => {
                let info = self.expr(body);
                Some(Arc::new(self.summarize(params, info)))
            }
            _ => None,
        }
    }

    /// Apply an operator with summary `s` (named `name`) to `args`.
    /// Also returns the levels of the arguments.
    fn apply(&mut self, name: &str, s: &Summary, args: &[Expr], span: Span, skip: usize) -> (Info, Vec<u8>) {
        let mut out = s.free.clone();
        out.level = s.level;
        let infos: Vec<Info> = args.iter().map(|a| self.expr(a)).collect();
        let levels: Vec<u8> = infos.iter().map(|i| i.level).collect();
        let argn = |i: usize| if i >= skip { i - skip + 1 } else { i + 1 };
        // Arguments passed on to operator arguments.
        for &(f, j, p) in &s.arg_params {
            let (Some(fa), Some(pi)) = (args.get(f), infos.get(p)) else { continue };
            if let ExprKind::OpArg(OpRef::Param(g)) = &*fa.kind {
                for &q in &pi.params {
                    out.arg_params.insert((*g, j, q));
                }
                let e = out.arg_cons.entry((*g, j)).or_insert(pi.level);
                *e = (*e).max(pi.level);
            } else if let Some(fs) = self.op_summary(fa) {
                let max = fs.max(j);
                if pi.level > max {
                    if !pi.bad {
                        self.arg_error(span, name, argn(p));
                    }
                    out.bad = true;
                }
                for &q in &pi.params {
                    constrain(&mut out.cons, q, max);
                }
            }
        }
        for &(g, j, p) in &s.free_arg_params {
            let Some(pi) = infos.get(p) else { continue };
            for &q in &pi.params {
                out.arg_params.insert((g, j, q));
            }
            let e = out.arg_cons.entry((g, j)).or_insert(pi.level);
            *e = (*e).max(pi.level);
        }
        for &(f, j, p) in &s.bound_arg_free {
            let Some(fa) = args.get(f) else { continue };
            if let ExprKind::OpArg(OpRef::Param(g)) = &*fa.kind {
                out.arg_params.insert((*g, j, p));
            } else if let Some(fs) = self.op_summary(fa) {
                constrain(&mut out.cons, p, fs.max(j));
            }
        }
        for (i, (a, ai)) in args.iter().zip(infos).enumerate() {
            let max = s.max(i);
            if ai.level > max {
                if !s.free.bad && !ai.bad {
                    let n = argn(i);
                    self.arg_error(span, name, n);
                }
                out.bad = true;
            }
            for &p in &ai.params {
                constrain(&mut out.cons, p, max);
            }
            if let Some(need) = s.min_max.get(i).filter(|m| !m.is_empty()) {
                if let ExprKind::OpArg(OpRef::Param(l)) = &*a.kind {
                    for (j, &m) in need.iter().enumerate() {
                        let e = out.arg_cons.entry((*l, j)).or_insert(m);
                        *e = (*e).max(m);
                    }
                } else if let Some(arg) = self.op_summary(a) {
                    for (j, &m) in need.iter().enumerate() {
                        if arg.max(j) < m {
                            out.bad = true;
                            let n = argn(i);
                            self.error(
                                span,
                                format!(
                                    "Level error in applying operator {name}:\nThe permitted level of argument {} of the operator argument {n} \nmust be at least {m}.",
                                    j + 1
                                ),
                            );
                        }
                    }
                }
            }
            if s.nonleibniz.get(i).copied().unwrap_or(false) {
                out.nonleibniz.extend(ai.params.iter().copied());
            }
            if s.weight(i) {
                out.absorb(&ai);
            } else {
                out.constraints(&ai);
            }
        }
        (out, levels)
    }

    /// Apply a built-in, with SANY's additional checks on temporal operators.
    fn builtin(&mut self, b: Builtin, args: &[Expr], span: Span) -> Info {
        let s = builtin_summary(b, args.len());
        let (name, ..) = builtin_spec(b);
        let (mut out, levels) = self.apply(name, &s, args, span, 0);
        match b {
            Builtin::Always | Builtin::Eventually => {
                let (form, ok) = if b == Builtin::Always {
                    ("[] followed by action not of form [A]_v.", true)
                } else {
                    ("<> followed by action not of form <<A>>_v.", false)
                };
                if let Some(a) = args.first() {
                    let exempt = match &*a.kind {
                        ExprKind::BoxAction { .. } => ok,
                        ExprKind::AngleAction { .. } => !ok,
                        ExprKind::Let { .. } => true,
                        _ => false,
                    };
                    if levels[0] == ACTION && !exempt {
                        self.error(span, form.into());
                        out.bad = true;
                    }
                }
            }
            Builtin::LeadsTo | Builtin::WhilePlus => {
                if levels.contains(&ACTION) {
                    self.error(span, "Action used where only temporal formula or state predicate allowed.".into());
                    out.bad = true;
                }
            }
            Builtin::Implies | Builtin::Equiv => out.bad |= self.mixed(name, &levels, span),
            _ => {}
        }
        out
    }

    /// SANY: a Boolean operator cannot combine temporal formulas and actions.
    fn mixed(&mut self, name: &str, levels: &[u8], span: Span) -> bool {
        let bad = levels.contains(&TEMPORAL) && levels.contains(&ACTION);
        if bad {
            self.error(span, format!("{name} has both temporal formula and action as arguments."));
        }
        bad
    }

    /// Operands of a construct with a fixed maximum level and weight 1.
    /// Returns their levels.
    fn operands(&mut self, name: &str, es: &[&Expr], max: u8, span: Span, out: &mut Info) -> Vec<u8> {
        let mut levels = Vec::with_capacity(es.len());
        for (i, e) in es.iter().enumerate() {
            let ei = self.expr(e);
            levels.push(ei.level);
            if ei.level > max {
                if !ei.bad {
                    self.arg_error(span, name, i + 1);
                }
                out.bad = true;
            }
            for &p in &ei.params {
                constrain(&mut out.cons, p, max);
            }
            out.absorb(&ei);
        }
        levels
    }

    /// Bounded binders (`\E x \in S : body`, `[x \in S |-> body]`, ...):
    /// ranges at most action level, the body at most `max`.
    pub(super) fn binder(&mut self, name: &str, bounds: &[Bound], body: &Expr, max: u8, check_body: bool, span: Span) -> Info {
        let mut out = Info::default();
        let mut range_levels = Vec::new();
        for b in bounds {
            let ri = self.expr(&b.set);
            if ri.level > ACTION && !ri.bad {
                out.bad = true;
                let var = b.vars.locals().first().map(|l| self.p.locals[l.idx()].name.clone()).unwrap_or_default();
                self.error(
                    b.set.span,
                    format!("Level error in applying operator {name}:\nThe level of the range for the bounded variable {var} \nexceeds the maximum level allowed by the operator."),
                );
            }
            range_levels.push((ri.level, b.set.span));
            out.absorb(&ri);
        }
        let bi = self.expr(body);
        if check_body && bi.level > max {
            if !bi.bad {
                self.arg_error(span, name, 1);
            }
            out.bad = true;
        }
        for &p in &bi.params {
            constrain(&mut out.cons, p, max);
        }
        out.absorb(&bi);
        if out.level == TEMPORAL && (name == "$BoundedExists" || name == "$BoundedForall") {
            for (l, span) in range_levels {
                if l == ACTION {
                    self.error(span, "Action-level bound of quantified temporal formula.".into());
                    out.bad = true;
                }
            }
        }
        out
    }

    pub(super) fn expr(&mut self, e: &Expr) -> Info {
        let span = e.span;
        match &*e.kind {
            ExprKind::Num(_) | ExprKind::Decimal(_) | ExprKind::Str(_) | ExprKind::Bool(_) | ExprKind::Const(_) => Info::at(CONSTANT),
            ExprKind::Var(_) => Info::at(1),
            ExprKind::InstVar { subst, .. } => {
                let mut i = Info::at(1);
                let s = self.expr(subst);
                i.absorb(&s);
                i
            }
            ExprKind::Local(l) => {
                let mut i = Info::default();
                i.params.insert(*l);
                i
            }
            ExprKind::At => self.at.last().cloned().unwrap_or_default(),
            ExprKind::OpArg(r) => match r {
                OpRef::Def(d) => {
                    let s = self.summary(*d);
                    let mut i = s.free.clone();
                    i.level = s.level;
                    i
                }
                OpRef::Param(l) => {
                    let mut i = Info::default();
                    i.params.insert(*l);
                    i
                }
                OpRef::Const(_) => Info::default(),
                OpRef::Builtin(b) => Info::at(builtin_spec(*b).1),
            },
            ExprKind::Lambda { params, body } => {
                let info = self.expr(body);
                let s = self.summarize(params, info);
                let mut i = s.free;
                i.level = s.level;
                i
            }
            ExprKind::Apply { op, args } => match op {
                OpRef::Param(l) if !args.is_empty() => {
                    let mut out = Info::default();
                    out.params.insert(*l);
                    for (j, a) in args.iter().enumerate() {
                        let ai = self.expr(a);
                        let e = out.arg_cons.entry((*l, j)).or_insert(ai.level);
                        *e = (*e).max(ai.level);
                        for &p in &ai.params {
                            out.arg_params.insert((*l, j, p));
                        }
                        out.absorb(&ai);
                    }
                    out
                }
                OpRef::Def(d) => {
                    let s = self.summary(*d);
                    let name = self.p.defs[d.idx()].name.clone();
                    let skip = self.p.def_inst[d.idx()];
                    self.apply(&name, &s, args, span, skip).0
                }
                OpRef::Builtin(b) => self.builtin(*b, args, span),
                OpRef::Const(_) => self.apply("", &Summary::lenient(args.len()), args, span, 0).0,
                // The `!args.is_empty()` arm above takes every applied
                // parameter, so `args` is empty here: nothing to absorb.
                OpRef::Param(l) => {
                    let mut out = Info::default();
                    out.params.insert(*l);
                    out
                }
            },
            ExprKind::Builtin { op, args } => self.builtin(*op, args, span),
            ExprKind::And(es) | ExprKind::Or(es) => {
                let mut out = Info::default();
                let refs: Vec<&Expr> = es.iter().collect();
                let levels = self.operands("", &refs, TEMPORAL, span, &mut out);
                let is_and = matches!(&*e.kind, ExprKind::And(_));
                // A junction list starts with its bullet; infix `/\` is binary.
                let src = &self.p.files[span.file.0 as usize].src;
                let text = src.get(span.start as usize..).unwrap_or("");
                let list = ["/\\", "\\/", "\\land", "\\lor", "\u{2227}", "\u{2228}"].iter().any(|b| text.starts_with(b));
                let name = match (is_and, list) {
                    (true, false) => "\\land",
                    (false, false) => "\\lor",
                    (true, true) => "Conjunction list",
                    (false, true) => "Disjunction list",
                };
                out.bad |= self.mixed(name, &levels, span);
                out
            }
            ExprKind::Quant { kind, bounds, body } => self.bounded_quant_level(*kind, bounds, body, span),
            ExprKind::QuantUnbounded { body, .. } => self.expr(body),
            ExprKind::TemporalQuant { body, .. } => self.temporal_quant_level(body),
            ExprKind::Choose { vars, set, body } => self.choose_level(vars, set, body, span),
            ExprKind::If { cond, then, els } => {
                let mut out = Info::default();
                self.operands("$IfThenElse", &[cond, then, els], TEMPORAL, span, &mut out);
                out
            }
            ExprKind::Case { arms, other } => {
                let mut out = Info::default();
                let mut es: Vec<&Expr> = arms.iter().flat_map(|(g, v)| [g, v]).collect();
                es.extend(other.iter());
                self.operands("$Case", &es, TEMPORAL, span, &mut out);
                out
            }
            ExprKind::Let { defs, body } => self.let_level(defs, body),
            ExprKind::SetEnum(es) => {
                let mut out = Info::default();
                let refs: Vec<&Expr> = es.iter().collect();
                self.operands("$SetEnumerate", &refs, ACTION, span, &mut out);
                out
            }
            ExprKind::Tuple(es) => {
                let mut out = Info::default();
                let refs: Vec<&Expr> = es.iter().collect();
                self.operands("$Tuple", &refs, ACTION, span, &mut out);
                out
            }
            ExprKind::SetFilter { bound, pred } => self.set_filter_level(bound, pred, span),
            ExprKind::SetMap { expr, bounds } => self.set_map_level(expr, bounds, span),
            ExprKind::FnConstruct { bounds, body } => self.fn_construct_level(bounds, body, span),
            ExprKind::FnApp { func, args } => {
                let mut out = Info::default();
                let mut es: Vec<&Expr> = vec![func];
                es.extend(args.iter());
                self.operands("$FcnApply", &es, ACTION, span, &mut out);
                out
            }
            ExprKind::FnSet { domain, range } => {
                let mut out = Info::default();
                self.operands("$SetOfFcns", &[domain, range], ACTION, span, &mut out);
                out
            }
            ExprKind::Record(fs) => {
                let mut out = Info::default();
                let es: Vec<&Expr> = fs.iter().map(|(_, v)| v).collect();
                self.operands("$RcdConstructor", &es, TEMPORAL, span, &mut out);
                out
            }
            ExprKind::RecordSet(fs) => {
                let mut out = Info::default();
                let es: Vec<&Expr> = fs.iter().map(|(_, v)| v).collect();
                self.operands("$SetOfRcds", &es, ACTION, span, &mut out);
                out
            }
            ExprKind::Field { record, .. } => {
                let mut out = Info::default();
                self.operands("$RcdSelect", &[record], ACTION, span, &mut out);
                out
            }
            ExprKind::Except { base, updates } => {
                let bi = self.expr(base);
                let mut out = Info::default();
                if bi.level > ACTION {
                    if !bi.bad {
                        self.arg_error(span, "$Except", 1);
                    }
                    out.bad = true;
                }
                for &p in &bi.params {
                    constrain(&mut out.cons, p, ACTION);
                }
                out.absorb(&bi);
                for (k, (keys, v)) in updates.iter().enumerate() {
                    let mut ui = Info::default();
                    for key in keys {
                        if let ExceptKey::Index(ix) = key {
                            for x in ix {
                                let xi = self.expr(x);
                                ui.absorb(&xi);
                            }
                        }
                    }
                    self.at.push(bi.clone());
                    let vi = self.expr(v);
                    self.at.pop();
                    ui.absorb(&vi);
                    if ui.level > ACTION {
                        if !ui.bad {
                            self.arg_error(span, "$Except", k + 2);
                        }
                        out.bad = true;
                    }
                    for &p in &ui.params {
                        constrain(&mut out.cons, p, ACTION);
                    }
                    out.absorb(&ui);
                }
                out
            }
            ExprKind::BoxAction { action, sub } | ExprKind::AngleAction { action, sub } => {
                let name = if matches!(&*e.kind, ExprKind::BoxAction { .. }) { "$SquareAct" } else { "$AngleAct" };
                let s = Summary {
                    level: ACTION,
                    weights: vec![false, false],
                    max: vec![ACTION, 1],
                    min_max: vec![Vec::new(); 2],
                    arg_params: Vec::new(),
                    free_arg_params: Vec::new(),
                    bound_arg_free: Vec::new(),
                    nonleibniz: vec![true; 2],
                    free: Info::default(),
                };
                self.apply(name, &s, &[action.clone(), sub.clone()], span, 0).0
            }
            // (`enabled` is `sub` and `action` again, resolved for ENABLED.)
            ExprKind::Fairness { kind, sub, action, .. } => {
                let name = if *kind == FairnessKind::Weak { "$WF" } else { "$SF" };
                let s = Summary {
                    level: TEMPORAL,
                    weights: vec![false, false],
                    max: vec![1, ACTION],
                    min_max: vec![Vec::new(); 2],
                    arg_params: Vec::new(),
                    free_arg_params: Vec::new(),
                    bound_arg_free: Vec::new(),
                    nonleibniz: vec![true; 2],
                    free: Info::default(),
                };
                self.apply(name, &s, &[sub.clone(), action.clone()], span, 0).0
            }
        }
    }
}

impl Program {
    /// SANY's level checks over the whole program: every definition, the
    /// ASSUMEs (constant level) and the substitutions of every instance
    /// (constants by constant-level expressions, variables by state-level
    /// ones). Errors go to `self.errors`; definition levels are recorded.
    pub(super) fn check_levels(&mut self) {
        // The substitution for each declaration of each instance context.
        // (context, substitution, declaration is a VARIABLE, its name, the
        // module, the INSTANCE, whether its level is checked)
        let mut substs: Vec<(usize, Expr, bool, Arc<str>, Arc<str>, Span, bool)> = Vec::new();
        // ASSUMEs of instantiated modules, with their substitutions applied.
        let mut inst_assumes: Vec<(usize, Expr)> = Vec::new();
        for ctx in 0..self.ctxs.len() {
            // (A context's copy for ENABLED has the same substitutions.)
            if self.ctxs[ctx].copy_of.is_some() {
                continue;
            }
            let Some(si) = &self.ctxs[ctx].subst else { continue };
            let (target, span) = (si.target, si.span);
            let sc = self.scope(ctx, target);
            let mut decls: Vec<(Arc<str>, usize, bool)> = self.scopes[sc]
                .names
                .iter()
                .filter_map(|(n, s)| match s {
                    Sym::Decl { ctx: c, arity, var } if *c == ctx => Some((n.clone(), *arity, *var)),
                    _ => None,
                })
                .collect();
            decls.sort();
            let params = self.ctxs[ctx].inst_params.clone();
            let vals: Vec<Expr> = params
                .into_iter()
                .map(|(n, a)| {
                    let l = self.new_local(n, a, span);
                    self.local_ref(l, span)
                })
                .collect();
            let mname = self.mods[target].name.clone();
            // SANY: anything can be substituted for the constants of a
            // constant module.
            let constant = self.is_constant_module(target, &mut Vec::new());
            for (name, arity, var) in decls {
                if let Ok(e) = self.substitute(ctx, &vals, &name, arity, var, Vec::new(), span) {
                    substs.push((ctx, e, var, name, mname.clone(), span, !constant || var));
                }
            }
            let ast = self.mods[target].ast.clone();
            for u in &ast.units {
                if let tlx_front::ast::Unit::Assume { body, .. } = u {
                    let mut env = super::Env::new(ctx, target);
                    env.inst_args = vals.clone();
                    if let Ok(e) = self.expr(&mut env, body) {
                        inst_assumes.push((ctx, e));
                    }
                }
            }
        }
        // Resolve any definitions queued while expanding substitutions (e.g.
        // a LET INSTANCE inside a WITH expression).
        self.drain_worklist();

        let n = self.defs.len();
        let mut c = Checker {
            p: self,
            memo: vec![None; n],
            in_progress: vec![false; n],
            errors: Vec::new(),
            at: Vec::new(),
            stack: Vec::new(),
            muted: vec![false; self.ctxs.len()],
        };
        for (ctx, e, var, name, module, span, check) in &substs {
            if matches!(&*e.kind, ExprKind::OpArg(_) | ExprKind::Lambda { .. }) {
                if let Some(s) = c.op_summary(e) {
                    if s.nonleibniz.iter().any(|&b| b) {
                        c.error(
                            *span,
                            format!("Error in instantiating module '{module}':\n A non-Leibniz operator substituted for '{name}'."),
                        );
                        c.muted[*ctx] = true;
                    }
                }
            }
            let info = c.expr(e);
            let max = if *var { 1 } else { CONSTANT };
            if *check && info.level > max && !info.bad {
                c.error(
                    *span,
                    format!(
                        "Level error in instantiating module '{module}':\nThe level of the expression or operator substituted for '{name}' \nmust be at most {max}."
                    ),
                );
                c.muted[*ctx] = true;
            }
        }
        for d in 0..n {
            c.summary(DefId(d as u32));
        }
        for (ctx, e) in &inst_assumes {
            if !c.muted[*ctx] {
                c.expr(e);
            }
        }
        // SANY: a parameter of a (module-level) RECURSIVE operator cannot be
        // primed.
        for d in 0..n {
            let src = &c.p.def_src[d];
            let super::DefUnit::Op(od) = &src.unit else { continue };
            if src.state == super::DefState::Local || !c.p.recursive_decl(src.module, &od.name.name) {
                continue;
            }
            let Some(s) = c.memo[d].clone() else { continue };
            let skip = c.p.def_inst[d];
            for (j, &m) in s.max.iter().enumerate().skip(skip) {
                if m < ACTION {
                    c.error(od.span, format!("Argument {} of recursive operator {} is primed", j - skip + 1, od.name.name));
                }
            }
        }
        for a in &self.assumes {
            let info = c.expr(a);
            if info.level > CONSTANT && !info.bad {
                let l = info.level;
                c.error(a.span, format!("Level error: assumptions must be level 0 (Constant),\nbut this one has level {l}."));
            }
        }
        let memo = std::mem::take(&mut c.memo);
        let errors = std::mem::take(&mut c.errors);
        self.level_memo = memo;
        self.errors.extend(errors);
    }

    /// The level of an expression of the program (its parameters taken as
    /// constants).
    pub fn expr_level(&self, e: &Expr) -> u8 {
        let n = self.defs.len();
        let mut memo = self.level_memo.clone();
        memo.resize(n, None);
        let mut c = Checker {
            p: self,
            memo,
            in_progress: vec![false; n],
            errors: Vec::new(),
            at: Vec::new(),
            stack: Vec::new(),
            muted: Vec::new(),
        };
        c.expr(e).level
    }

    /// TLC's checks of the levels of the definitions named by the
    /// configuration: INVARIANTs must be state predicates and PROPERTYs must
    /// not be (or contain conjuncts that are) actions.
    pub fn check_cfg_levels(&mut self, cfg: &tlx_front::cfg::Config) -> Option<CfgLevelError> {
        let resolve = |p: &mut Program, name: &str| -> Option<DefId> {
            // A cfg replacement `Inv <- Other` names the definition used.
            let target = cfg.last_constant_subst(name).unwrap_or(name);
            match p.lookup_root(target)? {
                RootSymbol::Def(d) => Some(d),
                _ => None,
            }
        };
        for name in &cfg.invariants {
            let Some(d) = resolve(self, name) else { continue };
            if self.defs[d.idx()].params.is_empty() && self.def_level(d).is_some_and(|l| l >= ACTION) {
                return Some(CfgLevelError::Invariant(format!(
                    "The invariant {name} is not a state predicate (one with no primes or temporal operators).\n\
                     Note that a bug can cause TLC to incorrectly report this error.\n\
                     If you believe your TLA+ or PlusCal specification to be correct,\n\
                     please check if this bug described in LevelNode.java starting at line 590ff affects you."
                )));
            }
        }
        for name in &cfg.properties {
            let Some(d) = resolve(self, name) else { continue };
            if !self.defs[d.idx()].params.is_empty() {
                continue;
            }
            let DefKind::Op(body) = self.defs[d.idx()].kind.clone() else { continue };
            if let Some(msg) = self.action_property(name, &body, &mut Vec::new()) {
                return Some(CfgLevelError::Property(msg));
            }
        }
        None
    }

    /// TLC (SpecProcessor.processConfigProps): the first action-level part
    /// of PROPERTY `name` with body `e`.
    fn action_property(&self, name: &str, e: &Expr, seen: &mut Vec<DefId>) -> Option<String> {
        match &*e.kind {
            ExprKind::And(es) => es.iter().find_map(|x| self.action_property(name, x, seen)),
            ExprKind::Let { body, .. } => self.action_property(name, body, seen),
            ExprKind::Apply { op: OpRef::Def(d), args } if args.is_empty() && !seen.contains(d) => {
                let def = &self.defs[d.idx()];
                match &def.kind {
                    DefKind::Op(body) if def.builtin.is_none() && def.params.is_empty() => {
                        seen.push(*d);
                        let opname = def.name.rsplit('!').next().unwrap_or(&def.name).to_string();
                        self.action_property(&opname, body, seen)
                    }
                    _ => None,
                }
            }
            _ if self.expr_level(e) == ACTION => {
                let at = self.location(e.span);
                let hint = match &*e.kind {
                    ExprKind::BoxAction { .. } => format!(
                        "To check that action {name} holds in *every* step of the behavior, define a temporal property by applying the \"always\" temporal operator ([]) to the formula at {at} (compare page 90 of Specifying Systems at https://lamport.azurewebsites.net/tla/book.html)."
                    ),
                    ExprKind::AngleAction { .. } => format!(
                        "To check that infinitely many {name} steps occur, define a temporal property by applying the \"always eventually\" temporal operator combination ([]<>) to the formula at {at} (compare page 91 of Specifying Systems at https://lamport.azurewebsites.net/tla/book.html)."
                    ),
                    _ => format!(
                        "To check that action {name} holds in *every* step of the behavior, define a temporal property: Let A be the formula at {at}; rewrite A as [][A]_v, where v is a state function (typically the tuple of variables) (compare page 90 of Specifying Systems at https://lamport.azurewebsites.net/tla/book.html)."
                    ),
                };
                Some(format!(
                    "The formula {name} at {at} is an action-level formula (i.e., it contains no temporal operators). Only temporal-level (or state-level) formulas are allowed under PROPERTY or PROPERTIES. {hint}"
                ))
            }
            _ => None,
        }
    }

    /// TLC's description of a source range: `line L, col C to line L2, col
    /// C2 of module M`.
    pub fn location(&self, span: Span) -> String {
        // The innermost module containing the range.
        let module = self
            .mods
            .iter()
            .filter(|m| m.ast.span.file == span.file && m.ast.span.start <= span.start && span.end <= m.ast.span.end)
            .min_by_key(|m| m.ast.span.end - m.ast.span.start)
            .map_or_else(|| "?".to_string(), |m| m.name.to_string());
        crate::source::SourceRange::of(self.file(span.file), span, crate::source::EndTrim::Raw, module).to_string()
    }

    /// Whether `name` is declared RECURSIVE at the top level of module `m`.
    fn recursive_decl(&self, m: super::ModIdx, name: &str) -> bool {
        self.mods[m].ast.units.iter().any(|u| match u {
            tlx_front::ast::Unit::Recursive(ds) => ds.iter().any(|d| &*d.name.name == name),
            _ => false,
        })
    }

    /// Whether module `m` is a constant module (SANY): it declares no
    /// variables and none of its definitions (nor those of the modules it
    /// extends or instantiates) can be above constant level, i.e. it uses no
    /// action or temporal operators.
    pub(super) fn is_constant_module(&mut self, m: super::ModIdx, seen: &mut Vec<super::ModIdx>) -> bool {
        if seen.contains(&m) {
            return true;
        }
        seen.push(m);
        let ast = self.mods[m].ast.clone();
        for e in &ast.extends {
            if let Some(em) = self.find_module(e) {
                if !self.is_constant_module(em, seen) {
                    return false;
                }
            }
        }
        for u in &ast.units {
            let nonconst = match u {
                tlx_front::ast::Unit::Variables(_) => true,
                tlx_front::ast::Unit::OpDef(od) => nonconstant_ops(&od.body),
                tlx_front::ast::Unit::FnDef(fd) => nonconstant_ops(&fd.body) || fd.bounds.iter().any(|b| nonconstant_ops(&b.set)),
                tlx_front::ast::Unit::Instance(inst) => {
                    inst.substs.iter().any(|(_, e)| nonconstant_ops(e))
                        || self.find_instance_module(m, &inst.module).is_some_and(|t| !self.is_constant_module(t, seen))
                }
                _ => false,
            };
            if nonconst {
                return false;
            }
        }
        true
    }

    /// The level (0 constant, 1 state, 2 action, 3 temporal) of a definition
    /// with its parameters taken as constants, as computed when the program
    /// was loaded.
    pub fn def_level(&self, d: DefId) -> Option<u8> {
        self.level_memo.get(d.idx()).and_then(|s| s.as_ref()).map(|s| s.level)
    }
}

/// An error TLC reports when processing the configuration.
#[derive(Clone, Debug)]
pub enum CfgLevelError {
    /// An INVARIANT that is not a state predicate (TLC exits with 76).
    Invariant(String),
    /// A PROPERTY with an action-level part (TLC exits with 151).
    Property(String),
}

impl CfgLevelError {
    pub fn message(&self) -> &str {
        match self {
            CfgLevelError::Invariant(m) | CfgLevelError::Property(m) => m,
        }
    }
}

/// Whether `e` uses an operator whose result is above constant level.
fn nonconstant_ops(e: &tlx_front::ast::Expr) -> bool {
    use tlx_front::ast::ExprKind as A;
    let mut found = false;
    tlx_front::ast::walk(e, &mut |x| {
        found |= match &*x.kind {
            A::OpAppl { prefix, name, .. } => {
                prefix.is_empty() && matches!(&*name.name, "'" | "UNCHANGED" | "ENABLED" | "[]" | "<>" | "~>" | "-+->" | "\\cdot")
            }
            A::BoxAction { .. } | A::AngleAction { .. } | A::Fairness { .. } | A::TemporalQuant { .. } => true,
            _ => false,
        };
    });
    found
}
