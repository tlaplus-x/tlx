//! Set filters over sets of sequences decided on prefixes.
//!
//! `{s \in [1..n -> R] : P}` evaluates `P` on |R|^n sequences (and a
//! bounded `Seq(R)`, `UNION {[1..k -> R] : k \in 1..n}`, on all of their
//! lengths): `SortedSeqs == {s \in Seq(V) : \A i, j \in 1..Len(s) : i < j
//! => s[i] =< s[j]}` with 5 values up to length 8 is half a million
//! evaluations. When `P` reads `s` only as `s[i]` (with `i` not depending on
//! the components), `Len(s)` and `DOMAIN s`, and uses the components only
//! in comparisons, integer arithmetic and Boolean operators (definitions
//! applied are expanded), `P` can be evaluated on a prefix
//! of `s` in three-valued logic (a component beyond the prefix unknown):
//! it is often decided by the prefix (a prefix that is not sorted), and
//! then has that value on every sequence extending it, which are
//! consecutive in the enumeration order (lexicographic). The sequences are
//! enumerated as a tree of prefixes, each decided subtree skipped or
//! emitted whole.
//!
//! Errors: before the prefixes of one length are evaluated, `P` is
//! evaluated with every component unknown, following every branch that
//! some sequence may take (a known condition, which is the same for all
//! sequences, takes its branch only), and each operation on an unknown
//! value is tried on every value it may have. If that evaluation meets no
//! possible error (an index outside `1..n`, a comparison of values it is
//! not defined on, arithmetic overflow, a non-Boolean operand of a Boolean
//! operator), no sequence's evaluation errs, so the order in which TLC
//! evaluates `P`'s parts (short-circuiting left to right) cannot change its
//! value, and three-valued logic gives the same value. Anything else (an
//! unsupported construct, a possible error) leaves the filter to the
//! interpreter.

use std::cell::OnceCell;
use std::rc::Rc;

use tlx_front::ast::QuantKind;
use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{BoundVars, DefId, DefKind, Expr, ExprKind as H, LocalId, OpRef};
use tlx_value::{arith, ops, order, Value};

use crate::env::{Binding, Env};
use crate::interp::{ConstVal, Interp};

/// At most this many nested expansions of definitions in the predicate.
const MAX_INLINE: usize = 32;

/// At most this many nodes in the compiled predicate.
const MAX_NODES: usize = 4096;

/// At most this many node evaluations in one evaluation of the predicate
/// with every component unknown (`SeqPred::check`).
const MAX_STEPS: usize = 1 << 20;

/// At most this many iterations of a constant-domain quantifier unrolled at
/// compile time into a flat junction.
const MAX_UNROLL: usize = 64;

/// A set filter's predicate compiled for evaluation on prefixes.
pub(crate) struct SeqPred {
    root: Node,
    slots: usize,
    quants: usize,
}

enum Node {
    Lit(Value),
    /// A bound variable of a quantifier in the predicate.
    Slot(usize),
    /// `Len(s)`.
    Len,
    /// `DOMAIN s`.
    Domain,
    /// `s[i]`.
    At(Box<Node>),
    /// `s[k]` for a constant 0-based index `k` (`1 <= k + 1`).
    AtConst(usize),
    /// A strict builtin (`apply`).
    Op(B, Vec<Node>),
    /// `{a, b, ...}` of known values.
    SetEnum(Vec<Node>),
    And(Vec<Node>),
    Or(Vec<Node>),
    Implies(Box<Node>, Box<Node>),
    If(Box<(Node, Node, Node)>),
    /// `\A` or `\E` (number `id`): its variables (slot, index in
    /// `sets`).
    Quant {
        id: usize,
        exists: bool,
        vars: Vec<(usize, usize)>,
        sets: Vec<Node>,
        body: Box<Node>,
    },
}

impl Node {
    /// Whether evaluating `self` can only succeed with a `Value::Bool` (so
    /// unwrapping a singleton `And`/`Or`/`Implies` cannot skip the Boolean
    /// type check during `SeqPred::check`).
    fn is_bool_guaranteed(&self) -> bool {
        match self {
            Node::Lit(Value::Bool(_)) | Node::And(_) | Node::Or(_) | Node::Implies(..) | Node::Quant { .. } => true,
            Node::Op(op, _) => {
                matches!(op, B::Eq | B::Neq | B::Lt | B::Le | B::Gt | B::Ge | B::In | B::NotIn | B::Equiv | B::Not)
            }
            _ => false,
        }
    }
}

/// What a name stands for while compiling.
#[derive(Clone)]
enum Name {
    /// The filtered sequence.
    Seq,
    /// A known compile-time constant value (e.g. an unrolled quantifier var).
    Lit(Value),
    Slot(usize),
    /// A parameter of an expanded definition: its argument, passed by name
    /// (compiled in `scope`). Constant literal results are cached in `lit` so
    /// repeated references during bounded recursive unfolding stay linear.
    Arg {
        expr: Expr,
        scope: Scope,
        lit: Rc<OnceCell<Value>>,
    },
}

/// A `LET` definition in lexical scope during predicate compilation.
#[derive(Clone)]
struct LetEntry {
    scope: Scope,
    lit: Rc<OnceCell<Value>>,
}

/// Persistent lexical scope during predicate compilation so by-name arguments
/// and nested `LET` / recursive expansions resolve in their defining scope.
#[derive(Clone, Default)]
struct Scope {
    names: Rc<[(LocalId, Name)]>,
    lets: Rc<[(DefId, LetEntry)]>,
}

impl Scope {
    fn lookup_local(&self, l: LocalId) -> Option<&Name> {
        self.names.iter().rev().find(|(x, _)| *x == l).map(|(_, n)| n)
    }

    fn lookup_let(&self, d: DefId) -> Option<&LetEntry> {
        self.lets.iter().rev().find(|(x, _)| *x == d).map(|(_, e)| e)
    }

    fn extend_names(&self, extra: impl IntoIterator<Item = (LocalId, Name)>) -> Scope {
        let mut names = self.names.to_vec();
        names.extend(extra);
        Scope { names: Rc::from(names), lets: self.lets.clone() }
    }

    fn with_let(&self, d: DefId, entry: LetEntry) -> Scope {
        let mut lets = self.lets.to_vec();
        lets.push((d, entry));
        Scope { names: self.names.clone(), lets: Rc::from(lets) }
    }
}

struct Compiler<'a> {
    ip: &'a Interp,
    env: &'a Env,
    slots: usize,
    quants: usize,
    nodes: usize,
    depth: usize,
}

impl SeqPred {
    /// The predicate `pred` (in `env`) of a filter with bound variables
    /// `vars`, if it has the form described in the module documentation.
    pub(crate) fn compile(ip: &Interp, vars: &BoundVars, pred: &Expr, env: &Env) -> Option<SeqPred> {
        let BoundVars::Many(ls) = vars else { return None };
        let [x] = ls.as_slice() else { return None };
        let scope = Scope::default().extend_names([(*x, Name::Seq)]);
        let mut c = Compiler { ip, env, slots: 0, quants: 0, nodes: 0, depth: 0 };
        let root = c.expr(pred, &scope)?;
        Some(SeqPred { root, slots: c.slots, quants: c.quants })
    }

    /// The elements of `[1..n -> range]` satisfying the predicate, in
    /// enumeration order: `Ok(None)` if the predicate may fail on one (see
    /// the module documentation), else whether the enumeration completed.
    /// `v(x, Some(true))` visits an element known to satisfy it; an
    /// element the evaluation on prefixes does not decide (not expected
    /// after the check) is left to `v(x, None)`.
    pub(crate) fn filter(
        &self,
        n: usize,
        range: &[Value],
        v: &mut dyn FnMut(Value, Option<bool>) -> tlx_value::Result<bool>,
    ) -> tlx_value::Result<Option<bool>> {
        let (int_bounds, sorted_ints) = range_int_info(range);
        if !self.check(n, range, int_bounds) {
            return Ok(None);
        }
        let mut ev = Eval {
            n,
            prefix: Vec::with_capacity(n),
            slots: vec![Value::Bool(false); self.slots],
            sets: vec![Vec::new(); self.quants],
            check: None,
            int_bounds,
            next_bounds: None,
            steps: 0,
        };
        let mut idx = Vec::with_capacity(n);
        if sorted_ints && n >= 1 && range.len() > 1 {
            self.walk_split(&mut ev, range, &mut idx, 0, range.len(), v).map(Some)
        } else {
            self.walk(&mut ev, range, &mut idx, v).map(Some)
        }
    }

    /// Whether no evaluation of the predicate on a sequence of
    /// `[1..n -> range]` errs (every component unknown, every branch some
    /// sequence may take).
    fn check(&self, n: usize, range: &[Value], int_bounds: Option<(i64, i64)>) -> bool {
        let mut ev = Eval {
            n,
            prefix: Vec::new(),
            slots: vec![Value::Bool(false); self.slots],
            sets: vec![Vec::new(); self.quants],
            check: Some(range),
            int_bounds,
            next_bounds: None,
            steps: 0,
        };
        match ev.node(&self.root) {
            Some(V::K(Value::Bool(_))) => true,
            Some(V::U(Some(vs))) => vs.iter().all(|v| matches!(v, Value::Bool(_))),
            _ => false,
        }
    }

    /// The sequences extending `ev.prefix` when `range` consists of sorted
    /// integers: narrows `s[prefix.len() + 1]` by binary interval splitting
    /// over `range[lo..hi]` in left-to-right order so integer bounds and
    /// sums prune dead subranges in O(log |range|) evaluations.
    fn walk_split(
        &self,
        ev: &mut Eval,
        range: &[Value],
        idx: &mut Vec<usize>,
        lo: usize,
        hi: usize,
        v: &mut dyn FnMut(Value, Option<bool>) -> tlx_value::Result<bool>,
    ) -> tlx_value::Result<bool> {
        let lo_val = range[lo].as_int().unwrap();
        let hi_val = range[hi - 1].as_int().unwrap();
        ev.next_bounds = Some((lo_val, hi_val));
        let res = ev.node(&self.root);
        ev.next_bounds = None;
        match res {
            Some(V::K(Value::Bool(false))) => Ok(true),
            Some(V::K(Value::Bool(true))) => emit_range(ev, range, idx, lo, hi, Some(true), v),
            Some(V::U(_)) => {
                if hi - lo == 1 {
                    ev.prefix.push(range[lo].clone());
                    idx.push(lo);
                    let done = if ev.prefix.len() < ev.n {
                        self.walk_split(ev, range, idx, 0, range.len(), v)
                    } else {
                        v(Value::tuple(ev.prefix.clone()), None)
                    };
                    ev.prefix.pop();
                    idx.pop();
                    done
                } else {
                    let mid = lo + (hi - lo) / 2;
                    if !self.walk_split(ev, range, idx, lo, mid, v)? {
                        return Ok(false);
                    }
                    self.walk_split(ev, range, idx, mid, hi, v)
                }
            }
            _ => emit_range(ev, range, idx, lo, hi, None, v),
        }
    }

    /// The sequences extending the prefix `ev.prefix` (positions `idx` in
    /// `range`).
    fn walk(
        &self,
        ev: &mut Eval,
        range: &[Value],
        idx: &mut Vec<usize>,
        v: &mut dyn FnMut(Value, Option<bool>) -> tlx_value::Result<bool>,
    ) -> tlx_value::Result<bool> {
        match ev.node(&self.root) {
            Some(V::K(Value::Bool(false))) => Ok(true),
            Some(V::K(Value::Bool(true))) => extensions(ev.n, range, idx, &ev.prefix, &mut |x| v(x, Some(true))),
            Some(V::U(_)) if ev.prefix.len() < ev.n => {
                for (i, r) in range.iter().enumerate() {
                    ev.prefix.push(r.clone());
                    idx.push(i);
                    let done = self.walk(ev, range, idx, v);
                    ev.prefix.pop();
                    idx.pop();
                    if !done? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => extensions(ev.n, range, idx, &ev.prefix, &mut |x| v(x, None)),
        }
    }
}

/// Emit every sequence extending `ev.prefix` with `range[lo..hi]` at the next
/// position, in enumeration order.
fn emit_range(
    ev: &mut Eval,
    range: &[Value],
    idx: &mut Vec<usize>,
    lo: usize,
    hi: usize,
    known: Option<bool>,
    v: &mut dyn FnMut(Value, Option<bool>) -> tlx_value::Result<bool>,
) -> tlx_value::Result<bool> {
    for (i, r) in range[lo..hi].iter().enumerate() {
        ev.prefix.push(r.clone());
        idx.push(lo + i);
        let done = extensions(ev.n, range, idx, &ev.prefix, &mut |x| v(x, known));
        ev.prefix.pop();
        idx.pop();
        if !done? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Integer range info for `range`: `(min, max)` when every element is an
/// integer, and whether those integers appear in non-decreasing order.
fn range_int_info(range: &[Value]) -> (Option<(i64, i64)>, bool) {
    let Some(first) = range.first().and_then(|v| v.as_int().ok()) else {
        return (None, false);
    };
    let (mut lo, mut hi, mut prev, mut sorted) = (first, first, first, true);
    for v in &range[1..] {
        let Ok(x) = v.as_int() else {
            return (None, false);
        };
        if x < prev {
            sorted = false;
        }
        prev = x;
        lo = lo.min(x);
        hi = hi.max(x);
    }
    (Some((lo, hi)), sorted)
}

/// Every sequence of length `n` extending `prefix` (positions `idx` in
/// `range`), in enumeration order.
fn extensions(
    n: usize,
    range: &[Value],
    idx: &[usize],
    prefix: &[Value],
    f: &mut dyn FnMut(Value) -> tlx_value::Result<bool>,
) -> tlx_value::Result<bool> {
    let k = prefix.len();
    let mut pos: Vec<usize> = idx.to_vec();
    pos.resize(n, 0);
    let mut cur: Vec<Value> = prefix.to_vec();
    cur.extend((k..n).map(|_| range[0].clone()));
    loop {
        if !f(Value::tuple(cur.clone()))? {
            return Ok(false);
        }
        let mut i = n;
        loop {
            if i == k {
                return Ok(true);
            }
            i -= 1;
            pos[i] += 1;
            if pos[i] < range.len() {
                cur[i] = range[pos[i]].clone();
                break;
            }
            pos[i] = 0;
            cur[i] = range[0].clone();
        }
    }
}

impl Compiler<'_> {
    fn node(&mut self, n: Node) -> Option<Node> {
        self.nodes += 1;
        (self.nodes <= MAX_NODES).then_some(n)
    }

    /// Whether `e` denotes the filtered sequence (in `scope`).
    fn is_seq(&self, e: &Expr, scope: &Scope) -> bool {
        match &*e.kind {
            H::Local(l) => match scope.lookup_local(*l) {
                Some(Name::Seq) => true,
                Some(Name::Arg { expr, scope: arg_scope, .. }) => self.is_seq(expr, arg_scope),
                _ => false,
            },
            _ => false,
        }
    }

    fn exprs(&mut self, es: &[Expr], scope: &Scope) -> Option<Vec<Node>> {
        es.iter().map(|e| self.expr(e, scope)).collect()
    }

    fn apply_def(&mut self, d: DefId, args: &[Expr], scope: &Scope) -> Option<Node> {
        let d = self.ip.redirect_def(d);
        if let Some(v) = self.ip.def_value.get(&d) {
            return args.is_empty().then(|| self.node(Node::Lit(v.clone())))?;
        }
        if args.is_empty() && self.ip.is_const_def(d) {
            if let Some(cached) = self.ip.const_cache[d.idx()].get() {
                return match cached {
                    Ok(v) => self.node(Node::Lit(v.clone())),
                    Err(_) => None,
                };
            }
        }
        let def = &self.ip.prog.defs[d.idx()];
        if let Some(b) = def.builtin {
            return self.builtin(b, args, scope);
        }
        if self.ip.def_effectful(d) || !self.ip.def_defer_errors[d.idx()] {
            return None;
        }
        let DefKind::Op(body) = &def.kind else { return None };
        if self.depth >= MAX_INLINE || def.params.len() != args.len() {
            return None;
        }
        let (base_scope, let_lit) = if self.ip.prog.def_is_let(d) {
            let entry = scope.lookup_let(d)?;
            if args.is_empty() {
                if let Some(v) = entry.lit.get() {
                    return self.node(Node::Lit(v.clone()));
                }
            }
            (entry.scope.clone(), args.is_empty().then(|| entry.lit.clone()))
        } else {
            (Scope::default(), None)
        };
        let bindings: Vec<(LocalId, Name)> = def
            .params
            .iter()
            .zip(args)
            .map(|(p, a)| {
                let name = if self.is_seq(a, scope) {
                    Name::Seq
                } else {
                    Name::Arg { expr: a.clone(), scope: scope.clone(), lit: Rc::new(OnceCell::new()) }
                };
                (*p, name)
            })
            .collect();
        let callee_scope = if bindings.is_empty() { base_scope } else { base_scope.extend_names(bindings) };
        self.depth += 1;
        let r = self.expr(body, &callee_scope);
        self.depth -= 1;
        if let (Some(lit), Some(Node::Lit(v))) = (let_lit, &r) {
            let _ = lit.set(v.clone());
        }
        r
    }

    fn expr(&mut self, e: &Expr, scope: &Scope) -> Option<Node> {
        let n = match &*e.kind {
            H::Num(n) if *n <= i32::MAX as i128 => Node::Lit(Value::Int(*n as i64)),
            H::Bool(b) => Node::Lit(Value::Bool(*b)),
            H::Str(s) => Node::Lit(Value::Str(self.ip.syms.get(s))),
            H::SetEnum(es) => {
                let ns = self.exprs(es, scope)?;
                if ns.iter().all(|n| matches!(n, Node::Lit(_))) {
                    let vs: Vec<Value> = ns
                        .into_iter()
                        .map(|n| match n {
                            Node::Lit(v) => v,
                            _ => unreachable!(),
                        })
                        .collect();
                    Node::Lit(Value::set_literal(vs).ok()?)
                } else {
                    Node::SetEnum(ns)
                }
            }
            H::Const(c) => match &self.ip.consts[c.idx()] {
                Some(ConstVal::Value(v)) => Node::Lit(v.clone()),
                Some(ConstVal::Def(d)) => return self.apply_def(*d, &[], scope),
                _ => return None,
            },
            H::Local(l) => match scope.lookup_local(*l) {
                Some(Name::Lit(v)) => Node::Lit(v.clone()),
                Some(Name::Slot(i)) => Node::Slot(*i),
                Some(Name::Arg { expr, scope: arg_scope, lit }) => {
                    if let Some(v) = lit.get() {
                        return self.node(Node::Lit(v.clone()));
                    }
                    let expr = expr.clone();
                    let arg_scope = arg_scope.clone();
                    let lit = lit.clone();
                    let r = self.expr(&expr, &arg_scope)?;
                    if let Node::Lit(v) = &r {
                        let _ = lit.set(v.clone());
                    }
                    return Some(r);
                }
                Some(Name::Seq) => return None,
                None => match self.env.lookup(*l) {
                    Some(Binding::Val(v)) => Node::Lit(v.clone()),
                    _ => return None,
                },
            },
            H::FnApp { func, args } if self.is_seq(func, scope) => match args.as_slice() {
                [i] => match self.expr(i, scope)? {
                    Node::Lit(Value::Int(k)) if k >= 1 => Node::AtConst((k - 1) as usize),
                    idx => Node::At(Box::new(idx)),
                },
                _ => return None,
            },
            H::Builtin { op, args } | H::Apply { op: OpRef::Builtin(op), args } => return self.builtin(*op, args, scope),
            H::Apply { op: OpRef::Def(d), args } => return self.apply_def(*d, args, scope),
            H::Let { defs, body } => {
                let mut let_scope = scope.clone();
                for d in defs {
                    if matches!(self.ip.prog.defs[d.idx()].kind, DefKind::Op(_)) {
                        let entry = LetEntry { scope: let_scope.clone(), lit: Rc::new(OnceCell::new()) };
                        let_scope = let_scope.with_let(*d, entry);
                    }
                }
                return self.expr(body, &let_scope);
            }
            H::Choose { vars, set: Some(s_expr), body } => {
                let BoundVars::Many(ls) = vars else { return None };
                if ls.len() != 1 || !matches!(&*body.kind, H::Bool(true)) {
                    return None;
                }
                let Node::Lit(s_val) = self.expr(s_expr, scope)? else { return None };
                let chosen = choose_first(&s_val)?;
                Node::Lit(chosen)
            }
            H::And(es) => return self.compile_junction(es, false, scope),
            H::Or(es) => return self.compile_junction(es, true, scope),
            H::If { cond, then, els } => match self.expr(cond, scope)? {
                Node::Lit(Value::Bool(true)) => return self.expr(then, scope),
                Node::Lit(Value::Bool(false)) => return self.expr(els, scope),
                Node::Lit(_) => return None,
                cond => Node::If(Box::new((cond, self.expr(then, scope)?, self.expr(els, scope)?))),
            },
            H::Quant { kind, bounds, body } => {
                let exists = *kind == QuantKind::Exists;
                let sets = bounds.iter().map(|b| self.expr(&b.set, scope)).collect::<Option<Vec<_>>>()?;
                if let Some(unrolled) = self.try_unroll_quant(exists, bounds, &sets, body, scope) {
                    return Some(unrolled);
                }
                let mut vars = Vec::new();
                let mut extra = Vec::new();
                for (k, b) in bounds.iter().enumerate() {
                    let BoundVars::Many(ls) = &b.vars else { return None };
                    for l in ls {
                        vars.push((self.slots, k));
                        extra.push((*l, Name::Slot(self.slots)));
                        self.slots += 1;
                    }
                }
                let inner_scope = scope.extend_names(extra);
                let body = self.expr(body, &inner_scope)?;
                self.quants += 1;
                Node::Quant { id: self.quants - 1, exists, vars, sets, body: Box::new(body) }
            }
            _ => return None,
        };
        self.node(n)
    }

    /// Compile `/\` (`or = false`) or `\/` (`or = true`), folding constant
    /// operands while preserving earlier non-constant operands before an
    /// absorbing constant so `SeqPred::check` still checks them for errors.
    fn compile_junction(&mut self, es: &[Expr], or: bool, scope: &Scope) -> Option<Node> {
        let mut kept = Vec::with_capacity(es.len());
        for e in es {
            match self.expr(e, scope)? {
                Node::Lit(Value::Bool(b)) if b == or => {
                    if kept.is_empty() {
                        return self.node(Node::Lit(Value::Bool(or)));
                    }
                    kept.push(Node::Lit(Value::Bool(or)));
                    break;
                }
                Node::Lit(Value::Bool(_)) => {}
                Node::Lit(_) => return None,
                Node::And(inner) if !or => kept.extend(inner),
                Node::Or(inner) if or => kept.extend(inner),
                n => kept.push(n),
            }
        }
        match kept.len() {
            0 => self.node(Node::Lit(Value::Bool(!or))),
            1 if kept[0].is_bool_guaranteed() => Some(kept.pop().unwrap()),
            _ => self.node(if or { Node::Or(kept) } else { Node::And(kept) }),
        }
    }

    /// Unroll a small constant-domain quantifier (`<= MAX_UNROLL` total
    /// instances) into a flat junction so inner dependent bounds (like
    /// `\A i \in 1..P : \A j \in (i+1)..P : s[i] =< s[j]`) fold into direct
    /// `AtConst` comparisons with zero runtime quantifier overhead.
    fn try_unroll_quant(
        &mut self,
        exists: bool,
        bounds: &[tlx_sema::hir::Bound],
        sets: &[Node],
        body: &Expr,
        scope: &Scope,
    ) -> Option<Node> {
        let mut slots: Vec<(LocalId, Vec<Value>)> = Vec::new();
        let mut total: usize = 1;
        for (b, s) in bounds.iter().zip(sets) {
            let BoundVars::Many(ls) = &b.vars else { return None };
            let Node::Lit(v) = s else { return None };
            let elems: Vec<Value> = match v {
                Value::Interval(lo, hi) => {
                    let len = (*hi as i128 - *lo as i128 + 1).max(0);
                    if len > MAX_UNROLL as i128 {
                        return None;
                    }
                    (*lo..=*hi).map(Value::Int).collect()
                }
                Value::Set(es) => {
                    if es.len() > MAX_UNROLL {
                        return None;
                    }
                    es.to_vec()
                }
                _ => return None,
            };
            for l in ls {
                total = total.checked_mul(elems.len())?;
                if total > MAX_UNROLL {
                    return None;
                }
                slots.push((*l, elems.clone()));
            }
        }
        if total == 0 {
            return self.node(Node::Lit(Value::Bool(!exists)));
        }
        let saved_nodes = self.nodes;
        let saved_slots = self.slots;
        let saved_quants = self.quants;
        let mut out = Vec::with_capacity(total);
        let mut idx = vec![0usize; slots.len()];
        loop {
            let inner = scope.extend_names(slots.iter().enumerate().map(|(k, (l, es))| (*l, Name::Lit(es[idx[k]].clone()))));
            let Some(n) = self.expr(body, &inner) else {
                self.nodes = saved_nodes;
                self.slots = saved_slots;
                self.quants = saved_quants;
                return None;
            };
            match n {
                Node::Lit(Value::Bool(b)) if b == exists => {
                    if out.is_empty() {
                        return self.node(Node::Lit(Value::Bool(exists)));
                    }
                    out.push(Node::Lit(Value::Bool(exists)));
                    return self.node(if exists { Node::Or(out) } else { Node::And(out) });
                }
                Node::Lit(Value::Bool(_)) => {}
                Node::Lit(_) => {
                    self.nodes = saved_nodes;
                    self.slots = saved_slots;
                    self.quants = saved_quants;
                    return None;
                }
                Node::And(inner) if !exists => out.extend(inner),
                Node::Or(inner) if exists => out.extend(inner),
                n => out.push(n),
            }
            // Advance odometer, first slot fastest (matching TLC's
            // `ContextEnumerator` and `Interp::for_each_binding`).
            let mut k = 0;
            loop {
                if k == slots.len() {
                    return match out.len() {
                        0 => self.node(Node::Lit(Value::Bool(!exists))),
                        1 if out[0].is_bool_guaranteed() => Some(out.pop().unwrap()),
                        _ => self.node(if exists { Node::Or(out) } else { Node::And(out) }),
                    };
                }
                idx[k] += 1;
                if idx[k] < slots[k].1.len() {
                    break;
                }
                idx[k] = 0;
                k += 1;
            }
        }
    }

    fn builtin(&mut self, op: B, args: &[Expr], scope: &Scope) -> Option<Node> {
        if self.ip.builtin_override(op).is_some() {
            return None;
        }
        let n = match (op, args) {
            (B::Len, [s]) if self.is_seq(s, scope) => Node::Len,
            (B::Domain, [s]) if self.is_seq(s, scope) => Node::Domain,
            (B::Implies, [a, b]) => match self.expr(a, scope)? {
                Node::Lit(Value::Bool(false)) => Node::Lit(Value::Bool(true)),
                Node::Lit(Value::Bool(true)) => {
                    let b = self.expr(b, scope)?;
                    if b.is_bool_guaranteed() {
                        return Some(b);
                    }
                    Node::And(vec![b])
                }
                Node::Lit(_) => return None,
                a => Node::Implies(Box::new(a), Box::new(self.expr(b, scope)?)),
            },
            (B::SetMinus | B::Cup | B::Cap, [a, b]) => {
                let (Node::Lit(x), Node::Lit(y)) = (self.expr(a, scope)?, self.expr(b, scope)?) else { return None };
                let v = match op {
                    B::SetMinus => ops::difference(&x, &y).ok()?,
                    B::Cup => ops::union(&x, &y).ok()?,
                    B::Cap => ops::intersect(&x, &y).ok()?,
                    _ => unreachable!(),
                };
                Node::Lit(v)
            }
            (B::Cardinality, [a]) => {
                let Node::Lit(x) = self.expr(a, scope)? else { return None };
                Node::Lit(Value::Int(ops::cardinality(&x).ok()?))
            }
            (
                B::Eq | B::Neq | B::Lt | B::Le | B::Gt | B::Ge | B::In | B::NotIn | B::Equiv | B::Plus | B::Minus | B::Mul | B::DotDot,
                [_, _],
            )
            | (B::Not | B::Neg, [_]) => {
                let ns = self.exprs(args, scope)?;
                if ns.iter().all(|n| matches!(n, Node::Lit(_))) {
                    let refs: Vec<&Value> = ns
                        .iter()
                        .map(|n| match n {
                            Node::Lit(v) => v,
                            _ => unreachable!(),
                        })
                        .collect();
                    Node::Lit(apply(op, &refs)?)
                } else {
                    Node::Op(op, ns)
                }
            }
            _ => return None,
        };
        self.node(n)
    }
}

/// First element of `s` in TLC's normalized order (for constant `CHOOSE x \in S : TRUE`).
fn choose_first(s: &Value) -> Option<Value> {
    if ops::streams_normalized(s) {
        let mut found = None;
        ops::for_each_enumerated(s, &mut |x| {
            found = Some(x);
            Ok(false)
        })
        .ok()?;
        return found;
    }
    match s {
        Value::Set(es) => es.first().cloned(),
        Value::Interval(lo, hi) => (*lo <= *hi).then_some(Value::Int(*lo)),
        _ => ops::enumerate_normalized(s).ok()?.into_iter().next(),
    }
}

/// A value in three-valued evaluation.
#[derive(Clone)]
enum V {
    /// Known.
    K(Value),
    /// Unknown integer guaranteed to lie in `[lo, hi]` (`lo <= hi`, within TLC's i32 range).
    IntRange(i64, i64),
    /// Not known (it depends on a component beyond the prefix); while
    /// checking, the values it may have.
    U(Option<Rc<Vec<Value>>>),
}

/// At most this many values an unknown value may have while checking.
const MAX_CASES: usize = 1 << 10;

/// At most this many combinations of the values of unknown operands tried
/// while checking one operation.
const MAX_COMBINATIONS: usize = 1 << 16;

struct Eval<'a> {
    n: usize,
    /// The known components.
    prefix: Vec<Value>,
    slots: Vec<Value>,
    /// The sets of each quantifier (reused buffers).
    sets: Vec<Vec<Value>>,
    /// Checking (`SeqPred::check`): every component unknown (some element
    /// of this range), operations on unknown values tried on every value
    /// they may have.
    check: Option<&'a [Value]>,
    /// `(min, max)` of `range` when every element of `range` is an integer.
    int_bounds: Option<(i64, i64)>,
    /// Narrowed integer bounds `(lo, hi)` of `s[prefix.len() + 1]` while
    /// binary-splitting its range slice.
    next_bounds: Option<(i64, i64)>,
    steps: usize,
}

impl Eval<'_> {
    /// An unknown value that may have the values `vs` (while checking).
    fn unknown(&self, vs: impl FnOnce() -> Vec<Value>) -> V {
        V::U(self.check.map(|_| Rc::new(vs())))
    }

    /// An unknown Boolean.
    fn unknown_bool(&self) -> V {
        self.unknown(|| vec![Value::Bool(false), Value::Bool(true)])
    }

    #[inline]
    fn at_index(&self, idx0: usize) -> V {
        if let Some(v) = self.prefix.get(idx0) {
            V::K(v.clone())
        } else if idx0 == self.prefix.len() {
            if let Some((lo, hi)) = self.next_bounds.or(self.int_bounds) {
                int_val(lo, hi)
            } else {
                self.unknown(|| self.check.unwrap_or_default().to_vec())
            }
        } else if let Some((lo, hi)) = self.int_bounds {
            int_val(lo, hi)
        } else {
            self.unknown(|| self.check.unwrap_or_default().to_vec())
        }
    }

    /// `None`: fails (possibly, while checking).
    fn node(&mut self, e: &Node) -> Option<V> {
        if self.check.is_some() {
            self.steps += 1;
            if self.steps > MAX_STEPS {
                return None;
            }
        }
        Some(match e {
            Node::Lit(v) => V::K(v.clone()),
            Node::Slot(i) => V::K(self.slots[*i].clone()),
            Node::Len => V::K(Value::Int(self.n as i64)),
            Node::Domain => V::K(Value::Interval(1, self.n as i64)),
            Node::At(i) => match self.node(i)? {
                V::K(Value::Int(i)) if i >= 1 && i as usize <= self.n => self.at_index(i as usize - 1),
                _ => return None,
            },
            Node::AtConst(idx0) => {
                if *idx0 < self.n {
                    self.at_index(*idx0)
                } else {
                    return None;
                }
            }
            Node::And(es) => self.junction(es, false)?,
            Node::Or(es) => self.junction(es, true)?,
            Node::Implies(a, b) => match self.boolean(a)? {
                Some(false) => V::K(Value::Bool(true)),
                Some(true) => match self.boolean(b)? {
                    Some(b) => V::K(Value::Bool(b)),
                    None => self.unknown_bool(),
                },
                None => match self.boolean(b)? {
                    Some(true) => V::K(Value::Bool(true)),
                    _ => self.unknown_bool(),
                },
            },
            Node::If(ite) => match self.boolean(&ite.0)? {
                Some(true) => self.node(&ite.1)?,
                Some(false) => self.node(&ite.2)?,
                None => {
                    let (a, b) = (self.node(&ite.1)?, self.node(&ite.2)?);
                    match (a, b) {
                        (V::K(x), V::K(y)) if order::certainly_equal(&x, &y) => V::K(x),
                        (a, b) if int_bounds_of(&a).is_some() && int_bounds_of(&b).is_some() => {
                            let (a0, a1) = int_bounds_of(&a).unwrap();
                            let (b0, b1) = int_bounds_of(&b).unwrap();
                            int_val(a0.min(b0), a1.max(b1))
                        }
                        (_, _) if self.check.is_none() => V::U(None),
                        (a, b) => {
                            let mut vs = cases(&a)?;
                            for y in cases(&b)? {
                                if !vs.iter().any(|v| order::certainly_equal(v, &y)) {
                                    vs.push(y);
                                }
                            }
                            if vs.len() > MAX_CASES {
                                return None;
                            }
                            self.unknown(|| vs)
                        }
                    }
                }
            },
            Node::Quant { id, exists, vars, sets, body } => {
                // (A quantifier is not evaluated inside itself: its buffer
                // is free.)
                let mut elems = std::mem::take(&mut self.sets[*id]);
                elems.clear();
                for s in sets {
                    match self.node(s)? {
                        V::K(s @ (Value::Set(_) | Value::Interval(..))) => elems.push(s),
                        _ => return None,
                    }
                }
                let mut unknown = false;
                let decided = self.quant(*exists, vars, &elems, body, 0, &mut unknown);
                self.sets[*id] = elems;
                if decided? {
                    V::K(Value::Bool(*exists))
                } else if unknown {
                    self.unknown_bool()
                } else {
                    V::K(Value::Bool(!*exists))
                }
            }
            Node::SetEnum(es) => {
                let mut vs = Vec::with_capacity(es.len());
                for e in es {
                    match self.node(e)? {
                        V::K(v) => vs.push(v),
                        V::IntRange(..) | V::U(_) => return None,
                    }
                }
                V::K(Value::set_from(vs).ok()?)
            }
            Node::Op(op, args) => match args.as_slice() {
                [a] => {
                    let a = self.node(a)?;
                    self.op(*op, &[a])?
                }
                [a, b] => {
                    let a = self.node(a)?;
                    let b = self.node(b)?;
                    self.op(*op, &[a, b])?
                }
                _ => return None,
            },
        })
    }

    /// The instances of a quantifier from variable `k` on: whether one
    /// decided it (`exists`: one is TRUE, else one is FALSE); `unknown`:
    /// one is not known.
    fn quant(&mut self, exists: bool, vars: &[(usize, usize)], sets: &[Value], body: &Node, k: usize, unknown: &mut bool) -> Option<bool> {
        let Some(&(slot, set)) = vars.get(k) else {
            return Some(match self.boolean(body)? {
                Some(b) => b == exists,
                None => {
                    *unknown = true;
                    false
                }
            });
        };
        // (The enumeration order of a set or an interval is its order.)
        match &sets[set] {
            Value::Interval(lo, hi) => {
                for i in *lo..=*hi {
                    self.slots[slot] = Value::Int(i);
                    if self.quant(exists, vars, sets, body, k + 1, unknown)? {
                        return Some(true);
                    }
                }
            }
            Value::Set(es) => {
                for v in es.iter() {
                    self.slots[slot] = v.clone();
                    if self.quant(exists, vars, sets, body, k + 1, unknown)? {
                        return Some(true);
                    }
                }
            }
            _ => return None,
        }
        Some(false)
    }

    /// `/\` (`or` false) or `\/` of `es`.
    fn junction(&mut self, es: &[Node], or: bool) -> Option<V> {
        let mut unknown = false;
        for e in es {
            match self.boolean(e)? {
                Some(b) if b == or => return Some(V::K(Value::Bool(or))),
                Some(_) => {}
                None => unknown = true,
            }
        }
        Some(if unknown { self.unknown_bool() } else { V::K(Value::Bool(!or)) })
    }

    /// A Boolean operand: its value if known.
    fn boolean(&mut self, e: &Node) -> Option<Option<bool>> {
        match self.node(e)? {
            V::K(Value::Bool(b)) => Some(Some(b)),
            V::U(Some(vs)) => match vs.as_slice() {
                [Value::Bool(b)] => Some(Some(*b)),
                vs if vs.iter().all(|v| matches!(v, Value::Bool(_))) => Some(None),
                _ => None,
            },
            V::U(None) => Some(None),
            _ => None,
        }
    }

    fn op(&mut self, op: B, vs: &[V]) -> Option<V> {
        match vs {
            [V::K(x)] => return Some(V::K(apply(op, &[x])?)),
            [V::K(x), V::K(y)] => return Some(V::K(apply(op, &[x, y])?)),
            _ => {}
        }
        if let Some(r) = self.op_int_range(op, vs) {
            return r;
        }
        if self.check.is_none() {
            return Some(V::U(None));
        }
        // An unknown operand: the operation must be defined whatever its
        // value is; the result may be any of the results.
        let cs = vs.iter().map(cases).collect::<Option<Vec<_>>>()?;
        if cs.iter().map(Vec::len).product::<usize>() > MAX_COMBINATIONS {
            return None;
        }
        let mut out: Vec<Value> = Vec::new();
        let mut args: Vec<&Value> = Vec::with_capacity(cs.len());
        if !combinations(&cs, &mut args, &mut |a| {
            let Some(r) = apply(op, a) else { return false };
            if !out.iter().any(|v| order::certainly_equal(v, &r)) {
                out.push(r);
            }
            out.len() <= MAX_CASES
        }) {
            return None;
        }
        Some(V::U(Some(Rc::new(out))))
    }

    /// Interval arithmetic and comparisons when at least one operand is
    /// `V::IntRange`: `Some(Ok_opt)` means handled (with `None` signaling a
    /// possible type or overflow error), `None` delegates to the generic path.
    fn op_int_range(&self, op: B, vs: &[V]) -> Option<Option<V>> {
        match vs {
            [V::IntRange(a, b)] if op == B::Neg => {
                let lo = -(*b as i128);
                let hi = -(*a as i128);
                Some(checked_int_range(lo, hi))
            }
            [V::IntRange(..)] => Some(None),
            [x, y] if matches!(x, V::IntRange(..)) || matches!(y, V::IntRange(..)) => {
                if let (Some((a, b)), Some((c, d))) = (int_bounds_of(x), int_bounds_of(y)) {
                    return Some(self.int_binop(op, (a, b), (c, d)));
                }
                if matches!(op, B::In | B::NotIn) {
                    if let (V::IntRange(a, b), V::K(set)) = (x, y) {
                        return self.int_range_in(*a, *b, set, op == B::NotIn);
                    }
                }
                // Comparing or operating on an integer range with a known non-int
                // fails in TLC (except `x \in {}` handled above).
                if matches!(x, V::K(_)) || matches!(y, V::K(_)) {
                    return Some(None);
                }
                None
            }
            _ => None,
        }
    }

    fn int_binop(&self, op: B, (a, b): (i64, i64), (c, d): (i64, i64)) -> Option<V> {
        let (a128, b128, c128, d128) = (a as i128, b as i128, c as i128, d as i128);
        match op {
            B::Plus => checked_int_range(a128 + c128, b128 + d128),
            B::Minus => checked_int_range(a128 - d128, b128 - c128),
            B::Mul => {
                let ps = [a128 * c128, a128 * d128, b128 * c128, b128 * d128];
                checked_int_range(*ps.iter().min().unwrap(), *ps.iter().max().unwrap())
            }
            B::Lt => Some(if b < c {
                V::K(Value::Bool(true))
            } else if a >= d {
                V::K(Value::Bool(false))
            } else {
                self.unknown_bool()
            }),
            B::Le => Some(if b <= c {
                V::K(Value::Bool(true))
            } else if a > d {
                V::K(Value::Bool(false))
            } else {
                self.unknown_bool()
            }),
            B::Gt => Some(if a > d {
                V::K(Value::Bool(true))
            } else if b <= c {
                V::K(Value::Bool(false))
            } else {
                self.unknown_bool()
            }),
            B::Ge => Some(if a >= d {
                V::K(Value::Bool(true))
            } else if b < c {
                V::K(Value::Bool(false))
            } else {
                self.unknown_bool()
            }),
            B::Eq => Some(if b < c || d < a {
                V::K(Value::Bool(false))
            } else if a == b && c == d && a == c {
                V::K(Value::Bool(true))
            } else {
                self.unknown_bool()
            }),
            B::Neq => Some(if b < c || d < a {
                V::K(Value::Bool(true))
            } else if a == b && c == d && a == c {
                V::K(Value::Bool(false))
            } else {
                self.unknown_bool()
            }),
            _ => None,
        }
    }

    fn int_range_in(&self, a: i64, b: i64, set: &Value, negate: bool) -> Option<Option<V>> {
        let decide = |known: Option<bool>| {
            Some(match known {
                Some(res) => V::K(Value::Bool(res ^ negate)),
                None => self.unknown_bool(),
            })
        };
        match set {
            Value::Interval(slo, shi) => {
                let res = if *slo > *shi || b < *slo || a > *shi {
                    Some(false)
                } else if a >= *slo && b <= *shi {
                    Some(true)
                } else {
                    None
                };
                Some(decide(res))
            }
            Value::Set(es) if es.is_empty() => Some(decide(Some(false))),
            Value::Set(es) if es.iter().all(|e| matches!(e, Value::Int(_))) => {
                let first = es.first().unwrap().as_int().unwrap();
                let last = es.last().unwrap().as_int().unwrap();
                let res = if b < first || a > last { Some(false) } else { None };
                Some(decide(res))
            }
            _ => None,
        }
    }
}

fn int_val(lo: i64, hi: i64) -> V {
    if lo == hi {
        V::K(Value::Int(lo))
    } else {
        V::IntRange(lo, hi)
    }
}

fn int_bounds_of(v: &V) -> Option<(i64, i64)> {
    match v {
        V::K(Value::Int(i)) => Some((*i, *i)),
        V::IntRange(lo, hi) => Some((*lo, *hi)),
        _ => None,
    }
}

fn checked_int_range(lo: i128, hi: i128) -> Option<V> {
    if lo < i32::MIN as i128 || hi > i32::MAX as i128 {
        return None;
    }
    Some(int_val(lo as i64, hi as i64))
}

/// The values a value may have (while checking).
fn cases(v: &V) -> Option<Vec<Value>> {
    match v {
        V::K(v) => Some(vec![v.clone()]),
        V::IntRange(lo, hi) => {
            let len = (*hi as i128 - *lo as i128 + 1).max(0);
            if len > MAX_CASES as i128 {
                return None;
            }
            Some((*lo..=*hi).map(Value::Int).collect())
        }
        V::U(vs) => vs.as_ref().map(|vs| vs.to_vec()),
    }
}

/// Calls `f` on every combination of one value of each of `cs` (after
/// `args`) while it returns true; false if it returned false.
fn combinations<'v>(cs: &'v [Vec<Value>], args: &mut Vec<&'v Value>, f: &mut dyn FnMut(&[&Value]) -> bool) -> bool {
    let Some((first, rest)) = cs.split_first() else { return f(args) };
    for v in first {
        args.push(v);
        let ok = combinations(rest, args, f);
        args.pop();
        if !ok {
            return false;
        }
    }
    true
}

/// A strict builtin on known values, as the interpreter evaluates it
/// (`None` where that fails).
fn apply(op: B, a: &[&Value]) -> Option<Value> {
    let int = |v: &Value| if let Value::Int(i) = v { Some(*i) } else { None };
    let boolean = |v: &Value| if let Value::Bool(b) = v { Some(*b) } else { None };
    Some(match (op, a) {
        (B::Eq, [x, y]) => Value::Bool(order::eq_tlc(x, y).ok()?),
        (B::Neq, [x, y]) => Value::Bool(!order::eq_tlc(x, y).ok()?),
        (B::In, [x, s]) => Value::Bool(ops::member(x, s).ok()?),
        (B::NotIn, [x, s]) => Value::Bool(!ops::member(x, s).ok()?),
        (B::Not, [x]) => Value::Bool(!boolean(x)?),
        (B::Equiv, [x, y]) => Value::Bool(boolean(x)? == boolean(y)?),
        (B::Lt, [x, y]) => Value::Bool(int(x)? < int(y)?),
        (B::Le, [x, y]) => Value::Bool(int(x)? <= int(y)?),
        (B::Gt, [x, y]) => Value::Bool(int(x)? > int(y)?),
        (B::Ge, [x, y]) => Value::Bool(int(x)? >= int(y)?),
        (B::Plus, [x, y]) => Value::Int(arith::add(int(x)?, int(y)?).ok()?),
        (B::Minus, [x, y]) => Value::Int(arith::sub(int(x)?, int(y)?).ok()?),
        (B::Mul, [x, y]) => Value::Int(arith::mul(int(x)?, int(y)?).ok()?),
        (B::Neg, [x]) => Value::Int(arith::neg(int(x)?).ok()?),
        (B::DotDot, [x, y]) => ops::interval(int(x)?, int(y)?),
        _ => return None,
    })
}
