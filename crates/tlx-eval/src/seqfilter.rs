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

use std::rc::Rc;

use tlx_front::ast::QuantKind;
use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{BoundVars, DefKind, Expr, ExprKind as H, LocalId, OpRef};
use tlx_value::{arith, ops, order, Value};

use crate::env::{Binding, Env};
use crate::interp::{ConstVal, Interp};

/// At most this many nested expansions of definitions in the predicate.
const MAX_INLINE: usize = 8;

/// At most this many nodes in the compiled predicate.
const MAX_NODES: usize = 4096;

/// At most this many node evaluations in one evaluation of the predicate
/// with every component unknown (`SeqPred::check`).
const MAX_STEPS: usize = 1 << 20;

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

/// What a name stands for while compiling.
#[derive(Clone)]
enum Name {
    /// The filtered sequence.
    Seq,
    Slot(usize),
    /// A parameter of an expanded definition: its argument, passed by name
    /// (compiled in the scope `names[..n]`).
    Arg(Expr, usize),
}

struct Compiler<'a> {
    ip: &'a Interp,
    env: &'a Env,
    names: Vec<(LocalId, Name)>,
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
        let mut c = Compiler { ip, env, names: vec![(*x, Name::Seq)], slots: 0, quants: 0, nodes: 0, depth: 0 };
        let root = c.expr(pred)?;
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
        if !self.check(n, range) {
            return Ok(None);
        }
        let mut ev = Eval {
            n,
            prefix: Vec::with_capacity(n),
            slots: vec![Value::Bool(false); self.slots],
            sets: vec![Vec::new(); self.quants],
            check: None,
            steps: 0,
        };
        let mut idx = Vec::with_capacity(n);
        self.walk(&mut ev, range, &mut idx, v).map(Some)
    }

    /// Whether no evaluation of the predicate on a sequence of
    /// `[1..n -> range]` errs (every component unknown, every branch some
    /// sequence may take).
    fn check(&self, n: usize, range: &[Value]) -> bool {
        let mut ev = Eval {
            n,
            prefix: Vec::new(),
            slots: vec![Value::Bool(false); self.slots],
            sets: vec![Vec::new(); self.quants],
            check: Some(range),
            steps: 0,
        };
        match ev.node(&self.root) {
            Some(V::K(Value::Bool(_))) => true,
            Some(V::U(Some(vs))) => vs.iter().all(|v| matches!(v, Value::Bool(_))),
            _ => false,
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

    /// What `l` stands for in the scope `names[..upto]`.
    fn lookup(&self, l: LocalId, upto: usize) -> Option<Name> {
        self.names[..upto].iter().rev().find(|(x, _)| *x == l).map(|(_, n)| n.clone())
    }

    /// Whether `e` denotes the filtered sequence (in `names[..upto]`).
    fn is_seq(&self, e: &Expr, upto: usize) -> bool {
        match &*e.kind {
            H::Local(l) => match self.lookup(*l, upto) {
                Some(Name::Seq) => true,
                Some(Name::Arg(a, at)) => self.is_seq(&a, at),
                _ => false,
            },
            _ => false,
        }
    }

    fn exprs(&mut self, es: &[Expr]) -> Option<Vec<Node>> {
        es.iter().map(|e| self.expr(e)).collect()
    }

    fn expr(&mut self, e: &Expr) -> Option<Node> {
        let n = match &*e.kind {
            H::Num(n) if *n <= i32::MAX as i128 => Node::Lit(Value::Int(*n as i64)),
            H::Bool(b) => Node::Lit(Value::Bool(*b)),
            H::Str(s) => Node::Lit(Value::Str(self.ip.syms.get(s))),
            H::SetEnum(es) => Node::SetEnum(self.exprs(es)?),
            H::Const(c) => match &self.ip.consts[c.idx()] {
                Some(ConstVal::Value(v)) => Node::Lit(v.clone()),
                _ => return None,
            },
            H::Local(l) => match self.lookup(*l, self.names.len()) {
                Some(Name::Slot(i)) => Node::Slot(i),
                Some(Name::Arg(a, at)) => {
                    let inner = self.names.split_off(at);
                    let r = self.expr(&a);
                    self.names.extend(inner);
                    return r;
                }
                Some(Name::Seq) => return None,
                None => match self.env.lookup(*l) {
                    Some(Binding::Val(v)) => Node::Lit(v.clone()),
                    _ => return None,
                },
            },
            H::FnApp { func, args } if self.is_seq(func, self.names.len()) => match args.as_slice() {
                [i] => Node::At(Box::new(self.expr(i)?)),
                _ => return None,
            },
            H::Builtin { op, args } | H::Apply { op: OpRef::Builtin(op), args } => return self.builtin(*op, args),
            H::Apply { op: OpRef::Def(d), args } => {
                let d = self.ip.redirect_def(*d);
                if self.ip.def_value.contains_key(&d) {
                    return None;
                }
                let def = &self.ip.prog.defs[d.idx()];
                if let Some(b) = def.builtin {
                    return self.builtin(b, args);
                }
                let DefKind::Op(body) = &def.kind else { return None };
                if self.depth >= MAX_INLINE || self.ip.is_recursive(d) || self.ip.prog.def_is_let(d) || def.params.len() != args.len() {
                    return None;
                }
                // The arguments are passed by name, in the scope of the
                // application (`names[..at]`). (The body cannot name the
                // locals of the application: local ids are unique per
                // binding site.)
                let at = self.names.len();
                for (p, a) in def.params.iter().zip(args) {
                    self.names.push((*p, Name::Arg(a.clone(), at)));
                }
                self.depth += 1;
                let r = self.expr(body);
                self.depth -= 1;
                self.names.truncate(at);
                return r;
            }
            H::And(es) => Node::And(self.exprs(es)?),
            H::Or(es) => Node::Or(self.exprs(es)?),
            H::If { cond, then, els } => Node::If(Box::new((self.expr(cond)?, self.expr(then)?, self.expr(els)?))),
            H::Quant { kind, bounds, body } => {
                let sets = bounds.iter().map(|b| self.expr(&b.set)).collect::<Option<Vec<_>>>()?;
                let n0 = self.names.len();
                let mut vars = Vec::new();
                for (k, b) in bounds.iter().enumerate() {
                    let BoundVars::Many(ls) = &b.vars else { return None };
                    for l in ls {
                        vars.push((self.slots, k));
                        self.names.push((*l, Name::Slot(self.slots)));
                        self.slots += 1;
                    }
                }
                let body = self.expr(body);
                self.names.truncate(n0);
                self.quants += 1;
                Node::Quant { id: self.quants - 1, exists: *kind == QuantKind::Exists, vars, sets, body: Box::new(body?) }
            }
            _ => return None,
        };
        self.node(n)
    }

    fn builtin(&mut self, op: B, args: &[Expr]) -> Option<Node> {
        if self.ip.builtin_override(op).is_some() {
            return None;
        }
        let n = match (op, args) {
            (B::Len, [s]) if self.is_seq(s, self.names.len()) => Node::Len,
            (B::Domain, [s]) if self.is_seq(s, self.names.len()) => Node::Domain,
            (B::Implies, [a, b]) => Node::Implies(Box::new(self.expr(a)?), Box::new(self.expr(b)?)),
            (
                B::Eq | B::Neq | B::Lt | B::Le | B::Gt | B::Ge | B::In | B::NotIn | B::Equiv | B::Plus | B::Minus | B::Mul | B::DotDot,
                [_, _],
            )
            | (B::Not | B::Neg, [_]) => Node::Op(op, self.exprs(args)?),
            _ => return None,
        };
        self.node(n)
    }
}

/// A value in three-valued evaluation.
#[derive(Clone)]
enum V {
    /// Known.
    K(Value),
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
                V::K(Value::Int(i)) if i >= 1 && i as usize <= self.n => match self.prefix.get(i as usize - 1) {
                    Some(v) => V::K(v.clone()),
                    None => self.unknown(|| self.check.unwrap_or_default().to_vec()),
                },
                _ => return None,
            },
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
                        (a, b) if self.check.is_none() => V::U(None),
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
                        V::U(_) => return None,
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
}

/// The values a value may have (while checking).
fn cases(v: &V) -> Option<Vec<Value>> {
    match v {
        V::K(v) => Some(vec![v.clone()]),
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
