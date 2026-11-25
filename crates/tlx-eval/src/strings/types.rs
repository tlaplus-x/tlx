//! The type inference of `StringMakers::for_states`: which values may be
//! strings.

use std::collections::HashMap;

use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{Bound, BoundVars, DefId, DefKind, ExceptKey, Expr, ExprKind as H, LocalId, OpRef, VarId};
use tlx_value::Value;

use super::makes_strings;
use crate::env::{Binding, Env, OpVal};
use crate::interp::ConstVal;
use crate::Interp;

/// What the type inference knows about a value: whether it may be a string.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum Ty {
    /// No value.
    Bot,
    /// Not a string; the parameter covers its components: the values of a
    /// function (sequence, tuple, record) and the elements of a set (not
    /// the domain of a function: a record's are strings).
    Ns(Box<Ty>),
    /// Any value, a string included.
    Top,
}

/// Nesting depth of the types of the state variables (deeper is `Top`):
/// bounds the fixpoint iteration.
const DEPTH: usize = 6;

/// At most this many passes over the model to infer the types of the
/// variables (a pass only grows them; `DEPTH` bounds their height).
const MAX_PASSES: usize = 4 * DEPTH;

/// At most this many expressions analyzed per pass or query (definitions
/// are expanded at each application): the analysis fails beyond.
const BUDGET: usize = 1 << 20;

/// At most this many nested expansions of a definition that is not
/// recursive (through operator arguments); deeper ones are analyzed as
/// recursion.
const MAX_NESTED: usize = 4;

impl Ty {
    fn ns(c: Ty) -> Ty {
        Ty::Ns(Box::new(c))
    }

    /// A number, Boolean or model value.
    fn scalar() -> Ty {
        Ty::ns(Ty::Bot)
    }

    fn may_be_string(&self) -> bool {
        matches!(self, Ty::Top)
    }

    fn comp(&self) -> Ty {
        match self {
            Ty::Ns(c) => (**c).clone(),
            t => t.clone(),
        }
    }

    /// The components at nesting depth `k`.
    fn get(&self, k: usize) -> Ty {
        (0..k).fold(self.clone(), |t, _| t.comp())
    }

    fn join(self, o: Ty) -> Ty {
        match (self, o) {
            (Ty::Bot, t) | (t, Ty::Bot) => t,
            (Ty::Ns(a), Ty::Ns(b)) => Ty::ns(a.join(*b)),
            _ => Ty::Top,
        }
    }

    /// Joins `v` into the components at depth `k` (an EXCEPT).
    fn put(self, k: usize, v: Ty) -> Ty {
        match self {
            t if k == 0 => t.join(v),
            Ty::Ns(c) => Ty::ns(c.put(k - 1, v)),
            t => t,
        }
    }

    fn truncate(self, depth: usize) -> Ty {
        match self {
            Ty::Ns(_) if depth == 0 => Ty::Top,
            Ty::Ns(c) => Ty::ns(c.truncate(depth - 1)),
            t => t,
        }
    }

    fn of_value(v: &Value, depth: usize) -> Ty {
        let all = |vs: &mut dyn Iterator<Item = &Value>| Ty::ns(vs.fold(Ty::Bot, |t, x| t.join(Ty::of_value(x, depth - 1))));
        match v {
            Value::Str(_) => Ty::Top,
            Value::Bool(_) | Value::Int(_) | Value::ModelValue(_) => Ty::scalar(),
            _ if depth == 0 => Ty::Top,
            Value::Interval(..) => Ty::ns(Ty::scalar()),
            Value::Set(es) | Value::Tuple(es) => all(&mut es.iter()),
            Value::Record(fs) => all(&mut fs.iter().map(|(_, x)| x)),
            Value::Fcn(ps, _) => all(&mut ps.iter().map(|(_, x)| x)),
            Value::LazySet(_) | Value::LazyFcn(_) => Ty::ns(Ty::Top),
        }
    }
}

/// The types of the state variables of a model (see
/// `StringMakers::for_states`): the least fixpoint of the values assigned
/// to them in the initial predicate and the actions, given their types.
/// `None` if the analysis fails.
pub(super) fn infer_vars(ip: &Interp, init: &Expr, actions: &[(&Expr, &Env)]) -> Option<Vec<Ty>> {
    let mut vars = vec![Ty::Bot; ip.prog.vars.len()];
    for _ in 0..MAX_PASSES {
        let mut t = Typer::new(ip, &vars, true);
        t.init = true;
        t.expr(init);
        t.init = false;
        // (Generic analyses compare assignment targets by the mode.)
        t.generic.clear();
        for (a, env) in actions {
            t.root = (*env).clone();
            t.expr(a);
        }
        if t.failed {
            return None;
        }
        let next: Vec<Ty> = t.assigned.into_iter().map(|x| x.truncate(DEPTH)).collect();
        if next == vars {
            return Some(vars);
        }
        vars = next;
    }
    None
}

/// Whether evaluating `e` in `env` may create strings, given the types of
/// the variables; `None` if the analysis fails.
pub(super) fn creates_strings(ip: &Interp, vars: &[Ty], e: &Expr, env: &Env) -> Option<bool> {
    let mut t = Typer::new(ip, vars, false);
    t.root = env.clone();
    t.expr(e);
    (!t.failed).then_some(t.strings)
}

/// What a local name is bound to.
#[derive(Clone)]
enum Bind {
    /// A value; for an operator parameter, the assignment target its
    /// argument denotes (passed by name: `Send(v) == v' = ...`).
    Val(Ty, Tgt),
    /// An operator argument.
    Op(OpBind),
    /// A call-by-name argument in the environment of a root expression
    /// (an action instance: `\E p \in P : A(p)` split by TLC's rules).
    Name(Expr, Env),
    /// A parameter of a definition analyzed for any arguments.
    Opaque,
}

#[derive(Clone)]
enum OpBind {
    Ref(OpRef),
    Lambda(Vec<LocalId>, Expr),
}

/// An argument of an operator application, as recursion compares them.
#[derive(Clone, PartialEq)]
enum Arg {
    Val(Ty, Tgt),
    Op(OpRef),
    Lambda(*const H),
}

impl Arg {
    /// Whether an analysis with argument `o` covers this one, comparing the
    /// assignment targets in `parts` (see `Tgt::within`).
    fn within(&self, o: &Arg, parts: Parts) -> bool {
        match (self, o) {
            (Arg::Val(t, g), Arg::Val(o, h)) => g.within(h, parts) && t.clone().join(o.clone()) == *o,
            (a, o) => a == o,
        }
    }
}

/// Which assignment targets of arguments matter: as the left-hand side of
/// an assignment in an action (`target`), as a primed or initial-predicate
/// variable (`var`).
#[derive(Clone, Copy)]
struct Parts {
    target: bool,
    var: bool,
}

/// Whether an expression denotes a variable as an assignment target.
#[derive(Clone, Copy, PartialEq)]
enum Target {
    Var(VarId),
    No,
    Unknown,
}

/// The assignment targets an argument expression denotes: in an action
/// (`target`) and in the initial predicate (`var_of`).
#[derive(Clone, Copy, PartialEq)]
struct Tgt {
    target: Target,
    var: Target,
}

impl Tgt {
    const NONE: Tgt = Tgt { target: Target::No, var: Target::No };

    /// Whether an analysis with an argument denoting `o` covers this one in
    /// `parts`. (An argument that is no assignment target is covered by
    /// one that is: that analysis only records more assignments.)
    fn within(&self, o: &Tgt, parts: Parts) -> bool {
        let within = |a: Target, b: Target| a == Target::No || a == b;
        (!parts.target || within(self.target, o.target)) && (!parts.var || within(self.var, o.var))
    }
}

/// Abstract interpretation of expressions over `Ty`: their types, whether
/// they may create strings (`strings`) and, when inferring the types of
/// the variables, the values assigned to them (`assigned`; the targets as
/// `enumerate` recognizes them, followed through parameters passed by name
/// and 0-ary definitions). Definitions are expanded at each application,
/// their parameters bound to the types of the arguments; a recursive
/// definition is analyzed once for arguments of any type (`generic_def`),
/// as are operators applied by builtins. Anything the analysis does not
/// follow (an assignment to or the application of a parameter of such a
/// definition, too many expressions) makes it fail (`failed`): the caller
/// then falls back to the syntactic analysis.
struct Typer<'a> {
    ip: &'a Interp,
    vars: &'a [Ty],
    /// Collecting assignments (inferring the types of the variables).
    collect: bool,
    assigned: Vec<Ty>,
    /// In the initial predicate (unprimed variables are assigned).
    init: bool,
    strings: bool,
    failed: bool,
    env: Vec<(LocalId, Bind)>,
    /// The environment of the root expression (outside `env`).
    root: Env,
    /// The values `@` stands for.
    at: Vec<Ty>,
    /// The definitions being expanded, with their arguments (`args`).
    expanding: Vec<(DefId, Option<Vec<Arg>>)>,
    /// The definitions analyzed for any arguments (`generic_def`), and
    /// their arguments.
    generic: HashMap<DefId, Option<Vec<Arg>>>,
    /// Applications of global definitions to value arguments (only when not
    /// collecting assignments, which depend on the arguments themselves).
    memo: HashMap<(DefId, Vec<Ty>), (Ty, bool)>,
    budget: usize,
}

impl<'a> Typer<'a> {
    fn new(ip: &'a Interp, vars: &'a [Ty], collect: bool) -> Typer<'a> {
        let assigned = if collect { vars.to_vec() } else { Vec::new() };
        Typer {
            ip,
            vars,
            collect,
            assigned,
            init: false,
            strings: false,
            failed: false,
            env: Vec::new(),
            root: Env::default(),
            at: Vec::new(),
            expanding: Vec::new(),
            generic: HashMap::new(),
            memo: HashMap::new(),
            budget: BUDGET,
        }
    }

    fn lookup(&self, l: LocalId) -> Option<Bind> {
        self.lookup_in(l, None)
    }

    /// The binding of `l`: in `env`, then in the root environment; or, given
    /// `root` (the environment of a call-by-name argument of the root),
    /// only there.
    fn lookup_in(&self, l: LocalId, root: Option<&Env>) -> Option<Bind> {
        if root.is_none() {
            if let Some((_, b)) = self.env.iter().rev().find(|(x, _)| *x == l) {
                return Some(b.clone());
            }
        }
        Some(match root.unwrap_or(&self.root).lookup(l)? {
            Binding::Val(v) => Bind::Val(Ty::of_value(v, DEPTH), Tgt::NONE),
            Binding::Op(OpVal::Ref(r)) => Bind::Op(OpBind::Ref(*r)),
            b @ (Binding::Thunk(_) | Binding::Name(..)) => match b.by_name(&self.ip.prog) {
                Some((e, env)) => Bind::Name(e.clone(), env.clone()),
                None => Bind::Opaque,
            },
            Binding::Op(OpVal::Lambda { .. }) | Binding::LetCache(_) => Bind::Opaque,
        })
    }

    /// Binds the variables of `bounds` (each to the elements of its set).
    fn bind_bounds(&mut self, bounds: &[Bound]) {
        for b in bounds {
            let elem = self.expr(&b.set).comp();
            self.bind_vars(&b.vars, elem);
        }
    }

    fn bind_vars(&mut self, vars: &BoundVars, elem: Ty) {
        let t = match vars {
            BoundVars::Many(_) => elem,
            BoundVars::Tuple(_) => elem.comp(),
        };
        for l in vars.locals() {
            self.env.push((*l, Bind::Val(t.clone(), Tgt::NONE)));
        }
    }

    /// Binds the parameters of an operator to the arguments.
    fn bind_params(&mut self, params: &[LocalId], args: &[Expr]) {
        let binds: Vec<Bind> = (0..params.len())
            .map(|i| match args.get(i) {
                Some(a) => match &*a.kind {
                    H::OpArg(r) => self.op_bind(*r),
                    H::Lambda { params, body } => Bind::Op(OpBind::Lambda(params.clone(), body.clone())),
                    _ => {
                        let g = self.tgt(a);
                        Bind::Val(self.expr(a), g)
                    }
                },
                None => Bind::Opaque,
            })
            .collect();
        self.env.extend(params.iter().copied().zip(binds));
    }

    /// The arguments bound to parameters in `env[n..]` (none if one is
    /// opaque).
    fn args(&self, n: usize) -> Option<Vec<Arg>> {
        self.env[n..]
            .iter()
            .map(|(_, b)| match b {
                Bind::Val(t, g) => Some(Arg::Val(t.clone(), *g)),
                Bind::Op(OpBind::Ref(r)) => Some(Arg::Op(*r)),
                Bind::Op(OpBind::Lambda(_, body)) => Some(Arg::Lambda(std::sync::Arc::as_ptr(&body.kind))),
                Bind::Name(..) | Bind::Opaque => None,
            })
            .collect()
    }

    fn op_bind(&self, r: OpRef) -> Bind {
        match r {
            OpRef::Param(l) => self.lookup(l).unwrap_or(Bind::Opaque),
            r => Bind::Op(OpBind::Ref(r)),
        }
    }

    fn join_all<'e>(&mut self, es: impl IntoIterator<Item = &'e Expr>) -> Ty {
        es.into_iter().fold(Ty::Bot, |t, e| {
            let x = self.expr(e);
            t.join(x)
        })
    }

    fn expr(&mut self, e: &Expr) -> Ty {
        if self.failed {
            return Ty::Top;
        }
        if self.budget == 0 {
            self.failed = true;
            return Ty::Top;
        }
        self.budget -= 1;
        let n = self.env.len();
        let t = match &*e.kind {
            H::Num(_) | H::Decimal(_) | H::Bool(_) => Ty::scalar(),
            H::Str(_) => Ty::Top,
            H::Var(v) => self.vars[v.idx()].clone(),
            H::InstVar { subst, .. } => self.expr(subst),
            H::Const(c) => match &self.ip.consts[c.idx()] {
                Some(ConstVal::Value(v)) => Ty::of_value(v, DEPTH),
                Some(ConstVal::Def(d)) => self.call(*d, &[]),
                _ => Ty::Top,
            },
            H::Local(l) => match self.lookup(*l) {
                Some(Bind::Val(t, _)) => t,
                Some(Bind::Name(e, env)) => {
                    // (In its own environment only.)
                    let root = std::mem::replace(&mut self.root, env);
                    let locals = std::mem::take(&mut self.env);
                    let t = self.expr(&e);
                    self.env = locals;
                    self.root = root;
                    t
                }
                _ => Ty::Top,
            },
            H::Apply { op, args } => self.apply(*op, args),
            H::Builtin { op, args } => self.builtin(*op, args),
            H::OpArg(_) | H::Lambda { .. } => {
                self.op_generic(e);
                Ty::Top
            }
            H::And(es) | H::Or(es) => {
                self.join_all(es);
                Ty::scalar()
            }
            H::Quant { bounds, body, .. } => {
                self.bind_bounds(bounds);
                self.expr(body);
                Ty::scalar()
            }
            H::QuantUnbounded { vars, body, .. } | H::TemporalQuant { vars, body, .. } => {
                self.env.extend(vars.iter().map(|l| (*l, Bind::Val(Ty::Top, Tgt::NONE))));
                self.expr(body);
                Ty::scalar()
            }
            H::Choose { vars, set, body } => {
                let elem = match set {
                    Some(s) => self.expr(s).comp(),
                    None => Ty::Top,
                };
                self.bind_vars(vars, elem.clone());
                self.expr(body);
                elem
            }
            H::If { cond, then, els } => {
                self.expr(cond);
                self.join_all([then, els])
            }
            H::Case { arms, other } => {
                let mut t = Ty::Bot;
                for (g, v) in arms {
                    self.expr(g);
                    let x = self.expr(v);
                    t = t.join(x);
                }
                match other {
                    Some(o) => {
                        let x = self.expr(o);
                        t.join(x)
                    }
                    None => t,
                }
            }
            H::Let { body, .. } => self.expr(body),
            H::SetEnum(es) | H::Tuple(es) => Ty::ns(self.join_all(es)),
            H::SetFilter { bound, pred } => {
                let s = self.expr(&bound.set);
                self.bind_vars(&bound.vars, s.comp());
                self.expr(pred);
                s
            }
            H::SetMap { expr, bounds } => {
                self.bind_bounds(bounds);
                Ty::ns(self.expr(expr))
            }
            H::FnConstruct { bounds, body } => {
                self.bind_bounds(bounds);
                Ty::ns(self.expr(body))
            }
            H::FnApp { func, args } => {
                let f = self.expr(func);
                self.join_all(args);
                f.comp()
            }
            H::FnSet { domain, range } => {
                self.expr(domain);
                Ty::ns(Ty::ns(self.expr(range).comp()))
            }
            H::Record(fs) => Ty::ns(self.join_all(fs.iter().map(|(_, v)| v))),
            H::RecordSet(fs) => {
                let mut t = Ty::Bot;
                for (_, v) in fs {
                    let x = self.expr(v).comp();
                    t = t.join(x);
                }
                Ty::ns(Ty::ns(t))
            }
            H::Field { record, .. } => self.expr(record).comp(),
            H::Except { base, updates } => {
                let mut t = self.expr(base);
                for (keys, v) in updates {
                    for k in keys {
                        if let ExceptKey::Index(ix) = k {
                            self.join_all(ix);
                        }
                    }
                    self.at.push(t.get(keys.len()));
                    let x = self.expr(v);
                    self.at.pop();
                    t = t.put(keys.len(), x);
                }
                t
            }
            H::At => self.at.last().cloned().unwrap_or(Ty::Top),
            H::BoxAction { action, sub } | H::AngleAction { action, sub } | H::Fairness { action, sub, .. } => {
                self.join_all([action, sub]);
                Ty::scalar()
            }
        };
        self.env.truncate(n);
        t
    }

    fn apply(&mut self, op: OpRef, args: &[Expr]) -> Ty {
        match op {
            OpRef::Def(d) => self.call(d, args),
            OpRef::Builtin(b) => self.builtin(b, args),
            OpRef::Const(c) => match self.ip.const_op_ref(c) {
                Some(r @ (OpRef::Def(_) | OpRef::Builtin(_))) => self.apply(r, args),
                _ => {
                    self.failed = true;
                    Ty::Top
                }
            },
            OpRef::Param(l) => match self.lookup(l) {
                Some(Bind::Op(OpBind::Ref(r))) => self.apply(r, args),
                Some(Bind::Op(OpBind::Lambda(params, body))) => {
                    let n = self.env.len();
                    self.bind_params(&params, args);
                    let t = self.expr(&body);
                    self.env.truncate(n);
                    t
                }
                _ => {
                    self.failed = true;
                    Ty::Top
                }
            },
        }
    }

    /// An application of definition `d`.
    fn call(&mut self, d: DefId, args: &[Expr]) -> Ty {
        let ip = self.ip;
        let d = ip.redirect_def(d);
        let def = &ip.prog.defs[d.idx()];
        if let Some(v) = ip.def_value.get(&d) {
            return Ty::of_value(v, DEPTH);
        }
        if let Some(b) = def.builtin {
            return self.builtin(b, args);
        }
        if ip.def_const[d.idx()] {
            if let Some(Ok(v)) = ip.const_cache[d.idx()].get() {
                return Ty::of_value(v, DEPTH);
            }
        }
        let body = match &def.kind {
            DefKind::Pending => {
                self.strings = true;
                self.join_all(args);
                return Ty::Top;
            }
            DefKind::Op(body) | DefKind::Fn { body, .. } => body,
        };
        // (A definition that is not recursive can still be expanded inside
        // itself, through an operator argument: `ReduceSeq(LAMBDA ...)` with
        // another `ReduceSeq` in the LAMBDA.)
        let nested = self.expanding.iter().filter(|(x, _)| *x == d).count();
        if nested > 0 && (ip.is_recursive(d) || nested >= MAX_NESTED) {
            // Recursion. (A recursive function definition: its body is being
            // analyzed.)
            let n = self.env.len();
            self.bind_params(&def.params, args);
            let inner = self.args(n);
            self.env.truncate(n);
            if let DefKind::Fn { .. } = def.kind {
                return Ty::ns(Ty::Top);
            }
            // An operator applied to arguments an enclosing application
            // covers (values of smaller types, the same operators): that
            // analysis covers this one too (the analysis is monotone).
            // Otherwise analyzed for any arguments.
            // (SANY rejects a primed parameter of a recursive operator: its
            // arguments are only assignment targets as left-hand sides in
            // an action, or in the initial predicate.)
            let parts = if ip.is_recursive(d) { Parts { target: !self.init, var: self.init } } else { Parts { target: true, var: true } };
            let covers = |outer: &Option<Vec<Arg>>| match (outer, &inner) {
                (Some(o), Some(inner)) => o.len() == inner.len() && o.iter().zip(inner).all(|(o, a)| a.within(o, parts)),
                _ => false,
            };
            let covered = !ip.def_by_name[d.idx()]
                && (self.expanding.iter().any(|(x, outer)| *x == d && covers(outer)) || self.generic.get(&d).is_some_and(covers));
            if !covered {
                if self.generic.contains_key(&d) {
                    self.failed = true;
                } else {
                    self.generic_def(d, args);
                }
            }
            return Ty::Top;
        }
        let n = self.env.len();
        self.bind_params(&def.params, args);
        let frame = self.args(n);
        let key = if self.collect || ip.prog.def_is_let(d) {
            None
        } else {
            let ts: Option<Vec<Ty>> = frame.iter().flatten().map(|a| if let Arg::Val(t, _) = a { Some(t.clone()) } else { None }).collect();
            frame.as_ref().and(ts).map(|ts| (d, ts))
        };
        if let Some((t, s)) = key.as_ref().and_then(|k| self.memo.get(k)).cloned() {
            self.strings |= s;
            self.env.truncate(n);
            return t;
        }
        let outer = std::mem::replace(&mut self.strings, false);
        self.expanding.push((d, frame));
        let t = match &def.kind {
            DefKind::Fn { bounds, .. } => {
                self.bind_bounds(bounds);
                Ty::ns(self.expr(body))
            }
            _ => self.expr(body),
        };
        self.expanding.pop();
        self.env.truncate(n);
        if let Some(k) = key {
            self.memo.insert(k, (t.clone(), self.strings));
        }
        self.strings |= outer;
        t
    }

    /// Definition `d` applied to `args` (none: values), their values of
    /// any types.
    fn generic_def(&mut self, d: DefId, args: &[Expr]) {
        let ip = self.ip;
        let d = ip.redirect_def(d);
        let def = &ip.prog.defs[d.idx()];
        if ip.def_value.contains_key(&d) || self.generic.contains_key(&d) {
            return;
        }
        if let Some(b) = def.builtin {
            self.strings |= makes_strings(b);
            return;
        }
        let binds: Vec<Bind> = def
            .params
            .iter()
            .enumerate()
            .map(|(i, l)| match args.get(i).map(|a| (a, &*a.kind)) {
                Some((_, H::OpArg(r))) => self.op_bind(*r),
                Some((_, H::Lambda { params, body })) => Bind::Op(OpBind::Lambda(params.clone(), body.clone())),
                None if ip.prog.locals[l.idx()].arity > 0 => Bind::Opaque,
                Some((a, _)) => Bind::Val(Ty::Top, self.tgt(a)),
                None => Bind::Val(Ty::Top, Tgt::NONE),
            })
            .collect();
        let n = self.env.len();
        self.env.extend(def.params.iter().copied().zip(binds));
        let frame = self.args(n);
        self.generic.insert(d, frame.clone());
        self.expanding.push((d, frame));
        match &def.kind {
            DefKind::Pending => self.strings = true,
            DefKind::Op(body) => {
                self.expr(body);
            }
            DefKind::Fn { bounds, body } => {
                self.bind_bounds(bounds);
                self.expr(body);
            }
        }
        self.expanding.pop();
        self.env.truncate(n);
    }

    /// An operator argument (`e` is an `OpArg` or a LAMBDA) applied to any
    /// arguments: by a builtin, or where it is not an operator's argument.
    fn op_generic(&mut self, e: &Expr) {
        let (params, body) = match &*e.kind {
            H::Lambda { params, body } => (params.clone(), body.clone()),
            H::OpArg(r) => match self.op_bind(*r) {
                Bind::Op(OpBind::Ref(OpRef::Def(d))) => return self.generic_def(d, &[]),
                Bind::Op(OpBind::Ref(OpRef::Builtin(b))) => return self.strings |= makes_strings(b),
                Bind::Op(OpBind::Ref(OpRef::Const(c))) => {
                    return match self.ip.const_op_ref(c) {
                        Some(OpRef::Def(d)) => self.generic_def(d, &[]),
                        Some(OpRef::Builtin(b)) => self.strings |= makes_strings(b),
                        _ => self.failed = true,
                    };
                }
                Bind::Op(OpBind::Lambda(params, body)) => (params, body),
                _ => return self.failed = true,
            },
            _ => {
                self.expr(e);
                return;
            }
        };
        let n = self.env.len();
        self.env.extend(params.iter().map(|l| (*l, Bind::Val(Ty::Top, Tgt::NONE))));
        self.expr(&body);
        self.env.truncate(n);
    }

    fn tgt(&self, a: &Expr) -> Tgt {
        Tgt { target: self.target(a, None), var: self.var_of(a, None) }
    }

    /// The variable `lhs` assigns as the left-hand side of `=`, `\in` or
    /// `\subseteq` (as `enumerate` recognizes it), in environment `root`.
    fn target(&self, lhs: &Expr, root: Option<&Env>) -> Target {
        if self.init {
            return self.var_of(lhs, root);
        }
        match &*lhs.kind {
            H::Builtin { op: B::Prime, args } => self.var_of(&args[0], root),
            H::Local(l) => match self.lookup_in(*l, root) {
                Some(Bind::Val(_, g)) => g.target,
                Some(Bind::Name(a, env)) => self.target(&a, Some(&env)),
                Some(Bind::Opaque) => Target::Unknown,
                _ => Target::No,
            },
            H::Apply { op: OpRef::Def(d), args } if args.is_empty() => match self.ip.plain_op_body(*d) {
                Some((_, body)) => self.target(body, root),
                None => Target::No,
            },
            _ => Target::No,
        }
    }

    fn var_of(&self, e: &Expr, root: Option<&Env>) -> Target {
        match &*e.kind {
            H::Var(v) => Target::Var(*v),
            H::Local(l) => match self.lookup_in(*l, root) {
                Some(Bind::Val(_, g)) => g.var,
                Some(Bind::Name(a, env)) => self.var_of(&a, Some(&env)),
                Some(Bind::Opaque) => Target::Unknown,
                _ => Target::No,
            },
            H::Apply { op: OpRef::Def(d), args } if args.is_empty() => match self.ip.plain_op_body(*d) {
                Some((_, body)) => self.var_of(body, root),
                None => Target::No,
            },
            _ => Target::No,
        }
    }

    fn builtin(&mut self, op: B, args: &[Expr]) -> Ty {
        let mut ts = Vec::with_capacity(args.len());
        for a in args {
            ts.push(match &*a.kind {
                H::OpArg(_) | H::Lambda { .. } => {
                    self.op_generic(a);
                    Ty::Top
                }
                _ => self.expr(a),
            });
        }
        let arg = |i: usize| ts.get(i).cloned().unwrap_or(Ty::Top);
        if self.collect && matches!(op, B::Eq | B::In | B::SubsetEq) && !args.is_empty() {
            match self.target(&args[0], None) {
                Target::Var(v) => {
                    let t = match op {
                        B::Eq => arg(1),
                        B::In => arg(1).comp(),
                        _ => Ty::ns(arg(1).comp()),
                    };
                    let a = std::mem::replace(&mut self.assigned[v.idx()], Ty::Bot);
                    self.assigned[v.idx()] = a.join(t);
                }
                Target::Unknown => self.failed = true,
                Target::No => {}
            }
        }
        let comps = ts.iter().fold(Ty::Bot, |t, x| t.join(x.comp()));
        match op {
            // A string only from strings (`\o` of a string and anything else
            // fails), a sequence from sequences.
            B::Concat if arg(0).may_be_string() && arg(1).may_be_string() => {
                self.strings = true;
                Ty::Top
            }
            B::Concat => Ty::ns(comps),
            B::Tail | B::SubSeq if arg(0).may_be_string() => {
                self.strings = true;
                Ty::Top
            }
            B::Tail | B::SubSeq | B::SelectSeq | B::SortSeq | B::Prime | B::TLCEval | B::TLCCache => arg(0),
            // A string only from three strings (TLC's `StringUtils.replace`);
            // from sequences its elements are reused, so no string is created.
            B::ReplaceAllSubSeqs if arg(0).may_be_string() && arg(1).may_be_string() && arg(2).may_be_string() => {
                self.strings = true;
                Ty::Top
            }
            // Otherwise the result may be `r` or `t` themselves (the
            // definition's first two guards) or a sequence of their elements.
            B::ReplaceAllSubSeqs => Ty::ns(arg(0).comp().join(arg(2).comp())).join(arg(0)).join(arg(2)),
            op if makes_strings(op) => {
                self.strings = true;
                Ty::Top
            }
            B::Eq
            | B::Neq
            | B::In
            | B::NotIn
            | B::Not
            | B::Implies
            | B::Equiv
            | B::Unchanged
            | B::Enabled
            | B::SubsetEq
            | B::Always
            | B::Eventually
            | B::LeadsTo
            | B::Compose
            | B::WhilePlus => Ty::scalar(),
            B::Lt | B::Gt | B::Le | B::Ge | B::IsFiniteSet | B::Assert | B::PrintT | B::TLCSet | B::BagIn | B::IsABag | B::SqSubseteq => {
                Ty::scalar()
            }
            B::Plus
            | B::Minus
            | B::Mul
            | B::Pow
            | B::Div
            | B::Mod
            | B::Neg
            | B::Len
            | B::Cardinality
            | B::Gcd
            | B::Atoi
            | B::Choose
            | B::JavaTime
            | B::BagCardinality
            | B::CopiesIn => Ty::scalar(),
            B::Nat | B::Int | B::DotDot | B::Boolean | B::EmptyBag => Ty::ns(Ty::scalar()),
            B::StringSet | B::Domain => Ty::ns(Ty::Top),
            B::Subset | B::Seq | B::Permutations => Ty::ns(Ty::ns(arg(0).comp())),
            B::Union => Ty::ns(arg(0).comp().comp()),
            B::Cup | B::Cap | B::SetMinus | B::AtAt => Ty::ns(comps),
            B::Times => Ty::ns(Ty::ns(comps)),
            B::Append => Ty::ns(arg(0).comp().join(arg(1))),
            B::Head | B::RandomElement | B::SetMax | B::SetMin => arg(0).comp(),
            B::SetToSeq => Ty::ns(arg(0).comp()),
            B::Print => arg(1),
            B::ColonGt => Ty::ns(arg(1)),
            _ => Ty::Top,
        }
    }
}
