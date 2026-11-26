//! Pre-resolved expression trees: what the interpreter decides about an
//! expression every time it evaluates it (which kind of node, which
//! built-in, whether a cfg override applies, the symbol of a string or
//! field name, the value of a literal) is decided once, when an expression
//! of the program is first evaluated (`Interp::code_of`), and the
//! evaluation runs on the result (`Interp::exec`). Kinds of expressions
//! without a node of their own are evaluated by the tree-walking evaluator
//! (`Node::Tree`, `Interp::eval_tree`), whose subexpressions come back here.
//! The values, errors (messages and locations) and evaluation order are the
//! tree-walker's: each node does what `eval_inner` does for its expression.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::*;
use tlx_value::{ops, Sym, Value};

use crate::apply::{apply_tail, field_tail, Cow};
use crate::builtins::{builtin1, compare2, is_compare2, is_plain1, is_plain2};
use crate::env::{Binding, Env};
use crate::error::EResult;
use crate::eval::{as_bool, fn_domain, BoundElems, Ctx, Elems, AT};
use crate::except::{self, Unchanged};
use crate::interp::local::{self, Slot};
use crate::interp::{ConstVal, Interp};
use crate::lazy::LambdaFcn;

/// An expression of the program, resolved for evaluation.
pub(crate) struct Code {
    node: Node,
    span: Span,
}

enum Node {
    /// A numeral, string or boolean.
    Lit(Value),
    /// A compound constant value (a set, tuple or record of literals): read
    /// from this thread's copy (`local`, slot `Slot::Hoist(2 * n)`) when
    /// owned, so that threads do not share its reference count.
    Shared(Value, usize),
    /// A closed constant expression (`Interp::closed`): its value is kept
    /// per thread (`local`, slot `Slot::Hoist(2 * n + KeepLazy)`) once
    /// computed, unless it is large (then the flag is set and it is computed
    /// at every use).
    Hoist(Box<Code>, usize, AtomicBool),
    Var(VarId),
    /// A bound local (also `@`).
    Local(LocalId),
    Const(ConstId),
    /// A 0-ary definition (`Interp::call_def`).
    Call0(DefId),
    /// A 0-ary definition the cfg assigns a value (`Def = value`; the
    /// definition after redirection).
    CfgDef(DefId),
    /// A 0-ary constant-level definition (`def_const`; the definition after
    /// redirection), not recursive.
    ConstDef(DefId),
    /// A 0-ary state-level definition memoized per state
    /// (`def_state_cacheable`; the definition after redirection), not
    /// recursive.
    StateDef(DefId),
    /// Any other application of an operator (`Interp::apply`).
    Apply(OpRef, Vec<Expr>),
    /// An application of a user-defined operator without operator
    /// parameters (`Interp::call_def_with_args`).
    Call(Box<Call>),
    /// A strict binary built-in (`is_plain2`) without a cfg override.
    Bin(B, Box<[Code; 2]>),
    /// `x \in {e1, ...}` (true) / `x \notin {e1, ...}`: the element's and the
    /// set elements' code.
    InEnum(bool, Box<Code>, Box<[Code]>),
    /// `S \cup {e}` / `S \ {e}` (`B::Cup` / `B::SetMinus` with a singleton
    /// set enumeration): the set's and the element's code.
    SetOne(B, Box<[Code; 2]>),
    /// A strict unary built-in (`is_plain1`) without a cfg override.
    Un(B, Box<Code>),
    Not(Box<Code>),
    /// Any other built-in (`Interp::builtin`).
    Builtin(B, Vec<Expr>),
    And(Box<[Code]>),
    Or(Box<[Code]>),
    /// `\E` (true) or `\A` over the bindings of the bounds.
    Quant(bool, Vec<Bound>, Box<Code>),
    /// Condition, then, else.
    If(Box<[Code; 3]>),
    Case(Box<[(Code, Code)]>, Option<Box<Code>>),
    Let(Box<[DefId]>, Box<Code>),
    SetEnum(Box<[Code]>),
    Tuple(Box<[Code]>),
    Record(Box<[(Sym, Code)]>),
    FnApp(Box<Code>, Box<[Code]>),
    Field(Box<Code>, Sym),
    /// `{x \in S : P}`: the bound (whose set is evaluated by its code), the
    /// predicate's expression (for a lazy filter) and code.
    SetFilter(Box<(Bound, Code, Expr, Code)>),
    /// `{e : x \in S, ...}`.
    SetMap(Vec<Bound>, Box<Code>),
    /// `[x \in S, ... |-> e]`: the bounds, the body's expression (for a lazy
    /// function) and code.
    FnConstruct(Box<(Vec<Bound>, Expr, Code)>),
    /// `CHOOSE x \in S : P`: the binder, the set's and the predicate's code.
    Choose(Box<(BoundVars, Code, Code)>),
    /// `[S -> T]`.
    FnSet(Box<[Code; 2]>),
    RecordSet(Box<[(Sym, Code)]>),
    /// `[f EXCEPT !p1 = e1, ...]`.
    Except(Box<Code>, Box<[(Box<[Key]>, Code)]>),
    /// Evaluated by the tree-walker.
    Tree(Expr),
}

/// `Node::Call`: what `call_def_with_args` decides from the definition.
struct Call {
    /// The definition (after cfg redirection).
    d: DefId,
    params: Box<[LocalId]>,
    /// The argument expressions (bound by name) and their code.
    exprs: Vec<Expr>,
    args: Box<[Code]>,
    recursive: bool,
    memo: bool,
    by_name: bool,
    defer_errors: bool,
    let_def: bool,
}

/// The most elements of a tuple built in place (`try_arc_slice`).
const SMALL: usize = 16;

/// A slice of the values `f(i)` for `i` in `0..n` (`n <= SMALL`; computed
/// in order) in one allocation: the values are kept on the stack first. On
/// an error the values made so far are dropped.
fn try_arc_slice<T>(n: usize, mut f: impl FnMut(usize) -> EResult<T>) -> EResult<Arc<[T]>> {
    let mut vals: [std::mem::MaybeUninit<T>; SMALL] = [const { std::mem::MaybeUninit::uninit() }; SMALL];
    for i in 0..n {
        match f(i) {
            Ok(v) => {
                vals[i].write(v);
            }
            Err(e) => {
                for v in &mut vals[..i] {
                    // SAFETY: the values before `i` were written above.
                    unsafe { v.assume_init_drop() };
                }
                return Err(e);
            }
        }
    }
    // SAFETY: each of the `n` values is read once; the exact-size
    // iterator makes one allocation.
    Ok((0..n).map(|k| unsafe { vals[k].assume_init_read() }).collect())
}

/// The most elements of a tuple key looked up without building the tuple
/// (`exec_fn_app`).
const TUPLE_KEY: usize = 4;

/// A key of an EXCEPT path.
enum Key {
    Field(Sym),
    /// `[e]` or `[e1, ..., en]` (a tuple).
    Index(Box<[Code]>),
}

impl Interp {
    /// The code of `e` if it is an expression of the program (compiled on
    /// first use).
    #[inline]
    pub(crate) fn code_of(&self, e: &Expr) -> Option<&Code> {
        let id = self.prog.expr_id(e)?;
        let slot = self.codes.get(id.index())?;
        Some(slot.get_or_init(|| self.compile(e)))
    }

    fn compile(&self, e: &Expr) -> Code {
        self.compile_in(e, true)
    }

    /// The code of `e`; with `hoist`, its largest closed constant
    /// subexpressions are hoisted (`Node::Hoist`).
    fn compile_in(&self, e: &Expr, hoist: bool) -> Code {
        if hoist && hoistable(e) && self.closed(e, &mut Vec::new()) {
            let inner = self.compile_in(e, false);
            if matches!(inner.node, Node::Lit(_) | Node::Shared(..)) {
                return inner;
            }
            let slot = self.hoist_slot();
            return Code { node: Node::Hoist(Box::new(inner), slot, AtomicBool::new(false)), span: e.span };
        }
        let codes = |es: &[Expr]| es.iter().map(|x| self.compile_in(x, hoist)).collect::<Box<[Code]>>();
        let unchanged = |op: B| op.java_only_name().is_none() && self.builtin_override(op).is_none();
        let node = match &*e.kind {
            ExprKind::Num(n) if *n <= i32::MAX as i128 => Node::Lit(Value::Int(*n as i64)),
            ExprKind::Str(s) => Node::Lit(Value::Str(self.syms.get(s))),
            ExprKind::Bool(b) => Node::Lit(Value::Bool(*b)),
            ExprKind::Var(v) => Node::Var(*v),
            ExprKind::Local(l) => Node::Local(*l),
            ExprKind::At => Node::Local(AT),
            ExprKind::Const(c) => Node::Const(*c),
            ExprKind::Apply { op: OpRef::Def(d), args } if args.is_empty() => self.compile_call0(*d),
            ExprKind::Apply { op: OpRef::Def(d), args } => self.compile_call(*d, args, hoist),
            ExprKind::Apply { op, args } => Node::Apply(*op, args.clone()),
            ExprKind::Builtin { op: B::Not, args } if args.len() == 1 && unchanged(B::Not) => {
                Node::Not(Box::new(self.compile_in(&args[0], hoist)))
            }
            ExprKind::Builtin { op: op @ (B::In | B::NotIn), args }
                if args.len() == 2 && unchanged(*op) && matches!(&*args[1].kind, ExprKind::SetEnum(es) if !es.is_empty()) =>
            {
                let ExprKind::SetEnum(es) = &*args[1].kind else { unreachable!() };
                let elems = codes(es);
                if literals(&elems).is_some() {
                    // (A literal set: built once, `Node::Bin`.)
                    Node::Bin(*op, Box::new([self.compile_in(&args[0], hoist), self.compile_in(&args[1], hoist)]))
                } else {
                    Node::InEnum(*op == B::In, Box::new(self.compile_in(&args[0], hoist)), elems)
                }
            }
            ExprKind::Builtin { op: op @ (B::Cup | B::SetMinus), args }
                if args.len() == 2 && unchanged(*op) && matches!(&*args[1].kind, ExprKind::SetEnum(es) if es.len() == 1) =>
            {
                let ExprKind::SetEnum(es) = &*args[1].kind else { unreachable!() };
                Node::SetOne(*op, Box::new([self.compile_in(&args[0], hoist), self.compile_in(&es[0], hoist)]))
            }
            ExprKind::Builtin { op, args } if args.len() == 2 && is_plain2(*op) && unchanged(*op) => {
                Node::Bin(*op, Box::new([self.compile_in(&args[0], hoist), self.compile_in(&args[1], hoist)]))
            }
            ExprKind::Builtin { op, args } if args.len() == 1 && is_plain1(*op) && unchanged(*op) => {
                Node::Un(*op, Box::new(self.compile_in(&args[0], hoist)))
            }
            ExprKind::Builtin { op, args } => Node::Builtin(*op, args.clone()),
            ExprKind::And(es) => Node::And(codes(es)),
            ExprKind::Or(es) => Node::Or(codes(es)),
            ExprKind::Quant { kind, bounds, body } => {
                Node::Quant(*kind == QuantKind::Exists, bounds.clone(), Box::new(self.compile_in(body, hoist)))
            }
            ExprKind::If { cond, then, els } => {
                Node::If(Box::new([self.compile_in(cond, hoist), self.compile_in(then, hoist), self.compile_in(els, hoist)]))
            }
            ExprKind::Case { arms, other } => Node::Case(
                arms.iter().map(|(g, v)| (self.compile_in(g, hoist), self.compile_in(v, hoist))).collect(),
                other.as_ref().map(|o| Box::new(self.compile_in(o, hoist))),
            ),
            ExprKind::Let { defs, body } => Node::Let(defs.clone().into(), Box::new(self.compile_in(body, hoist))),
            ExprKind::SetEnum(es) => {
                let cs = codes(es);
                match literals(&cs).map(Value::set_literal) {
                    Some(Ok(v)) => self.shared(v),
                    _ => Node::SetEnum(cs),
                }
            }
            ExprKind::Tuple(es) => {
                let cs = codes(es);
                match literals(&cs) {
                    Some(vs) => self.shared(Value::tuple(vs)),
                    None => Node::Tuple(cs),
                }
            }
            ExprKind::Record(fs) => Node::Record(fs.iter().map(|(n, x)| (self.syms.get(n), self.compile_in(x, hoist))).collect()),
            ExprKind::FnApp { func, args } => Node::FnApp(Box::new(self.compile_in(func, hoist)), codes(args)),
            ExprKind::Field { record, field } => Node::Field(Box::new(self.compile_in(record, hoist)), self.syms.get(field)),
            ExprKind::SetFilter { bound, pred } => {
                Node::SetFilter(Box::new((bound.clone(), self.compile_in(&bound.set, hoist), pred.clone(), self.compile_in(pred, hoist))))
            }
            ExprKind::SetMap { expr, bounds } => Node::SetMap(bounds.clone(), Box::new(self.compile_in(expr, hoist))),
            ExprKind::FnConstruct { bounds, body } => {
                Node::FnConstruct(Box::new((bounds.clone(), body.clone(), self.compile_in(body, hoist))))
            }
            ExprKind::Choose { vars, set: Some(set), body } => {
                Node::Choose(Box::new((vars.clone(), self.compile_in(set, hoist), self.compile_in(body, hoist))))
            }
            ExprKind::FnSet { domain, range } => Node::FnSet(Box::new([self.compile_in(domain, hoist), self.compile_in(range, hoist)])),
            ExprKind::RecordSet(fs) => Node::RecordSet(fs.iter().map(|(n, x)| (self.syms.get(n), self.compile_in(x, hoist))).collect()),
            ExprKind::Except { base, updates } => Node::Except(
                Box::new(self.compile_in(base, hoist)),
                updates
                    .iter()
                    .map(|(keys, val)| {
                        let keys = keys
                            .iter()
                            .map(|k| match k {
                                ExceptKey::Field(f) => Key::Field(self.syms.get(f)),
                                ExceptKey::Index(ix) => Key::Index(codes(ix)),
                            })
                            .collect();
                        (keys, self.compile_in(val, hoist))
                    })
                    .collect(),
            ),
            _ => Node::Tree(e.clone()),
        };
        Code { node, span: e.span }
    }

    /// A 0-ary definition: what `call_def` decides from the definition alone.
    fn compile_call0(&self, d: DefId) -> Node {
        if self.is_recursive(d) {
            return Node::Call0(d);
        }
        let t = if self.def_value.get(&d).is_some() { d } else { self.redirect_def(d) };
        if self.def_value.get(&t).is_some() {
            Node::CfgDef(t)
        } else if self.prog.defs[t.idx()].builtin.is_none() && self.def_const[t.idx()] && !self.is_recursive(t) {
            Node::ConstDef(t)
        } else if self.prog.defs[t.idx()].builtin.is_none() && self.def_state_cacheable[t.idx()] && !self.is_recursive(t) {
            Node::StateDef(t)
        } else {
            Node::Call0(d)
        }
    }

    /// An application of definition `d` to `args` (non-empty): what
    /// `Interp::apply` decides from the definition alone.
    fn compile_call(&self, d: DefId, args: &[Expr], hoist: bool) -> Node {
        let apply = || Node::Apply(OpRef::Def(d), args.to_vec());
        if self.def_value.get(&d).is_some() {
            return apply();
        }
        let t = self.redirect_def(d);
        let def = &self.prog.defs[t.idx()];
        if def.builtin.is_some()
            || !matches!(def.kind, DefKind::Op(_))
            || def.params.len() != args.len()
            || def.params.iter().any(|p| self.prog.locals[p.idx()].arity > 0)
        {
            return apply();
        }
        Node::Call(Box::new(Call {
            d: t,
            params: def.params.clone().into(),
            exprs: args.to_vec(),
            args: args.iter().map(|a| self.compile_in(a, hoist)).collect(),
            recursive: self.is_recursive(t),
            memo: self.def_memo[t.idx()],
            by_name: self.def_by_name[t.idx()],
            defer_errors: self.def_defer_errors[t.idx()],
            let_def: self.prog.def_is_let(t),
        }))
    }

    /// `Node::Call` (`call_def_with_args`).
    #[inline(never)]
    fn exec_call(self: &Arc<Self>, c: &Call, env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        let _depth = if c.recursive { Some(crate::depth::Guard::enter(span)?) } else { None };
        if c.memo && cx.s0.is_none() && cx.s1.is_none() {
            return self.call_def_memo(c.d, &c.exprs, env, cx, span);
        }
        // (`by_name(cx)`.)
        if c.by_name && !cx.init {
            let env2 = self.bind_params(&c.params, &c.exprs, env, cx, self.def_env(c.d, env), true, c.defer_errors)?;
            return self.def_body(c.d, &env2, cx, span);
        }
        let base = if c.let_def { env.clone() } else { Env::default() };
        let mut error = None;
        let env2 = base.bind_all(c.params.iter().zip(c.args.iter()).zip(c.exprs.iter()).map_while(|((p, a), e)| {
            let b = match self.exec(a, env, cx) {
                Ok(v) => Binding::Val(v),
                Err(err) if c.defer_errors && !crate::depth::is_depth_error(&err) => self.bind_by_name(e, env),
                Err(err) => {
                    error = Some(err);
                    return None;
                }
            };
            Some((*p, b))
        }));
        if let Some(err) = error {
            return Err(err);
        }
        self.def_body(c.d, &env2, cx, span)
    }

    /// A constant value: a literal, or shared (`Node::Shared`).
    fn shared(&self, v: Value) -> Node {
        match v {
            Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::ModelValue(_) | Value::Interval(..) => Node::Lit(v),
            _ => Node::Shared(v, self.hoist_slot()),
        }
    }

    /// A fresh hoisting slot (`Node::Shared`, `Node::Hoist`).
    fn hoist_slot(&self) -> usize {
        self.hoist_slots.fetch_add(1, Ordering::Relaxed)
    }

    /// Whether `e` has the same value wherever it is evaluated (TLC: a
    /// constant-level expression with no free bound variable): it mentions
    /// no variable, no local bound outside it (`bound`: the ones bound
    /// inside, around this subexpression), nothing nondeterministic or
    /// effectful, no operator argument and no LET definition.
    fn closed(&self, e: &Expr, bound: &mut Vec<LocalId>) -> bool {
        let n = bound.len();
        let ok = match &*e.kind {
            ExprKind::Num(_) | ExprKind::Str(_) | ExprKind::Bool(_) => true,
            ExprKind::Local(l) => bound.contains(l),
            ExprKind::At => bound.contains(&AT),
            ExprKind::Const(c) => self.const_closed(*c),
            ExprKind::Apply { op, args } => self.op_closed(*op) && args.iter().all(|a| self.closed(a, bound)),
            ExprKind::Builtin { op, args } => self.builtin_closed(*op) && args.iter().all(|a| self.closed(a, bound)),
            ExprKind::OpArg(op) => self.op_closed(*op),
            ExprKind::And(es) | ExprKind::Or(es) | ExprKind::SetEnum(es) | ExprKind::Tuple(es) => es.iter().all(|x| self.closed(x, bound)),
            ExprKind::Quant { bounds, body, .. } => self.bounds_closed(bounds, bound) && self.closed(body, bound),
            ExprKind::Choose { vars, set: Some(set), body } => {
                self.closed(set, bound) && {
                    bound.extend(vars.locals());
                    self.closed(body, bound)
                }
            }
            ExprKind::If { cond, then, els } => self.closed(cond, bound) && self.closed(then, bound) && self.closed(els, bound),
            ExprKind::Case { arms, other } => {
                arms.iter().all(|(g, v)| self.closed(g, bound) && self.closed(v, bound))
                    && other.as_ref().is_none_or(|o| self.closed(o, bound))
            }
            ExprKind::SetFilter { bound: b, pred } => {
                self.closed(&b.set, bound) && {
                    bound.extend(b.vars.locals());
                    self.closed(pred, bound)
                }
            }
            ExprKind::SetMap { expr, bounds } => self.bounds_closed(bounds, bound) && self.closed(expr, bound),
            ExprKind::FnConstruct { bounds, body } => self.bounds_closed(bounds, bound) && self.closed(body, bound),
            ExprKind::FnApp { func, args } => self.closed(func, bound) && args.iter().all(|a| self.closed(a, bound)),
            ExprKind::FnSet { domain, range } => self.closed(domain, bound) && self.closed(range, bound),
            ExprKind::Record(fs) | ExprKind::RecordSet(fs) => fs.iter().all(|(_, x)| self.closed(x, bound)),
            ExprKind::Field { record, .. } => self.closed(record, bound),
            ExprKind::Except { base, updates } => {
                self.closed(base, bound)
                    && updates.iter().all(|(keys, val)| {
                        keys.iter().all(|k| match k {
                            ExceptKey::Field(_) => true,
                            ExceptKey::Index(ix) => ix.iter().all(|x| self.closed(x, bound)),
                        }) && {
                            bound.push(AT);
                            let ok = self.closed(val, bound);
                            bound.pop();
                            ok
                        }
                    })
            }
            _ => false,
        };
        bound.truncate(n);
        ok
    }

    /// Whether the sets of `bounds` are closed (`closed`); binds their
    /// variables in `bound` (for the body).
    fn bounds_closed(&self, bounds: &[Bound], bound: &mut Vec<LocalId>) -> bool {
        for b in bounds {
            if !self.closed(&b.set, bound) {
                return false;
            }
        }
        for b in bounds {
            bound.extend(b.vars.locals());
        }
        true
    }

    fn const_closed(&self, c: ConstId) -> bool {
        match &self.consts[c.idx()] {
            Some(ConstVal::Value(_) | ConstVal::Table(_)) => true,
            Some(ConstVal::Def(d)) => self.op_closed(OpRef::Def(*d)),
            Some(ConstVal::Op(r)) => self.op_closed(*r),
            None => false,
        }
    }

    /// Whether applying `op` to closed arguments is closed.
    fn op_closed(&self, op: OpRef) -> bool {
        match op {
            OpRef::Def(d) => {
                if self.def_value.get(&d).is_some() {
                    return true;
                }
                let t = self.redirect_def(d);
                if self.def_value.get(&t).is_some() {
                    return true;
                }
                match self.prog.defs[t.idx()].builtin {
                    Some(b) => self.builtin_closed(b),
                    None => !self.prog.def_is_let(t) && self.def_pure[t.idx()] && !self.def_effectful[t.idx()],
                }
            }
            OpRef::Builtin(b) => self.builtin_closed(b),
            OpRef::Const(c) => self.const_closed(c),
            OpRef::Param(_) => false,
        }
    }

    fn builtin_closed(&self, b: B) -> bool {
        if let Some(d) = self.builtin_override(b) {
            // (`Nat <- NatOverride`: the definition applied instead.)
            return self.prog.defs[self.redirect_def(d).idx()].builtin.is_none() && self.op_closed(OpRef::Def(d));
        }
        crate::interp::constant_level_builtin(b)
    }

    /// The value of `c` (`eval` of its expression).
    #[inline]
    pub(crate) fn exec(self: &Arc<Self>, c: &Code, env: &Env, cx: &Ctx) -> EResult<Value> {
        match &c.node {
            Node::Lit(v) => return Ok(v.clone()),
            Node::Local(l) => {
                if let Some(Binding::Val(v)) = env.lookup(*l) {
                    return Ok(v.clone());
                }
            }
            _ => {}
        }
        self.exec_slow(c, env, cx)
    }

    #[inline(never)]
    fn exec_slow(self: &Arc<Self>, c: &Code, env: &Env, cx: &Ctx) -> EResult<Value> {
        match self.exec_inner(c, env, cx) {
            Ok(v) => Ok(v),
            Err(err) => Err(err.with_span(c.span)),
        }
    }

    fn exec_inner(self: &Arc<Self>, c: &Code, env: &Env, cx: &Ctx) -> EResult<Value> {
        // The common nodes; the others in `exec_other` (a small frame here).
        match &c.node {
            Node::Lit(v) => Ok(v.clone()),
            Node::Var(v) => self.read_var(*v, cx, c.span),
            Node::Local(l) => self.read_local(*l, env, cx),
            Node::Call0(d) => self.call_def(*d, env, cx, c.span),
            // (`call_def` of the definition.)
            Node::StateDef(d) if !cx.keep_lazy => self.call_def_cached(*d, env, cx, c.span),
            Node::Call(call) => self.exec_call(call, env, cx, c.span),
            Node::Bin(op, ab) => self.exec_bin(*op, ab, env, cx),
            Node::FnApp(f, args) => Ok(self.exec_fn_app(f, args, env, cx)?.into_owned()),
            Node::Field(r, field) => Ok(self.exec_field(r, *field, env, cx)?.into_owned()),
            Node::Not(..) | Node::And(..) | Node::Or(..) | Node::Quant(..) | Node::InEnum(..) => {
                Ok(Value::Bool(self.exec_bool_inner(c, env, cx)?))
            }
            Node::If(t) => {
                if self.exec_bool(&t[0], env, cx)? {
                    self.exec(&t[1], env, cx)
                } else {
                    self.exec(&t[2], env, cx)
                }
            }
            _ => self.exec_other(c, env, cx),
        }
    }

    #[inline(never)]
    fn exec_other(self: &Arc<Self>, c: &Code, env: &Env, cx: &Ctx) -> EResult<Value> {
        Ok(match &c.node {
            Node::Lit(v) => v.clone(),
            Node::Shared(v, n) => local::get(self.uid, Slot::Hoist(2 * n), || Ok::<_, crate::error::EvalError>(v.clone()))?,
            Node::Hoist(inner, n, big) => self.exec_hoisted(inner, *n, big, env, cx)?,
            Node::Var(v) => self.read_var(*v, cx, c.span)?,
            Node::Local(l) => self.read_local(*l, env, cx)?,
            Node::Const(k) => self.const_value(*k, c.span)?,
            Node::Call0(d) => self.call_def(*d, env, cx, c.span)?,
            Node::CfgDef(d) => {
                let v = self.def_value.get(d).expect("a cfg value");
                local::get(self.uid, Slot::Def(d.idx()), || Ok::<_, crate::error::EvalError>(v.clone()))?
            }
            Node::ConstDef(d) | Node::StateDef(d) if cx.keep_lazy => self.call_def(*d, env, cx, c.span)?,
            Node::StateDef(d) => self.call_def_cached(*d, env, cx, c.span)?,
            Node::ConstDef(d) => self.call_def_cached(*d, env, cx, c.span)?,
            Node::Apply(op, args) => self.apply(*op, args, env, cx, c.span)?,
            Node::Call(call) => self.exec_call(call, env, cx, c.span)?,
            Node::Bin(op, ab) => self.exec_bin(*op, ab, env, cx)?,
            Node::Un(op, a) => builtin1(*op, &*self.exec_cow(a, env, cx)?)?,
            Node::Builtin(op, args) => self.builtin(*op, args, env, cx, c.span)?,
            Node::Not(..) | Node::And(..) | Node::Or(..) | Node::Quant(..) | Node::InEnum(..) => {
                Value::Bool(self.exec_bool_inner(c, env, cx)?)
            }
            Node::If(t) => {
                if self.exec_bool(&t[0], env, cx)? {
                    self.exec(&t[1], env, cx)?
                } else {
                    self.exec(&t[2], env, cx)?
                }
            }
            Node::Case(arms, other) => {
                for (g, v) in arms.iter() {
                    if self.exec_bool(g, env, cx)? {
                        return self.exec(v, env, cx);
                    }
                }
                match other {
                    Some(o) => self.exec(o, env, cx)?,
                    None => return Err(crate::error::EvalError::new("Attempted to evaluate a CASE with no conditions true.")),
                }
            }
            Node::Let(defs, body) => {
                let (env2, _frame) = self.let_env(defs, env);
                self.exec(body, &env2, cx)?
            }
            Node::SetEnum(cs) => Value::set_literal(cs.iter().map(|x| self.exec(x, env, cx)).collect::<EResult<Vec<_>>>()?)?,
            Node::Tuple(cs) if cs.len() <= SMALL => Value::Tuple(try_arc_slice(cs.len(), |i| self.exec(&cs[i], env, cx))?),
            Node::Tuple(cs) => Value::tuple(cs.iter().map(|x| self.exec(x, env, cx)).collect::<EResult<Vec<_>>>()?),
            Node::Record(fs) => Value::record(fs.iter().map(|(n, x)| Ok((*n, self.exec(x, env, cx)?))).collect::<EResult<Vec<_>>>()?),
            Node::FnApp(f, args) => self.exec_fn_app(f, args, env, cx)?.into_owned(),
            Node::Field(r, field) => self.exec_field(r, *field, env, cx)?.into_owned(),
            Node::SetFilter(f) => {
                let (bound, set, pred_expr, pred) = &**f;
                let set = self.exec(set, env, cx)?;
                if set.enum_elements().is_none() && !matches!(set, Value::Interval(..)) {
                    return Ok(crate::lazy::lazy_filter(self, &bound.vars, set, pred_expr, env, cx));
                }
                let mut out = Vec::new();
                for x in Elems::of(&set)? {
                    let env2 = self.bind_bound_vars(&bound.vars, x.clone(), env)?;
                    if self.exec_bool(pred, &env2, cx)? {
                        tlx_value::limits::push(&mut out, x)?;
                    }
                }
                Value::set_enum(out)?
            }
            Node::SetMap(bounds, expr) => {
                let mut out = Vec::new();
                self.for_each_binding(bounds, env, cx, &mut |env2| {
                    tlx_value::limits::push(&mut out, self.exec(expr, env2, cx)?)?;
                    Ok(true)
                })?;
                Value::set_enum(out)?
            }
            Node::FnConstruct(f) => {
                let (bounds, body_expr, body) = &**f;
                let sets = self.bound_sets(bounds, env, cx)?;
                // (`fn_construct`.)
                let plain = sets.iter().all(|s| matches!(s, Value::Set(_) | Value::Interval(..)));
                let domain = fn_domain(sets)?;
                if !plain || cx.keep_lazy {
                    let f = LambdaFcn::new(self.clone(), bounds.to_vec(), body_expr.clone(), domain, env.clone(), cx, plain);
                    return Ok(Value::LazyFcn(Arc::new(f)));
                }
                let mut pairs = Vec::new();
                for x in ops::enumerate_normalized(&domain)? {
                    let env2 = self.bind_fn_args(bounds, &x, env)?;
                    let v = self.exec(body, &env2, cx)?;
                    pairs.push((x, v));
                }
                Value::fcn_over(&domain, pairs)?
            }
            Node::Choose(ch) => {
                let (vars, set, body) = &**ch;
                let s = self.exec(set, env, cx)?;
                let always_true = matches!(body.node, Node::Lit(Value::Bool(true))) && matches!(vars, BoundVars::Many(ls) if ls.len() == 1);
                self.choose_in(vars, &s, env, always_true, &mut |env2| self.exec_bool(body, env2, cx))?
            }
            Node::FnSet(dr) => {
                let d = self.exec_cow(&dr[0], env, cx)?;
                let r = self.exec_cow(&dr[1], env, cx)?;
                ops::fcn_set(&d, &r)?
            }
            Node::RecordSet(fs) => ops::record_set(fs.iter().map(|(n, x)| Ok((*n, self.exec(x, env, cx)?))).collect::<EResult<Vec<_>>>()?)?,
            Node::Except(base, updates) => self.exec_except(base, updates, env, cx)?,
            Node::SetOne(op, sx) => self.exec_set_one(*op, sx, env, cx)?,
            Node::Tree(e) => self.eval_tree(e, env, cx)?,
        })
    }

    /// `[base EXCEPT !path1 = e1, ...]` (`except::except`, `Interp::except`).
    fn exec_except(self: &Arc<Self>, base: &Code, updates: &[(Box<[Key]>, Code)], env: &Env, cx: &Ctx) -> EResult<Value> {
        let base = self.exec_cow(base, env, cx)?;
        except::except(
            base,
            updates,
            env,
            Unchanged::Keep,
            |(keys, _)| {
                keys.iter()
                    .map(|k| match k {
                        Key::Field(f) => Ok(Value::Str(*f)),
                        Key::Index(ix) => match &ix[..] {
                            [x] => self.exec(x, env, cx),
                            _ => Ok(Value::tuple(ix.iter().map(|x| self.exec(x, env, cx)).collect::<EResult<Vec<_>>>()?)),
                        },
                    })
                    .collect()
            },
            |(_, val), env| self.exec(val, env, cx),
        )
    }

    /// The value of a closed constant expression (`Node::Hoist`).
    fn exec_hoisted(self: &Arc<Self>, inner: &Code, n: usize, big: &AtomicBool, env: &Env, cx: &Ctx) -> EResult<Value> {
        if big.load(Ordering::Relaxed) {
            return self.exec(inner, env, cx);
        }
        let slot = Slot::Hoist(2 * n + cx.keep_lazy as usize);
        if let Some(v) = local::peek(self.uid, slot) {
            return Ok(v);
        }
        let v = self.exec(inner, env, cx)?;
        let mut budget = crate::memo::MAX_VALUE_NODES;
        if crate::memo::small(&v, &mut budget) {
            local::put(self.uid, slot, v.clone());
        } else {
            big.store(true, Ordering::Relaxed);
        }
        Ok(v)
    }

    /// `x \in {es}` (`Node::InEnum`): `ops::member(x, set_from(es))`. When
    /// `x` and the elements are all untyped model values, all integers or
    /// all strings, neither normalizing the set nor the membership test can
    /// fail and membership is equality with an element: no set is built.
    #[inline(never)]
    fn exec_in_enum(self: &Arc<Self>, x: &Code, es: &[Code], env: &Env, cx: &Ctx) -> EResult<bool> {
        let xv = self.exec_cow(x, env, cx)?;
        let vals = es.iter().map(|e| self.exec(e, env, cx)).collect::<EResult<Vec<_>>>()?;
        let kind = |v: &Value| match v {
            Value::ModelValue(m) if m.model_value_type().is_none() => 1,
            Value::Int(_) => 2,
            Value::Str(_) => 3,
            _ => 0,
        };
        let k = kind(&xv);
        if k != 0 && vals.iter().all(|v| kind(v) == k) {
            return Ok(vals.contains(&*xv));
        }
        Ok(ops::member(&xv, &Value::set_literal(vals)?)?)
    }

    /// `Node::SetOne`: `ops::union` / `ops::difference` with the singleton
    /// set of `x` (the same comparisons, in the same order, as the merge
    /// and the membership test; reuse requires inert self-comparison for union).
    #[inline(never)]
    fn exec_set_one(self: &Arc<Self>, op: B, sx: &[Code; 2], env: &Env, cx: &Ctx) -> EResult<Value> {
        use std::cmp::Ordering;
        use tlx_value::order::cmp_tlc;
        let s = self.exec_cow(&sx[0], env, cx)?;
        let x = self.exec(&sx[1], env, cx)?;
        // A set that already holds more elements than the bound allows can only
        // be reproduced by the growing construction: TLC copies it into a fresh
        // `ValueVec` for `\cup` and `\` too, so the bound applies even when the
        // result is the same set. Let the shared operation decide; every other
        // operand keeps the singleton fast path.
        if let Value::Set(es) = &*s {
            if es.len() as i64 > tlx_value::limits::growth_limit() {
                let t = Value::set_from(vec![x])?;
                return Ok(if op == B::SetMinus { ops::difference(&s, &t)? } else { ops::union(&s, &t)? });
            }
        }
        if let Value::Set(es) = &*s {
            if op == B::SetMinus {
                // (`member(e, {x})`: `cmp_tlc(e, x)`.)
                let mut out: Option<Vec<Value>> = None;
                for (i, e) in es.iter().enumerate() {
                    // Compare once: lazy values can evaluate effects here.
                    if cmp_tlc(e, &x)? == Ordering::Equal {
                        if out.is_none() {
                            let mut prefix = Vec::with_capacity(es.len() - 1);
                            prefix.extend_from_slice(&es[..i]);
                            out = Some(prefix);
                        }
                    } else if let Some(out) = &mut out {
                        out.push(e.clone());
                    }
                }
                return Ok(match out {
                    Some(out) => Value::Set(out.into()),
                    None => s.into_owned(),
                });
            }
            if !es.is_empty() {
                // (`merge_sorted(s, {x})`: `cmp_tlc(x, e)` along `s`.)
                let mut at = es.len();
                for (i, e) in es.iter().enumerate() {
                    match cmp_tlc(&x, e)? {
                        Ordering::Less => {
                            at = i;
                            break;
                        }
                        Ordering::Equal => {
                            // The same witnesses are retained, but outer identity
                            // must not skip later errors or effects in the tail.
                            return Ok(if tlx_value::order::self_comparison_is_inert(&s) {
                                s.into_owned()
                            } else {
                                Value::Set(es.to_vec().into())
                            });
                        }
                        Ordering::Greater => {}
                    }
                }
                tlx_value::limits::check_set_size(es.len() + 1)?;
                let mut out = Vec::with_capacity(es.len() + 1);
                out.extend_from_slice(&es[..at]);
                out.push(x);
                out.extend_from_slice(&es[at..]);
                return Ok(Value::Set(out.into()));
            }
        }
        let t = Value::set_from(vec![x])?;
        Ok(if op == B::SetMinus { ops::difference(&s, &t)? } else { ops::union(&s, &t)? })
    }

    /// A strict binary built-in (`Node::Bin`).
    #[inline(never)]
    fn exec_bin(self: &Arc<Self>, op: B, ab: &[Code; 2], env: &Env, cx: &Ctx) -> EResult<Value> {
        let a = self.exec_cow(&ab[0], env, cx)?;
        let b = self.exec_cow(&ab[1], env, cx)?;
        if let (Value::Int(x), Value::Int(y)) = (&*a, &*b) {
            match op {
                B::Plus => return Ok(Value::Int(tlx_value::arith::add(*x, *y)?)),
                B::Minus => return Ok(Value::Int(tlx_value::arith::sub(*x, *y)?)),
                B::Lt => return Ok(Value::Bool(x < y)),
                B::Gt => return Ok(Value::Bool(x > y)),
                B::Le => return Ok(Value::Bool(x <= y)),
                B::Ge => return Ok(Value::Bool(x >= y)),
                _ => {}
            }
        }
        self.builtin2(op, &a, &b)
    }

    /// `exec` of a boolean (`eval_bool`).
    #[inline]
    pub(crate) fn exec_bool(self: &Arc<Self>, c: &Code, env: &Env, cx: &Ctx) -> EResult<bool> {
        match self.exec_bool_inner(c, env, cx) {
            Ok(b) => Ok(b),
            Err(err) => Err(err.with_span(c.span)),
        }
    }

    fn exec_bool_inner(self: &Arc<Self>, c: &Code, env: &Env, cx: &Ctx) -> EResult<bool> {
        match &c.node {
            Node::Lit(Value::Bool(b)) => Ok(*b),
            Node::Not(a) => Ok(!self.exec_bool(a, env, cx)?),
            Node::And(cs) => {
                for x in cs.iter() {
                    if !self.exec_bool(x, env, cx)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Node::Or(cs) => {
                for x in cs.iter() {
                    if self.exec_bool(x, env, cx)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Node::Quant(exists, bounds, body) => self.exec_quant(*exists, bounds, body, env, cx),
            Node::Bin(op, ab) if is_compare2(*op) => self.exec_compare(*op, ab, env, cx),
            Node::InEnum(is_in, x, es) => Ok(self.exec_in_enum(x, es, env, cx)? == *is_in),
            _ => {
                let v = self.exec_inner(c, env, cx)?;
                as_bool(&v, c.span)
            }
        }
    }

    /// A comparison (`Node::Bin` with `is_compare2`).
    #[inline(never)]
    fn exec_compare(self: &Arc<Self>, op: B, ab: &[Code; 2], env: &Env, cx: &Ctx) -> EResult<bool> {
        let a = self.exec_cow(&ab[0], env, cx)?;
        let b = self.exec_cow(&ab[1], env, cx)?;
        if let (Value::Int(x), Value::Int(y)) = (&*a, &*b) {
            match op {
                B::Lt => return Ok(x < y),
                B::Gt => return Ok(x > y),
                B::Le => return Ok(x <= y),
                B::Ge => return Ok(x >= y),
                B::Eq => return Ok(x == y),
                B::Neq => return Ok(x != y),
                _ => {}
            }
        }
        compare2(op, &a, &b)
    }

    /// `\E` / `\A` (`eval_inner`'s `Quant`; `for_each_binding`'s order).
    #[inline(never)]
    fn exec_quant(self: &Arc<Self>, exists: bool, bounds: &[Bound], body: &Code, env: &Env, cx: &Ctx) -> EResult<bool> {
        // One variable over one set: the binding is updated in place
        // (`for_each_binding`'s common case).
        if let [Bound { vars: BoundVars::Many(ls), set }] = bounds {
            if let [l] = ls.as_slice() {
                let mut elems = match self.bound_elems(set, env, cx)? {
                    BoundElems::Elems(elems) => elems,
                    // The domain cannot be materialized: stream it
                    // (`for_each_enumerated`; see `BoundElems` on how this
                    // relates to TLC's materializing bound) and stop at the
                    // first witness.
                    BoundElems::Stream(v) => {
                        let mut found = !exists;
                        let mut err = None;
                        ops::for_each_enumerated(&v, &mut |x| {
                            let r = self.exec_bool(body, &env.bind_val(*l, x), cx);
                            match r {
                                Ok(want) if want == exists => {
                                    found = exists;
                                    Ok(false)
                                }
                                Ok(_) => Ok(true),
                                Err(e) => {
                                    err = Some(e);
                                    Ok(false)
                                }
                            }
                        })?;
                        return match err {
                            Some(e) => Err(e),
                            None => Ok(found),
                        };
                    }
                };
                let Some(first) = elems.next() else {
                    return Ok(!exists);
                };
                let mut env2 = env.bind_val(*l, first);
                loop {
                    if self.exec_bool(body, &env2, cx)? == exists {
                        return Ok(exists);
                    }
                    let Some(x) = elems.next() else {
                        return Ok(!exists);
                    };
                    if let Err(x) = env2.rebind_head(x) {
                        env2 = env.bind_val(*l, x);
                    }
                }
            }
        }
        let mut found = !exists;
        self.for_each_binding(bounds, env, cx, &mut |env2| {
            if self.exec_bool(body, env2, cx)? == exists {
                found = exists;
                return Ok(false);
            }
            Ok(true)
        })?;
        Ok(found)
    }

    /// `exec`, borrowing the value where it is stored (`eval_cow`).
    #[inline]
    pub(crate) fn exec_cow<'a>(self: &'a Arc<Self>, c: &'a Code, env: &'a Env, cx: &Ctx<'a>) -> EResult<Cow<'a>> {
        match &c.node {
            Node::Lit(v) => return Ok(Cow::Ref(v)),
            Node::Local(l) => {
                if let Some(Binding::Val(v)) = env.lookup(*l) {
                    return Ok(Cow::Ref(v));
                }
            }
            Node::Var(v) if !cx.primed && !cx.init => {
                if let Some(s0) = cx.s0 {
                    return Ok(Cow::Ref(&s0[v.idx()]));
                }
            }
            _ => {}
        }
        self.exec_cow_slow(c, env, cx)
    }

    #[inline(never)]
    fn exec_cow_slow<'a>(self: &'a Arc<Self>, c: &'a Code, env: &'a Env, cx: &Ctx<'a>) -> EResult<Cow<'a>> {
        match &c.node {
            Node::Lit(v) | Node::Shared(v, _) => Ok(Cow::Ref(v)),
            Node::Var(v) => {
                let r = if cx.primed || cx.init { cx.s1.and_then(|s1| s1[v.idx()].as_ref()) } else { cx.s0.map(|s0| &s0[v.idx()]) };
                match r {
                    Some(x) => Ok(Cow::Ref(x)),
                    None => self.exec(c, env, cx).map(Cow::Own),
                }
            }
            Node::Local(l) => match env.lookup(*l) {
                Some(Binding::Val(v)) => Ok(Cow::Ref(v)),
                _ => self.exec(c, env, cx).map(Cow::Own),
            },
            Node::Const(k) => match &self.consts[k.idx()] {
                Some(ConstVal::Value(v)) => Ok(Cow::Ref(v)),
                _ => self.exec(c, env, cx).map(Cow::Own),
            },
            Node::Call0(d) => match self.const_def_ref(*d) {
                Some(v) => Ok(Cow::Ref(v)),
                None => self.exec(c, env, cx).map(Cow::Own),
            },
            Node::CfgDef(d) => Ok(Cow::Ref(self.def_value.get(d).expect("a cfg value"))),
            Node::ConstDef(d) => match self.const_cache[d.idx()].get() {
                Some(Ok(v)) => Ok(Cow::Ref(v)),
                _ => self.exec(c, env, cx).map(Cow::Own),
            },
            Node::FnApp(f, args) => self.exec_fn_app(f, args, env, cx).map_err(|err| err.with_span(c.span)),
            Node::Field(r, field) => self.exec_field(r, *field, env, cx).map_err(|err| err.with_span(c.span)),
            Node::Bin(op, ab) => self.exec_bin(*op, ab, env, cx).map(Cow::Own).map_err(|err| err.with_span(c.span)),
            _ => self.exec(c, env, cx).map(Cow::Own),
        }
    }

    /// `f[args]` (`fn_app_cow`).
    #[inline(never)]
    fn exec_fn_app<'a>(self: &'a Arc<Self>, f: &'a Code, args: &'a [Code], env: &'a Env, cx: &Ctx<'a>) -> EResult<Cow<'a>> {
        let fv = self.exec_cow(f, env, &cx.lazy(true))?;
        let elems = match args {
            [a] => match &a.node {
                Node::Tuple(es) if es.len() <= TUPLE_KEY => Some(&es[..]),
                _ => None,
            },
            _ => Some(args),
        };
        let arg = match elems {
            // `f[<<e1, ..., en>>]` or `f[e1, ..., en]`: looked up without
            // building the tuple when `ops::apply_tuple_ref` can.
            Some(es) if es.len() <= TUPLE_KEY => {
                let mut vals = [const { Value::Bool(false) }; TUPLE_KEY];
                for (v, e) in vals.iter_mut().zip(es) {
                    *v = self.exec(e, env, cx)?;
                }
                let found = match fv {
                    Cow::Ref(fr) => ops::apply_tuple_ref(fr, &vals[..es.len()]).map(Cow::Ref),
                    Cow::Own(ref fo) => ops::apply_tuple_ref(fo, &vals[..es.len()]).map(|v| Cow::Own(v.clone())),
                };
                if let Some(v) = found {
                    // (An explicit function's stored value: `kept_point`.)
                    return Ok(v);
                }
                Cow::Own(Value::Tuple(vals.into_iter().take(es.len()).collect()))
            }
            Some(es) => Cow::Own(Value::tuple(es.iter().map(|x| self.exec(x, env, cx)).collect::<EResult<Vec<_>>>()?)),
            None => self.exec_cow(&args[0], env, cx)?,
        };
        apply_tail(fv, &arg, cx)
    }

    /// `r.field` (`field_cow`).
    #[inline(never)]
    fn exec_field<'a>(self: &'a Arc<Self>, r: &'a Code, field: Sym, env: &'a Env, cx: &Ctx<'a>) -> EResult<Cow<'a>> {
        let rv = self.exec_cow(r, env, cx)?;
        field_tail(rv, field)
    }
}

/// Whether hoisting `e` (if closed) saves work: it builds a value or
/// enumerates (not a literal, a read or a scalar operation).
fn hoistable(e: &Expr) -> bool {
    match &*e.kind {
        ExprKind::SetEnum(es) | ExprKind::Tuple(es) => !es.is_empty() || matches!(&*e.kind, ExprKind::Tuple(_)),
        ExprKind::Record(_)
        | ExprKind::RecordSet(_)
        | ExprKind::FnSet { .. }
        | ExprKind::SetFilter { .. }
        | ExprKind::SetMap { .. }
        | ExprKind::FnConstruct { .. }
        | ExprKind::Choose { .. }
        | ExprKind::Except { .. }
        | ExprKind::Quant { .. } => true,
        ExprKind::Apply { args, .. } => !args.is_empty(),
        ExprKind::Builtin { op, .. } => matches!(
            op,
            B::Cup
                | B::Cap
                | B::SetMinus
                | B::Concat
                | B::Append
                | B::Domain
                | B::Union
                | B::Subset
                | B::Tail
                | B::Times
                | B::Seq
                | B::Cardinality
                | B::Permutations
                | B::SubSeq
                | B::SelectSeq
        ),
        _ => false,
    }
}

/// The values of `cs` if they are all literals or constants.
fn literals(cs: &[Code]) -> Option<Vec<Value>> {
    cs.iter()
        .map(|c| match &c.node {
            Node::Lit(v) | Node::Shared(v, _) => Some(v.clone()),
            _ => None,
        })
        .collect()
}
