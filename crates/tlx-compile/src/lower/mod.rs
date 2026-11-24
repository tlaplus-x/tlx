//! Lowering HIR to the typed IR (`crate::ir`).
//!
//! Statement lowering mirrors `tlx_eval::enumerate` (TLC's Init/Next
//! enumeration) with the set of assigned next-state variables tracked
//! statically along each continuation path. Anything that cannot be lowered
//! with exactly the interpreter's semantics makes the whole action
//! `Unsupported` (it is then run by the interpreter); expressions the lowerer
//! does not specialize fall back to `ExprKind::Interp`.
//!
//! Values of state variables keep their layout encoding (`Lowerer::with_typing`)
//! and the typed fast paths apply.
//!
//! Submodules:
//! - `stmt`: actions and Init as CPS statement trees (enumeration);
//! - `analysis`: syntactic queries on HIR in a lowering environment
//!   (assignment targets, may-assign/may-branch, constness, peeling);
//! - `expr`: expression lowering with value semantics, operator inlining and
//!   the interpreter fallback;
//! - `typed`: typed fast paths (dispatch, arithmetic, equality, conditionals,
//!   action operators in expressions);
//! - `select`: function application, record fields, EXCEPT, sequences;
//! - `sets`: set operators, bitsets and sorted-array sets, iteration;
//! - `member`: set membership;
//! - `construct`: destination-driven construction into an encoding;
//! - `maps`: maps (functions over a varying subset of a key universe);
//! - `consts`: encodings and shapes of constant values;
//! - `materialize`: definitions materialized once per predicate evaluation;
//! - `frame`: the state of the frame being lowered (its temps and lowering
//!   context), reset at every entry point and swapped around the body of a
//!   compiled function;
//! - `regions`: boxed regions (mixed mode): folding, widening and hoisting,
//!   and the region table.
//!
//! Shape ids are interned on demand, and constant shapes prefer shapes that
//! are already interned (`consts`), so the order of interning is observable:
//! keep it stable when moving code around.

mod analysis;
mod binders;
mod calls;
mod choose;
mod construct;
mod consts;
mod count;
mod cse;
mod expr;
mod fold;
mod frame;
mod maps;
mod materialize;
mod member;
mod refs;
mod regions;
mod select;
mod sets;
mod stmt;
pub(crate) mod summary;
pub use summary::AnalyzedTyping;
mod summary_hir;
mod typed;

use std::sync::Arc;

use tlx_eval::enumerate::Action;
use tlx_eval::env::{Binding, Env, OpVal};
use tlx_eval::Interp;
use tlx_layout::Shape;
use tlx_sema::hir::{self, LocalId, OpRef};
use tlx_value::Value;

use crate::ir::*;
use crate::types::Typing;

use frame::Frame;
use materialize::Materialized;

pub(crate) use regions::{free_temps, stmt_bound_temps};
pub(crate) use sets::{flat_radices, rankable, union_radices, word_ranked_set};

/// Why an action could not be lowered (it is then interpreted).
#[derive(Clone, Debug)]
pub struct Unsupported(pub String);

type LResult<T> = Result<T, Unsupported>;

fn unsupported<T>(msg: impl Into<String>) -> LResult<T> {
    Err(Unsupported(msg.into()))
}

/// Maximum number of statement nodes per action (CPS duplication budget).
const STMT_BUDGET: usize = 20_000;
const BUDGET_EXCEEDED: &str = "statement budget exceeded";
/// Maximum operator inlining depth.
const INLINE_DEPTH: usize = 64;
/// Levels a RECURSIVE operator is unrolled in compiled code.
const RECURSION_UNROLL: usize = 6;
/// Levels a recursion whose arguments are compile-time constants (or passed
/// through unchanged) is unrolled: its conditions fold, so each level is
/// one instance of the body.
const CONST_RECURSION_UNROLL: usize = 64;

/// Lowering-time binding of a local.
#[derive(Clone)]
enum LBind {
    /// A runtime IR value.
    Ir(Expr),
    /// A call-by-name argument: lowered where it is used.
    Thunk(hir::Expr, LEnv),
    /// An operator argument.
    Op(LOp),
}

/// An operator-valued argument.
#[derive(Clone)]
enum LOp {
    Ref(OpRef),
    Lambda(Arc<[LocalId]>, hir::Expr, LEnv),
}

/// Lowering environment: IR bindings layered over the interpreter
/// environment of the action instance (constant parameter bindings).
#[derive(Clone)]
struct LEnv {
    binds: Arc<Vec<(LocalId, LBind)>>,
    base: Env,
}

impl LEnv {
    fn new(base: Env) -> LEnv {
        LEnv { binds: Arc::new(Vec::new()), base }
    }

    fn bind(&self, l: LocalId, b: LBind) -> LEnv {
        let mut v = (*self.binds).clone();
        v.push((l, b));
        LEnv { binds: Arc::new(v), base: self.base.clone() }
    }

    fn lookup(&self, l: LocalId, prog: &tlx_sema::Program) -> Option<LBind> {
        if let Some((_, b)) = self.binds.iter().rev().find(|(x, _)| *x == l) {
            return Some(b.clone());
        }
        match self.base.lookup(l)? {
            Binding::Val(v) => Some(LBind::Ir(val_lit(v.clone()))),
            Binding::Op(OpVal::Ref(r)) => Some(LBind::Op(LOp::Ref(*r))),
            Binding::Op(OpVal::Lambda { params, body, env }) => {
                Some(LBind::Op(LOp::Lambda(params.clone(), body.clone(), LEnv::new(env.clone()))))
            }
            Binding::Thunk(t) => Some(LBind::Thunk(t.expr.clone(), LEnv::new(t.env.clone()))),
            Binding::Name(id, env) => Some(LBind::Thunk(prog.arena_expr(*id).clone(), LEnv::new(env.clone()))),
            Binding::LetCache(_) => None,
        }
    }
}

/// A pending conjunct of a continuation.
#[derive(Clone)]
enum Item {
    Expr(hir::Expr, LEnv),
    /// `<<A>>_sub`: `sub` must change.
    MustChange(hir::Expr, LEnv),
    /// End of the body of `Repeat` `id`: count the path.
    Count(u32),
}

/// Continuation: pending conjuncts (innermost first).
#[derive(Clone, Default)]
struct Cont(Option<Arc<(Item, Cont)>>);

impl Cont {
    fn push(&self, item: Item) -> Cont {
        Cont(Some(Arc::new((item, self.clone()))))
    }
}

/// Static enumeration state.
#[derive(Clone)]
struct St {
    /// Lowering Init (variables are assigned unprimed).
    init: bool,
    /// Next-state variables assigned on this path.
    assigned: Vec<bool>,
    /// Operator expansion depth.
    depth: usize,
    /// Enumerating for `ENABLED`: the end of a path emits even if some
    /// variables are not assigned.
    partial: bool,
}

impl St {
    fn new(nvars: usize, init: bool, assigned: bool) -> St {
        St { init, assigned: vec![assigned; nvars], depth: 0, partial: false }
    }

    fn all_assigned(&self) -> bool {
        self.assigned.iter().all(|a| *a)
    }

    /// One operator expansion deeper.
    fn deeper(&self) -> St {
        St { depth: self.depth + 1, ..self.clone() }
    }
}

pub struct Lowerer<'a> {
    ip: &'a Arc<Interp>,
    /// Layout of encoded states.
    pub typing: AnalyzedTyping,
    /// State of the frame being lowered: the temps of the current entry
    /// point or compiled function and its lowering context. Every entry
    /// point starts from an empty frame, and a compiled function body swaps
    /// the caller's frame out and back (see `frame::Frame`). The fields
    /// below outlive a frame.
    frame: Frame,
    /// Statement nodes lowered since the current entry point was entered,
    /// against `STMT_BUDGET` (see `count`). Not frame-scoped: the body of a
    /// compiled function lowered within the entry point counts against the
    /// same budget (`calls::lower_fn_body`).
    stmts: usize,
    /// Next `Repeat` id. Not frame-scoped: the C backend names the loop
    /// state of a `Stmt::Repeat` after the id (`cgen/stmt.rs`), so the
    /// numbering continues across frames instead of restarting with them.
    repeats: u32,
    /// Which expressions may create strings (not folded at compile time).
    strings: tlx_eval::strings::StringMakers<'a>,
    /// TLC ordering plans, including finite rank tables, shared by shape.
    order_plans: std::collections::HashMap<Shape, Option<Arc<[u64]>>>,
    /// Values of closed constant expressions that do not depend on the
    /// environment, by expression identity (see `const_value`; the
    /// expression is kept alive so that its address is not reused).
    const_cache: std::cell::RefCell<std::collections::HashMap<usize, (Arc<hir::ExprKind>, Option<Value>)>>,
    /// Compiled functions (RECURSIVE operators).
    calls: calls::Calls,
    /// Count the paths of non-assigning branching conjuncts instead of
    /// enumerating them (see `count`).
    count_branches: bool,
    /// Bodies of lazily applied functions being counted (recursion depth).
    /// Not frame-scoped: the counting pass pushes and pops inside one frame
    /// (`count::count_apply`), so the stack is balanced either way.
    count_stack: Vec<usize>,
    /// Shape boxed regions (R3 folding, R9 widening and hoisting; see
    /// `regions`); tests turn it off.
    pub regions: bool,
}

// The frame-scoped fields are read and written as `self.<field>`, so that
// the rest of the lowering needs no `self.frame.` prefix and the swap around
// a compiled function body (see `frame::Frame::swap`) cannot be forgotten in
// one place. The frame has no inherent methods that collide with a
// `Lowerer` method, so method calls still resolve to the lowerer.
impl std::ops::Deref for Lowerer<'_> {
    type Target = Frame;

    fn deref(&self) -> &Frame {
        &self.frame
    }
}

impl std::ops::DerefMut for Lowerer<'_> {
    fn deref_mut(&mut self) -> &mut Frame {
        &mut self.frame
    }
}

impl<'a> Lowerer<'a> {
    /// Lowering for encoded states in `layout`.
    pub fn with_typing(ip: &'a Arc<Interp>, typing: Typing) -> Lowerer<'a> {
        Lowerer {
            ip,
            typing: AnalyzedTyping::new(typing),
            frame: Frame::default(),
            stmts: 0,
            repeats: 0,
            strings: tlx_eval::strings::StringMakers::typed(ip),
            order_plans: Default::default(),
            const_cache: Default::default(),
            calls: Default::default(),
            count_branches: false,
            count_stack: Vec::new(),
            regions: true,
        }
    }

    /// The typing, with the shapes and functions registered while lowering.
    pub fn into_typing(self) -> Typing {
        self.typing.into_inner()
    }

    // ------------------------------------------------------------------
    // entry points

    pub fn lower_action(&mut self, a: &Action) -> LResult<ActionFn> {
        match self.lower_stmt_fn(a.name.clone(), &a.expr, LEnv::new(a.env.clone()), false) {
            // Enumerating every branch is too large: count the paths of
            // non-assigning conjuncts instead.
            Err(Unsupported(m)) if m == BUDGET_EXCEEDED => {
                self.count_branches = true;
                let r = self.lower_stmt_fn(a.name.clone(), &a.expr, LEnv::new(a.env.clone()), false);
                self.count_branches = false;
                r
            }
            r => r,
        }
    }

    pub fn lower_init(&mut self, init: &hir::Expr) -> LResult<ActionFn> {
        self.lower_stmt_fn("Init".into(), init, LEnv::new(Env::default()), true)
    }

    /// A state predicate (invariant).
    pub fn lower_pred(&mut self, name: &str, e: &hir::Expr) -> PredFn {
        self.lower_pred_fn(name, e, false)
    }

    /// A predicate over a transition (an action property such as
    /// `[A]_v`): every variable has a next-state value.
    pub fn lower_trans_pred(&mut self, name: &str, e: &hir::Expr) -> PredFn {
        self.lower_pred_fn(name, e, true)
    }

    /// Run `f` in a fresh frame and put the caller's frame back afterwards.
    ///
    /// Every entry point and every compiled function body lowers from an
    /// empty frame (CODE-12). The frame the caller was in must be restored on
    /// every supported exit, so the `?` inside `f` cannot leave the failed
    /// frame in place: the swap back happens once, after `f` returned.
    fn in_frame<T>(&mut self, f: impl FnOnce(&mut Self) -> LResult<T>) -> LResult<T> {
        let outer = self.frame.swap();
        let r = f(self);
        self.frame = outer;
        r
    }

    fn lower_stmt_fn(&mut self, name: Arc<str>, e: &hir::Expr, env: LEnv, init: bool) -> LResult<ActionFn> {
        self.stmts = 0;
        self.in_frame(|this| {
            let st = St::new(this.nvars(), init, false);
            let mut body = this.go(e, &env, &Cont::default(), &st)?;
            this.hoist_stmt(&mut body);
            // The action's temps are the frame's; `ActionFn` keeps them and
            // the caller's frame comes back.
            let temps = std::mem::take(&mut this.frame.temps);
            Ok(ActionFn { name, temps, body })
        })
    }

    /// A state predicate (`transition` false) or transition predicate in
    /// the interpreter environment `env` (e.g. a quantified liveness atom).
    pub fn lower_pred_in(&mut self, name: &str, e: &hir::Expr, env: &Env, transition: bool) -> PredFn {
        self.lower_pred_env(name, e, LEnv::new(env.clone()), transition)
    }

    /// An action that computes the state expression `e` (e.g. the VIEW) in
    /// the encoding of variable `var` of the typing's layout, assigns it to
    /// that next-state variable and emits; the other variables of the
    /// emitted state are meaningless. `var` may be an extra variable that
    /// the spec does not declare.
    pub fn lower_value_action(&mut self, name: &str, e: &hir::Expr, var: usize) -> Option<ActionFn> {
        let sid = *self.typing.var_sid.get(var)?;
        // No fallible step follows, so the plain swap is the whole scope.
        let outer = self.frame.swap();
        let st = St::new(self.nvars(), false, false);
        self.mat = Some(Materialized::default());
        let v = self.expr_into(e, &LEnv::new(Env::default()), &st, sid);
        let v = self.coerce_enc(v, sid);
        let mut value = self.wrap_materialized(v);
        self.hoist_pred(&mut value);
        let temps = std::mem::take(&mut self.frame.temps);
        self.frame = outer;
        Some(ActionFn { name: name.into(), temps, body: Stmt::Assign { var: var as u32, value, body: Box::new(Stmt::Emit) } })
    }

    fn lower_pred_fn(&mut self, name: &str, e: &hir::Expr, transition: bool) -> PredFn {
        self.lower_pred_env(name, e, LEnv::new(Env::default()), transition)
    }

    fn lower_pred_env(&mut self, name: &str, e: &hir::Expr, env: LEnv, transition: bool) -> PredFn {
        // Infallible operator lowering: the plain swap is the whole scope.
        let outer = self.frame.swap();
        self.stmts = 0;
        let st = St::new(self.nvars(), false, transition);
        self.mat = Some(Materialized::default());
        let body = self.bool_expr(e, &env, &st);
        let mut body = self.wrap_materialized(body);
        self.hoist_pred(&mut body);
        let temps = std::mem::take(&mut self.frame.temps);
        self.frame = outer;
        PredFn { name: name.into(), temps, body }
    }

    // ------------------------------------------------------------------
    // small helpers

    fn nvars(&self) -> usize {
        self.ip.prog.vars.len()
    }

    /// Type of state variable `v` (its encoding).
    fn var_ty(&self, v: usize) -> Ty {
        self.typing.var_ty(v)
    }

    /// Shape of state variable `v`.
    fn var_sid(&self, v: usize) -> ShapeId {
        self.typing.var_sid[v]
    }

    fn var_expr(&self, v: usize) -> Expr {
        Expr::new(self.var_ty(v), ExprKind::Var(v as u32))
    }

    fn next_var_expr(&self, v: usize) -> Expr {
        Expr::new(self.var_ty(v), ExprKind::NextVar(v as u32))
    }

    fn temp(&mut self, ty: Ty) -> Temp {
        self.temps.push(ty);
        (self.temps.len() - 1) as Temp
    }

    /// `r`, a result decided by the shape of `x` alone (e.g. `Len` of a
    /// fixed-length tuple), with `x` still evaluated first unless that
    /// cannot fail: TLC evaluates the operand and reports its errors, and
    /// an encoded value may carry a runtime layout miss (a `Fail` bailing
    /// out to the interpreter, e.g. an EXCEPT value that does not fit the
    /// slot's shape) that the shape does not show.
    fn after_eval(&mut self, x: Expr, r: Expr) -> Expr {
        if self.cannot_fail(&x) {
            return r;
        }
        let (_, bind) = self.share(x);
        let_in(bind, r)
    }

    /// Whether evaluating `x` cannot fail: a constant, (a part of) a
    /// variable or temp, or an application of one whose argument is always
    /// in the domain (an atom table without absent entries, an integer
    /// whose range is covered).
    fn cannot_fail(&mut self, x: &Expr) -> bool {
        match &*x.kind {
            ExprKind::Const(_) | ExprKind::ConstWords(_) | ExprKind::Var(_) | ExprKind::NextVar(_) | ExprKind::Temp(_) => true,
            ExprKind::Slice { base, .. } => self.cannot_fail(base),
            ExprKind::Index { base, arg, map, .. } => {
                let covered = match map {
                    IndexMap::Table(t) => match &*arg.kind {
                        // A binder over a constant list: only its elements.
                        ExprKind::Temp(a) if self.temp_words.contains_key(a) => {
                            self.temp_words[a].iter().all(|&w| t.get(w as usize).is_some_and(|&s| s >= 0))
                        }
                        _ => t.iter().all(|&s| s >= 0),
                    },
                    IndexMap::IntRange { lo, n } => self.int_range(arg).is_some_and(|(a, b)| a >= *lo && b < *lo + *n as i64),
                };
                covered && self.cannot_fail(base) && self.cannot_fail(arg)
            }
            _ => false,
        }
    }

    /// `x` itself if it is trivial to duplicate, else a fresh temp together
    /// with the binding to wrap around its uses (see `let_in`).
    fn share(&mut self, x: Expr) -> (Expr, Option<(Temp, Expr)>) {
        if is_trivial(&x) {
            return (x, None);
        }
        let t = self.temp(x.ty);
        self.note_temp(t, &x);
        (temp_ref(x.ty, t), Some((t, x)))
    }

    /// A fresh temp of type `ety` bound to the elements of iteration source
    /// `src`; the possible encodings of a constant list of one-word
    /// elements are recorded (an application of a function to it is then
    /// known to be in the domain, see `cannot_fail`).
    fn iter_temp(&mut self, ety: Ty, src: &Expr) -> Temp {
        let t = self.temp(ety);
        if let ExprKind::ConstElems { words, count, .. } = &*src.kind {
            if words.len() == *count as usize {
                self.temp_words.insert(t, words.clone());
            }
        }
        t
    }

    /// Record what is statically known about the value `x` bound to temp
    /// `t`: the range of an integer, a cardinality bound of a set.
    fn note_temp(&mut self, t: Temp, x: &Expr) {
        if x.ty == Ty::Int {
            if let Some(r) = self.int_range(x) {
                self.temp_ranges.insert(t, r);
            }
        } else if let Some(n) = self.card_bound(x) {
            self.temp_cards.insert(t, n);
        }
    }

    /// Count a statement node against the budget.
    fn count(&mut self) -> LResult<()> {
        self.stmts += 1;
        if self.stmts > STMT_BUDGET {
            return unsupported(BUDGET_EXCEEDED);
        }
        Ok(())
    }

    /// Base environment for the body of definition `d`: a LET definition
    /// sees the environment of its use, a module-level one starts empty.
    fn def_env(&self, d: hir::DefId, env: &LEnv) -> LEnv {
        if self.ip.prog.def_is_let(d) {
            env.clone()
        } else {
            LEnv::new(Env::default())
        }
    }

    // ------------------------------------------------------------------
    // shapes (typed lowering)

    fn shape_of(&self, t: Ty) -> Option<&Shape> {
        match t {
            Ty::Enc(sid) => Some(self.typing.shape(sid)),
            _ => None,
        }
    }

    /// Intern `s`.
    fn sid(&mut self, s: &Shape) -> ShapeId {
        self.typing.id(s)
    }

    /// Words of the encoding of `s` (interning it).
    fn words_of(&mut self, s: &Shape) -> u32 {
        let id = self.sid(s);
        self.words(id)
    }

    /// Words of the encoding of interned shape `sid`.
    fn words(&self, sid: ShapeId) -> u32 {
        self.typing.words(sid)
    }

    /// The word at `offset` of `base`, holding an integer in `0..=hi`.
    fn int_word(&mut self, base: Expr, offset: usize, hi: i64) -> Expr {
        let sid = self.sid(&Shape::Int { lo: 0, hi });
        Expr::new(Ty::Int, ExprKind::Convert(Expr::new(Ty::Enc(sid), ExprKind::Slice { base, loc: FieldLoc::Words(offset) })))
    }

    /// Build a composite of shape `sid` (`Record`, `Tuple`, `Fcn`) from its
    /// component expressions `parts`: emits `Pack` when any field is sub-word
    /// packed, else `Concat`.
    fn pack_shape(&self, sid: ShapeId, parts: Vec<Expr>) -> Expr {
        let fl = FieldLayout::of_shape(self.typing.shape(sid)).expect("product/fcn shape");
        let mut locs = fl.locs.into_vec();
        for i in 0..parts.len().saturating_sub(locs.len()) {
            locs.push(FieldLoc::Words(fl.words + i));
        }
        debug_assert_eq!(locs.len(), parts.len());
        self.pack_locs(sid, locs, parts)
    }

    /// Build a composite of shape `sid` placing `parts[i]` at `locs[i]`: emits
    /// `Concat` when all locations are contiguous word offsets covering
    /// `words(sid)`, else `Pack`.
    fn pack_locs(&self, sid: ShapeId, locs: Vec<FieldLoc>, parts: Vec<Expr>) -> Expr {
        let has_bits = locs.iter().any(|l| matches!(l, FieldLoc::Bits(_)));
        if !has_bits {
            let mut off = 0usize;
            let mut contiguous = true;
            for (loc, p) in locs.iter().zip(&parts) {
                let FieldLoc::Words(w) = *loc else { unreachable!() };
                let Ty::Enc(psid) = p.ty else {
                    contiguous = false;
                    break;
                };
                if w != off {
                    contiguous = false;
                    break;
                }
                off += self.words(psid) as usize;
            }
            if contiguous && off == self.words(sid) as usize {
                return Expr::new(Ty::Enc(sid), ExprKind::Concat(parts));
            }
        }
        Expr::new(Ty::Enc(sid), ExprKind::Pack { locs: locs.into(), parts })
    }
}

// ---------------------------------------------------------------------------
// IR construction helpers

/// A boxed constant.
fn val_lit(v: Value) -> Expr {
    Expr::new(Ty::Val, ExprKind::Const(v))
}

fn bool_lit(b: bool) -> Expr {
    Expr::new(Ty::Bool, ExprKind::Const(if b { Value::TRUE } else { Value::FALSE }))
}

fn int_lit(i: i64) -> Expr {
    Expr::new(Ty::Int, ExprKind::Const(Value::Int(i)))
}

/// A constant, unboxed when scalar.
fn const_expr(v: Value) -> Expr {
    match v {
        Value::Bool(_) => Expr::new(Ty::Bool, ExprKind::Const(v)),
        Value::Int(_) => Expr::new(Ty::Int, ExprKind::Const(v)),
        v => val_lit(v),
    }
}

fn temp_ref(ty: Ty, t: Temp) -> Expr {
    Expr::new(ty, ExprKind::Temp(t))
}

fn not(x: Expr) -> Expr {
    Expr::new(Ty::Bool, ExprKind::Not(x))
}

fn and(parts: Vec<Expr>) -> Expr {
    Expr::new(Ty::Bool, ExprKind::And(parts))
}

fn or(parts: Vec<Expr>) -> Expr {
    let mut parts = int_ranges(parts);
    if parts.len() == 1 {
        return parts.pop().unwrap();
    }
    Expr::new(Ty::Bool, ExprKind::Or(parts))
}

/// Adjacent disjuncts `x = c1`, `x = c2`, ... (the same integer `x`,
/// consecutive constants in any order) as one range test
/// `c_min <= x /\ x <= c_max` (e.g. `x \in {-1, 0, 1}`).
fn int_ranges(parts: Vec<Expr>) -> Vec<Expr> {
    fn eq_const(e: &Expr) -> Option<(&Expr, i64)> {
        let ExprKind::Eq(a, b) = &*e.kind else { return None };
        match (&*a.kind, &*b.kind) {
            (_, ExprKind::Const(Value::Int(c))) if a.ty == Ty::Int => Some((a, *c)),
            (ExprKind::Const(Value::Int(c)), _) if b.ty == Ty::Int => Some((b, *c)),
            _ => None,
        }
    }
    let mut out: Vec<Expr> = Vec::with_capacity(parts.len());
    let mut i = 0;
    while i < parts.len() {
        let Some((x, c)) = eq_const(&parts[i]).filter(|(x, _)| simple_int(x)) else {
            out.push(parts[i].clone());
            i += 1;
            continue;
        };
        let mut cs = vec![c];
        let mut j = i + 1;
        while let Some((y, d)) = parts.get(j).and_then(eq_const) {
            if !same_simple(x, y) {
                break;
            }
            cs.push(d);
            j += 1;
        }
        cs.sort_unstable();
        cs.dedup();
        let (lo, hi) = (cs[0], cs[cs.len() - 1]);
        if cs.len() >= 2 && hi.checked_sub(lo).is_some_and(|d| d as u64 == cs.len() as u64 - 1) {
            let ge = Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Ge, x.clone(), int_lit(lo)));
            let le = Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Le, x.clone(), int_lit(hi)));
            out.push(and(vec![ge, le]));
        } else {
            out.extend(parts[i..j].iter().cloned());
        }
        i = j;
    }
    out
}

/// An integer read from a variable or temp (no runtime error, cheap to
/// evaluate twice).
fn simple_int(e: &Expr) -> bool {
    match &*e.kind {
        ExprKind::Temp(_) | ExprKind::Var(_) | ExprKind::NextVar(_) => true,
        ExprKind::Convert(x) | ExprKind::Slice { base: x, .. } => simple_int(x),
        _ => false,
    }
}

/// Structural equality of two `simple_int` expressions.
fn same_simple(a: &Expr, b: &Expr) -> bool {
    a.ty == b.ty
        && match (&*a.kind, &*b.kind) {
            (ExprKind::Temp(x), ExprKind::Temp(y)) => x == y,
            (ExprKind::Var(x), ExprKind::Var(y)) | (ExprKind::NextVar(x), ExprKind::NextVar(y)) => x == y,
            (ExprKind::Convert(x), ExprKind::Convert(y)) => same_simple(x, y),
            (ExprKind::Slice { base: x, loc: i }, ExprKind::Slice { base: y, loc: j }) => i == j && same_simple(x, y),
            _ => false,
        }
}

/// Conjunction, `TRUE` if empty.
fn and_all(parts: Vec<Expr>) -> Expr {
    if parts.is_empty() {
        bool_lit(true)
    } else {
        and(parts)
    }
}

/// Disjunction, `FALSE` if empty.
fn or_any(parts: Vec<Expr>) -> Expr {
    if parts.is_empty() {
        bool_lit(false)
    } else {
        or(parts)
    }
}

fn eq(a: Expr, b: Expr) -> Expr {
    Expr::new(Ty::Bool, ExprKind::Eq(a, b))
}

fn is_false(e: &Expr) -> bool {
    matches!(&*e.kind, ExprKind::Const(Value::Bool(false)))
}

/// Pure and cheap: may be duplicated instead of bound to a temp.
fn is_trivial(x: &Expr) -> bool {
    match &*x.kind {
        ExprKind::Const(_) | ExprKind::ConstWords(_) | ExprKind::Var(_) | ExprKind::NextVar(_) | ExprKind::Temp(_) => true,
        // Cheap to recompute, and keeping the structure (e.g. an integer
        // range) lets consumers specialize.
        ExprKind::Convert(y) | ExprKind::SeqLen(y) => is_trivial(y),
        ExprKind::ValOp { op: tlx_sema::builtins::Builtin::DotDot, args } => args.iter().all(is_trivial),
        _ => false,
    }
}

/// `body` under `Let`s. Bindings are given innermost first: the last one is
/// evaluated first, so a binding may use the temps of later ones.
fn let_in(bindings: impl IntoIterator<Item = (Temp, Expr)>, body: Expr) -> Expr {
    bindings.into_iter().fold(body, |b, (temp, value)| Expr::new(b.ty, ExprKind::Let { temp, value, body: b }))
}

fn to_val(x: Expr) -> Expr {
    if x.ty == Ty::Val {
        x
    } else {
        Expr::new(Ty::Val, ExprKind::Convert(x))
    }
}

fn to_bool(x: Expr) -> Expr {
    if x.ty == Ty::Bool {
        x
    } else {
        Expr::new(Ty::Bool, ExprKind::Convert(x))
    }
}

/// The expression of an `as_int`/`as_bool` result, converted or not.
fn either(r: Result<Expr, Expr>) -> Expr {
    match r {
        Ok(x) | Err(x) => x,
    }
}

fn guard(cond: Expr, then: Stmt) -> Stmt {
    Stmt::Guard { cond, then: Box::new(then) }
}

/// `IF c THEN t ELSE f` as two guarded branches.
fn if_stmt(c: Expr, t: Stmt, f: Stmt) -> Stmt {
    let nc = not(c.clone());
    Stmt::Branches(vec![guard(c, t), guard(nc, f)])
}

#[cfg(test)]
mod frame_tests {
    use super::*;
    use tlx_layout::{Layout, Shape};
    use tlx_runtime::Model;
    use tlx_testkit::spec;

    /// A recursive operator is compiled to a function, so lowering `Next`
    /// exercises the nested frame of `calls::lower_fn_body` as well as the
    /// frame of the entry point; `G` is a second, independent function
    /// applied after `F`, whose lowering would see `F` on the inline stack
    /// if the nested frame leaked back into the entry point.
    const SPEC: &str = r#"---- MODULE Frame ----
EXTENDS Naturals, FiniteSets
VARIABLES x, y
RECURSIVE F(_), G(_)
F(n) == IF n <= 0 THEN 0 ELSE F(n - 1) + 1
G(n) == IF n <= 0 THEN 0 ELSE G(n - 1) + 1
Init == x = 0 /\ y = 0
Next == x < 3 /\ x' = F(x) /\ y' = G(x)
Inv == x <= y + 3 /\ Cardinality({v \in 1..4 : v <= x}) >= 0
====
"#;

    /// `\A` over a state-dependent domain with an assigning body: the
    /// lowering cannot enumerate it and fails, which exercises the error
    /// exit of an entry point.
    const ERR_SPEC: &str = r#"---- MODULE FrameErr ----
EXTENDS Naturals
VARIABLES x
Init == x = 0
Next == \A i \in {j \in 1..3 : j <= x} : x' = i
====
"#;

    fn model(src: &str, invariants: bool) -> tlx_eval::InterpModel {
        let cfg = if invariants { "INIT Init\nNEXT Next\nINVARIANT Inv\n" } else { "INIT Init\nNEXT Next\n" };
        spec::load(src, cfg)
    }

    fn lowerer(model: &tlx_eval::InterpModel) -> Lowerer<'_> {
        let layout = Arc::new(Layout::new(vec![Shape::Int { lo: 0, hi: 8 }, Shape::Int { lo: 0, hi: 8 }]));
        Lowerer::with_typing(&model.ip, Typing::new(layout))
    }

    fn action<'a>(model: &'a tlx_eval::InterpModel, name: &str) -> &'a Action {
        model.actions().iter().find(|a| &*a.name == name).unwrap_or_else(|| panic!("no action {name}"))
    }

    /// Put a value a fresh frame does not have in every frame-scoped field:
    /// a frame that the caller's data reached is then visible in the lowered
    /// result and in what the entry point leaves behind.
    fn junk(lw: &mut Lowerer<'_>) {
        lw.frame.temps.push(Ty::Int);
        lw.frame.temp_ranges.insert(0, (1, 2));
        lw.frame.temp_cards.insert(0, 3);
        lw.frame.temp_words.insert(0, vec![1u64, 2].into());
        lw.frame.mat = Some(Materialized::default());
        lw.frame.at = Some(int_lit(7));
        lw.frame.inline_stack = vec![hir::DefId(0)];
        lw.frame.fn_result = vec![(hir::DefId(0), Ty::Int)];
        lw.frame.primed = true;
    }

    /// Every field of `junk` is still there.
    fn assert_junk(lw: &Lowerer<'_>) {
        assert_eq!(lw.frame.temps.len(), 1, "temps");
        assert_eq!(lw.frame.temp_ranges.get(&0), Some(&(1, 2)), "temp_ranges");
        assert_eq!(lw.frame.temp_cards.get(&0), Some(&3), "temp_cards");
        assert!(lw.frame.temp_words.contains_key(&0), "temp_words");
        assert!(lw.frame.mat.is_some(), "mat");
        assert!(lw.frame.at.is_some(), "at");
        assert_eq!(lw.frame.inline_stack, vec![hir::DefId(0)], "inline_stack");
        assert_eq!(lw.frame.fn_result, vec![(hir::DefId(0), Ty::Int)], "fn_result");
        assert!(lw.frame.primed, "primed");
    }

    /// No frame-scoped field is left behind.
    fn assert_empty(lw: &Lowerer<'_>) {
        assert!(lw.frame.temps.is_empty(), "temps");
        assert!(lw.frame.temp_ranges.is_empty(), "temp_ranges");
        assert!(lw.frame.temp_cards.is_empty(), "temp_cards");
        assert!(lw.frame.temp_words.is_empty(), "temp_words");
        assert!(lw.frame.mat.is_none(), "mat");
        assert!(lw.frame.at.is_none(), "at");
        assert!(lw.frame.inline_stack.is_empty(), "inline_stack");
        assert!(lw.frame.fn_result.is_empty(), "fn_result");
        assert!(!lw.frame.primed, "primed");
    }

    fn dump(s: &Stmt) -> String {
        let mut out = String::new();
        crate::ir_fmt::stmt(s, 0, &mut out);
        out
    }

    #[test]
    fn entry_point_ignores_the_caller_frame() {
        let m = model(SPEC, true);
        let reference = {
            let mut lw = lowerer(&m);
            dump(&lw.lower_action(action(&m, "Next")).expect("Next lowers").body)
        };
        let mut lw = lowerer(&m);
        junk(&mut lw);
        let lowered = lw.lower_action(action(&m, "Next")).expect("Next lowers");
        assert_eq!(dump(&lowered.body), reference, "the caller's frame reached the entry point");
        assert_junk(&lw);
    }

    #[test]
    fn entry_point_leaves_no_residue() {
        let m = model(SPEC, true);
        let mut lw = lowerer(&m);
        lw.lower_init(m.init_expr()).expect("Init lowers");
        assert_empty(&lw);
        let i = m.invariant_names().iter().position(|n| n == "Inv").expect("Inv");
        lw.lower_pred("Inv", &m.invariant_exprs()[i]);
        assert_empty(&lw);
        // A forward reference for the prediction: lowering an action that
        // applies two functions leaves neither frame behind either.
        lw.lower_action(action(&m, "Next")).expect("Next lowers");
        assert_empty(&lw);
    }

    #[test]
    fn entry_point_restores_the_caller_frame_on_an_error() {
        let m = model(ERR_SPEC, false);
        let mut lw = lowerer(&m);
        junk(&mut lw);
        match lw.lower_action(action(&m, "Next")) {
            Err(e) => assert!(e.0.contains("state-dependent"), "unexpected error: {}", e.0),
            Ok(_) => panic!("a state-dependent \\A domain over an assigning body must not lower"),
        }
        assert_junk(&lw);
    }

    #[test]
    fn in_frame_runs_empty_and_restores_on_both_exits() {
        let m = model(SPEC, false);
        let mut lw = lowerer(&m);
        junk(&mut lw);
        let inside = lw.in_frame(|this| Ok((this.frame.temps.len(), this.frame.primed))).expect("no error");
        assert_eq!(inside, (0, false), "the body must run in a fresh frame");
        assert_junk(&lw);
        let r: LResult<()> = lw.in_frame(|_| unsupported("boom"));
        assert!(r.is_err(), "the error must propagate");
        assert_junk(&lw);
    }
}
