//! Incremental IR and JIT reuse across layout-miss restarts.
//!
//! When a layout miss widens variable `v`, actions and predicates whose HIR
//! and lowered IR never inspect `v`'s shape (at most copying `v` unchanged via
//! `Stmt::Assign { var: v, value: ExprKind::Var(v), .. }`) lower identically
//! under the new layout up to `ShapeId` / `FuncId` remapping and updating
//! the `Ty::Enc` on those unchanged copies. Reusing them avoids re-lowering
//! unchanged parts of large specs on every layout-miss restart while still
//! verifying the full assembled program with `verify::Program`.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use tlx_eval::env::{Binding, Env};
use tlx_eval::model::liveness::StateAtom;
use tlx_eval::{Interp, InterpModel};
use tlx_layout::Shape;
use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{self, ConstId, DefId, DefKind, ExprKind as H, LocalId, OpRef};

use crate::binding::{Flow, Policy, Scope, State};
use crate::ir::{ActionFn, Expr, ExprKind, FnDef, PredFn, RefOp, ShapeId, Stmt, Ty};
use crate::lower::Lowerer;
use crate::types::Typing;

/// Cross-attempt compilation cache owned by `Speculation` in `enc::driver`.
#[derive(Default)]
pub(crate) struct CompileCache {
    prev: Option<PrevIr>,
    #[cfg(feature = "jit")]
    pub(crate) jit: crate::jit::JitCache,
}

/// Verified IR snapshot from the previous attempt along with exact per-item
/// shape dependencies.
struct PrevIr {
    typing: Typing,
    def_shapes: Vec<(DefId, Shape)>,
    next_repeat: u32,
    actions: Vec<Option<CachedAction>>,
    invariants: Vec<CachedPred>,
    aprops: Vec<CachedPred>,
}

struct CachedAction {
    func: ActionFn,
    deps: IrDeps,
}

struct CachedPred {
    func: PredFn,
    deps: IrDeps,
}

/// Variables whose layout shape an IR item depends on (excluding pure
/// `UNCHANGED` copies `Assign { var: v, value: Var(v) }`).
#[derive(Clone)]
struct IrDeps {
    vars: Vec<bool>,
    /// Conservative bailout: depends on an unknown set of variables (e.g. an
    /// `Interp` node, `ENABLED`, or an unresolved override) and is never reused.
    all: bool,
}

impl IrDeps {
    fn new(nvars: usize) -> Self {
        Self { vars: vec![false; nvars], all: false }
    }

    fn mark_var(&mut self, v: usize) {
        if let Some(bit) = self.vars.get_mut(v) {
            *bit = true;
        }
    }

    fn unaffected(&self, changed_vars: &[bool]) -> bool {
        !self.all && self.vars.iter().zip(changed_vars).all(|(&dep, &chg)| !(dep && chg))
    }
}

/// Session that imports unaffected actions and predicates from `prev` into
/// `lw`, remapping `ShapeId`s, `FuncId`s, and pure `UNCHANGED` copy types.
pub(crate) struct ReuseSession<'a> {
    prev: &'a PrevIr,
    changed_vars: Vec<bool>,
    defs_changed: bool,
    shape_map: HashMap<ShapeId, ShapeId>,
    fn_map: HashMap<u32, u32>,
}

impl CompileCache {
    /// Start an incremental reuse session against the new `layout` and
    /// `def_shapes`, advancing `lw`'s `Repeat` id counter past any ids that
    /// reused IR may reference.
    pub(crate) fn begin<'a>(
        &'a self,
        lw: &mut Lowerer<'_>,
        new_vars: &[Shape],
        new_defs: &[(DefId, Shape)],
        n_actions: usize,
        n_invariants: usize,
        n_aprops: usize,
    ) -> Option<ReuseSession<'a>> {
        let prev = self.prev.as_ref()?;
        if prev.typing.layout.vars.len() != new_vars.len()
            || prev.actions.len() != n_actions
            || prev.invariants.len() != n_invariants
            || prev.aprops.len() != n_aprops
        {
            return None;
        }
        let changed_vars: Vec<bool> = prev.typing.layout.vars.iter().zip(new_vars).map(|(a, b)| a != b).collect();
        let defs_changed = prev.def_shapes != new_defs;
        lw.set_repeats(prev.next_repeat);
        Some(ReuseSession { prev, changed_vars, defs_changed, shape_map: HashMap::new(), fn_map: HashMap::new() })
    }

    /// Record the verified IR of the current attempt for subsequent restarts.
    /// Dependencies are the union of HIR-level variable references (via the
    /// shared `crate::binding` walk, before shape-dependent constant folding
    /// can prune a branch or fold a guard to `FALSE`) and compiled-IR read
    /// summaries (via `Lowerer::expression_summary`).
    pub(crate) fn update(
        &mut self,
        base: &InterpModel,
        lw: &Lowerer<'_>,
        def_shapes: &[(DefId, Shape)],
        actions: &[Option<ActionFn>],
        invariants: &[PredFn],
        aprops: &[PredFn],
    ) {
        let typing: &Typing = &lw.typing;
        let nvars = typing.layout.vars.len();
        let actions = actions
            .iter()
            .enumerate()
            .map(|(i, a)| {
                a.as_ref().map(|f| {
                    let mut deps = IrDeps::new(nvars);
                    if let Some(act) = base.actions().get(i) {
                        scan_hir(&base.ip, &act.expr, &act.env, true, &mut deps);
                    } else {
                        deps.all = true;
                    }
                    scan_stmt_ir(&f.body, lw, typing, &mut deps);
                    CachedAction { func: f.clone(), deps }
                })
            })
            .collect();
        let empty_env = Env::default();
        let mut inv_hirs: Vec<(&hir::Expr, &Env)> = Vec::with_capacity(invariants.len());
        for e in base.invariant_exprs() {
            inv_hirs.push((e, &empty_env));
        }
        for e in base.constraint_exprs() {
            inv_hirs.push((e, &empty_env));
        }
        for atom in base.live.state_atoms.iter() {
            if let StateAtom::Pred(a) = atom {
                inv_hirs.push((&a.expr, &a.env));
            }
        }
        let invariants = invariants
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let mut deps = IrDeps::new(nvars);
                if let Some(&(e, env)) = inv_hirs.get(i) {
                    scan_hir(&base.ip, e, env, false, &mut deps);
                } else {
                    deps.all = true;
                }
                add_expr_summary(&p.body, lw, &mut deps);
                CachedPred { func: p.clone(), deps }
            })
            .collect();
        let mut aprop_hirs: Vec<(&hir::Expr, &Env)> = Vec::with_capacity(aprops.len());
        for e in base.action_property_exprs() {
            aprop_hirs.push((e, &empty_env));
        }
        for e in base.action_constraint_exprs() {
            aprop_hirs.push((e, &empty_env));
        }
        for atom in base.live.action_atoms.iter() {
            aprop_hirs.push((&atom.expr, &atom.env));
        }
        let aprops = aprops
            .iter()
            .enumerate()
            .map(|(i, p)| {
                let mut deps = IrDeps::new(nvars);
                if let Some(&(e, env)) = aprop_hirs.get(i) {
                    scan_hir(&base.ip, e, env, false, &mut deps);
                } else {
                    deps.all = true;
                }
                add_expr_summary(&p.body, lw, &mut deps);
                CachedPred { func: p.clone(), deps }
            })
            .collect();
        self.prev = Some(PrevIr {
            typing: typing.clone(),
            def_shapes: def_shapes.to_vec(),
            next_repeat: lw.repeats(),
            actions,
            invariants,
            aprops,
        });
    }
}

impl ReuseSession<'_> {
    /// Import cached action `i` into `lw` if its shape dependencies are
    /// unaffected by the layout change.
    pub(crate) fn reuse_action(&mut self, i: usize, lw: &mut Lowerer<'_>) -> Option<ActionFn> {
        let cached = self.prev.actions.get(i)?.as_ref()?;
        if !cached.deps.unaffected(&self.changed_vars) {
            return None;
        }
        let temps = cached.func.temps.iter().map(|&t| self.remap_ty(t, lw)).collect();
        let body = self.remap_stmt(&cached.func.body, lw);
        Some(ActionFn { name: cached.func.name.clone(), temps, body })
    }

    /// Import cached invariant `i` into `lw` if neither its variable shape
    /// dependencies nor the materialized definitions changed.
    pub(crate) fn reuse_invariant(&mut self, i: usize, lw: &mut Lowerer<'_>) -> Option<PredFn> {
        if self.defs_changed {
            return None;
        }
        let cached = self.prev.invariants.get(i)?;
        if !cached.deps.unaffected(&self.changed_vars) {
            return None;
        }
        let temps = cached.func.temps.iter().map(|&t| self.remap_ty(t, lw)).collect();
        let body = self.remap_expr(&cached.func.body, lw);
        Some(PredFn { name: cached.func.name.clone(), temps, body })
    }

    /// Import cached action property `i` into `lw` if neither its variable
    /// shape dependencies nor the materialized definitions changed.
    pub(crate) fn reuse_aprop(&mut self, i: usize, lw: &mut Lowerer<'_>) -> Option<PredFn> {
        if self.defs_changed {
            return None;
        }
        let cached = self.prev.aprops.get(i)?;
        if !cached.deps.unaffected(&self.changed_vars) {
            return None;
        }
        let temps = cached.func.temps.iter().map(|&t| self.remap_ty(t, lw)).collect();
        let body = self.remap_expr(&cached.func.body, lw);
        Some(PredFn { name: cached.func.name.clone(), temps, body })
    }

    fn remap_sid(&mut self, old: ShapeId, lw: &mut Lowerer<'_>) -> ShapeId {
        if let Some(&new) = self.shape_map.get(&old) {
            return new;
        }
        let shape = self.prev.typing.shape(old);
        let new = lw.typing.id(shape);
        self.shape_map.insert(old, new);
        new
    }

    fn remap_ty(&mut self, ty: Ty, lw: &mut Lowerer<'_>) -> Ty {
        match ty {
            Ty::Enc(sid) => Ty::Enc(self.remap_sid(sid, lw)),
            other => other,
        }
    }

    fn remap_fn(&mut self, old_id: u32, lw: &mut Lowerer<'_>) -> u32 {
        if let Some(&new_id) = self.fn_map.get(&old_id) {
            return new_id;
        }
        let old_f = &self.prev.typing.funcs[old_id as usize];
        let new_id = lw.typing.funcs.len() as u32;
        self.fn_map.insert(old_id, new_id);
        let placeholder = FnDef {
            name: old_f.name.clone(),
            params: Vec::new(),
            temps: Vec::new(),
            ret: Ty::Val,
            body: Expr::new(Ty::Val, ExprKind::Fail(Arc::from("importing cached function"))),
            budgeted: old_f.budgeted,
        };
        lw.typing.funcs.push(placeholder);
        let temps = old_f.temps.iter().map(|&t| self.remap_ty(t, lw)).collect();
        let ret = self.remap_ty(old_f.ret, lw);
        let body = self.remap_expr(&old_f.body, lw);
        lw.typing.funcs[new_id as usize] =
            FnDef { name: old_f.name.clone(), params: old_f.params.clone(), temps, ret, body, budgeted: old_f.budgeted };
        lw.typing.funcs_changed();
        new_id
    }

    fn remap_stmt(&mut self, s: &Stmt, lw: &mut Lowerer<'_>) -> Stmt {
        let mut out = s.clone();
        self.remap_stmt_in_place(&mut out, lw);
        out
    }

    fn remap_stmt_in_place(&mut self, s: &mut Stmt, lw: &mut Lowerer<'_>) {
        if let Stmt::Assign { var, value, body } = s {
            if is_unchanged_copy(*var, value, &self.prev.typing) {
                value.ty = Ty::Enc(lw.typing.var_sid[*var as usize]);
                self.remap_stmt_in_place(body, lw);
                return;
            }
        }
        if let Some(e) = s.expr_mut() {
            self.remap_expr_in_place(e, lw);
        }
        s.for_each_sub_stmt_mut(&mut |sub| self.remap_stmt_in_place(sub, lw));
    }

    fn remap_expr(&mut self, e: &Expr, lw: &mut Lowerer<'_>) -> Expr {
        let mut out = e.clone();
        self.remap_expr_in_place(&mut out, lw);
        out
    }

    fn remap_expr_in_place(&mut self, e: &mut Expr, lw: &mut Lowerer<'_>) {
        e.ty = self.remap_ty(e.ty, lw);
        match &mut *e.kind {
            ExprKind::ConstElems { elem, .. } => *elem = self.remap_sid(*elem, lw),
            ExprKind::RefOp { op: RefOp::FromEnc(sid) | RefOp::ToEnc(sid), args } => {
                *sid = self.remap_sid(*sid, lw);
                for a in args {
                    self.remap_expr_in_place(a, lw);
                }
                return;
            }
            ExprKind::Call { func, args } => {
                *func = self.remap_fn(*func, lw);
                for a in args {
                    self.remap_expr_in_place(a, lw);
                }
                return;
            }
            ExprKind::Enabled(sub) => {
                self.remap_stmt_in_place(sub, lw);
                return;
            }
            _ => {}
        }
        e.for_each_child_mut(&mut |c| self.remap_expr_in_place(c, lw));
    }
}

/// Whether `Stmt::Assign { var, value, .. }` is a pure `UNCHANGED var` copy
/// (`value` is `ExprKind::Var(var)` in `var`'s layout shape).
fn is_unchanged_copy(var: u32, value: &Expr, typing: &Typing) -> bool {
    matches!(&*value.kind, ExprKind::Var(u) if *u == var) && typing.var_sid.get(var as usize).is_some_and(|&sid| value.ty == Ty::Enc(sid))
}

/// Record transitive variable reads of IR expression `e` using the shared
/// compiled-function summary graph (`Lowerer::expression_summary`).
fn add_expr_summary(e: &Expr, lw: &Lowerer<'_>, deps: &mut IrDeps) {
    match lw.expression_summary(e).reads {
        Some(reads) => {
            for v in reads.cur.into_iter().chain(reads.next) {
                deps.mark_var(v as usize);
            }
        }
        None => deps.all = true,
    }
}

/// Walk lowered statement `s` for assignment targets and expression/callee
/// reads, exempting pure `UNCHANGED` copies `Assign { var: v, value: Var(v) }`.
fn scan_stmt_ir(s: &Stmt, lw: &Lowerer<'_>, typing: &Typing, deps: &mut IrDeps) {
    if let Stmt::Assign { var, value, body } = s {
        if is_unchanged_copy(*var, value, typing) {
            scan_stmt_ir(body, lw, typing, deps);
            return;
        }
        deps.mark_var(*var as usize);
    }
    if let Some(e) = s.expr() {
        add_expr_summary(e, lw, deps);
    }
    s.for_each_sub_stmt(&mut |sub| scan_stmt_ir(sub, lw, typing, deps));
}

/// Policy over the shared `crate::binding` HIR driver that collects every
/// state variable referenced before shape-dependent constant folding, while
/// exempting statement-position `UNCHANGED` over pure variable tuples (which
/// `scan_stmt_ir` verifies against the lowered IR).
struct CacheHirPolicy<'a> {
    deps: &'a mut IrDeps,
    seen: HashSet<(DefId, bool)>,
    stmt_pos: bool,
}

impl CacheHirPolicy<'_> {
    fn walk_with(&mut self, s: &mut State<'_>, e: &hir::Expr, depth: usize, stmt_pos: bool) {
        let saved = std::mem::replace(&mut self.stmt_pos, stmt_pos);
        s.walk(self, e, depth);
        self.stmt_pos = saved;
    }

    fn is_pure_var_tuple(s: &State<'_>, e: &hir::Expr, depth: usize) -> bool {
        if depth > 16 {
            return false;
        }
        match &*e.kind {
            H::Var(_) => true,
            H::Tuple(es) => es.iter().all(|c| Self::is_pure_var_tuple(s, c, depth + 1)),
            H::Apply { op: OpRef::Def(d), args } if args.is_empty() => {
                let d = s.ip.redirect_def(*d);
                let def = &s.ip.prog.defs[d.idx()];
                if def.builtin.is_some() || s.ip.has_def_value(d) {
                    return false;
                }
                match &def.kind {
                    DefKind::Op(body) => {
                        if s.ip.prog.def_is_let(d) {
                            Self::is_pure_var_tuple(s, body, depth + 1)
                        } else {
                            let empty = State::new(s.ip, Scope::Single, Env::default());
                            Self::is_pure_var_tuple(&empty, body, depth + 1)
                        }
                    }
                    _ => false,
                }
            }
            H::Local(l) => match s.lookup(*l) {
                Some(Binding::Thunk(t)) => {
                    let sub = State::new(s.ip, Scope::Single, t.env.clone());
                    Self::is_pure_var_tuple(&sub, &t.expr, depth + 1)
                }
                Some(Binding::Name(id, tenv)) => {
                    let sub = State::new(s.ip, Scope::Single, tenv.clone());
                    Self::is_pure_var_tuple(&sub, s.ip.prog.arena_expr(*id), depth + 1)
                }
                _ => false,
            },
            _ => false,
        }
    }
}

impl Policy for CacheHirPolicy<'_> {
    fn node(&mut self, s: &mut State<'_>, e: &hir::Expr, depth: usize) -> Flow {
        if self.deps.all || depth > 64 {
            self.deps.all = true;
            return Flow::Done;
        }
        if self.stmt_pos {
            let next_depth = depth + 1;
            match &*e.kind {
                H::Builtin { op: B::Unchanged, args } if Self::is_pure_var_tuple(s, &args[0], 0) => {
                    return Flow::Done;
                }
                H::And(es) | H::Or(es) => {
                    for c in es {
                        self.walk_with(s, c, next_depth, true);
                    }
                    return Flow::Done;
                }
                H::If { cond, then, els } => {
                    self.walk_with(s, cond, next_depth, false);
                    self.walk_with(s, then, next_depth, true);
                    self.walk_with(s, els, next_depth, true);
                    return Flow::Done;
                }
                H::Case { arms, other } => {
                    for (g, v) in arms {
                        self.walk_with(s, g, next_depth, false);
                        self.walk_with(s, v, next_depth, true);
                    }
                    if let Some(o) = other {
                        self.walk_with(s, o, next_depth, true);
                    }
                    return Flow::Done;
                }
                H::Quant { bounds, body, .. } => {
                    for b in bounds {
                        self.walk_with(s, &b.set, next_depth, false);
                    }
                    self.walk_with(s, body, next_depth, true);
                    return Flow::Done;
                }
                H::Builtin { op: B::Implies, args } => {
                    self.walk_with(s, &args[0], next_depth, false);
                    self.walk_with(s, &args[1], next_depth, true);
                    return Flow::Done;
                }
                H::Let { defs, body } => {
                    let saved = std::mem::replace(&mut self.stmt_pos, false);
                    for d in defs {
                        s.def(self, *d);
                    }
                    self.stmt_pos = saved;
                    self.walk_with(s, body, next_depth, true);
                    return Flow::Done;
                }
                H::Apply { op, args } => {
                    for a in args {
                        self.walk_with(s, a, next_depth, false);
                    }
                    let saved = self.stmt_pos;
                    self.op(s, *op, depth);
                    self.stmt_pos = saved;
                    return Flow::Done;
                }
                H::Local(l) => {
                    let saved = self.stmt_pos;
                    s.local(self, *l, depth);
                    self.stmt_pos = saved;
                    return Flow::Done;
                }
                _ => {
                    // Everything else (assignments `=`, `\in`, `\subseteq`,
                    // primes, value expressions, `ENABLED`, etc.) is not a
                    // statement-position `UNCHANGED` wrapper; fall through to
                    // the shared `binding::State` walk in value mode.
                    self.stmt_pos = false;
                }
            }
        }
        if let H::Var(v) = &*e.kind {
            self.deps.mark_var(v.idx());
        }
        Flow::Children
    }

    fn builtin(&mut self, s: &mut State<'_>, op: B, _args: &[hir::Expr], _depth: usize) -> Flow {
        if s.ip.is_builtin_overridden(op) {
            self.deps.all = true;
            return Flow::Done;
        }
        Flow::Children
    }

    fn child_depth(&self, depth: usize) -> usize {
        depth + 1
    }

    fn def(&mut self, s: &mut State<'_>, d: DefId) -> bool {
        if self.deps.all {
            return false;
        }
        let def = &s.ip.prog.defs[d.idx()];
        if def.builtin.is_some() || s.ip.has_def_value(d) {
            return false;
        }
        self.seen.insert((d, self.stmt_pos))
    }

    fn pending_def(&mut self, _s: &mut State<'_>, _d: DefId) {
        self.deps.all = true;
    }

    fn local(&mut self, _s: &mut State<'_>, _l: LocalId, depth: usize) -> bool {
        if depth > 64 {
            self.deps.all = true;
            return false;
        }
        true
    }

    fn constant(&mut self, s: &mut State<'_>, c: ConstId, _depth: usize) {
        if let Some(d) = s.ip.const_def(c) {
            let saved = std::mem::replace(&mut self.stmt_pos, false);
            s.def(self, d);
            self.stmt_pos = saved;
        }
    }

    fn op_const(&mut self, s: &mut State<'_>, c: ConstId, _depth: usize) {
        match s.ip.const_op_ref(c) {
            Some(OpRef::Def(d)) => s.def(self, d),
            Some(OpRef::Builtin(_)) => {}
            _ => self.deps.all = true,
        }
    }
}

fn scan_hir(ip: &Interp, e: &hir::Expr, env: &Env, stmt_pos: bool, deps: &mut IrDeps) {
    let mut state = State::new(ip, Scope::Single, env.clone());
    let mut policy = CacheHirPolicy { deps, seen: HashSet::new(), stmt_pos };
    state.walk(&mut policy, e, 0);
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use tlx_layout::{Layout, Shape};
    use tlx_runtime::Model;
    use tlx_testkit::{module, spec};

    use super::*;
    use crate::verify::Program;

    #[test]
    fn reuses_unaffected_actions_and_predicates_across_var0_widening() {
        let src = module(
            "CacheReuseUnit",
            r#"
EXTENDS Naturals, FiniteSets
VARIABLES bag, x, y
Init == bag = {} /\ x = 0 /\ y = 0
TouchBag == bag' = bag \cup {x} /\ x' = (x + 1) % 4 /\ UNCHANGED y
TouchXY == x' = (x + 1) % 4 /\ y' = (y + 1) % 4 /\ UNCHANGED bag
Next == TouchBag \/ TouchXY
InvXY == x <= 3 /\ y <= 3
InvBag == Cardinality(bag) <= 4
"#,
        );
        let cfg = "INIT Init\nNEXT Next\nINVARIANT InvXY\nINVARIANT InvBag\n";
        let base = spec::load(&src, cfg);

        // Attempt 0: bag has max_card 1.
        let int03 = Shape::Int { lo: 0, hi: 3 };
        let layout0 = Arc::new(Layout::new(vec![Shape::Set { elem: Box::new(int03.clone()), max_card: 1 }, int03.clone(), int03.clone()]));
        let mut lw0 = Lowerer::with_typing(&base.ip, Typing::new(layout0));
        let init0 = lw0.lower_init(base.init_expr()).ok();
        let acts0: Vec<_> = base.actions().iter().map(|a| lw0.lower_action(a).ok()).collect();
        let invs0: Vec<_> = base.invariant_exprs().iter().zip(base.invariant_names()).map(|(e, n)| lw0.lower_pred(n, e)).collect();
        Program::new(&lw0.typing, init0.as_ref(), &acts0, &invs0, &[]).expect("attempt 0 valid");

        let mut cache = CompileCache::default();
        cache.update(&base, &lw0, &[], &acts0, &invs0, &[]);

        // Attempt 1: var 0 (`bag`) widens to max_card 4, shifting offsets of x and y.
        let layout1 = Arc::new(Layout::new(vec![Shape::Set { elem: Box::new(int03.clone()), max_card: 4 }, int03.clone(), int03.clone()]));
        let mut lw1 = Lowerer::with_typing(&base.ip, Typing::new(layout1.clone()));
        let mut sess = cache.begin(&mut lw1, &layout1.vars, &[], acts0.len(), invs0.len(), 0).expect("reuse session");

        // TouchBag inspects bag -> must NOT reuse; TouchXY only copies bag unchanged -> MUST reuse.
        let mut reused_names = Vec::new();
        let mut acts1 = Vec::new();
        for (i, a) in base.actions().iter().enumerate() {
            if let Some(f) = sess.reuse_action(i, &mut lw1) {
                reused_names.push(a.name.to_string());
                acts1.push(Some(f));
            } else {
                acts1.push(lw1.lower_action(a).ok());
            }
        }
        assert!(reused_names.iter().any(|n| n.contains("TouchXY")), "expected TouchXY reused, got {reused_names:?}");
        assert!(!reused_names.iter().any(|n| n.contains("TouchBag")), "TouchBag must not be reused, got {reused_names:?}");

        // InvXY does not read bag -> MUST reuse; InvBag reads bag -> must NOT reuse.
        let mut reused_invs = Vec::new();
        let mut invs1 = Vec::new();
        for (i, (e, n)) in base.invariant_exprs().iter().zip(base.invariant_names()).enumerate() {
            if let Some(p) = sess.reuse_invariant(i, &mut lw1) {
                reused_invs.push(n.clone());
                invs1.push(p);
            } else {
                invs1.push(lw1.lower_pred(n, e));
            }
        }
        assert_eq!(reused_invs, vec!["InvXY".to_string()]);
        drop(sess);

        let init1 = lw1.lower_init(base.init_expr()).ok();
        let verified1 = Program::new(&lw1.typing, init1.as_ref(), &acts1, &invs1, &[]).expect("reused attempt 1 verifies");

        // Verify JIT cache also reuses compiled machine code for TouchXY and InvXY.
        #[cfg(feature = "jit")]
        {
            let verified0 = Program::new(&lw0.typing, init0.as_ref(), &acts0, &invs0, &[]).unwrap();
            let _j0 =
                crate::jit::library_with_cache(&verified0, None, None, base.action_names(), base.invariant_names(), Some(&mut cache.jit))
                    .expect("attempt 0 JIT");
            let before = cache.jit.entry_count();
            let _j1 =
                crate::jit::library_with_cache(&verified1, None, None, base.action_names(), base.invariant_names(), Some(&mut cache.jit))
                    .expect("attempt 1 JIT");
            assert!(before > 0);
            assert!(cache.jit.hits() > 0, "expected JIT cache hits for unaffected functions across var 0 widening");
        }
    }

    #[test]
    fn folded_out_of_range_guard_is_not_reused_when_variable_widens() {
        let src = module(
            "FoldedGuard",
            r#"
EXTENDS Naturals
VARIABLES n, x
Init == n = 0 /\ x = 0
Inc == n < 15 /\ n' = n + 1 /\ UNCHANGED x
Late == n = 15 /\ x' = 1 /\ UNCHANGED n
Next == Inc \/ Late
InvLate == n = 15 => x <= 1
"#,
        );
        let cfg = "INIT Init\nNEXT Next\nINVARIANT InvLate\n";
        let base = spec::load(&src, cfg);

        // Attempt 0: n is 0..2, so `n = 15` folds to FALSE in Late (`Stmt::Stop`)
        // and InvLate (`Const(true)`).
        let layout0 = Arc::new(Layout::new(vec![Shape::Int { lo: 0, hi: 2 }, Shape::Int { lo: 0, hi: 1 }]));
        let mut lw0 = Lowerer::with_typing(&base.ip, Typing::new(layout0));
        let acts0: Vec<_> = base.actions().iter().map(|a| lw0.lower_action(a).ok()).collect();
        let invs0: Vec<_> = base.invariant_exprs().iter().zip(base.invariant_names()).map(|(e, n)| lw0.lower_pred(n, e)).collect();
        let mut cache = CompileCache::default();
        cache.update(&base, &lw0, &[], &acts0, &invs0, &[]);

        // Attempt 1: n widens to 0..15; neither Late nor InvLate may be reused!
        let layout1 = Arc::new(Layout::new(vec![Shape::Int { lo: 0, hi: 15 }, Shape::Int { lo: 0, hi: 1 }]));
        let mut lw1 = Lowerer::with_typing(&base.ip, Typing::new(layout1.clone()));
        let mut sess = cache.begin(&mut lw1, &layout1.vars, &[], acts0.len(), invs0.len(), 0).unwrap();
        for i in 0..acts0.len() {
            assert!(sess.reuse_action(i, &mut lw1).is_none(), "action {i} depends on n via HIR and must re-lower");
        }
        assert!(sess.reuse_invariant(0, &mut lw1).is_none(), "InvLate depends on n via HIR and must re-lower");
    }

    #[test]
    fn constant_override_dependency_invalidates_cached_ir() {
        let src = module(
            "ConstOverrideDep",
            r#"
EXTENDS Naturals
CONSTANT C
VARIABLES x, y
Override == y
Init == x = 0 /\ y = 0
UseConst == C = 10 /\ x' = 1 /\ UNCHANGED y
OnlyX == x < 2 /\ x' = x + 1 /\ UNCHANGED y
Next == UseConst \/ OnlyX
InvConst == C = 10 => x <= 2
InvX == x <= 2
"#,
        );
        let cfg = "CONSTANT C <- Override\nINIT Init\nNEXT Next\nINVARIANT InvConst\nINVARIANT InvX\n";
        let base = spec::load(&src, cfg);

        // Attempt 0: y is 0..2, so `C = 10` (via `C <- Override == y`) folds to FALSE.
        let layout0 = Arc::new(Layout::new(vec![Shape::Int { lo: 0, hi: 2 }, Shape::Int { lo: 0, hi: 2 }]));
        let mut lw0 = Lowerer::with_typing(&base.ip, Typing::new(layout0));
        let acts0: Vec<_> = base.actions().iter().map(|a| lw0.lower_action(a).ok()).collect();
        let invs0: Vec<_> = base.invariant_exprs().iter().zip(base.invariant_names()).map(|(e, n)| lw0.lower_pred(n, e)).collect();
        let mut cache = CompileCache::default();
        cache.update(&base, &lw0, &[], &acts0, &invs0, &[]);

        // Attempt 1: y widens to 0..10. `UseConst` and `InvConst` read y through
        // `CONSTANT C <- Override` and MUST NOT be reused, while `OnlyX` and `InvX` MUST be reused.
        let layout1 = Arc::new(Layout::new(vec![Shape::Int { lo: 0, hi: 2 }, Shape::Int { lo: 0, hi: 10 }]));
        let mut lw1 = Lowerer::with_typing(&base.ip, Typing::new(layout1.clone()));
        let mut sess = cache.begin(&mut lw1, &layout1.vars, &[], acts0.len(), invs0.len(), 0).unwrap();
        let mut reused_acts = Vec::new();
        for (i, a) in base.actions().iter().enumerate() {
            if sess.reuse_action(i, &mut lw1).is_some() {
                reused_acts.push(a.name.to_string());
            }
        }
        assert!(reused_acts.iter().any(|n| n.contains("OnlyX")), "OnlyX should reuse, got {reused_acts:?}");
        assert!(!reused_acts.iter().any(|n| n.contains("UseConst")), "UseConst reads y via C <- Override, got {reused_acts:?}");
        assert!(sess.reuse_invariant(0, &mut lw1).is_none(), "InvConst reads y via C <- Override and must re-lower");
        assert!(sess.reuse_invariant(1, &mut lw1).is_some(), "InvX does not depend on y and should reuse");
    }
}
