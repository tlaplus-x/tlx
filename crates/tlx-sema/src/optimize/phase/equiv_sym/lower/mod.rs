//! Lower normalized HIR formulas and set predicates into the `EquivRule` Lean IR
//! with explicit De Bruijn local bindings; value expression and `.cfg` constant
//! lowering live in [`expr`].

mod expr;

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use tlx_front::cfg::CfgValue;

use super::{AtomKey, GroupInfo, GroupMask};
use crate::optimize::phase::sym_totality::{CheckEnv, Shape, TotalityChecker};
use crate::{builtins::Builtin as B, hir::*, Program};

const MAX_NODES: usize = 60_000;
const MAX_EMITTED_BYTES: usize = 1_000_000;

/// One local slot on the De Bruijn stack (`0` = top / innermost).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Slot {
    Local(LocalId, AtomKind),
    At,
    Temp,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum AtomKind {
    Unknown,
    Atom,
    AtomSet,
}

pub(super) struct LowerCtx<'a> {
    program: &'a Program,
    groups: &'a [GroupInfo],
    all_keys: &'a BTreeSet<Arc<str>>,
    consts: &'a BTreeMap<ConstId, &'a CfgValue>,
    totality: &'a TotalityChecker<'a>,
    check_env: CheckEnv,
    in_verified_quant: bool,
    locals: Vec<Slot>,
    nodes: usize,
    emitted_bytes: usize,
    pub(super) used_groups: GroupMask,
    pub(super) atoms: Vec<AtomKey>,
    atom_ids: BTreeMap<AtomKey, usize>,
    pub(super) atom_ops: Vec<String>,
    atom_op_ids: BTreeMap<String, usize>,
    pub(super) atom_set_ops: Vec<String>,
    atom_set_op_ids: BTreeMap<String, usize>,
    pub(super) atom_set_aggs: Vec<String>,
    atom_set_agg_ids: BTreeMap<String, usize>,
    pub(super) atom_rels: Vec<String>,
    atom_rel_ids: BTreeMap<String, usize>,
    pub(super) atom_preds: Vec<String>,
    atom_pred_ids: BTreeMap<String, usize>,
}

impl<'a> LowerCtx<'a> {
    pub(super) fn new(
        program: &'a Program,
        groups: &'a [GroupInfo],
        all_keys: &'a BTreeSet<Arc<str>>,
        consts: &'a BTreeMap<ConstId, &'a CfgValue>,
        totality: &'a TotalityChecker<'a>,
    ) -> Self {
        Self {
            program,
            groups,
            all_keys,
            consts,
            totality,
            check_env: CheckEnv::default(),
            in_verified_quant: false,
            locals: Vec::new(),
            nodes: 0,
            emitted_bytes: 0,
            used_groups: 0,
            atoms: Vec::new(),
            atom_ids: BTreeMap::new(),
            atom_ops: Vec::new(),
            atom_op_ids: BTreeMap::new(),
            atom_set_ops: Vec::new(),
            atom_set_op_ids: BTreeMap::new(),
            atom_set_aggs: Vec::new(),
            atom_set_agg_ids: BTreeMap::new(),
            atom_rels: Vec::new(),
            atom_rel_ids: BTreeMap::new(),
            atom_preds: Vec::new(),
            atom_pred_ids: BTreeMap::new(),
        }
    }

    fn bump(&mut self) -> Option<()> {
        self.nodes += 1;
        (self.nodes <= MAX_NODES && self.emitted_bytes <= MAX_EMITTED_BYTES).then_some(())
    }

    fn charge(&mut self, s: String) -> Option<String> {
        self.emitted_bytes = self.emitted_bytes.saturating_add(s.len());
        (self.emitted_bytes <= MAX_EMITTED_BYTES).then_some(s)
    }

    fn atom_id(&mut self, key: AtomKey) -> usize {
        if let Some(&id) = self.atom_ids.get(&key) {
            return id;
        }
        let id = self.atoms.len();
        self.atoms.push(key.clone());
        self.atom_ids.insert(key, id);
        id
    }

    fn atom_op_id(&mut self, label: &str) -> usize {
        if let Some(&id) = self.atom_op_ids.get(label) {
            return id;
        }
        let id = self.atom_ops.len();
        self.atom_ops.push(label.to_string());
        self.atom_op_ids.insert(label.to_string(), id);
        id
    }

    fn atom_set_op_id(&mut self, label: &str) -> usize {
        if let Some(&id) = self.atom_set_op_ids.get(label) {
            return id;
        }
        let id = self.atom_set_ops.len();
        self.atom_set_ops.push(label.to_string());
        self.atom_set_op_ids.insert(label.to_string(), id);
        id
    }

    fn atom_set_agg_id(&mut self, label: &str) -> usize {
        if let Some(&id) = self.atom_set_agg_ids.get(label) {
            return id;
        }
        let id = self.atom_set_aggs.len();
        self.atom_set_aggs.push(label.to_string());
        self.atom_set_agg_ids.insert(label.to_string(), id);
        id
    }

    fn atom_rel_id(&mut self, label: &str) -> usize {
        if let Some(&id) = self.atom_rel_ids.get(label) {
            return id;
        }
        let id = self.atom_rels.len();
        self.atom_rels.push(label.to_string());
        self.atom_rel_ids.insert(label.to_string(), id);
        id
    }

    fn atom_pred_id(&mut self, label: &str) -> usize {
        if let Some(&id) = self.atom_pred_ids.get(label) {
            return id;
        }
        let id = self.atom_preds.len();
        self.atom_preds.push(label.to_string());
        self.atom_pred_ids.insert(label.to_string(), id);
        id
    }

    fn lookup_local(&self, id: LocalId) -> Option<usize> {
        self.locals.iter().rev().position(|&s| matches!(s, Slot::Local(l, _) if l == id))
    }

    fn local_atom_kind(&self, id: LocalId) -> AtomKind {
        self.locals
            .iter()
            .rev()
            .find_map(|&s| match s {
                Slot::Local(l, k) if l == id => Some(k),
                _ => None,
            })
            .unwrap_or(AtomKind::Unknown)
    }

    fn elem_atom_kind(&self, set_expr: &Expr) -> AtomKind {
        if self.is_definitely_atom_set(set_expr) {
            return AtomKind::Atom;
        }
        if let ExprKind::Builtin { op: B::Subset, args } = &*set_expr.kind {
            if args.len() == 1 && self.is_definitely_atom_set(&args[0]) {
                return AtomKind::AtomSet;
            }
        }
        if let ExprKind::Builtin { op: B::KSubset, args } = &*set_expr.kind {
            if args.len() == 2 && self.is_definitely_atom_set(&args[1]) {
                return AtomKind::AtomSet;
            }
        }
        AtomKind::Unknown
    }

    fn lookup_at(&self) -> Option<usize> {
        self.locals.iter().rev().position(|&s| s == Slot::At)
    }

    fn mask_lean(&self, mask: GroupMask) -> String {
        let mut parts = Vec::new();
        for gi in 0..self.groups.len() {
            if (mask & (1 << gi)) != 0 {
                parts.push(format!("g.val == {gi}"));
            }
        }
        if parts.is_empty() {
            "(fun _ => false)".to_string()
        } else {
            format!("(fun g => {})", parts.join(" || "))
        }
    }

    fn int_expr(&mut self, n: i128) -> String {
        let id = self.atom_id(AtomKey::Int(n));
        format!("(Expr.atom {id})")
    }

    fn str_atom_id(&mut self, s: &Arc<str>) -> usize {
        self.atom_id(AtomKey::Str(s.clone()))
    }

    pub(super) fn lower_form(&mut self, e: &Expr, allow_prime: bool) -> Option<String> {
        let out = self.lower_form_rec(e, allow_prime, false, allow_prime)?;
        self.charge(out)
    }

    pub(super) fn lower_action_pred(&mut self, e: &Expr) -> Option<String> {
        let out = self.lower_form_rec(e, true, false, false)?;
        self.charge(out)
    }

    fn lower_form_rec(&mut self, e: &Expr, allow_prime: bool, in_prime: bool, in_action_pos: bool) -> Option<String> {
        self.bump()?;
        match &*e.kind {
            ExprKind::Bool(b) => Some(format!("(Form.truth {b})")),
            ExprKind::And(es) => {
                if es.is_empty() {
                    return Some("(Form.truth true)".to_string());
                }
                let saved = self.check_env.clone();
                let mut acc = self.lower_form_rec(&es[0], allow_prime, in_prime, in_action_pos);
                if acc.is_some() {
                    self.totality.apply_positive_fact(&es[0], in_prime, &mut self.check_env);
                    for item in &es[1..] {
                        match self.lower_form_rec(item, allow_prime, in_prime, in_action_pos) {
                            Some(rhs) => {
                                acc = self.charge(format!("(Form.conj {} {rhs})", acc.unwrap()));
                                if acc.is_none() {
                                    break;
                                }
                                self.totality.apply_positive_fact(item, in_prime, &mut self.check_env);
                            }
                            None => {
                                acc = None;
                                break;
                            }
                        }
                    }
                }
                self.check_env = saved;
                acc
            }
            ExprKind::Or(es) => {
                if es.is_empty() {
                    return Some("(Form.truth false)".to_string());
                }
                let saved = self.check_env.clone();
                let mut acc = self.lower_form_rec(&es[0], allow_prime, in_prime, in_action_pos);
                if acc.is_some() {
                    self.totality.apply_negative_fact(&es[0], in_prime, &mut self.check_env);
                    for item in &es[1..] {
                        match self.lower_form_rec(item, allow_prime, in_prime, in_action_pos) {
                            Some(rhs) => {
                                acc = self.charge(format!("(Form.disj {} {rhs})", acc.unwrap()));
                                if acc.is_none() {
                                    break;
                                }
                                self.totality.apply_negative_fact(item, in_prime, &mut self.check_env);
                            }
                            None => {
                                acc = None;
                                break;
                            }
                        }
                    }
                }
                self.check_env = saved;
                acc
            }
            ExprKind::If { cond, then, els } => {
                let c = self.lower_form_rec(cond, allow_prime, in_prime, false)?;
                let saved = self.check_env.clone();
                self.totality.apply_positive_fact(cond, in_prime, &mut self.check_env);
                let y = self.lower_form_rec(then, allow_prime, in_prime, in_action_pos);
                self.check_env = saved.clone();
                self.totality.apply_negative_fact(cond, in_prime, &mut self.check_env);
                let n = self.lower_form_rec(els, allow_prime, in_prime, in_action_pos);
                self.check_env = saved;
                let (y, n) = (y?, n?);
                self.charge(format!("(Form.ite {c} {y} {n})"))
            }
            ExprKind::Case { arms, other } => {
                let o = other.as_ref()?;
                let mut acc = self.lower_form_rec(o, allow_prime, in_prime, in_action_pos)?;
                for (cond, body) in arms.iter().rev() {
                    let c = self.lower_form_rec(cond, allow_prime, in_prime, false)?;
                    let y = self.lower_form_rec(body, allow_prime, in_prime, in_action_pos)?;
                    acc = format!("(Form.ite {c} {y} {acc})");
                }
                Some(acc)
            }
            ExprKind::BoxAction { action, sub } => {
                if !allow_prime || in_prime {
                    return None;
                }
                let fa = self.lower_form_rec(action, allow_prime, false, false)?;
                let fu = self.lower_unchanged(sub)?;
                self.charge(format!("(Form.disj {fa} {fu})"))
            }
            ExprKind::AngleAction { action, sub } => {
                if !allow_prime || in_prime {
                    return None;
                }
                let fa = self.lower_form_rec(action, allow_prime, false, false)?;
                let fu = self.lower_unchanged(sub)?;
                self.charge(format!("(Form.conj {fa} (Form.neg {fu}))"))
            }
            ExprKind::Quant { kind, bounds, body } => self.lower_quant(*kind, bounds, body, allow_prime, in_prime, in_action_pos),
            ExprKind::Builtin { op, args } => match (op, args.as_slice()) {
                (B::Not, [a]) => {
                    let inner = self.lower_form_rec(a, allow_prime, in_prime, false)?;
                    Some(format!("(Form.neg {inner})"))
                }
                (B::Implies, [a, b]) => {
                    let fa = self.lower_form_rec(a, allow_prime, in_prime, false)?;
                    let fb = self.lower_form_rec(b, allow_prime, in_prime, false)?;
                    Some(format!("(Form.impl {fa} {fb})"))
                }
                (B::Equiv, [a, b]) => {
                    let fa = self.lower_form_rec(a, allow_prime, in_prime, false)?;
                    let fb = self.lower_form_rec(b, allow_prime, in_prime, false)?;
                    Some(format!("(Form.iff {fa} {fb})"))
                }
                (B::Eq, [a, b]) => {
                    let ea = self.lower_expr_rec(a, allow_prime, in_prime)?;
                    let eb = self.lower_expr_rec(b, allow_prime, in_prime)?;
                    Some(format!("(Form.eq {ea} {eb})"))
                }
                (B::Neq, [a, b]) => {
                    let ea = self.lower_expr_rec(a, allow_prime, in_prime)?;
                    let eb = self.lower_expr_rec(b, allow_prime, in_prime)?;
                    Some(format!("(Form.neg (Form.eq {ea} {eb}))"))
                }
                (B::In, [a, s]) => {
                    let ea = self.lower_expr_rec(a, allow_prime, in_prime)?;
                    let sp = self.lower_set_pred_rec(s, allow_prime, in_prime)?;
                    Some(format!("(Form.mem {ea} {sp})"))
                }
                (B::NotIn, [a, s]) => {
                    let ea = self.lower_expr_rec(a, allow_prime, in_prime)?;
                    let sp = self.lower_set_pred_rec(s, allow_prime, in_prime)?;
                    Some(format!("(Form.neg (Form.mem {ea} {sp}))"))
                }
                (B::SubsetEq, [a, b]) => {
                    let ea = self.lower_expr_rec(a, allow_prime, in_prime)?;
                    let sp = self.lower_set_pred_rec(b, allow_prime, in_prime)?;
                    Some(format!("(Form.subsetEq {ea} {sp})"))
                }
                (B::Unchanged, [arg]) => {
                    if !allow_prime || in_prime {
                        return None;
                    }
                    self.lower_unchanged(arg)
                }
                (B::Prime, [arg]) => {
                    if !allow_prime || in_prime {
                        return None;
                    }
                    self.lower_form_rec(arg, allow_prime, true, false)
                }
                (B::Lt | B::Le | B::Gt | B::Ge, [a, b]) => {
                    let ea = self.lower_expr_rec(a, allow_prime, in_prime)?;
                    let eb = self.lower_expr_rec(b, allow_prime, in_prime)?;
                    let id = self.atom_rel_id(op.name());
                    Some(format!("(Form.atomRel {id} [{ea}, {eb}])"))
                }
                (B::IsFiniteSet, [s]) => {
                    let es = self.lower_expr_rec(s, allow_prime, in_prime)?;
                    self.charge(format!("(Form.isFiniteSet {es})"))
                }
                (B::IsInjective, [f]) => {
                    let ef = self.lower_expr_rec(f, allow_prime, in_prime)?;
                    Some(format!(
                        "(Form.letBind {ef} (Form.all (SetPred.expr (Expr.domain (Expr.localVar 0))) \
                         (Form.all (SetPred.expr (Expr.domain (Expr.localVar 1))) \
                         (Form.impl (Form.eq (Expr.fnApp (Expr.localVar 2) (Expr.localVar 1)) \
                         (Expr.fnApp (Expr.localVar 2) (Expr.localVar 0))) \
                         (Form.eq (Expr.localVar 1) (Expr.localVar 0))))))"
                    ))
                }
                (B::TLCEval, [a]) => self.lower_form_rec(a, allow_prime, in_prime, in_action_pos),
                (B::Assert, _) => None,
                _ => {
                    let expr = self.lower_expr_rec(e, allow_prime, in_prime)?;
                    Some(format!("(Form.ofExpr {expr})"))
                }
            },
            _ => {
                let expr = self.lower_expr_rec(e, allow_prime, in_prime)?;
                Some(format!("(Form.ofExpr {expr})"))
            }
        }
    }

    fn lower_unchanged(&mut self, arg: &Expr) -> Option<String> {
        match &*arg.kind {
            ExprKind::Var(v) => {
                let idx = v.idx();
                if idx >= self.program.vars.len() {
                    return None;
                }
                Some(format!("(Form.eq (Expr.primeVar ⟨{idx}, by decide⟩) (Expr.var ⟨{idx}, by decide⟩))"))
            }
            ExprKind::Tuple(es) => {
                if es.is_empty() {
                    return Some("(Form.truth true)".to_string());
                }
                let mut acc = self.lower_unchanged(&es[0])?;
                for item in &es[1..] {
                    let rhs = self.lower_unchanged(item)?;
                    acc = format!("(Form.conj {acc} {rhs})");
                }
                Some(acc)
            }
            _ => {
                let lhs = self.lower_expr_rec(arg, true, true)?;
                let rhs = self.lower_expr_rec(arg, true, false)?;
                Some(format!("(Form.eq {lhs} {rhs})"))
            }
        }
    }

    fn lower_quant(
        &mut self,
        kind: QuantKind,
        bounds: &[Bound],
        body: &Expr,
        allow_prime: bool,
        in_prime: bool,
        in_action_pos: bool,
    ) -> Option<String> {
        let body_action_pos = in_action_pos && kind == QuantKind::Exists && allow_prime && !in_prime;
        if !self.in_verified_quant {
            let quant_expr = Expr::new(ExprKind::Quant { kind, bounds: bounds.to_vec(), body: body.clone() }, body.span);
            let ok = if body_action_pos {
                self.totality.check_action_quant_safe(&quant_expr, in_prime, &self.check_env)
            } else {
                self.totality.check_form_total(&quant_expr, allow_prime, in_prime, &self.check_env)
            };
            if !ok {
                return None;
            }
            self.in_verified_quant = true;
            let res = self.lower_quant_inner(kind, bounds, body, allow_prime, in_prime, body_action_pos);
            self.in_verified_quant = false;
            return res;
        }
        self.lower_quant_inner(kind, bounds, body, allow_prime, in_prime, body_action_pos)
    }

    fn lower_quant_inner(
        &mut self,
        kind: QuantKind,
        bounds: &[Bound],
        body: &Expr,
        allow_prime: bool,
        in_prime: bool,
        in_action_pos: bool,
    ) -> Option<String> {
        if bounds.is_empty() {
            return self.lower_form_rec(body, allow_prime, in_prime, in_action_pos);
        }
        let b = &bounds[0];
        let rest = &bounds[1..];
        let ctor = match kind {
            QuantKind::Forall => "Form.all",
            QuantKind::Exists => "Form.some",
        };
        match &b.vars {
            BoundVars::Many(ids) => {
                let ak = self.elem_atom_kind(&b.set);
                let (elem_shape, dom_origin) = self.totality.bound_elem_info(&b.set, in_prime, &self.check_env);
                let mut doms = Vec::with_capacity(ids.len());
                let mut bound_ids = Vec::with_capacity(ids.len());
                let mut ok = true;
                for &id in ids {
                    match self.lower_set_pred_rec(&b.set, allow_prime, in_prime) {
                        Some(dom) => {
                            doms.push(dom);
                            self.locals.push(Slot::Local(id, ak));
                            self.check_env.bind_local(id, elem_shape.clone(), dom_origin.clone());
                            bound_ids.push(id);
                        }
                        None => {
                            ok = false;
                            break;
                        }
                    }
                }
                let inner = if ok { self.lower_quant_inner(kind, rest, body, allow_prime, in_prime, in_action_pos) } else { None };
                for id in bound_ids.into_iter().rev() {
                    self.locals.pop();
                    self.check_env.unbind_local(id);
                }
                let mut acc = inner?;
                for dom in doms.into_iter().rev() {
                    acc = self.charge(format!("({ctor} {dom} {acc})"))?;
                }
                Some(acc)
            }
            BoundVars::Tuple(ids) => {
                let elem_shapes = self.totality.prove_tuple_set_arity(&b.set, ids.len(), in_prime, &self.check_env)?;
                let dom = self.lower_set_pred_rec(&b.set, allow_prime, in_prime)?;
                self.locals.push(Slot::Temp);
                let inner = self.bind_tuple_for_form(ids, &elem_shapes, 0, |ctx| {
                    ctx.lower_quant_inner(kind, rest, body, allow_prime, in_prime, in_action_pos)
                });
                self.locals.pop();
                let inner = inner?;
                self.charge(format!("({ctor} {dom} {inner})"))
            }
        }
    }

    fn bind_tuple_for_form<F>(&mut self, ids: &[LocalId], elem_shapes: &[Shape], tuple_depth: usize, f: F) -> Option<String>
    where
        F: FnOnce(&mut Self) -> Option<String>,
    {
        if ids.is_empty() {
            return f(self);
        }
        self.bind_tuple_form_step(ids, elem_shapes, 0, tuple_depth, f)
    }

    fn bind_tuple_form_step<F>(&mut self, ids: &[LocalId], elem_shapes: &[Shape], idx: usize, tuple_depth: usize, f: F) -> Option<String>
    where
        F: FnOnce(&mut Self) -> Option<String>,
    {
        if idx == ids.len() {
            return f(self);
        }
        let one_based = self.int_expr((idx + 1) as i128);
        let proj = format!("(Expr.fnApp (Expr.localVar {tuple_depth}) {one_based})");
        self.locals.push(Slot::Local(ids[idx], AtomKind::Unknown));
        self.check_env.bind_local(ids[idx], elem_shapes[idx].clone(), None);
        let body = self.bind_tuple_form_step(ids, elem_shapes, idx + 1, tuple_depth + 1, f);
        self.locals.pop();
        self.check_env.unbind_local(ids[idx]);
        let body = body?;
        self.charge(format!("(Form.letBind {proj} {body})"))
    }

    fn bind_tuple_expr_step<F>(&mut self, ids: &[LocalId], elem_shapes: &[Shape], idx: usize, tuple_depth: usize, f: F) -> Option<String>
    where
        F: FnOnce(&mut Self) -> Option<String>,
    {
        if idx == ids.len() {
            return f(self);
        }
        let one_based = self.int_expr((idx + 1) as i128);
        let proj = format!("(Expr.fnApp (Expr.localVar {tuple_depth}) {one_based})");
        self.locals.push(Slot::Local(ids[idx], AtomKind::Unknown));
        self.check_env.bind_local(ids[idx], elem_shapes[idx].clone(), None);
        let body = self.bind_tuple_expr_step(ids, elem_shapes, idx + 1, tuple_depth + 1, f);
        self.locals.pop();
        self.check_env.unbind_local(ids[idx]);
        let body = body?;
        self.charge(format!("(Expr.letBind {proj} {body})"))
    }

    fn lower_set_pred_rec(&mut self, e: &Expr, allow_prime: bool, in_prime: bool) -> Option<String> {
        self.bump()?;
        match &*e.kind {
            ExprKind::Const(cid) => {
                let val = *self.consts.get(cid)?;
                if let Some((mask, fixed)) = self.try_group_set(val) {
                    if fixed.is_empty() && mask != 0 {
                        self.used_groups |= mask;
                        let m = self.mask_lean(mask);
                        return Some(format!("(SetPred.group {m})"));
                    }
                }
                let expr = self.lower_cfg_value(val)?;
                Some(format!("(SetPred.expr {expr})"))
            }
            ExprKind::SetEnum(es) => {
                let items: Vec<_> = es.iter().map(|x| self.lower_expr_rec(x, allow_prime, in_prime)).collect::<Option<_>>()?;
                Some(format!("(SetPred.enum [{}])", items.join(", ")))
            }
            ExprKind::SetFilter { bound, pred } => {
                let dom = self.lower_set_pred_rec(&bound.set, allow_prime, in_prime)?;
                match &bound.vars {
                    BoundVars::Many(ids) if ids.len() == 1 => {
                        let ak = self.elem_atom_kind(&bound.set);
                        let (elem_shape, dom_origin) = self.totality.bound_elem_info(&bound.set, in_prime, &self.check_env);
                        self.locals.push(Slot::Local(ids[0], ak));
                        self.check_env.bind_local(ids[0], elem_shape, dom_origin);
                        let f = self.lower_form_rec(pred, allow_prime, in_prime, false);
                        self.locals.pop();
                        self.check_env.unbind_local(ids[0]);
                        let f = f?;
                        self.charge(format!("(SetPred.filter {dom} {f})"))
                    }
                    BoundVars::Tuple(ids) => {
                        let elem_shapes = self.totality.prove_tuple_set_arity(&bound.set, ids.len(), in_prime, &self.check_env)?;
                        self.locals.push(Slot::Temp);
                        let f =
                            self.bind_tuple_for_form(ids, &elem_shapes, 0, |ctx| ctx.lower_form_rec(pred, allow_prime, in_prime, false));
                        self.locals.pop();
                        let f = f?;
                        self.charge(format!("(SetPred.filter {dom} {f})"))
                    }
                    _ => None,
                }
            }
            ExprKind::FnSet { domain, range } => {
                let d = self.lower_set_pred_rec(domain, allow_prime, in_prime)?;
                let r = self.lower_set_pred_rec(range, allow_prime, in_prime)?;
                Some(format!("(SetPred.fnSet {d} {r})"))
            }
            ExprKind::RecordSet(fields) => {
                let mut pairs = Vec::with_capacity(fields.len());
                for (name, set) in fields {
                    let fid = self.str_atom_id(name);
                    let sp = self.lower_set_pred_rec(set, allow_prime, in_prime)?;
                    pairs.push(format!("({fid}, {sp})"));
                }
                Some(format!("(SetPred.recSet [{}])", pairs.join(", ")))
            }
            ExprKind::Builtin { op, args } => match (op, args.as_slice()) {
                (B::Nat, []) => {
                    let id = self.atom_pred_id("Nat");
                    Some(format!("(SetPred.atomPred {id})"))
                }
                (B::Int, []) => {
                    let id = self.atom_pred_id("Int");
                    Some(format!("(SetPred.atomPred {id})"))
                }
                (B::StringSet, []) => {
                    let id = self.atom_pred_id("STRING");
                    Some(format!("(SetPred.atomPred {id})"))
                }
                (B::Boolean, []) => {
                    let t = self.atom_id(AtomKey::Bool(true));
                    let f = self.atom_id(AtomKey::Bool(false));
                    Some(format!("(SetPred.enum [(Expr.atom {t}), (Expr.atom {f})])"))
                }
                (B::Subset, [s]) => {
                    let inner = self.lower_set_pred_rec(s, allow_prime, in_prime)?;
                    Some(format!("(SetPred.subset {inner})"))
                }
                (B::KSubset, [k, s]) => {
                    let inner = self.lower_set_pred_rec(s, allow_prime, in_prime)?;
                    self.locals.push(Slot::Temp);
                    let ek = self.lower_expr_rec(k, allow_prime, in_prime);
                    self.locals.pop();
                    let ek = ek?;
                    Some(format!("(SetPred.filter (SetPred.subset {inner}) (Form.eq (Expr.card (Expr.localVar 0)) {ek}))"))
                }
                (B::Seq, [s]) => {
                    let inner = self.lower_set_pred_rec(s, allow_prime, in_prime)?;
                    Some(format!("(SetPred.seq {inner})"))
                }
                (B::Cup, [a, b]) => {
                    let sa = self.lower_set_pred_rec(a, allow_prime, in_prime)?;
                    let sb = self.lower_set_pred_rec(b, allow_prime, in_prime)?;
                    Some(format!("(SetPred.cup {sa} {sb})"))
                }
                (B::Cap, [a, b]) => {
                    let sa = self.lower_set_pred_rec(a, allow_prime, in_prime)?;
                    let sb = self.lower_set_pred_rec(b, allow_prime, in_prime)?;
                    Some(format!("(SetPred.cap {sa} {sb})"))
                }
                (B::SetMinus, [a, b]) => {
                    let sa = self.lower_set_pred_rec(a, allow_prime, in_prime)?;
                    let sb = self.lower_set_pred_rec(b, allow_prime, in_prime)?;
                    Some(format!("(SetPred.diff {sa} {sb})"))
                }
                (B::Times, ds) if !ds.is_empty() => {
                    let ps: Vec<_> = ds.iter().map(|d| self.lower_set_pred_rec(d, allow_prime, in_prime)).collect::<Option<_>>()?;
                    Some(format!("(SetPred.times [{}])", ps.join(", ")))
                }
                (B::TLCEval, [a]) => self.lower_set_pred_rec(a, allow_prime, in_prime),
                _ => {
                    let expr = self.lower_expr_rec(e, allow_prime, in_prime)?;
                    Some(format!("(SetPred.expr {expr})"))
                }
            },
            _ => {
                let expr = self.lower_expr_rec(e, allow_prime, in_prime)?;
                Some(format!("(SetPred.expr {expr})"))
            }
        }
    }
}
