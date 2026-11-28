//! Value expression (`Expr`), `EXCEPT` path, multi-binder comprehension, and
//! `.cfg` constant lowering for `equiv_sym`.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use tlx_front::cfg::CfgValue;

use super::{AtomKey, AtomKind, GroupMask, LowerCtx, Shape, Slot};
use crate::optimize::phase::sym_norm::{classify_ac_op, is_chooses_first_lambda, AcOpKind, RecOpKind};
use crate::{builtins::Builtin as B, hir::*};

/// One exact set of `k`-subsets of a single symmetric group, together with the
/// key-free fixed atoms every member shares (`try_symmetric_k_subsets`).
#[derive(Default)]
struct KSubsetStratum {
    group: Option<usize>,
    moved: BTreeSet<BTreeSet<Arc<str>>>,
}

impl LowerCtx<'_> {
    pub(super) fn lower_expr_rec(&mut self, e: &Expr, allow_prime: bool, in_prime: bool) -> Option<String> {
        self.bump()?;
        match &*e.kind {
            ExprKind::Num(n) => Some(self.int_expr(*n)),
            ExprKind::Str(s) => {
                let id = self.str_atom_id(s);
                Some(format!("(Expr.atom {id})"))
            }
            ExprKind::Bool(b) => {
                let id = self.atom_id(AtomKey::Bool(*b));
                Some(format!("(Expr.atom {id})"))
            }
            ExprKind::Decimal(d) => {
                let id = self.atom_id(AtomKey::Decimal(d.clone()));
                Some(format!("(Expr.atom {id})"))
            }
            ExprKind::Var(v) => {
                let idx = self.var_lean_idx(*v)?;
                if in_prime {
                    Some(format!("(Expr.primeVar ⟨{idx}, by decide⟩)"))
                } else {
                    Some(format!("(Expr.var ⟨{idx}, by decide⟩)"))
                }
            }
            ExprKind::Local(l) => {
                let idx = self.lookup_local(*l)?;
                Some(format!("(Expr.localVar {idx})"))
            }
            ExprKind::At => {
                let idx = self.lookup_at()?;
                Some(format!("(Expr.localVar {idx})"))
            }
            ExprKind::Const(cid) => {
                let val = *self.consts.get(cid)?;
                self.lower_cfg_value(val)
            }
            ExprKind::CfgLiteral(val) => self.lower_cfg_value(val),
            ExprKind::Tuple(es) => {
                let items: Vec<_> = es.iter().map(|x| self.lower_expr_rec(x, allow_prime, in_prime)).collect::<Option<_>>()?;
                Some(format!("(Expr.seqLit [{}])", items.join(", ")))
            }
            ExprKind::SetEnum(es) => {
                if let Some(cfg_set) = self.try_const_set_enum(es) {
                    if self.try_group_set(&cfg_set).is_some_and(|(mask, _)| mask != 0) {
                        return self.lower_cfg_value(&cfg_set);
                    }
                }
                let items: Vec<_> = es.iter().map(|x| self.lower_expr_rec(x, allow_prime, in_prime)).collect::<Option<_>>()?;
                Some(format!("(Expr.setEnum [{}])", items.join(", ")))
            }
            ExprKind::Record(fields) => {
                let mut pairs = Vec::with_capacity(fields.len());
                for (name, val) in fields {
                    let fid = self.str_atom_id(name);
                    let ev = self.lower_expr_rec(val, allow_prime, in_prime)?;
                    pairs.push(format!("({fid}, {ev})"));
                }
                Some(format!("(Expr.recLit [{}])", pairs.join(", ")))
            }
            ExprKind::Field { record, field } => {
                let rec = self.lower_expr_rec(record, allow_prime, in_prime)?;
                let fid = self.str_atom_id(field);
                Some(format!("(Expr.fnApp {rec} (Expr.atom {fid}))"))
            }
            ExprKind::FnApp { func, args } => {
                let f = self.lower_expr_rec(func, allow_prime, in_prime)?;
                let arg = if args.len() == 1 {
                    self.lower_expr_rec(&args[0], allow_prime, in_prime)?
                } else {
                    let items: Vec<_> = args.iter().map(|a| self.lower_expr_rec(a, allow_prime, in_prime)).collect::<Option<_>>()?;
                    format!("(Expr.seqLit [{}])", items.join(", "))
                };
                Some(format!("(Expr.fnApp {f} {arg})"))
            }
            ExprKind::Except { base, updates } => {
                let base_e = self.lower_expr_rec(base, allow_prime, in_prime)?;
                self.lower_except_seq(base_e, updates, allow_prime, in_prime)
            }
            ExprKind::FnConstruct { bounds, body } => self.lower_fn_construct(bounds, body, allow_prime, in_prime),
            ExprKind::SetFilter { bound, pred } => {
                let dom = self.lower_expr_rec(&bound.set, allow_prime, in_prime)?;
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
                        self.charge(format!("(Expr.setFilter {dom} {f})"))
                    }
                    BoundVars::Tuple(ids) => {
                        let elem_shapes = self.totality.prove_tuple_set_arity(&bound.set, ids.len(), in_prime, &self.check_env)?;
                        self.locals.push(Slot::Temp);
                        let f =
                            self.bind_tuple_for_form(ids, &elem_shapes, 0, |ctx| ctx.lower_form_rec(pred, allow_prime, in_prime, false));
                        self.locals.pop();
                        let f = f?;
                        self.charge(format!("(Expr.setFilter {dom} {f})"))
                    }
                    _ => None,
                }
            }
            ExprKind::SetMap { expr, bounds } => self.lower_set_map(expr, bounds, allow_prime, in_prime),
            ExprKind::FnSet { domain, range } => {
                let d = self.lower_expr_rec(domain, allow_prime, in_prime)?;
                let r = self.lower_expr_rec(range, allow_prime, in_prime)?;
                Some(format!("(Expr.fnSet {d} {r})"))
            }
            ExprKind::RecordSet(fields) => {
                let mut pairs = Vec::with_capacity(fields.len());
                for (name, set) in fields {
                    let fid = self.str_atom_id(name);
                    let es = self.lower_expr_rec(set, allow_prime, in_prime)?;
                    pairs.push(format!("({fid}, {es})"));
                }
                Some(format!("(Expr.recSet [{}])", pairs.join(", ")))
            }
            ExprKind::If { cond, then, els } => {
                let c = self.lower_form_rec(cond, allow_prime, in_prime, false)?;
                let saved = self.check_env.clone();
                self.totality.apply_positive_fact(cond, in_prime, &mut self.check_env);
                let y = self.lower_expr_rec(then, allow_prime, in_prime);
                self.check_env = saved.clone();
                self.totality.apply_negative_fact(cond, in_prime, &mut self.check_env);
                let n = self.lower_expr_rec(els, allow_prime, in_prime);
                self.check_env = saved;
                let (y, n) = (y?, n?);
                self.charge(format!("(Expr.ite {c} {y} {n})"))
            }
            ExprKind::Case { arms, other } => {
                let o = other.as_ref()?;
                let mut acc = self.lower_expr_rec(o, allow_prime, in_prime)?;
                for (cond, body) in arms.iter().rev() {
                    let c = self.lower_form_rec(cond, allow_prime, in_prime, false)?;
                    let y = self.lower_expr_rec(body, allow_prime, in_prime)?;
                    acc = format!("(Expr.ite {c} {y} {acc})");
                }
                Some(acc)
            }
            ExprKind::Choose { vars, set, body } => {
                let s = set.as_ref()?;
                let (elem_shape, dom_origin) = self.totality.bound_elem_info(s, in_prime, &self.check_env);
                if !self.totality.is_shape_key_free(&elem_shape) {
                    return None;
                }
                let dom = self.lower_expr_rec(s, allow_prime, in_prime)?;
                match vars {
                    BoundVars::Many(ids) if ids.len() == 1 => {
                        let ak = self.elem_atom_kind(s);
                        self.locals.push(Slot::Local(ids[0], ak));
                        self.check_env.bind_local(ids[0], elem_shape, dom_origin);
                        let pred = self.lower_form_rec(body, allow_prime, in_prime, false);
                        self.locals.pop();
                        self.check_env.unbind_local(ids[0]);
                        let pred = pred?;
                        self.charge(format!("(Expr.chooseKeyFree {dom} {pred})"))
                    }
                    BoundVars::Tuple(ids) => {
                        let elem_shapes = self.totality.prove_tuple_set_arity(s, ids.len(), in_prime, &self.check_env)?;
                        self.locals.push(Slot::Temp);
                        let pred =
                            self.bind_tuple_for_form(ids, &elem_shapes, 0, |ctx| ctx.lower_form_rec(body, allow_prime, in_prime, false));
                        self.locals.pop();
                        let pred = pred?;
                        self.charge(format!("(Expr.chooseKeyFree {dom} {pred})"))
                    }
                    _ => None,
                }
            }
            ExprKind::Apply { op: OpRef::Def(id), args } => match (self.totality.rec_op_kind(*id), args.as_slice()) {
                (Some(RecOpKind::FixSet), [init, step_lam]) => {
                    let ExprKind::Lambda { params, body } = &*step_lam.kind else { return None };
                    let [s_var] = params.as_slice() else { return None };
                    let (bound, acc_shape) = self.totality.fix_set_bound(init, *s_var, body, allow_prime, in_prime, &self.check_env)?;
                    let e_init = self.lower_expr_rec(init, allow_prime, in_prime)?;
                    self.locals.push(Slot::Local(*s_var, AtomKind::Unknown));
                    self.check_env.bind_local(*s_var, acc_shape, None);
                    let e_step = self.lower_expr_rec(body, allow_prime, in_prime);
                    self.locals.pop();
                    self.check_env.unbind_local(*s_var);
                    let e_step = e_step?;
                    self.charge(format!("(Expr.fixSet {bound} {e_init} {e_step})"))
                }
                (Some(RecOpKind::IterRec), [init, step_lam]) => {
                    let ExprKind::Lambda { params, body } = &*step_lam.kind else { return None };
                    let [x_var] = params.as_slice() else { return None };
                    let ExprKind::If { cond, then, els } = &*body.kind else { return None };
                    let (fuel, _, x_union) =
                        self.totality.iter_rec_info(init, *x_var, cond, then, els, allow_prime, in_prime, &self.check_env)?;
                    let e_init = self.lower_expr_rec(init, allow_prime, in_prime)?;
                    self.locals.push(Slot::Local(*x_var, AtomKind::Unknown));
                    self.check_env.bind_local(*x_var, x_union, None);
                    let e_cond = self.lower_form_rec(cond, allow_prime, in_prime, false);
                    let saved = self.check_env.clone();
                    self.totality.apply_positive_fact(cond, in_prime, &mut self.check_env);
                    let e_step = self.lower_expr_rec(then, allow_prime, in_prime);
                    self.check_env = saved.clone();
                    self.totality.apply_negative_fact(cond, in_prime, &mut self.check_env);
                    let e_base = self.lower_expr_rec(els, allow_prime, in_prime);
                    self.check_env = saved;
                    self.locals.pop();
                    self.check_env.unbind_local(*x_var);
                    let (e_cond, e_step, e_base) = (e_cond?, e_step?, e_base?);
                    self.charge(format!("(Expr.iterRec {fuel} {e_init} {e_cond} {e_step} {e_base})"))
                }
                _ => None,
            },
            ExprKind::And(_) | ExprKind::Or(_) | ExprKind::Quant { .. } => {
                let f = self.lower_form_rec(e, allow_prime, in_prime, false)?;
                Some(format!("(Expr.ofForm {f})"))
            }
            ExprKind::Builtin { op, args } => match (op, args.as_slice()) {
                (B::Prime, [arg]) => {
                    if !allow_prime || in_prime {
                        return None;
                    }
                    self.lower_expr_rec(arg, allow_prime, true)
                }
                (B::Boolean, []) => {
                    let t = self.atom_id(AtomKey::Bool(true));
                    let f = self.atom_id(AtomKey::Bool(false));
                    Some(format!("(Expr.setEnum [(Expr.atom {t}), (Expr.atom {f})])"))
                }
                (B::Domain, [f]) => {
                    let ef = self.lower_expr_rec(f, allow_prime, in_prime)?;
                    Some(format!("(Expr.domain {ef})"))
                }
                (B::ColonGt, [k, v]) => {
                    let ek = self.lower_expr_rec(k, allow_prime, in_prime)?;
                    let ev = self.lower_expr_rec(v, allow_prime, in_prime)?;
                    Some(format!("(Expr.colonGt {ek} {ev})"))
                }
                (B::AtAt, [f, g]) => {
                    let ef = self.lower_expr_rec(f, allow_prime, in_prime)?;
                    let eg = self.lower_expr_rec(g, allow_prime, in_prime)?;
                    Some(format!("(Expr.atAt {ef} {eg})"))
                }
                (B::Cup, [a, b]) => {
                    let ea = self.lower_expr_rec(a, allow_prime, in_prime)?;
                    let eb = self.lower_expr_rec(b, allow_prime, in_prime)?;
                    Some(format!("(Expr.cup {ea} {eb})"))
                }
                (B::Cap, [a, b]) => {
                    let ea = self.lower_expr_rec(a, allow_prime, in_prime)?;
                    let eb = self.lower_expr_rec(b, allow_prime, in_prime)?;
                    Some(format!("(Expr.cap {ea} {eb})"))
                }
                (B::SetMinus, [a, b]) => {
                    let ea = self.lower_expr_rec(a, allow_prime, in_prime)?;
                    let eb = self.lower_expr_rec(b, allow_prime, in_prime)?;
                    Some(format!("(Expr.setMinus {ea} {eb})"))
                }
                (B::Union, [s]) => {
                    let es = self.lower_expr_rec(s, allow_prime, in_prime)?;
                    Some(format!("(Expr.union {es})"))
                }
                (B::Subset, [s]) => {
                    let es = self.lower_expr_rec(s, allow_prime, in_prime)?;
                    Some(format!("(Expr.powerset {es})"))
                }
                (B::KSubset, [k, s]) => {
                    let es = self.lower_expr_rec(s, allow_prime, in_prime)?;
                    self.locals.push(Slot::Temp);
                    let ek = self.lower_expr_rec(k, allow_prime, in_prime);
                    self.locals.pop();
                    let ek = ek?;
                    Some(format!("(Expr.setFilter (Expr.powerset {es}) (Form.eq (Expr.card (Expr.localVar 0)) {ek}))"))
                }
                (B::Times, ds) if !ds.is_empty() => {
                    let items: Vec<_> = ds.iter().map(|d| self.lower_expr_rec(d, allow_prime, in_prime)).collect::<Option<_>>()?;
                    Some(format!("(Expr.cartesian [{}])", items.join(", ")))
                }
                (B::Cardinality, [s]) => {
                    let es = self.lower_expr_rec(s, allow_prime, in_prime)?;
                    Some(format!("(Expr.card {es})"))
                }
                (B::Len, [s]) => {
                    if !self.totality.is_definitely_seq(s, in_prime, &self.check_env) {
                        return None;
                    }
                    let es = self.lower_expr_rec(s, allow_prime, in_prime)?;
                    Some(format!("(Expr.len {es})"))
                }
                (B::Head, [s]) => {
                    if !self.totality.is_definitely_seq(s, in_prime, &self.check_env) {
                        return None;
                    }
                    let es = self.lower_expr_rec(s, allow_prime, in_prime)?;
                    Some(format!("(Expr.head {es})"))
                }
                (B::Tail, [s]) => {
                    if !self.totality.is_definitely_seq(s, in_prime, &self.check_env) {
                        return None;
                    }
                    let es = self.lower_expr_rec(s, allow_prime, in_prime)?;
                    Some(format!("(Expr.tail {es})"))
                }
                (B::Append, [s, elem]) => {
                    if !self.totality.is_definitely_seq(s, in_prime, &self.check_env) {
                        return None;
                    }
                    let es = self.lower_expr_rec(s, allow_prime, in_prime)?;
                    let ee = self.lower_expr_rec(elem, allow_prime, in_prime)?;
                    Some(format!("(Expr.append {es} {ee})"))
                }
                (B::Concat, [a, b]) => {
                    if !self.totality.is_definitely_seq(a, in_prime, &self.check_env)
                        || !self.totality.is_definitely_seq(b, in_prime, &self.check_env)
                    {
                        return None;
                    }
                    let ea = self.lower_expr_rec(a, allow_prime, in_prime)?;
                    let eb = self.lower_expr_rec(b, allow_prime, in_prime)?;
                    Some(format!("(Expr.concat {ea} {eb})"))
                }
                (B::SubSeq, [s, lo, hi]) => {
                    if !self.totality.is_definitely_seq(s, in_prime, &self.check_env) {
                        return None;
                    }
                    let es = self.lower_expr_rec(s, allow_prime, in_prime)?;
                    let elo = self.lower_expr_rec(lo, allow_prime, in_prime)?;
                    let ehi = self.lower_expr_rec(hi, allow_prime, in_prime)?;
                    Some(format!("(Expr.subseq {es} {elo} {ehi})"))
                }
                (B::SelectSeq, [s, lam]) => {
                    if !self.totality.is_definitely_seq(s, in_prime, &self.check_env) {
                        return None;
                    }
                    let ExprKind::Lambda { params, body } = &*lam.kind else { return None };
                    if params.len() != 1 {
                        return None;
                    }
                    let es = self.lower_expr_rec(s, allow_prime, in_prime)?;
                    let elem_shape = self.totality.bound_elem_info(s, in_prime, &self.check_env).0;
                    self.locals.push(Slot::Local(params[0], AtomKind::Unknown));
                    self.check_env.bind_local(params[0], elem_shape, None);
                    let pred = self.lower_form_rec(body, allow_prime, in_prime, false);
                    self.locals.pop();
                    self.check_env.unbind_local(params[0]);
                    let pred = pred?;
                    self.charge(format!("(Expr.selectSeq {es} {pred})"))
                }
                (B::FoldSet, [op_lam, base, set]) => {
                    let ac = classify_ac_op(op_lam)?;
                    let es = self.lower_expr_rec(set, allow_prime, in_prime)?;
                    let eb = self.lower_expr_rec(base, allow_prime, in_prime)?;
                    self.charge(format!("(Expr.foldSetAC {} {es} {eb} (Expr.localVar 0))", ac.lean_ctor()))
                }
                (B::FoldFunction, [op_lam, base, fun]) => self.lower_fold_function(op_lam, base, fun, allow_prime, in_prime),
                (B::FoldFunctionOnSet, [op_lam, base, fun, indices]) => {
                    let ac = classify_ac_op(op_lam)?;
                    let efun = self.lower_expr_rec(fun, allow_prime, in_prime)?;
                    self.locals.push(Slot::Temp);
                    let eidx = self.lower_expr_rec(indices, allow_prime, in_prime);
                    let eb = self.lower_expr_rec(base, allow_prime, in_prime);
                    self.locals.pop();
                    let (eidx, eb) = (eidx?, eb?);
                    self.charge(format!(
                        "(Expr.letBind {efun} (Expr.foldSetAC {} {eidx} {eb} (Expr.fnApp (Expr.localVar 1) (Expr.localVar 0))))",
                        ac.lean_ctor()
                    ))
                }
                (B::MapThenFoldSet, [op_lam, base, f_lam, choose_lam, set, ..]) if args.len() == 5 || args.len() == 6 => {
                    let ac = classify_ac_op(op_lam)?;
                    if !is_chooses_first_lambda(choose_lam) {
                        return None;
                    }
                    let ExprKind::Lambda { params, body } = &*f_lam.kind else { return None };
                    let [p] = params.as_slice() else { return None };
                    let es = self.lower_expr_rec(set, allow_prime, in_prime)?;
                    let eb = self.lower_expr_rec(base, allow_prime, in_prime)?;
                    let ak = self.elem_atom_kind(set);
                    let (elem_shape, dom_origin) = self.totality.bound_elem_info(set, in_prime, &self.check_env);
                    self.locals.push(Slot::Local(*p, ak));
                    self.check_env.bind_local(*p, elem_shape, dom_origin);
                    let ef = self.lower_expr_rec(body, allow_prime, in_prime);
                    self.locals.pop();
                    self.check_env.unbind_local(*p);
                    let ef = ef?;
                    self.charge(format!("(Expr.foldSetAC {} {es} {eb} {ef})", ac.lean_ctor()))
                }
                (B::FoldSeq, [op_lam, base, seq]) => {
                    if self.totality.is_definitely_seq(seq, in_prime, &self.check_env) {
                        self.lower_seq_fold(false, false, false, op_lam, base, seq, allow_prime, in_prime)
                    } else {
                        self.lower_fold_function(op_lam, base, seq, allow_prime, in_prime)
                    }
                }
                (B::FoldLeft, [op_lam, base, seq]) => self.lower_seq_fold(false, false, true, op_lam, base, seq, allow_prime, in_prime),
                (B::FoldRight, [op_lam, seq, base]) => self.lower_seq_fold(true, false, false, op_lam, base, seq, allow_prime, in_prime),
                (B::FoldLeftDomain, [op_lam, base, seq]) => {
                    self.lower_seq_fold(false, true, true, op_lam, base, seq, allow_prime, in_prime)
                }
                (B::FoldRightDomain, [op_lam, seq, base]) => {
                    self.lower_seq_fold(true, true, false, op_lam, base, seq, allow_prime, in_prime)
                }
                (B::EmptyBag, []) => Some("(Expr.recLit [])".to_string()),
                (B::SetToBag, [s]) => {
                    let es = self.lower_expr_rec(s, allow_prime, in_prime)?;
                    let one = self.int_expr(1);
                    Some(format!("(Expr.fnConstruct {es} {one})"))
                }
                (B::BagToSet, [b]) => {
                    let eb = self.lower_expr_rec(b, allow_prime, in_prime)?;
                    Some(format!("(Expr.domain {eb})"))
                }
                (B::CopiesIn, [elem, b]) => {
                    let ee = self.lower_expr_rec(elem, allow_prime, in_prime)?;
                    let eb = self.lower_expr_rec(b, allow_prime, in_prime)?;
                    Some(format!("(Expr.copiesIn {ee} {eb})"))
                }
                (B::BagCup, [b1, b2]) => {
                    let e1 = self.lower_expr_rec(b1, allow_prime, in_prime)?;
                    let e2 = self.lower_expr_rec(b2, allow_prime, in_prime)?;
                    Some(format!("(Expr.bagCup {e1} {e2})"))
                }
                (B::BagDiff, [b1, b2]) => {
                    let e1 = self.lower_expr_rec(b1, allow_prime, in_prime)?;
                    let e2 = self.lower_expr_rec(b2, allow_prime, in_prime)?;
                    Some(format!("(Expr.bagDiff {e1} {e2})"))
                }
                (B::BagUnion, [s]) => {
                    let es = self.lower_expr_rec(s, allow_prime, in_prime)?;
                    Some(format!("(Expr.bagUnion {es})"))
                }
                (B::BagCardinality, [b]) => {
                    let eb = self.lower_expr_rec(b, allow_prime, in_prime)?;
                    Some(format!("(Expr.bagCard {eb})"))
                }
                (B::BagOfAll, [f_lam, bag]) => {
                    let ExprKind::Lambda { params, body } = &*f_lam.kind else { return None };
                    let [p] = params.as_slice() else { return None };
                    let eb = self.lower_expr_rec(bag, allow_prime, in_prime)?;
                    let dom_shape = self.totality.bag_dom_shape(bag, in_prime, &self.check_env);
                    self.locals.push(Slot::Local(*p, AtomKind::Unknown));
                    self.check_env.bind_local(*p, dom_shape, Some((bag.clone(), in_prime)));
                    let ef = self.lower_expr_rec(body, allow_prime, in_prime);
                    self.locals.pop();
                    self.check_env.unbind_local(*p);
                    let ef = ef?;
                    self.charge(format!("(Expr.bagOfAll {eb} {ef})"))
                }
                (B::FoldBag, [op_lam, base, bag]) => {
                    let ac = classify_ac_op(op_lam)?;
                    let eb = self.lower_expr_rec(bag, allow_prime, in_prime)?;
                    let ebase = self.lower_expr_rec(base, allow_prime, in_prime)?;
                    self.charge(format!("(Expr.foldBag {} {eb} {ebase})", ac.lean_ctor()))
                }
                (B::Plus | B::Minus | B::Mul | B::Div | B::Mod | B::Pow | B::Gcd, [a, b]) => {
                    let ea = self.lower_expr_rec(a, allow_prime, in_prime)?;
                    let eb = self.lower_expr_rec(b, allow_prime, in_prime)?;
                    let id = self.atom_op_id(op.name());
                    Some(format!("(Expr.atomOp {id} [{ea}, {eb}])"))
                }
                (B::Neg | B::Atoi, [a]) => {
                    let ea = self.lower_expr_rec(a, allow_prime, in_prime)?;
                    let id = self.atom_op_id(op.name());
                    Some(format!("(Expr.atomOp {id} [{ea}])"))
                }
                (B::DotDot, [a, b]) => {
                    let ea = self.lower_expr_rec(a, allow_prime, in_prime)?;
                    let eb = self.lower_expr_rec(b, allow_prime, in_prime)?;
                    let id = self.atom_set_op_id("..");
                    Some(format!("(Expr.atomSetOp {id} [{ea}, {eb}])"))
                }
                (B::SetMax | B::SetMin, [s]) => {
                    let es = self.lower_expr_rec(s, allow_prime, in_prime)?;
                    let id = self.atom_set_agg_id(op.name());
                    Some(format!("(Expr.atomSetAgg {id} {es})"))
                }
                (B::TLCEval, [a]) => self.lower_expr_rec(a, allow_prime, in_prime),
                (
                    B::Not
                    | B::Implies
                    | B::Equiv
                    | B::Eq
                    | B::Neq
                    | B::In
                    | B::NotIn
                    | B::SubsetEq
                    | B::Lt
                    | B::Le
                    | B::Gt
                    | B::Ge
                    | B::IsFiniteSet
                    | B::IsInjective
                    | B::IsABag
                    | B::BagIn
                    | B::SqSubseteq,
                    _,
                ) => {
                    let f = self.lower_form_rec(e, allow_prime, in_prime, false)?;
                    Some(format!("(Expr.ofForm {f})"))
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn lower_fold_function(&mut self, op_lam: &Expr, base: &Expr, fun: &Expr, allow_prime: bool, in_prime: bool) -> Option<String> {
        let ac = classify_ac_op(op_lam)?;
        let efun = self.lower_expr_rec(fun, allow_prime, in_prime)?;
        self.locals.push(Slot::Temp);
        let eb = self.lower_expr_rec(base, allow_prime, in_prime);
        self.locals.pop();
        let eb = eb?;
        self.charge(format!(
            "(Expr.letBind {efun} (Expr.foldSetAC {} (Expr.domain (Expr.localVar 0)) {eb} (Expr.fnApp (Expr.localVar 1) (Expr.localVar 0))))",
            ac.lean_ctor()
        ))
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_seq_fold(
        &mut self,
        right: bool,
        on_domain: bool,
        acc_first: bool,
        op_lam: &Expr,
        base: &Expr,
        seq: &Expr,
        allow_prime: bool,
        in_prime: bool,
    ) -> Option<String> {
        if !self.totality.is_definitely_seq(seq, in_prime, &self.check_env) {
            return None;
        }
        let ExprKind::Lambda { params, body } = &*op_lam.kind else { return None };
        let [p0, p1] = params.as_slice() else { return None };
        let eseq = self.lower_expr_rec(seq, allow_prime, in_prime)?;
        let ebase = self.lower_expr_rec(base, allow_prime, in_prime)?;
        let (acc_param, item_param) = if acc_first { (*p0, *p1) } else { (*p1, *p0) };
        let (acc_shape, item_shape) =
            self.totality.seq_fold_body_shapes(op_lam, base, seq, on_domain, acc_first, in_prime, &self.check_env);
        let dom_origin = on_domain.then(|| (seq.clone(), in_prime));
        let item_ak = if on_domain { AtomKind::Atom } else { AtomKind::Unknown };
        // Push `acc` first (`localVar 1`) and `x` second (`localVar 0`), matching `push (push env acc) x`.
        self.locals.push(Slot::Local(acc_param, AtomKind::Unknown));
        self.check_env.bind_local(acc_param, acc_shape, None);
        self.locals.push(Slot::Local(item_param, item_ak));
        self.check_env.bind_local(item_param, item_shape, dom_origin);
        let estep = self.lower_expr_rec(body, allow_prime, in_prime);
        self.locals.pop();
        self.check_env.unbind_local(item_param);
        self.locals.pop();
        self.check_env.unbind_local(acc_param);
        let estep = estep?;
        self.charge(format!("(Expr.foldSeq {right} {on_domain} {eseq} {ebase} {estep})"))
    }

    fn lower_except_seq(&mut self, base: String, updates: &[(Vec<ExceptKey>, Expr)], allow_prime: bool, in_prime: bool) -> Option<String> {
        if updates.is_empty() {
            return Some(base);
        }
        let (path, rhs) = &updates[0];
        let rest = &updates[1..];
        self.locals.push(Slot::Temp);
        let updated = self.lower_except_path(0, path, rhs, allow_prime, in_prime);
        let result = match updated {
            Some(upd) => self.lower_except_seq(upd, rest, allow_prime, in_prime),
            None => None,
        };
        self.locals.pop();
        let result = result?;
        Some(format!("(Expr.letBind {base} {result})"))
    }

    fn lower_except_key(&mut self, key: &ExceptKey, allow_prime: bool, in_prime: bool) -> Option<String> {
        match key {
            ExceptKey::Field(name) => {
                let fid = self.str_atom_id(name);
                Some(format!("(Expr.atom {fid})"))
            }
            ExceptKey::Index(args) if args.len() == 1 => self.lower_expr_rec(&args[0], allow_prime, in_prime),
            ExceptKey::Index(args) => {
                let items: Vec<_> = args.iter().map(|a| self.lower_expr_rec(a, allow_prime, in_prime)).collect::<Option<_>>()?;
                Some(format!("(Expr.seqLit [{}])", items.join(", ")))
            }
        }
    }

    fn lower_except_path(
        &mut self,
        target_depth: usize,
        path: &[ExceptKey],
        rhs: &Expr,
        allow_prime: bool,
        in_prime: bool,
    ) -> Option<String> {
        if path.is_empty() {
            return None;
        }
        let key_e = self.lower_except_key(&path[0], allow_prime, in_prime)?;
        self.locals.push(Slot::Temp);
        let target_ref = format!("(Expr.localVar {})", target_depth + 1);
        let body = if path.len() == 1 {
            self.locals.push(Slot::At);
            let rhs_e = self.lower_expr_rec(rhs, allow_prime, in_prime);
            self.locals.pop();
            rhs_e.map(|r| format!("(Expr.except {target_ref} (Expr.localVar 0) {r})"))
        } else {
            self.locals.push(Slot::Temp);
            let sub = self.lower_except_path(0, &path[1..], rhs, allow_prime, in_prime);
            self.locals.pop();
            sub.map(|s| format!("(Expr.except {target_ref} (Expr.localVar 0) {s})"))
        };
        self.locals.pop();
        let body = body?;
        self.charge(format!("(Expr.letBind {key_e} {body})"))
    }

    fn lower_fn_construct(&mut self, bounds: &[Bound], body: &Expr, allow_prime: bool, in_prime: bool) -> Option<String> {
        if bounds.len() == 1 {
            let b = &bounds[0];
            match &b.vars {
                BoundVars::Many(ids) if ids.len() == 1 => {
                    let dom = self.lower_expr_rec(&b.set, allow_prime, in_prime)?;
                    let ak = self.elem_atom_kind(&b.set);
                    let (elem_shape, dom_origin) = self.totality.bound_elem_info(&b.set, in_prime, &self.check_env);
                    self.locals.push(Slot::Local(ids[0], ak));
                    self.check_env.bind_local(ids[0], elem_shape, dom_origin);
                    let eb = self.lower_expr_rec(body, allow_prime, in_prime);
                    self.locals.pop();
                    self.check_env.unbind_local(ids[0]);
                    let eb = eb?;
                    return self.charge(format!("(Expr.fnConstruct {dom} {eb})"));
                }
                BoundVars::Tuple(ids) => {
                    let elem_shapes = self.totality.prove_tuple_set_arity(&b.set, ids.len(), in_prime, &self.check_env)?;
                    let dom = self.lower_expr_rec(&b.set, allow_prime, in_prime)?;
                    self.locals.push(Slot::Temp);
                    let eb = self.bind_tuple_expr_step(ids, &elem_shapes, 0, 0, |ctx| ctx.lower_expr_rec(body, allow_prime, in_prime));
                    self.locals.pop();
                    let eb = eb?;
                    return self.charge(format!("(Expr.fnConstruct {dom} {eb})"));
                }
                _ => {}
            }
        }
        let mut doms = Vec::new();
        let mut vars: Vec<(BoundVars, Vec<Shape>)> = Vec::new();
        for b in bounds {
            let d = self.lower_expr_rec(&b.set, allow_prime, in_prime)?;
            match &b.vars {
                BoundVars::Many(ids) => {
                    let (es, _) = self.totality.bound_elem_info(&b.set, in_prime, &self.check_env);
                    for &id in ids {
                        doms.push(d.clone());
                        vars.push((BoundVars::Many(vec![id]), vec![es.clone()]));
                    }
                }
                BoundVars::Tuple(ids) => {
                    let elem_shapes = self.totality.prove_tuple_set_arity(&b.set, ids.len(), in_prime, &self.check_env)?;
                    doms.push(d);
                    vars.push((BoundVars::Tuple(ids.clone()), elem_shapes));
                }
            }
        }
        let cart = self.charge(format!("(Expr.cartesian [{}])", doms.join(", ")))?;
        self.locals.push(Slot::Temp);
        let eb = self.bind_fn_multi(&vars, 0, 0, body, allow_prime, in_prime);
        self.locals.pop();
        let eb = eb?;
        self.charge(format!("(Expr.fnConstruct {cart} {eb})"))
    }

    fn bind_fn_multi(
        &mut self,
        vars: &[(BoundVars, Vec<Shape>)],
        idx: usize,
        tuple_depth: usize,
        body: &Expr,
        allow_prime: bool,
        in_prime: bool,
    ) -> Option<String> {
        if idx == vars.len() {
            return self.lower_expr_rec(body, allow_prime, in_prime);
        }
        let one_based = self.int_expr((idx + 1) as i128);
        let proj = format!("(Expr.fnApp (Expr.localVar {tuple_depth}) {one_based})");
        match &vars[idx].0 {
            BoundVars::Many(ids) if ids.len() == 1 => {
                self.locals.push(Slot::Local(ids[0], AtomKind::Unknown));
                self.check_env.bind_local(ids[0], vars[idx].1[0].clone(), None);
                let inner = self.bind_fn_multi(vars, idx + 1, tuple_depth + 1, body, allow_prime, in_prime);
                self.locals.pop();
                self.check_env.unbind_local(ids[0]);
                let inner = inner?;
                self.charge(format!("(Expr.letBind {proj} {inner})"))
            }
            BoundVars::Tuple(ids) => {
                self.locals.push(Slot::Temp);
                let inner = self.bind_tuple_expr_step(ids, &vars[idx].1, 0, 0, |ctx| {
                    ctx.bind_fn_multi(vars, idx + 1, tuple_depth + 1 + ids.len(), body, allow_prime, in_prime)
                });
                self.locals.pop();
                let inner = inner?;
                self.charge(format!("(Expr.letBind {proj} {inner})"))
            }
            _ => None,
        }
    }

    fn lower_set_map(&mut self, expr: &Expr, bounds: &[Bound], allow_prime: bool, in_prime: bool) -> Option<String> {
        let mut flat: Vec<(&Expr, BoundVars)> = Vec::new();
        for b in bounds {
            match &b.vars {
                BoundVars::Many(ids) => {
                    for &id in ids {
                        flat.push((&b.set, BoundVars::Many(vec![id])));
                    }
                }
                BoundVars::Tuple(ids) => flat.push((&b.set, BoundVars::Tuple(ids.clone()))),
            }
        }
        if flat.is_empty() {
            return None;
        }
        self.lower_set_map_step(expr, &flat, allow_prime, in_prime)
    }

    fn lower_set_map_step(&mut self, expr: &Expr, flat: &[(&Expr, BoundVars)], allow_prime: bool, in_prime: bool) -> Option<String> {
        let (set, vars) = &flat[0];
        let dom = self.lower_expr_rec(set, allow_prime, in_prime)?;
        let is_last = flat.len() == 1;
        let mapped = match vars {
            BoundVars::Many(ids) if ids.len() == 1 => {
                let ak = self.elem_atom_kind(set);
                let (elem_shape, dom_origin) = self.totality.bound_elem_info(set, in_prime, &self.check_env);
                self.locals.push(Slot::Local(ids[0], ak));
                self.check_env.bind_local(ids[0], elem_shape, dom_origin);
                let inner = if is_last {
                    self.lower_expr_rec(expr, allow_prime, in_prime)
                } else {
                    self.lower_set_map_step(expr, &flat[1..], allow_prime, in_prime)
                };
                self.locals.pop();
                self.check_env.unbind_local(ids[0]);
                let inner = inner?;
                self.charge(format!("(Expr.setMap {dom} {inner})"))?
            }
            BoundVars::Tuple(ids) => {
                let elem_shapes = self.totality.prove_tuple_set_arity(set, ids.len(), in_prime, &self.check_env)?;
                self.locals.push(Slot::Temp);
                let inner = self.bind_tuple_expr_step(ids, &elem_shapes, 0, 0, |ctx| {
                    if is_last {
                        ctx.lower_expr_rec(expr, allow_prime, in_prime)
                    } else {
                        ctx.lower_set_map_step(expr, &flat[1..], allow_prime, in_prime)
                    }
                });
                self.locals.pop();
                let inner = inner?;
                self.charge(format!("(Expr.setMap {dom} {inner})"))?
            }
            _ => return None,
        };
        if is_last {
            Some(mapped)
        } else {
            self.charge(format!("(Expr.union {mapped})"))
        }
    }

    pub(super) fn try_const_set_enum(&self, es: &[Expr]) -> Option<CfgValue> {
        let mut vals = Vec::with_capacity(es.len());
        for e in es {
            let ExprKind::Const(cid) = &*e.kind else { return None };
            vals.push((*self.consts.get(cid)?).clone());
        }
        Some(CfgValue::Set(vals))
    }

    pub(super) fn try_group_set<'b>(&self, val: &'b CfgValue) -> Option<(GroupMask, Vec<&'b CfgValue>)> {
        let CfgValue::Set(elems) = val else { return None };
        let mut model_names: BTreeSet<&str> = BTreeSet::new();
        let mut fixed = Vec::new();
        for elem in elems {
            match elem {
                CfgValue::ModelValue(m) if self.all_keys.contains(m.as_str()) => {
                    model_names.insert(m.as_str());
                }
                _ => fixed.push(elem),
            }
        }
        let mut mask: GroupMask = 0;
        for (gi, g) in self.groups.iter().enumerate() {
            let count = g.key_set.iter().filter(|k| model_names.contains(k.as_ref())).count();
            if count == g.key_set.len() {
                mask |= 1 << gi;
            } else if count > 0 {
                return None;
            }
        }
        Some((mask, fixed))
    }

    /// A `.cfg` value that is one key-free atom, for the fixed part of a
    /// stratified `k`-subset family. Symmetric model values belong on the moved
    /// side and are never fixed here.
    fn fixed_atom_key(&self, v: &CfgValue) -> Option<AtomKey> {
        match v {
            CfgValue::Int(n) => Some(AtomKey::Int(i128::from(*n))),
            CfgValue::Str(s) => Some(AtomKey::Str(Arc::from(s.as_str()))),
            CfgValue::Bool(b) => Some(AtomKey::Bool(*b)),
            CfgValue::ModelValue(m) if !self.all_keys.contains(m.as_str()) => Some(AtomKey::Model(Arc::from(m.as_str()))),
            _ => None,
        }
    }

    /// Recognize a set of `k`-subsets of one group per fixed-atom stratum, e.g.
    /// `Quorum = {{a1, a2}, {a1, a3}, {a2, a3}}` or the mixed
    /// `{{a1, a2, fa1}, {a1, a3, fa1}, {a2, a3, fa1}, {a1, a2, a3}}` in which
    /// `fa1` is a key-free atom outside every group. Each inner set is split
    /// into the moved keys of one group and its key-free fixed atoms; all inner
    /// sets sharing a fixed-atom stratum must together be the exact union of
    /// the `|G_g|`-choose-`k` subsets of that group for the sizes `k` present.
    /// A stratum lowers to `{Q \cup F : Q \in SUBSET Group_g, Cardinality(Q) \in
    /// sizes}` and the strata combine with `\cup`, so no new certificate
    /// definition is needed.
    fn try_symmetric_k_subsets(&mut self, elems: &[CfgValue]) -> Option<String> {
        if elems.is_empty() {
            return None;
        }
        let mut strata: BTreeMap<BTreeSet<AtomKey>, KSubsetStratum> = BTreeMap::new();
        for elem in elems {
            let CfgValue::Set(sub) = elem else { return None };
            let mut fixed: BTreeSet<AtomKey> = BTreeSet::new();
            let mut moved: BTreeSet<Arc<str>> = BTreeSet::new();
            let mut group: Option<usize> = None;
            for item in sub {
                match item {
                    CfgValue::ModelValue(m) if self.all_keys.contains(m.as_str()) => {
                        let gi = self.groups.iter().position(|g| g.key_set.contains(m.as_str()))?;
                        if group.is_some_and(|prev| prev != gi) {
                            return None;
                        }
                        group = Some(gi);
                        moved.insert(Arc::from(m.as_str()));
                    }
                    other => {
                        fixed.insert(self.fixed_atom_key(other)?);
                    }
                }
            }
            let stratum = strata.entry(fixed).or_default();
            // No moved key: covered by the `k = 0` family of whichever group the
            // stratum's other members use.
            if let Some(gi) = group {
                if stratum.group.is_some_and(|prev| prev != gi) {
                    return None;
                }
                stratum.group = Some(gi);
            }
            stratum.moved.insert(moved);
        }
        // Every stratum must be exactly the union of its group's `k`-subsets.
        for stratum in strata.values() {
            let Some(gi) = stratum.group else { continue };
            let n = self.groups[gi].keys.len();
            let sizes: BTreeSet<usize> = stratum.moved.iter().map(BTreeSet::len).collect();
            let mut expected = 0usize;
            for bits in 0usize..(1usize << n) {
                if !sizes.contains(&(bits.count_ones() as usize)) {
                    continue;
                }
                expected += 1;
                let sub: BTreeSet<Arc<str>> = (0..n).filter(|&i| (bits & (1 << i)) != 0).map(|i| self.groups[gi].keys[i].clone()).collect();
                if !stratum.moved.contains(&sub) {
                    return None;
                }
            }
            if stratum.moved.len() != expected {
                return None;
            }
        }
        let mut parts: Vec<String> = Vec::with_capacity(strata.len());
        for (fixed, stratum) in &strata {
            let fixed_exprs: Vec<String> = fixed
                .iter()
                .map(|k| {
                    let id = self.atom_id_of(k.clone());
                    format!("(Expr.atom {id})")
                })
                .collect();
            let Some(gi) = stratum.group else {
                // A stratum of one fixed-only set: `{{F}}`, with no group read.
                parts.push(format!("(Expr.setEnum [(Expr.setEnum [{}])])", fixed_exprs.join(", ")));
                continue;
            };
            self.used_groups |= 1 << gi;
            let m = self.mask_lean(1 << gi);
            let sizes: BTreeSet<usize> = stratum.moved.iter().map(BTreeSet::len).collect();
            let size_exprs: Vec<String> = sizes.iter().map(|&k| self.int_expr(k as i128)).collect();
            let filtered = format!(
                "(Expr.setFilter (Expr.powerset (Expr.groupSet {m})) (Form.mem (Expr.card (Expr.localVar 0)) (SetPred.enum [{}])))",
                size_exprs.join(", ")
            );
            if fixed.is_empty() {
                parts.push(filtered);
            } else {
                parts.push(format!("(Expr.setMap {filtered} (Expr.cup (Expr.localVar 0) (Expr.setEnum [{}])))", fixed_exprs.join(", ")));
            }
        }
        let mut combined = parts.pop()?;
        while let Some(part) = parts.pop() {
            combined = format!("(Expr.cup {part} {combined})");
        }
        Some(combined)
    }

    pub(super) fn lower_cfg_value(&mut self, val: &CfgValue) -> Option<String> {
        self.bump()?;
        match val {
            CfgValue::Int(n) => Some(self.int_expr(i128::from(*n))),
            CfgValue::Str(s) => {
                let id = self.atom_id(AtomKey::Str(Arc::from(s.as_str())));
                Some(format!("(Expr.atom {id})"))
            }
            CfgValue::Bool(b) => {
                let id = self.atom_id(AtomKey::Bool(*b));
                Some(format!("(Expr.atom {id})"))
            }
            CfgValue::ModelValue(m) => {
                if self.all_keys.contains(m.as_str()) {
                    return None;
                }
                let id = self.atom_id(AtomKey::Model(Arc::from(m.as_str())));
                Some(format!("(Expr.atom {id})"))
            }
            CfgValue::Tuple(es) => {
                let items: Vec<_> = es.iter().map(|e| self.lower_cfg_value(e)).collect::<Option<_>>()?;
                Some(format!("(Expr.seqLit [{}])", items.join(", ")))
            }
            CfgValue::Set(elems) => {
                if let Some((mask, fixed)) = self.try_group_set(val) {
                    if mask != 0 {
                        self.used_groups |= mask;
                        let g = format!("(Expr.groupSet {})", self.mask_lean(mask));
                        if fixed.is_empty() {
                            return Some(g);
                        }
                        let fixed_exprs: Vec<_> = fixed.iter().map(|e| self.lower_cfg_value(e)).collect::<Option<_>>()?;
                        return Some(format!("(Expr.cup {g} (Expr.setEnum [{}]))", fixed_exprs.join(", ")));
                    }
                }
                if let Some(ksub) = self.try_symmetric_k_subsets(elems) {
                    return Some(ksub);
                }
                let items: Vec<_> = elems.iter().map(|e| self.lower_cfg_value(e)).collect::<Option<_>>()?;
                Some(format!("(Expr.setEnum [{}])", items.join(", ")))
            }
        }
    }

    /// Whether a `.cfg` value is one key-free atom: the same test `lower_cfg_value`
    /// applies when it lowers the value to `Expr.atom`.
    fn cfg_value_is_atom(&self, v: &CfgValue) -> bool {
        match v {
            CfgValue::Int(_) | CfgValue::Str(_) | CfgValue::Bool(_) => true,
            CfgValue::ModelValue(m) => !self.all_keys.contains(m.as_str()),
            _ => false,
        }
    }

    fn is_definitely_atom(&self, e: &Expr) -> bool {
        match &*e.kind {
            ExprKind::Num(_) | ExprKind::Str(_) | ExprKind::Bool(_) | ExprKind::Decimal(_) => true,
            ExprKind::CfgLiteral(v) => self.cfg_value_is_atom(v),
            ExprKind::Local(id) => self.local_atom_kind(*id) == AtomKind::Atom,
            ExprKind::Const(cid) => match self.consts.get(cid) {
                Some(CfgValue::Int(_) | CfgValue::Str(_) | CfgValue::Bool(_)) => true,
                Some(CfgValue::ModelValue(m)) => !self.all_keys.contains(m.as_str()),
                _ => false,
            },
            ExprKind::Builtin { op, args } => match op {
                B::Cardinality
                | B::Len
                | B::Plus
                | B::Minus
                | B::Mul
                | B::Div
                | B::Mod
                | B::Pow
                | B::Neg
                | B::Gcd
                | B::Atoi
                | B::SetMax
                | B::SetMin
                | B::Not
                | B::Implies
                | B::Equiv
                | B::Eq
                | B::Neq
                | B::In
                | B::NotIn
                | B::SubsetEq
                | B::Lt
                | B::Le
                | B::Gt
                | B::Ge
                | B::IsFiniteSet
                | B::IsInjective
                | B::IsABag
                | B::BagIn
                | B::SqSubseteq
                | B::CopiesIn
                | B::BagCardinality => true,
                B::TLCEval => args.first().is_some_and(|a| self.is_definitely_atom(a)),
                B::FoldSet | B::FoldFunction | B::FoldFunctionOnSet | B::MapThenFoldSet | B::FoldBag => args
                    .first()
                    .and_then(classify_ac_op)
                    .is_some_and(|ac| matches!(ac, AcOpKind::IntAdd | AcOpKind::IntMul | AcOpKind::BoolAnd | AcOpKind::BoolOr)),
                _ => false,
            },
            ExprKind::If { then, els, .. } => self.is_definitely_atom(then) && self.is_definitely_atom(els),
            ExprKind::And(_) | ExprKind::Or(_) | ExprKind::Quant { .. } => true,
            _ => false,
        }
    }

    pub(super) fn is_definitely_atom_set(&self, e: &Expr) -> bool {
        match &*e.kind {
            ExprKind::Local(id) => self.local_atom_kind(*id) == AtomKind::AtomSet,
            ExprKind::CfgLiteral(v) => match &**v {
                CfgValue::Set(es) => es.iter().all(|v| self.cfg_value_is_atom(v)),
                _ => false,
            },
            ExprKind::SetEnum(es) => es.iter().all(|x| self.is_definitely_atom(x)),
            ExprKind::SetFilter { bound, .. } => self.is_definitely_atom_set(&bound.set),
            ExprKind::SetMap { expr, .. } => self.is_definitely_atom(expr),
            ExprKind::Const(cid) => match self.consts.get(cid) {
                Some(CfgValue::Set(es)) => es.iter().all(|v| match v {
                    CfgValue::Int(_) | CfgValue::Str(_) | CfgValue::Bool(_) => true,
                    CfgValue::ModelValue(m) => !self.all_keys.contains(m.as_str()),
                    _ => false,
                }),
                _ => false,
            },
            ExprKind::Builtin { op, args } => match (op, args.as_slice()) {
                (B::DotDot, [_, _]) | (B::Boolean, []) => true,
                (B::Cup | B::Cap | B::SetMinus, [a, b]) => self.is_definitely_atom_set(a) && self.is_definitely_atom_set(b),
                (B::TLCEval, [a]) => self.is_definitely_atom_set(a),
                _ => false,
            },
            _ => false,
        }
    }
}
