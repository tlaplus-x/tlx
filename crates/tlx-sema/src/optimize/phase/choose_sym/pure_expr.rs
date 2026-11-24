//! Choice-free total expression lowering (`PureTest` and `PureExpr`).

use super::super::{max_local, variable};
use super::domain_infer::{exact_k_subset_family, group_mask_exact, independent, is_pure_bool_domain, VarShape};
use super::{subst_local, Emitter, GroupMask, KeyRef, Locals};
use crate::{builtins::Builtin as B, hir::*, visit};
use std::sync::Arc;

#[derive(Clone, Debug)]
pub(super) struct MsgBoundVar {
    pub local: LocalId,
    pub fields: Vec<Arc<str>>,
    pub key_field: Arc<str>,
    pub val_field: Option<Arc<str>>,
}

#[derive(Clone, Debug, Default)]
pub(super) struct AuxScope {
    pub msg_vars: Vec<MsgBoundVar>,
    pub proj_vals: Vec<LocalId>,
    pub count_nats: Vec<LocalId>,
    pub fold_ints: Vec<LocalId>,
}

struct LeafReads {
    map_reads: Vec<String>,
    slot_map_reads: Vec<String>,
    slot_fixed_reads: Vec<String>,
    flag_reads: Vec<String>,
    counts: Vec<(GroupMask, String)>,
    holes: Vec<String>,
}

impl LeafReads {
    fn new() -> Self {
        Self { map_reads: vec![], slot_map_reads: vec![], slot_fixed_reads: vec![], flag_reads: vec![], counts: vec![], holes: vec![] }
    }
}

impl Emitter<'_> {
    pub(super) fn pure_tests(&mut self, es: &[Expr], keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> Option<String> {
        let mut out = "(PureTest.truth true)".to_owned();
        for e in es {
            let t = self.pure_test(e, keys, aux)?;
            out = if out == "(PureTest.truth true)" { t } else { bounded(format!("(PureTest.conj {out} {t})"))? };
        }
        Some(out)
    }

    pub(super) fn pure_test(&mut self, e: &Expr, keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> Option<String> {
        let res = self.pure_test_inner(e, keys, aux)?;
        bounded(res)
    }

    fn pure_test_inner(&mut self, e: &Expr, keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> Option<String> {
        if self.contains_any_choose(e) {
            return None;
        }
        match &*e.kind {
            ExprKind::Bool(b) => return Some(format!("(PureTest.truth {b})")),
            ExprKind::And(es) => return self.pure_tests(es, keys, aux),
            ExprKind::Or(es) if !es.is_empty() => {
                let mut it = es.iter();
                let mut out = self.pure_test(it.next()?, keys, aux)?;
                for item in it {
                    out = bounded(format!("(PureTest.disj {out} {})", self.pure_test(item, keys, aux)?))?;
                }
                return Some(out);
            }
            ExprKind::Builtin { op, args } => match (op, args.as_slice()) {
                (B::Not, [a]) => return Some(format!("(PureTest.neg {})", self.pure_test(a, keys, aux)?)),
                (B::Implies, [a, b]) => {
                    return Some(format!(
                        "(PureTest.disj (PureTest.neg {}) {})",
                        self.pure_test(a, keys, aux)?,
                        self.pure_test(b, keys, aux)?
                    ))
                }
                (B::Equiv, [a, b]) => {
                    let ta = self.pure_test(a, keys, aux)?;
                    let tb = self.pure_test(b, keys, aux)?;
                    return Some(format!(
                        "(PureTest.disj (PureTest.conj {ta} {tb}) (PureTest.conj (PureTest.neg {ta}) (PureTest.neg {tb})))"
                    ));
                }
                (B::Eq | B::Neq, [a, b]) => {
                    if let Some(eq) = self.special_pure_eq(a, b, keys, aux) {
                        return Some(if *op == B::Eq { eq } else { format!("(PureTest.neg {eq})") });
                    }
                }
                (B::In | B::NotIn, [elem, set]) => {
                    if let Some(mem) = self.special_pure_membership(elem, set, keys, aux) {
                        return Some(if *op == B::In { mem } else { format!("(PureTest.neg {mem})") });
                    }
                }
                (B::SubsetEq, [a, b]) => {
                    if let Some(sub) = self.special_pure_subseteq(a, b, keys, aux) {
                        return Some(sub);
                    }
                }
                _ => {}
            },
            ExprKind::Quant { kind, bounds, body } => {
                if let Some(q) = self.quant_pure_test(*kind, bounds, body, keys, aux) {
                    return Some(q);
                }
            }
            ExprKind::If { cond, then, els } => {
                let c = self.pure_test(cond, keys, aux)?;
                return Some(format!(
                    "(PureTest.disj (PureTest.conj {c} {}) (PureTest.conj (PureTest.neg {c}) {}))",
                    self.pure_test(then, keys, aux)?,
                    self.pure_test(els, keys, aux)?
                ));
            }
            ExprKind::FnApp { func, args } => {
                if let Some((mask, flag_id)) = self.bool_map_flag_target(func) {
                    let [arg] = args.as_slice() else { return None };
                    let (kref, kmask, _) = self.key_ref(arg, keys, aux)?;
                    if (kmask & !mask) != 0 {
                        return None;
                    }
                    return Some(format!("(PureTest.flag ⟨{flag_id}, by decide⟩ {})", kref.lean()));
                }
            }
            _ => {}
        }
        self.pure_leaf(e, keys, aux, "PureTest")
    }

    fn quant_pure_test(
        &mut self,
        kind: QuantKind,
        bounds: &[Bound],
        body: &Expr,
        keys: &[(LocalId, GroupMask)],
        aux: &AuxScope,
    ) -> Option<String> {
        if bounds.is_empty() {
            return self.pure_test(body, keys, aux);
        }
        let bnd = &bounds[0];
        let BoundVars::Many(ids) = &bnd.vars else { return None };
        let rest = &bounds[1..];
        let quant = match kind {
            QuantKind::Forall => "all",
            QuantKind::Exists => "some",
        };
        if let Some(exact) = self.domains.exact_set(&bnd.set) {
            if let Some((mask, fixed)) = group_mask_exact(self.groups, &exact) {
                if mask != 0 && fixed.is_empty() {
                    let mut scope = keys.to_vec();
                    for &id in ids {
                        scope.insert(0, (id, mask));
                    }
                    let mut out = if rest.is_empty() {
                        self.pure_test(body, &scope, aux)?
                    } else {
                        self.quant_pure_test(kind, rest, body, &scope, aux)?
                    };
                    let m = self.mask_lean(mask);
                    for _ in ids {
                        out = format!("(PureTest.{quant} {m} {out})");
                    }
                    return Some(out);
                }
            }
        }
        if let Some(v) = variable(&bnd.set, false) {
            if let VarShape::KeySetFlag { mask, flag_id } = self.shapes[v.idx()] {
                let mut scope = keys.to_vec();
                for &id in ids {
                    scope.insert(0, (id, mask));
                }
                let inner =
                    if rest.is_empty() { self.pure_test(body, &scope, aux)? } else { self.quant_pure_test(kind, rest, body, &scope, aux)? };
                let mut guard_in = "(PureTest.truth true)".to_owned();
                for (offset, _) in ids.iter().enumerate() {
                    let pos = ids.len() - 1 - offset;
                    let mem = format!("(PureTest.flag ⟨{flag_id}, by decide⟩ (KeyRef.bound {pos}))");
                    guard_in = if guard_in == "(PureTest.truth true)" { mem } else { format!("(PureTest.conj {guard_in} {mem})") };
                }
                let mut out = match kind {
                    QuantKind::Forall => format!("(PureTest.disj (PureTest.neg {guard_in}) {inner})"),
                    QuantKind::Exists => format!("(PureTest.conj {guard_in} {inner})"),
                };
                let m = self.mask_lean(mask);
                for _ in ids {
                    out = format!("(PureTest.{quant} {m} {out})");
                }
                return Some(out);
            }
            if ids.len() == 1 {
                if let VarShape::MsgSet { mask, msg_id, ref fields, ref key_field, ref val_field } = self.shapes[v.idx()].clone() {
                    let id = ids[0];
                    let mut scope = keys.to_vec();
                    scope.insert(0, (id, mask));
                    let mut aux2 = aux.clone();
                    aux2.msg_vars.insert(
                        0,
                        MsgBoundVar { local: id, fields: fields.clone(), key_field: key_field.clone(), val_field: val_field.clone() },
                    );
                    let inner = if rest.is_empty() {
                        self.pure_test(body, &scope, &aux2)?
                    } else {
                        self.quant_pure_test(kind, rest, body, &scope, &aux2)?
                    };
                    let mquant = match kind {
                        QuantKind::Forall => "msgAll",
                        QuantKind::Exists => "msgSome",
                    };
                    return Some(format!("(PureTest.{mquant} ⟨{msg_id}, by decide⟩ {inner})"));
                }
            }
        }
        None
    }

    fn special_pure_eq(&mut self, a: &Expr, b: &Expr, keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> Option<String> {
        if let (Some((ka, _)), Some((kb, _))) = (self.key_or_fixed_ref(a, keys, aux), self.key_or_fixed_ref(b, keys, aux)) {
            if !matches!((ka, kb), (KeyRef::Fixed(_), KeyRef::Fixed(_))) {
                return Some(format!("(PureTest.equal {} {})", ka.lean(), kb.lean()));
            }
        }
        if let Some(eq) = self.msgset_empty_eq(a, b).or_else(|| self.msgset_empty_eq(b, a)) {
            return Some(eq);
        }
        if let Some(eq) = self.keyset_flag_empty_eq(a, b).or_else(|| self.keyset_flag_empty_eq(b, a)) {
            return Some(eq);
        }
        if let Some(eq) = self.map_pure_equality(a, b, keys, aux).or_else(|| self.map_pure_equality(b, a, keys, aux)) {
            return Some(eq);
        }
        if let Some(eq) = self.general_keyset_eq(a, b, keys, aux) {
            return Some(eq);
        }
        None
    }

    fn msgset_empty_eq(&self, a: &Expr, b: &Expr) -> Option<String> {
        let va = variable(a, false)?;
        let VarShape::MsgSet { msg_id, .. } = self.shapes[va.idx()] else { return None };
        let ExprKind::SetEnum(es) = &*b.kind else { return None };
        es.is_empty().then(|| format!("(PureTest.msgEmpty ⟨{msg_id}, by decide⟩)"))
    }

    fn keyset_flag_empty_eq(&self, a: &Expr, b: &Expr) -> Option<String> {
        let va = variable(a, false)?;
        let VarShape::KeySetFlag { mask, flag_id } = self.shapes[va.idx()] else { return None };
        let ExprKind::SetEnum(es) = &*b.kind else { return None };
        es.is_empty().then(|| {
            format!("(PureTest.all {} (PureTest.neg (PureTest.flag ⟨{flag_id}, by decide⟩ (KeyRef.bound 0))))", self.mask_lean(mask))
        })
    }

    fn map_pure_equality(&mut self, a: &Expr, b: &Expr, keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> Option<String> {
        let mask_a = match &*a.kind {
            ExprKind::Var(v) => match self.shapes[v.idx()] {
                VarShape::FixedMap { mask, .. } | VarShape::BoolMapFlag { mask, .. } => mask,
                _ => return None,
            },
            _ => return None,
        };
        if let ExprKind::FnConstruct { bounds, body } = &*b.kind {
            if bounds.len() == 1 {
                let BoundVars::Many(ids) = &bounds[0].vars else { return None };
                let [id] = ids.as_slice() else { return None };
                let exact = self.domains.exact_set(&bounds[0].set)?;
                let (mask_b, fixed) = group_mask_exact(self.groups, &exact)?;
                if mask_b == mask_a && fixed.is_empty() {
                    let mut scope = keys.to_vec();
                    scope.insert(0, (*id, mask_a));
                    let lhs = Expr::new(ExprKind::FnApp { func: a.clone(), args: vec![Expr::new(ExprKind::Local(*id), b.span)] }, b.span);
                    let eq_expr = Expr::new(ExprKind::Builtin { op: B::Eq, args: vec![lhs, body.clone()] }, b.span);
                    let inner = self.pure_test(&eq_expr, &scope, aux)?;
                    return Some(format!("(PureTest.all {} {inner})", self.mask_lean(mask_a)));
                }
            }
        }
        None
    }

    pub(super) fn keyset_expr_mask(&self, e: &Expr, keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> Option<GroupMask> {
        if let Some(v) = variable(e, false) {
            if let VarShape::KeySetFlag { mask, .. } = self.shapes[v.idx()] {
                return Some(mask);
            }
        }
        if let Some(exact) = self.domains.exact_set(e) {
            let (mask, fixed) = group_mask_exact(self.groups, &exact)?;
            if fixed.is_empty() {
                return Some(mask);
            }
            return None;
        }
        match &*e.kind {
            ExprKind::SetEnum(es) => {
                let mut mask = 0;
                for item in es {
                    let (_, km, has_fixed) = self.key_ref(item, keys, aux)?;
                    if has_fixed {
                        return None;
                    }
                    mask |= km;
                }
                Some(mask)
            }
            ExprKind::Builtin { op: B::Cup | B::Cap | B::SetMinus, args } if args.len() == 2 => {
                Some(self.keyset_expr_mask(&args[0], keys, aux)? | self.keyset_expr_mask(&args[1], keys, aux)?)
            }
            ExprKind::SetFilter { bound, .. } => self.keyset_expr_mask(&bound.set, keys, aux),
            _ => None,
        }
    }

    fn general_keyset_eq(&mut self, a: &Expr, b: &Expr, keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> Option<String> {
        let ma = self.keyset_expr_mask(a, keys, aux)?;
        let mb = self.keyset_expr_mask(b, keys, aux)?;
        let union_mask = ma | mb;
        if union_mask == 0 {
            return None;
        }
        let fresh = self.alloc_local();
        let mut scope = keys.to_vec();
        scope.insert(0, (fresh, union_mask));
        let in_a = self.key_in_set_pure(KeyRef::Bound(0), union_mask, a, &scope, aux)?;
        let in_b = self.key_in_set_pure(KeyRef::Bound(0), union_mask, b, &scope, aux)?;
        let iff = format!("(PureTest.disj (PureTest.conj {in_a} {in_b}) (PureTest.conj (PureTest.neg {in_a}) (PureTest.neg {in_b})))");
        Some(format!("(PureTest.all {} {iff})", self.mask_lean(union_mask)))
    }

    fn special_pure_membership(&mut self, elem: &Expr, set: &Expr, keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> Option<String> {
        if let Some(v) = variable(elem, false).filter(|v| self.is_non_core(*v)) {
            if self.domains.belongs(&self.domains.vars[v.idx()], set) {
                return Some("(PureTest.truth true)".into());
            }
            if let VarShape::KeySetFlag { mask, flag_id } = self.shapes[v.idx()] {
                if let Some((fmask, card)) = exact_k_subset_family(self.program, self.cfg, set, self.groups) {
                    if fmask == mask {
                        let id = self.atoms.len();
                        self.atoms.push(format!("KeySetFlag {flag_id} cardinality == {card} (k-subset family)"));
                        let spec = format!("⟨{id}, [], [], [], []⟩");
                        return Some(format!(
                            "(PureTest.bindCount {} (PureTest.flag ⟨{flag_id}, by decide⟩ (KeyRef.bound 0)) (PureTest.leaf {spec}))",
                            self.mask_lean(mask)
                        ));
                    }
                }
            }
        }
        if let Some((kref, kmask, has_fixed)) = self.key_ref(elem, keys, aux) {
            if !has_fixed {
                if let Some(res) = self.key_in_set_pure(kref, kmask, set, keys, aux) {
                    return Some(res);
                }
            } else if let KeyRef::Slot(slot_id) = kref {
                if let Some(exact) = self.domains.exact_set(set) {
                    if let Some((mask, fixed)) = group_mask_exact(self.groups, &exact) {
                        if mask != 0 && fixed.is_empty() {
                            return Some(format!("(PureTest.inGroup {} {})", KeyRef::Slot(slot_id).lean(), self.mask_lean(mask)));
                        }
                    }
                }
                if let Some(v) = variable(set, false) {
                    if let VarShape::KeySetFlag { mask, flag_id } = self.shapes[v.idx()] {
                        if (kmask & !mask) == 0 {
                            return Some(format!("(PureTest.flag ⟨{flag_id}, by decide⟩ {})", KeyRef::Slot(slot_id).lean()));
                        }
                    }
                }
            }
        }
        if let Some(v) = variable(set, false) {
            if let VarShape::KeySetFlag { .. } = self.shapes[v.idx()] {
                if independent(&self.eval_expr_domain(elem, &Locals::new()), self.all_keys)
                    && !self.mentions_non_core(elem)
                    && !self.mentions_keys(elem, keys, aux)
                {
                    return Some("(PureTest.truth false)".into());
                }
            }
            if let VarShape::MsgSet { mask, msg_id, ref fields, ref key_field, ref val_field } = self.shapes[v.idx()].clone() {
                let ExprKind::Record(fs) = &*elem.kind else { return None };
                let mut fnames: Vec<Arc<str>> = fs.iter().map(|(k, _)| k.clone()).collect();
                fnames.sort();
                if fnames == *fields {
                    let fresh = self.alloc_local();
                    let mut scope = keys.to_vec();
                    scope.insert(0, (fresh, mask));
                    let mut aux2 = aux.clone();
                    aux2.msg_vars.insert(
                        0,
                        MsgBoundVar { local: fresh, fields: fields.clone(), key_field: key_field.clone(), val_field: val_field.clone() },
                    );
                    let mut conj = Vec::new();
                    for (fname, fexpr) in fs {
                        let lhs = Expr::new(
                            ExprKind::Field { record: Expr::new(ExprKind::Local(fresh), elem.span), field: fname.clone() },
                            elem.span,
                        );
                        conj.push(Expr::new(ExprKind::Builtin { op: B::Eq, args: vec![lhs, fexpr.clone()] }, elem.span));
                    }
                    let body = self.pure_tests(&conj, &scope, &aux2)?;
                    return Some(format!("(PureTest.msgSome ⟨{msg_id}, by decide⟩ {body})"));
                }
            }
        }
        None
    }

    fn special_pure_subseteq(&mut self, a: &Expr, b: &Expr, keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> Option<String> {
        if let Some(v) = variable(a, false).filter(|v| self.is_non_core(*v)) {
            if self.domains.subset_belongs(&self.domains.vars[v.idx()], b) {
                return Some("(PureTest.truth true)".into());
            }
        }
        let ma = self.keyset_expr_mask(a, keys, aux)?;
        let mb = self.keyset_expr_mask(b, keys, aux)?;
        let mask = ma | mb;
        if mask == 0 {
            return None;
        }
        let fresh = self.alloc_local();
        let mut scope = keys.to_vec();
        scope.insert(0, (fresh, mask));
        let in_a = self.key_in_set_pure(KeyRef::Bound(0), mask, a, &scope, aux)?;
        let in_b = self.key_in_set_pure(KeyRef::Bound(0), mask, b, &scope, aux)?;
        Some(format!("(PureTest.all {} (PureTest.disj (PureTest.neg {in_a}) {in_b}))", self.mask_lean(mask)))
    }

    pub(super) fn key_in_set_pure(
        &mut self,
        kref: KeyRef,
        kmask: GroupMask,
        set: &Expr,
        keys: &[(LocalId, GroupMask)],
        aux: &AuxScope,
    ) -> Option<String> {
        if let Some(v) = variable(set, false) {
            if let VarShape::KeySetFlag { mask, flag_id } = self.shapes[v.idx()] {
                if (kmask & !mask) == 0 {
                    return Some(format!("(PureTest.flag ⟨{flag_id}, by decide⟩ {})", kref.lean()));
                }
                return Some(format!(
                    "(PureTest.conj (PureTest.inGroup {} {}) (PureTest.flag ⟨{flag_id}, by decide⟩ {}))",
                    kref.lean(),
                    self.mask_lean(mask),
                    kref.lean()
                ));
            }
        }
        if let Some(exact) = self.domains.exact_set(set) {
            if let Some((mask, fixed)) = group_mask_exact(self.groups, &exact) {
                if fixed.is_empty() {
                    return Some(if mask == 0 {
                        "(PureTest.truth false)".into()
                    } else {
                        format!("(PureTest.inGroup {} {})", kref.lean(), self.mask_lean(mask))
                    });
                }
            }
        }
        match &*set.kind {
            ExprKind::SetEnum(es) => {
                let mut out = "(PureTest.truth false)".to_owned();
                for item in es {
                    if let Some((iref, _, _)) = self.key_ref(item, keys, aux) {
                        let eq = format!("(PureTest.equal {} {})", kref.lean(), iref.lean());
                        out = if out == "(PureTest.truth false)" { eq } else { bounded(format!("(PureTest.disj {out} {eq})"))? };
                    } else if !independent(&self.eval_expr_domain(item, &Locals::new()), self.all_keys)
                        || self.mentions_non_core(item)
                        || self.mentions_keys(item, keys, aux)
                    {
                        return None;
                    }
                }
                Some(out)
            }
            ExprKind::Builtin { op, args } => match (op, args.as_slice()) {
                (B::Cup, [a, b]) => {
                    let ta = self.key_in_set_pure(kref, kmask, a, keys, aux)?;
                    let tb = self.key_in_set_pure(kref, kmask, b, keys, aux)?;
                    bounded(format!("(PureTest.disj {ta} {tb})"))
                }
                (B::Cap, [a, b]) => {
                    let ta = self.key_in_set_pure(kref, kmask, a, keys, aux)?;
                    let tb = self.key_in_set_pure(kref, kmask, b, keys, aux)?;
                    bounded(format!("(PureTest.conj {ta} {tb})"))
                }
                (B::SetMinus, [a, b]) => {
                    let ta = self.key_in_set_pure(kref, kmask, a, keys, aux)?;
                    let tb = self.key_in_set_pure(kref, kmask, b, keys, aux)?;
                    bounded(format!("(PureTest.conj {ta} (PureTest.neg {tb}))"))
                }
                _ => None,
            },
            ExprKind::SetFilter { bound, pred } => {
                let BoundVars::Many(ids) = &bound.vars else { return None };
                let [id] = ids.as_slice() else { return None };
                let in_dom = self.key_in_set_pure(kref, kmask, &bound.set, keys, aux)?;
                let kexpr = self.key_ref_expr(kref, keys, set.span)?;
                let sub = subst_local(pred, *id, &kexpr);
                let pt = self.pure_test(&sub, keys, aux)?;
                bounded(format!("(PureTest.conj {in_dom} {pt})"))
            }
            _ => None,
        }
    }

    pub(super) fn pure_expr(&mut self, e: &Expr, keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> Option<String> {
        if self.contains_any_choose(e) {
            return None;
        }
        if let ExprKind::If { cond, then, els } = &*e.kind {
            return bounded(format!(
                "(PureExpr.branch {} {} {})",
                self.pure_test(cond, keys, aux)?,
                self.pure_expr(then, keys, aux)?,
                self.pure_expr(els, keys, aux)?
            ));
        }
        if let Some(leaf) = self.pure_leaf(e, keys, aux, "PureExpr") {
            return Some(leaf);
        }
        let (scope_locals, _) = self.choose_scope_env(keys, aux);
        if let ExprKind::Record(fs) = &*e.kind {
            for (idx, (fname, fval)) in fs.iter().enumerate() {
                if !matches!(&*fval.kind, ExprKind::Bool(_))
                    && is_pure_bool_domain(&self.eval_expr_domain(fval, &scope_locals))
                    && !self.can_mask_pure(fval, keys, aux)
                {
                    if let Some(pt) = self.pure_test(fval, keys, aux) {
                        let mut fs_t = fs.clone();
                        fs_t[idx] = (fname.clone(), Expr::new(ExprKind::Bool(true), fval.span));
                        let mut fs_f = fs.clone();
                        fs_f[idx] = (fname.clone(), Expr::new(ExprKind::Bool(false), fval.span));
                        let yes = self.pure_expr(&Expr::new(ExprKind::Record(fs_t), e.span), keys, aux)?;
                        let no = self.pure_expr(&Expr::new(ExprKind::Record(fs_f), e.span), keys, aux)?;
                        return bounded(format!("(PureExpr.branch {pt} {yes} {no})"));
                    }
                }
            }
        }
        if !matches!(&*e.kind, ExprKind::Bool(_)) && is_pure_bool_domain(&self.eval_expr_domain(e, &scope_locals)) {
            if let Some(pt) = self.pure_test(e, keys, aux) {
                let yes = self.pure_leaf(&Expr::new(ExprKind::Bool(true), e.span), keys, aux, "PureExpr")?;
                let no = self.pure_leaf(&Expr::new(ExprKind::Bool(false), e.span), keys, aux, "PureExpr")?;
                return bounded(format!("(PureExpr.branch {pt} {yes} {no})"));
            }
        }
        None
    }

    fn can_mask_pure(&mut self, e: &Expr, keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> bool {
        let Some(mut next) = max_local(e).max(self.next_local).checked_add(1) else {
            return false;
        };
        let mut reads = LeafReads::new();
        let mut cur_aux = aux.clone();
        self.mask(e, keys, &mut cur_aux, &mut next, &mut reads).is_some()
    }

    fn pure_leaf(&mut self, e: &Expr, keys: &[(LocalId, GroupMask)], aux: &AuxScope, kind: &str) -> Option<String> {
        let mut next = max_local(e).max(self.next_local).checked_add(1)?;
        let mut reads = LeafReads::new();
        let mut cur_aux = aux.clone();
        let masked = self.mask(e, keys, &mut cur_aux, &mut next, &mut reads)?;
        let id = self.atoms.len();
        self.atoms.push(format!("{kind} HIR: {masked:#?}\nPayload holes: {:?}", reads.holes));
        let spec = format!(
            "⟨{id}, [{}], [{}], [{}], [{}]⟩",
            reads.map_reads.join(", "),
            reads.slot_map_reads.join(", "),
            reads.slot_fixed_reads.join(", "),
            reads.flag_reads.join(", ")
        );
        let mut term = format!("({kind}.leaf {spec})");
        for (cmask, pred) in reads.counts.into_iter().rev() {
            term = bounded(format!("({kind}.bindCount {} {pred} {term})", self.mask_lean(cmask)))?;
        }
        Some(term)
    }

    fn mask(&mut self, e: &Expr, keys: &[(LocalId, GroupMask)], aux: &mut AuxScope, next: &mut u32, reads: &mut LeafReads) -> Option<Expr> {
        if let Some(trivial) = self.mask_special_hole(e, keys, aux, next, reads) {
            return Some(trivial);
        }
        match &*e.kind {
            ExprKind::Var(v) if self.is_non_core(*v) => return None,
            ExprKind::Local(id) if keys.iter().any(|(k, _)| k == id) || aux.msg_vars.iter().any(|mv| mv.local == *id) => {
                return None;
            }
            ExprKind::Const(_) if !independent(&self.eval_expr_domain(e, &Locals::new()), self.all_keys) => return None,
            ExprKind::Builtin { op: B::Prime, .. } if self.mentions_non_core(e) => return None,
            ExprKind::Quant { .. }
            | ExprKind::Choose { .. }
            | ExprKind::FnConstruct { .. }
            | ExprKind::SetFilter { .. }
            | ExprKind::SetMap { .. }
                if self.mentions_non_core(e) || self.mentions_keys(e, keys, aux) =>
            {
                return None;
            }
            _ => {}
        }
        let mut masked = e.clone();
        let mut valid = true;
        visit::children_mut(&mut masked, &mut |child| {
            if let Some(c) = self.mask(child, keys, aux, next, reads) {
                *child = c;
            } else {
                valid = false;
            }
        });
        valid.then_some(masked)
    }

    fn mask_special_hole(
        &mut self,
        e: &Expr,
        keys: &[(LocalId, GroupMask)],
        aux: &AuxScope,
        next: &mut u32,
        reads: &mut LeafReads,
    ) -> Option<Expr> {
        if let ExprKind::Builtin { op: B::In, args } = &*e.kind {
            if let [val, set] = args.as_slice() {
                if let Some(v) = variable(val, false).filter(|v| self.is_non_core(*v)) {
                    if self.domains.belongs(&self.domains.vars[v.idx()], set) {
                        return Some(Expr::new(ExprKind::Bool(true), e.span));
                    }
                }
            }
        }
        if let ExprKind::Builtin { op: B::SubsetEq, args } = &*e.kind {
            if let [val, set] = args.as_slice() {
                if let Some(v) = variable(val, false).filter(|v| self.is_non_core(*v)) {
                    if self.domains.subset_belongs(&self.domains.vars[v.idx()], set) {
                        return Some(Expr::new(ExprKind::Bool(true), e.span));
                    }
                }
            }
        }
        if let ExprKind::Builtin { op: B::Cardinality, args } = &*e.kind {
            if let [arg] = args.as_slice() {
                if let Some((cmask, pred)) = self.cardinality_target(arg, keys, aux) {
                    let hole = LocalId(*next);
                    *next = next.checked_add(1)?;
                    reads.counts.push((cmask, pred));
                    reads.holes.push(format!("aux.nats count hole {hole:?}"));
                    return Some(Expr::new(ExprKind::Local(hole), e.span));
                }
            }
        }
        if let ExprKind::Field { record, field } = &*e.kind {
            if let ExprKind::Local(lid) = &*record.kind {
                if let Some((idx, mv)) = aux.msg_vars.iter().enumerate().find(|(_, mv)| mv.local == *lid) {
                    if *field == mv.key_field || !mv.fields.contains(field) {
                        return None;
                    }
                    let hole = LocalId(*next);
                    *next = next.checked_add(1)?;
                    if mv.val_field.as_ref() == Some(field) {
                        reads.holes.push(format!("msg_var[{idx}].val -> {hole:?}"));
                    } else {
                        reads.holes.push(format!("msg_var[{idx}].meta.{field} -> {hole:?}"));
                    }
                    return Some(Expr::new(ExprKind::Local(hole), e.span));
                }
            }
        }
        if let ExprKind::Local(lid) = &*e.kind {
            if let Some(idx) = aux.proj_vals.iter().position(|x| x == lid) {
                reads.holes.push(format!("aux.vals[{idx}] -> {lid:?}"));
                return Some(e.clone());
            }
            if let Some(idx) = aux.count_nats.iter().position(|x| x == lid) {
                reads.holes.push(format!("aux.nats[{idx}] -> {lid:?}"));
                return Some(e.clone());
            }
            if let Some(idx) = aux.fold_ints.iter().position(|x| x == lid) {
                reads.holes.push(format!("aux.ints[{idx}] -> {lid:?}"));
                return Some(e.clone());
            }
        }
        if let ExprKind::FnApp { func, args } = &*e.kind {
            if let Some((mask, map_id)) = self.fixed_map_target(func) {
                let [arg] = args.as_slice() else { return None };
                let (kref, kmask, _) = self.key_ref(arg, keys, aux)?;
                if (kmask & !mask) != 0 {
                    return None;
                }
                let hole = LocalId(*next);
                *next = next.checked_add(1)?;
                match kref {
                    KeyRef::Bound(idx) => reads.map_reads.push(format!("(⟨{map_id}, by decide⟩, {idx})")),
                    KeyRef::Slot(s) => reads.slot_map_reads.push(format!("(⟨{map_id}, by decide⟩, ⟨{s}, by decide⟩)")),
                    KeyRef::Fixed(_) => return None,
                }
                reads.holes.push(format!("map[{map_id}] -> {hole:?}"));
                return Some(Expr::new(ExprKind::Local(hole), e.span));
            }
            if let Some((mask, flag_id)) = self.bool_map_flag_target(func) {
                let [arg] = args.as_slice() else { return None };
                let (kref, kmask, _) = self.key_ref(arg, keys, aux)?;
                if (kmask & !mask) != 0 {
                    return None;
                }
                let hole = LocalId(*next);
                *next = next.checked_add(1)?;
                reads.flag_reads.push(format!("(⟨{flag_id}, by decide⟩, {})", kref.lean()));
                reads.holes.push(format!("flag[{flag_id}] -> {hole:?}"));
                return Some(Expr::new(ExprKind::Local(hole), e.span));
            }
        }
        None
    }

    fn cardinality_target(&mut self, set: &Expr, keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> Option<(GroupMask, String)> {
        if let Some(v) = variable(set, false) {
            if let VarShape::KeySetFlag { mask, flag_id } = self.shapes[v.idx()] {
                return Some((mask, format!("(PureTest.flag ⟨{flag_id}, by decide⟩ (KeyRef.bound 0))")));
            }
        }
        if let ExprKind::SetFilter { bound, pred } = &*set.kind {
            let BoundVars::Many(ids) = &bound.vars else { return None };
            let [id] = ids.as_slice() else { return None };
            if let Some(exact) = self.domains.exact_set(&bound.set) {
                let (mask, fixed) = group_mask_exact(self.groups, &exact)?;
                if mask != 0 && fixed.is_empty() {
                    let mut scope = keys.to_vec();
                    scope.insert(0, (*id, mask));
                    let p = self.pure_test(pred, &scope, aux)?;
                    return Some((mask, p));
                }
            }
        }
        None
    }

    pub(super) fn key_ref(&self, e: &Expr, keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> Option<(KeyRef, GroupMask, bool)> {
        match &*e.kind {
            ExprKind::Local(id) => {
                if aux.msg_vars.iter().any(|mv| mv.local == *id) {
                    return None;
                }
                let (pos, (_, mask)) = keys.iter().enumerate().find(|(_, (k, _))| k == id)?;
                Some((KeyRef::Bound(pos), *mask, false))
            }
            ExprKind::Var(v) => {
                if let VarShape::ScalarSlot { mask, has_fixed, slot_id } = self.shapes[v.idx()] {
                    Some((KeyRef::Slot(slot_id), mask, has_fixed))
                } else {
                    None
                }
            }
            ExprKind::Field { record, field } => {
                if let ExprKind::Local(lid) = &*record.kind {
                    if let Some(mv) = aux.msg_vars.iter().find(|mv| mv.local == *lid) {
                        if *field == mv.key_field {
                            let (pos, (_, mask)) = keys.iter().enumerate().find(|(_, (k, _))| k == lid)?;
                            return Some((KeyRef::Bound(pos), *mask, false));
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    pub(super) fn key_or_fixed_ref(&mut self, e: &Expr, keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> Option<(KeyRef, GroupMask)> {
        if let Some((kref, mask, _)) = self.key_ref(e, keys, aux) {
            return Some((kref, mask));
        }
        if let Some(atom) = self.domains.atom_value(e) {
            if !self.all_keys.contains(&atom) {
                let desc = format!("{atom:?}");
                let id = self.fixed_atoms.iter().position(|x| x == &desc).unwrap_or_else(|| {
                    let i = self.fixed_atoms.len();
                    self.fixed_atoms.push(desc);
                    i
                });
                return Some((KeyRef::Fixed(id), 0));
            }
        }
        None
    }

    fn fixed_map_target(&self, e: &Expr) -> Option<(GroupMask, usize)> {
        let ExprKind::Var(v) = &*e.kind else { return None };
        match self.shapes[v.idx()] {
            VarShape::FixedMap { mask, map_id } => Some((mask, map_id)),
            _ => None,
        }
    }

    pub(super) fn bool_map_flag_target(&self, e: &Expr) -> Option<(GroupMask, usize)> {
        let ExprKind::Var(v) = &*e.kind else { return None };
        match self.shapes[v.idx()] {
            VarShape::BoolMapFlag { mask, flag_id } => Some((mask, flag_id)),
            _ => None,
        }
    }

    pub(super) fn mentions_non_core(&self, e: &Expr) -> bool {
        if matches!(&*e.kind, ExprKind::Var(v) if self.is_non_core(*v)) {
            return true;
        }
        let mut found = false;
        visit::children(e, &mut |c| found |= self.mentions_non_core(c));
        found
    }

    pub(super) fn mentions_keys(&self, e: &Expr, keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> bool {
        if matches!(&*e.kind, ExprKind::Local(id) if keys.iter().any(|(k, _)| k == id) || aux.msg_vars.iter().any(|mv| mv.local == *id)) {
            return true;
        }
        let mut found = false;
        visit::children(e, &mut |c| found |= self.mentions_keys(c, keys, aux));
        found
    }

    pub(super) fn action_pure_tests(&mut self, es: &[Expr], keys: &[(LocalId, GroupMask)]) -> Option<String> {
        let mut out = "(ActionPureTest.truth true)".to_owned();
        for e in es {
            let t = self.action_pure_test(e, keys, false)?;
            out = if out == "(ActionPureTest.truth true)" { t } else { bounded(format!("(ActionPureTest.conj {out} {t})"))? };
        }
        Some(out)
    }

    fn action_pure_test(&mut self, e: &Expr, keys: &[(LocalId, GroupMask)], in_prime: bool) -> Option<String> {
        if self.contains_any_choose(e) {
            return None;
        }
        match &*e.kind {
            ExprKind::Bool(b) => return Some(format!("(ActionPureTest.truth {b})")),
            ExprKind::And(es) => {
                let mut out = "(ActionPureTest.truth true)".to_owned();
                for item in es {
                    let t = self.action_pure_test(item, keys, in_prime)?;
                    out = if out == "(ActionPureTest.truth true)" { t } else { bounded(format!("(ActionPureTest.conj {out} {t})"))? };
                }
                return Some(out);
            }
            ExprKind::Or(es) if !es.is_empty() => {
                let mut it = es.iter();
                let mut out = self.action_pure_test(it.next()?, keys, in_prime)?;
                for item in it {
                    out = bounded(format!("(ActionPureTest.disj {out} {})", self.action_pure_test(item, keys, in_prime)?))?;
                }
                return Some(out);
            }
            ExprKind::BoxAction { action, sub } if !in_prime => {
                let a = self.action_pure_test(action, keys, false)?;
                let u = self.action_pure_unchanged(sub, keys)?;
                return bounded(format!("(ActionPureTest.disj {a} {u})"));
            }
            ExprKind::AngleAction { action, sub } if !in_prime => {
                let a = self.action_pure_test(action, keys, false)?;
                let u = self.action_pure_unchanged(sub, keys)?;
                return bounded(format!("(ActionPureTest.conj {a} (ActionPureTest.neg {u}))"));
            }
            ExprKind::If { cond, then, els } => {
                let c = self.action_pure_test(cond, keys, in_prime)?;
                let t = self.action_pure_test(then, keys, in_prime)?;
                let el = self.action_pure_test(els, keys, in_prime)?;
                return bounded(format!(
                    "(ActionPureTest.disj (ActionPureTest.conj {c} {t}) (ActionPureTest.conj (ActionPureTest.neg {c}) {el}))"
                ));
            }
            ExprKind::Builtin { op, args } => match (op, args.as_slice()) {
                (B::Prime, [inner]) if !in_prime => return self.action_pure_test(inner, keys, true),
                (B::Unchanged, [sub]) if !in_prime => return self.action_pure_unchanged(sub, keys),
                (B::Not, [a]) => return bounded(format!("(ActionPureTest.neg {})", self.action_pure_test(a, keys, in_prime)?)),
                (B::Implies, [a, b]) => {
                    return bounded(format!(
                        "(ActionPureTest.disj (ActionPureTest.neg {}) {})",
                        self.action_pure_test(a, keys, in_prime)?,
                        self.action_pure_test(b, keys, in_prime)?
                    ));
                }
                (B::Equiv, [a, b]) => {
                    let ta = self.action_pure_test(a, keys, in_prime)?;
                    let tb = self.action_pure_test(b, keys, in_prime)?;
                    return bounded(format!(
                        "(ActionPureTest.disj (ActionPureTest.conj {ta} {tb}) (ActionPureTest.conj (ActionPureTest.neg {ta}) (ActionPureTest.neg {tb})))"
                    ));
                }
                (B::Eq | B::Neq, [a, b]) => {
                    if let (Some((ra, ma)), Some((rb, mb))) =
                        (self.action_key_ref(a, keys, in_prime), self.action_key_ref(b, keys, in_prime))
                    {
                        if (ma | mb) != 0 {
                            let eq = format!("(ActionPureTest.equal {} {})", ra.lean(), rb.lean());
                            return Some(if *op == B::Eq { eq } else { format!("(ActionPureTest.neg {eq})") });
                        }
                    }
                }
                (B::In | B::NotIn, [elem, set]) => {
                    if let Some((kref, kmask)) = self.action_key_ref(elem, keys, in_prime) {
                        if let Some(exact) = self.domains.exact_set(set) {
                            if let Some((mask, fixed)) = group_mask_exact(self.groups, &exact) {
                                if mask != 0 && fixed.is_empty() {
                                    let mem = format!("(ActionPureTest.inGroup {} {})", kref.lean(), self.mask_lean(mask));
                                    return Some(if *op == B::In { mem } else { format!("(ActionPureTest.neg {mem})") });
                                }
                            }
                        }
                        let (set_inner, set_prime) = match &*set.kind {
                            ExprKind::Builtin { op: B::Prime, args: pa } if !in_prime && pa.len() == 1 => (&pa[0], true),
                            _ => (set, in_prime),
                        };
                        if let Some(v) = variable(set_inner, false) {
                            if let VarShape::KeySetFlag { mask, flag_id } = self.shapes[v.idx()] {
                                if (kmask & !mask) == 0 {
                                    let mem = format!("(ActionPureTest.flag {set_prime} ⟨{flag_id}, by decide⟩ {})", kref.lean());
                                    return Some(if *op == B::In { mem } else { format!("(ActionPureTest.neg {mem})") });
                                }
                            }
                        }
                    }
                }
                _ => {}
            },
            ExprKind::FnApp { func, args } => {
                let (func_inner, func_prime) = match &*func.kind {
                    ExprKind::Builtin { op: B::Prime, args: pa } if !in_prime && pa.len() == 1 => (&pa[0], true),
                    _ => (func, in_prime),
                };
                if let Some((mask, flag_id)) = self.bool_map_flag_target(func_inner) {
                    let [arg] = args.as_slice() else { return None };
                    let (kref, kmask) = self.action_key_ref(arg, keys, in_prime)?;
                    if (kmask & !mask) != 0 {
                        return None;
                    }
                    return Some(format!("(ActionPureTest.flag {func_prime} ⟨{flag_id}, by decide⟩ {})", kref.lean()));
                }
            }
            ExprKind::Quant { kind, bounds, body } => {
                if let Some(q) = self.action_quant_pure_test(*kind, bounds, body, keys, in_prime) {
                    return Some(q);
                }
            }
            _ => {}
        }
        self.action_pure_leaf(e, keys, in_prime)
    }

    fn action_pure_unchanged(&mut self, sub: &Expr, keys: &[(LocalId, GroupMask)]) -> Option<String> {
        match &*sub.kind {
            ExprKind::Tuple(es) => {
                let mut out = "(ActionPureTest.truth true)".to_owned();
                for item in es {
                    let t = self.action_pure_unchanged(item, keys)?;
                    out = if out == "(ActionPureTest.truth true)" { t } else { bounded(format!("(ActionPureTest.conj {out} {t})"))? };
                }
                Some(out)
            }
            ExprKind::Var(v) => match self.shapes[v.idx()].clone() {
                VarShape::Core => {
                    let id = self.atoms.len();
                    self.atoms.push(format!("ActionPureTest UNCHANGED core var {v:?}"));
                    Some(format!("(ActionPureTest.leaf ⟨{id}, [], [], [], []⟩)"))
                }
                VarShape::ScalarSlot { slot_id, .. } => Some(format!(
                    "(ActionPureTest.equal (KeyRef2.slot true ⟨{slot_id}, by decide⟩) (KeyRef2.slot false ⟨{slot_id}, by decide⟩))"
                )),
                VarShape::FixedMap { mask, map_id } => {
                    let id = self.atoms.len();
                    self.atoms.push(format!("ActionPureTest UNCHANGED map {map_id} var {v:?}"));
                    let m = self.mask_lean(mask);
                    Some(format!(
                        "(ActionPureTest.all {m} (ActionPureTest.leaf ⟨{id}, [(true, ⟨{map_id}, by decide⟩, 0), (false, ⟨{map_id}, by decide⟩, 0)], [], [], []⟩))"
                    ))
                }
                VarShape::KeySetFlag { mask, flag_id } | VarShape::BoolMapFlag { mask, flag_id } => {
                    let m = self.mask_lean(mask);
                    let t = format!("(ActionPureTest.flag true ⟨{flag_id}, by decide⟩ (KeyRef2.bound 0))");
                    let f = format!("(ActionPureTest.flag false ⟨{flag_id}, by decide⟩ (KeyRef2.bound 0))");
                    Some(format!(
                        "(ActionPureTest.all {m} (ActionPureTest.disj (ActionPureTest.conj {t} {f}) (ActionPureTest.conj (ActionPureTest.neg {t}) (ActionPureTest.neg {f}))))"
                    ))
                }
                VarShape::MsgSet { mask, msg_id, .. } => {
                    let m = self.mask_lean(mask);
                    Some(format!("(ActionPureTest.all {m} (ActionPureTest.msgEq ⟨{msg_id}, by decide⟩ (KeyRef2.bound 0)))"))
                }
            },
            _ => {
                let primed = Expr::new(ExprKind::Builtin { op: B::Prime, args: vec![sub.clone()] }, sub.span);
                let eq = Expr::new(ExprKind::Builtin { op: B::Eq, args: vec![primed, sub.clone()] }, sub.span);
                self.action_pure_test(&eq, keys, false)
            }
        }
    }

    fn action_key_ref(&mut self, e: &Expr, keys: &[(LocalId, GroupMask)], in_prime: bool) -> Option<(super::ActionKeyRef, GroupMask)> {
        let (inner, primed) = match &*e.kind {
            ExprKind::Builtin { op: B::Prime, args } => {
                if in_prime || args.len() != 1 {
                    return None;
                }
                (&args[0], true)
            }
            _ => (e, in_prime),
        };
        let (kref, mask) = self.key_or_fixed_ref(inner, keys, &AuxScope::default())?;
        Some((super::ActionKeyRef::from_state(kref, primed), mask))
    }

    fn action_quant_pure_test(
        &mut self,
        kind: QuantKind,
        bounds: &[Bound],
        body: &Expr,
        keys: &[(LocalId, GroupMask)],
        in_prime: bool,
    ) -> Option<String> {
        if bounds.is_empty() {
            return self.action_pure_test(body, keys, in_prime);
        }
        let bnd = &bounds[0];
        let BoundVars::Many(ids) = &bnd.vars else { return None };
        let rest = &bounds[1..];
        let quant = match kind {
            QuantKind::Forall => "all",
            QuantKind::Exists => "some",
        };
        if let Some(exact) = self.domains.exact_set(&bnd.set) {
            if let Some((mask, fixed)) = group_mask_exact(self.groups, &exact) {
                if mask != 0 && fixed.is_empty() {
                    let mut scope = keys.to_vec();
                    for &id in ids {
                        scope.insert(0, (id, mask));
                    }
                    let mut out = if rest.is_empty() {
                        self.action_pure_test(body, &scope, in_prime)?
                    } else {
                        self.action_quant_pure_test(kind, rest, body, &scope, in_prime)?
                    };
                    let m = self.mask_lean(mask);
                    for _ in ids {
                        out = format!("(ActionPureTest.{quant} {m} {out})");
                    }
                    return Some(out);
                }
            }
        }
        None
    }

    fn action_pure_leaf(&mut self, e: &Expr, keys: &[(LocalId, GroupMask)], in_prime: bool) -> Option<String> {
        let mut next = max_local(e).max(self.next_local).checked_add(1)?;
        let mut map_reads = Vec::new();
        let mut slot_map_reads = Vec::new();
        let mut flag_reads = Vec::new();
        let mut holes = Vec::new();
        let masked = self.action_mask(e, keys, in_prime, &mut next, &mut map_reads, &mut slot_map_reads, &mut flag_reads, &mut holes)?;
        let id = self.atoms.len();
        self.atoms.push(format!("ActionPureTest HIR: {masked:#?}\nPayload holes: {holes:?}"));
        Some(format!(
            "(ActionPureTest.leaf ⟨{id}, [{}], [{}], [], [{}]⟩)",
            map_reads.join(", "),
            slot_map_reads.join(", "),
            flag_reads.join(", ")
        ))
    }

    #[allow(clippy::too_many_arguments)] // recursive two-state HIR masker threading fresh hole counter and map/slot/flag read accumulators
    fn action_mask(
        &mut self,
        e: &Expr,
        keys: &[(LocalId, GroupMask)],
        in_prime: bool,
        next: &mut u32,
        map_reads: &mut Vec<String>,
        slot_map_reads: &mut Vec<String>,
        flag_reads: &mut Vec<String>,
        holes: &mut Vec<String>,
    ) -> Option<Expr> {
        if let ExprKind::Builtin { op: B::Prime, args } = &*e.kind {
            if !in_prime && args.len() == 1 {
                let inner = self.action_mask(&args[0], keys, true, next, map_reads, slot_map_reads, flag_reads, holes)?;
                return Some(Expr::new(ExprKind::Builtin { op: B::Prime, args: vec![inner] }, e.span));
            }
            return None;
        }
        if let ExprKind::FnApp { func, args } = &*e.kind {
            let (func_inner, func_prime) = match &*func.kind {
                ExprKind::Builtin { op: B::Prime, args: pa } if !in_prime && pa.len() == 1 => (&pa[0], true),
                _ => (func, in_prime),
            };
            if let Some((mask, map_id)) = self.fixed_map_target(func_inner) {
                let [arg] = args.as_slice() else { return None };
                let (kref, kmask) = self.action_key_ref(arg, keys, in_prime)?;
                if (kmask & !mask) != 0 {
                    return None;
                }
                let hole = LocalId(*next);
                *next = next.checked_add(1)?;
                match kref {
                    super::ActionKeyRef::Bound(idx) => {
                        map_reads.push(format!("({func_prime}, ⟨{map_id}, by decide⟩, {idx})"));
                    }
                    super::ActionKeyRef::Slot { primed, slot_id } => {
                        slot_map_reads.push(format!("({func_prime}, ⟨{map_id}, by decide⟩, {primed}, ⟨{slot_id}, by decide⟩)"));
                    }
                    super::ActionKeyRef::Fixed(_) => return None,
                }
                holes.push(format!("map[{map_id}] -> {hole:?}"));
                return Some(Expr::new(ExprKind::Local(hole), e.span));
            }
            if let Some((mask, flag_id)) = self.bool_map_flag_target(func_inner) {
                let [arg] = args.as_slice() else { return None };
                let (kref, kmask) = self.action_key_ref(arg, keys, in_prime)?;
                if (kmask & !mask) != 0 {
                    return None;
                }
                let hole = LocalId(*next);
                *next = next.checked_add(1)?;
                flag_reads.push(format!("({func_prime}, ⟨{flag_id}, by decide⟩, {})", kref.lean()));
                holes.push(format!("flag[{flag_id}] -> {hole:?}"));
                return Some(Expr::new(ExprKind::Local(hole), e.span));
            }
        }
        let empty_aux = AuxScope::default();
        match &*e.kind {
            ExprKind::Var(v) if self.is_non_core(*v) => return None,
            ExprKind::Local(id) if keys.iter().any(|(k, _)| k == id) => return None,
            ExprKind::Const(_) if !independent(&self.eval_expr_domain(e, &Locals::new()), self.all_keys) => return None,
            ExprKind::BoxAction { .. } | ExprKind::AngleAction { .. } => return None,
            ExprKind::Builtin { op: B::Unchanged, .. } => return None,
            ExprKind::Quant { .. }
            | ExprKind::Choose { .. }
            | ExprKind::FnConstruct { .. }
            | ExprKind::SetFilter { .. }
            | ExprKind::SetMap { .. }
                if self.mentions_non_core(e) || self.mentions_keys(e, keys, &empty_aux) =>
            {
                return None;
            }
            _ => {}
        }
        let mut masked = e.clone();
        let mut valid = true;
        visit::children_mut(&mut masked, &mut |child| {
            if let Some(c) = self.action_mask(child, keys, in_prime, next, map_reads, slot_map_reads, flag_reads, holes) {
                *child = c;
            } else {
                valid = false;
            }
        });
        valid.then_some(masked)
    }
}

pub(super) fn bounded(term: String) -> Option<String> {
    (term.len() <= 1_000_000).then_some(term)
}
