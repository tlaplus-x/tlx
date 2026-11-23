//! Explicit equality/quantifier/membership/cardinality IR and payload-only semantic leaves.
use super::super::{max_local, variable};
use super::{group_mask_exact, independent, subst_local, Emitter, FieldShape, GroupMask, KeyRef, Locals, VarShape};
use crate::{builtins::Builtin as B, hir::*, visit};
use std::sync::Arc;

struct LeafReads {
    map_reads: Vec<String>,
    slot_map_reads: Vec<String>,
    slot_fixed_reads: Vec<String>,
    counts: Vec<(GroupMask, String)>,
    holes: Vec<LocalId>,
}

impl LeafReads {
    fn new() -> Self {
        Self { map_reads: vec![], slot_map_reads: vec![], slot_fixed_reads: vec![], counts: vec![], holes: vec![] }
    }
}

impl Emitter<'_> {
    pub(super) fn tests(&mut self, es: &[Expr], keys: &[(LocalId, GroupMask)]) -> Option<String> {
        let mut out = "(Test.truth true)".to_owned();
        for e in es {
            out = bounded(format!("(Test.conj {out} {})", self.test(e, keys)?))?;
        }
        Some(out)
    }

    pub(super) fn test(&mut self, e: &Expr, keys: &[(LocalId, GroupMask)]) -> Option<String> {
        let result = self.test_inner(e, keys)?;
        bounded(result)
    }

    fn test_inner(&mut self, e: &Expr, keys: &[(LocalId, GroupMask)]) -> Option<String> {
        match &*e.kind {
            ExprKind::And(es) => return self.tests(es, keys),
            ExprKind::Or(es) if !es.is_empty() => {
                let mut terms = es.iter().map(|e| self.test(e, keys));
                let mut out = terms.next()??;
                for t in terms {
                    out = bounded(format!("(Test.disj {out} {})", t?))?;
                }
                return Some(out);
            }
            ExprKind::Builtin { op, args } => match (op, args.as_slice()) {
                (B::Not, [a]) => return Some(format!("(Test.neg {})", self.test(a, keys)?)),
                (B::Implies, [a, b]) => return Some(format!("(Test.disj (Test.neg {}) {})", self.test(a, keys)?, self.test(b, keys)?)),
                (B::Equiv, [a, b]) => {
                    let ta = self.test(a, keys)?;
                    let tb = self.test(b, keys)?;
                    return Some(format!("(Test.disj (Test.conj {ta} {tb}) (Test.conj (Test.neg {ta}) (Test.neg {tb})))"));
                }
                (B::Eq | B::Neq, [a, b]) => {
                    if let Some(eq) = self.special_eq(a, b, keys) {
                        return Some(if *op == B::Eq { eq } else { format!("(Test.neg {eq})") });
                    }
                }
                (B::In | B::NotIn, [elem, set]) => {
                    if let Some(mem) = self.special_membership(elem, set, keys) {
                        return Some(if *op == B::In { mem } else { format!("(Test.neg {mem})") });
                    }
                }
                (B::SubsetEq, [a, b]) => {
                    if let Some(sub) = self.special_subseteq(a, b, keys) {
                        return Some(sub);
                    }
                }
                _ => {}
            },
            ExprKind::Quant { kind, bounds, body } => {
                if let Some(q) = self.quant_test(*kind, bounds, body, keys) {
                    return Some(q);
                }
            }
            ExprKind::If { cond, then, els } => {
                let condition = self.test(cond, keys)?;
                return Some(format!(
                    "(Test.disj (Test.conj {condition} {}) (Test.conj (Test.neg {condition}) {}))",
                    self.test(then, keys)?,
                    self.test(els, keys)?
                ));
            }
            _ => {}
        }
        self.leaf(e, keys, "Test")
    }

    fn quant_test(&mut self, kind: QuantKind, bounds: &[Bound], body: &Expr, keys: &[(LocalId, GroupMask)]) -> Option<String> {
        if bounds.is_empty() {
            return self.test(body, keys);
        }
        let bnd = &bounds[0];
        let BoundVars::Many(ids) = &bnd.vars else { return None };
        let rest_bounds = &bounds[1..];
        let quant = match kind {
            QuantKind::Forall => "all",
            QuantKind::Exists => "some",
        };
        // Case 1: exact set of keys (and optionally small fixed atoms, e.g. `RM \cup {0, 10}`).
        if let Some(exact) = self.domains.exact_set(&bnd.set) {
            if let Some((mask, fixed)) = group_mask_exact(self.groups, &exact) {
                if mask != 0 {
                    if fixed.is_empty() {
                        let mut scope = keys.to_vec();
                        for &id in ids {
                            scope.insert(0, (id, mask));
                        }
                        let mut out = if rest_bounds.is_empty() {
                            self.test(body, &scope)?
                        } else {
                            self.quant_test(kind, rest_bounds, body, &scope)?
                        };
                        let m = self.mask_lean(mask);
                        for _ in ids {
                            out = format!("(Test.{quant} {m} {out})");
                        }
                        return Some(out);
                    } else if fixed.len() <= 8 && ids.len() == 1 {
                        let id = ids[0];
                        let mut scope = keys.to_vec();
                        scope.insert(0, (id, mask));
                        let kpart = if rest_bounds.is_empty() {
                            self.test(body, &scope)?
                        } else {
                            self.quant_test(kind, rest_bounds, body, &scope)?
                        };
                        let mut acc = format!("(Test.{quant} {} {kpart})", self.mask_lean(mask));
                        let comb = match kind {
                            QuantKind::Forall => "conj",
                            QuantKind::Exists => "disj",
                        };
                        for atom in &fixed {
                            let aexpr = self.domains.atom_expr(atom, bnd.set.span)?;
                            let sub_body = subst_local(body, id, &aexpr);
                            let fpart = if rest_bounds.is_empty() {
                                self.test(&sub_body, keys)?
                            } else {
                                self.quant_test(kind, rest_bounds, &sub_body, keys)?
                            };
                            acc = bounded(format!("(Test.{comb} {acc} {fpart})"))?;
                        }
                        return Some(acc);
                    }
                }
            }
        }
        // Case 2: quantifying over a pure `KeySet` variable (`\A p \in tmPrepared : ...`).
        if let Some(v) = variable(&bnd.set, false) {
            if let VarShape::KeySet { mask, has_fixed: false, .. } = self.shapes[v.idx()] {
                let mut scope = keys.to_vec();
                for &id in ids {
                    scope.insert(0, (id, mask));
                }
                let inner_body =
                    if rest_bounds.is_empty() { self.test(body, &scope)? } else { self.quant_test(kind, rest_bounds, body, &scope)? };
                let mut guard_in = "(Test.truth true)".to_owned();
                for (offset, _) in ids.iter().enumerate() {
                    let pos = ids.len() - 1 - offset;
                    let mem = self.key_in_set_expr(KeyRef::Bound(pos), mask, &bnd.set, &scope)?;
                    guard_in = format!("(Test.conj {guard_in} {mem})");
                }
                let mut out = match kind {
                    QuantKind::Forall => format!("(Test.disj (Test.neg {guard_in}) {inner_body})"),
                    QuantKind::Exists => format!("(Test.conj {guard_in} {inner_body})"),
                };
                let m = self.mask_lean(mask);
                for _ in ids {
                    out = format!("(Test.{quant} {m} {out})");
                }
                return Some(out);
            }
        }
        None
    }

    fn special_eq(&mut self, a: &Expr, b: &Expr, keys: &[(LocalId, GroupMask)]) -> Option<String> {
        // 1. Key / Slot / Fixed equality (`p = q`, `owner = p`, `owner = "none"`, `sent = rcvd`).
        if let (Some(ka), Some(kb)) = (self.key_or_fixed_ref(a, keys), self.key_or_fixed_ref(b, keys)) {
            if !matches!((ka, kb), (KeyRef::Fixed(_), KeyRef::Fixed(_))) {
                return Some(format!("(Test.equal {} {})", ka.lean(), kb.lean()));
            }
        }
        // 2. Whole fixed-map equality: `m = [k \in K |-> e]` or `m1 = m2`.
        if let Some(eq) = self.map_equality(a, b, keys).or_else(|| self.map_equality(b, a, keys)) {
            return Some(eq);
        }
        // 3. KeySet equality: `S = RM`, `S = H \cup I`, `S = {}`, `S1 = S2`.
        if let Some(eq) = self.keyset_equality(a, b, keys).or_else(|| self.keyset_equality(b, a, keys)) {
            return Some(eq);
        }
        None
    }

    fn map_equality(&mut self, a: &Expr, b: &Expr, keys: &[(LocalId, GroupMask)]) -> Option<String> {
        let (mask_a, _) = self.fixed_map_target(a)?;
        // Case 2a: `m = [k \in K |-> body]`
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
                    let inner = self.test(&eq_expr, &scope)?;
                    return Some(format!("(Test.all {} {inner})", self.mask_lean(mask_a)));
                }
            }
        }
        // Case 2b: `m1 = m2` (both fixed maps over the same mask)
        if let Some((mask_b, _)) = self.fixed_map_target(b) {
            if mask_a == mask_b {
                let fresh = self.alloc_local();
                let mut scope = keys.to_vec();
                scope.insert(0, (fresh, mask_a));
                let k = Expr::new(ExprKind::Local(fresh), a.span);
                let la = Expr::new(ExprKind::FnApp { func: a.clone(), args: vec![k.clone()] }, a.span);
                let lb = Expr::new(ExprKind::FnApp { func: b.clone(), args: vec![k] }, b.span);
                let eq_expr = Expr::new(ExprKind::Builtin { op: B::Eq, args: vec![la, lb] }, a.span);
                let inner = self.test(&eq_expr, &scope)?;
                return Some(format!("(Test.all {} {inner})", self.mask_lean(mask_a)));
            }
        }
        None
    }

    fn keyset_equality(&mut self, a: &Expr, b: &Expr, keys: &[(LocalId, GroupMask)]) -> Option<String> {
        let var_a = variable(a, false)?;
        let VarShape::KeySet { mask: mask_a, has_fixed: fixed_a, .. } = self.shapes[var_a.idx()] else {
            return None;
        };
        let mut union_mask = mask_a;
        let mut fixed_part: Option<String> = None;
        if let Some(exact_b) = self.domains.exact_set(b) {
            let (mask_b, fixed_b) = group_mask_exact(self.groups, &exact_b)?;
            union_mask |= mask_b;
            if fixed_a {
                fixed_part = Some(self.core_leaf_from_desc(format!("KeySet fixed-part eq {fixed_b:?}: var {}", var_a.idx())));
            } else if !fixed_b.is_empty() {
                return Some("(Test.truth false)".into());
            }
        } else if let Some(var_b) = variable(b, false) {
            let VarShape::KeySet { mask: mask_b, has_fixed: fixed_b, .. } = self.shapes[var_b.idx()] else {
                return None;
            };
            union_mask |= mask_b;
            if fixed_a || fixed_b {
                fixed_part = Some(self.core_leaf_from_desc(format!("KeySet fixed-part eq: var {} vs var {}", var_a.idx(), var_b.idx())));
            }
        } else {
            return None;
        }
        let fresh = self.alloc_local();
        let mut scope = keys.to_vec();
        scope.insert(0, (fresh, union_mask));
        let in_a = self.key_in_set_expr(KeyRef::Bound(0), union_mask, a, &scope)?;
        let in_b = self.key_in_set_expr(KeyRef::Bound(0), union_mask, b, &scope)?;
        let iff = format!("(Test.disj (Test.conj {in_a} {in_b}) (Test.conj (Test.neg {in_a}) (Test.neg {in_b})))");
        let all = format!("(Test.all {} {iff})", self.mask_lean(union_mask));
        Some(match fixed_part {
            Some(fp) => format!("(Test.conj {fp} {all})"),
            None => all,
        })
    }

    fn special_membership(&mut self, elem: &Expr, set: &Expr, keys: &[(LocalId, GroupMask)]) -> Option<String> {
        // 1. Proved type membership for any variable: `v \in TypeSet`!
        if let Some(v) = variable(elem, false).filter(|v| self.is_non_core(*v)) {
            if self.domains.belongs(&self.domains.vars[v.idx()], set) {
                return Some("(Test.truth true)".into());
            }
        }
        // 2. Membership of a key/slot in an exact key set (`k \in K`, `owner \in Proc`).
        if let Some((kref, _kmask, _)) = self.key_ref(elem, keys) {
            if let Some(exact) = self.domains.exact_set(set) {
                if let Some((mask, fixed)) = group_mask_exact(self.groups, &exact) {
                    if mask != 0 && fixed.is_empty() {
                        return Some(format!("(Test.inGroup {} {})", kref.lean(), self.mask_lean(mask)));
                    }
                }
            }
        }
        // 3. Membership of a key/slot/fixed in a `KeySet` variable (`rm \in tmPrepared`).
        if let Some(v) = variable(set, false) {
            match self.shapes[v.idx()].clone() {
                VarShape::KeySet { mask, has_fixed, .. } => {
                    if let Some((kref, kmask, false)) = self.key_ref(elem, keys) {
                        return self.key_in_set_expr(kref, kmask, set, keys);
                    }
                    if let Some((KeyRef::Slot(slot_id), kmask, true)) = self.key_ref(elem, keys) {
                        let key_branch = self.key_in_set_expr(KeyRef::Slot(slot_id), kmask, set, keys)?;
                        if has_fixed {
                            let fixed_branch = self.slot_fixed_in_keyset_test(v, slot_id);
                            return Some(format!("(Test.disj {key_branch} {fixed_branch})"));
                        }
                        return Some(key_branch);
                    }
                    if independent(&self.domains.value(elem, &Locals::new()), self.all_keys) {
                        if has_fixed {
                            let leaf = self.leaf(elem, keys, "Test")?;
                            let id = self.atoms.len() - 1;
                            self.atoms[id].push_str(&format!("\nKeySet fixed-part membership in var {}", v.idx()));
                            return Some(leaf);
                        }
                        let _ = mask;
                        return Some("(Test.truth false)".into());
                    }
                }
                VarShape::RecordSet { keyed, has_free: _ } => {
                    let ExprKind::Record(fs) = &*elem.kind else { return None };
                    let mut field_names: Vec<Arc<str>> = fs.iter().map(|(k, _)| k.clone()).collect();
                    field_names.sort();
                    if let Some(sh) = keyed.iter().find(|sh| sh.fields == field_names) {
                        let (_, kexpr) = fs.iter().find(|(k, _)| *k == sh.key_field)?;
                        let (kref, _kmask, _has_fixed) = self.key_ref(kexpr, keys)?;
                        let rest: Vec<(Arc<str>, Expr)> = fs.iter().filter(|(k, _)| *k != sh.key_field).cloned().collect();
                        let rest_rec = Expr::new(ExprKind::Record(rest), elem.span);
                        let check = self.record_set_mem_test(sh.map_id, kref, &rest_rec, keys)?;
                        return Some(format!("(Test.conj (Test.inGroup {} {}) {check})", kref.lean(), self.mask_lean(sh.mask)));
                    }
                    // Key-free record tested against `msgs`: only depends on `msgs_free` in C!
                    let leaf = self.leaf(elem, keys, "Test")?;
                    let id = self.atoms.len() - 1;
                    self.atoms[id].push_str(&format!("\nRecordSet free-part membership in var {}", v.idx()));
                    return Some(leaf);
                }
                _ => {}
            }
        }
        None
    }

    fn special_subseteq(&mut self, a: &Expr, b: &Expr, keys: &[(LocalId, GroupMask)]) -> Option<String> {
        if let Some(v) = variable(a, false).filter(|v| self.is_non_core(*v)) {
            if self.domains.subset_belongs(&self.domains.vars[v.idx()], b) {
                return Some("(Test.truth true)".into());
            }
        }
        // General KeySet subset: `S1 \subseteq S2`
        if let Some(va) = variable(a, false) {
            if let VarShape::KeySet { mask: mask_a, has_fixed: fixed_a, .. } = self.shapes[va.idx()] {
                if let Some(vb) = variable(b, false) {
                    if let VarShape::KeySet { mask: mask_b, has_fixed: fixed_b, .. } = self.shapes[vb.idx()] {
                        let mask = mask_a | mask_b;
                        let fresh = self.alloc_local();
                        let mut scope = keys.to_vec();
                        scope.insert(0, (fresh, mask));
                        let in_a = self.key_in_set_expr(KeyRef::Bound(0), mask, a, &scope)?;
                        let in_b = self.key_in_set_expr(KeyRef::Bound(0), mask, b, &scope)?;
                        let imp = format!("(Test.disj (Test.neg {in_a}) {in_b})");
                        let all = format!("(Test.all {} {imp})", self.mask_lean(mask));
                        return Some(if fixed_a || fixed_b {
                            let fp = self.core_leaf_from_desc(format!("KeySet fixed-part subset: var {} <= var {}", va.idx(), vb.idx()));
                            format!("(Test.conj {fp} {all})")
                        } else {
                            all
                        });
                    }
                }
            }
        }
        None
    }

    pub(super) fn key_in_set_expr(&mut self, kref: KeyRef, _kmask: GroupMask, set: &Expr, keys: &[(LocalId, GroupMask)]) -> Option<String> {
        if let Some(v) = variable(set, false) {
            if let VarShape::KeySet { mask, map_id, .. } = self.shapes[v.idx()] {
                let read = self.keyset_mem_leaf(map_id, kref)?;
                return Some(format!("(Test.conj (Test.inGroup {} {}) {read})", kref.lean(), self.mask_lean(mask)));
            }
        }
        if let Some(exact) = self.domains.exact_set(set) {
            if let Some((mask, fixed)) = group_mask_exact(self.groups, &exact) {
                if !fixed.is_empty() && !matches!(kref, KeyRef::Bound(_)) {
                    return None;
                }
                return Some(if mask == 0 {
                    "(Test.truth false)".into()
                } else {
                    format!("(Test.inGroup {} {})", kref.lean(), self.mask_lean(mask))
                });
            }
        }
        match &*set.kind {
            ExprKind::SetEnum(es) => {
                let mut out = "(Test.truth false)".to_owned();
                for item in es {
                    if let Some((iref, _, _)) = self.key_ref(item, keys) {
                        out = bounded(format!("(Test.disj {out} (Test.equal {} {}))", kref.lean(), iref.lean()))?;
                    } else if matches!(kref, KeyRef::Bound(_)) && independent(&self.domains.value(item, &Locals::new()), self.all_keys) {
                        // A moved bound key can never equal a key-free item.
                    } else {
                        return None;
                    }
                }
                Some(out)
            }
            ExprKind::Builtin { op, args } => match (op, args.as_slice()) {
                (B::Cup, [a, b]) => {
                    let ta = self.key_in_set_expr(kref, _kmask, a, keys)?;
                    let tb = self.key_in_set_expr(kref, _kmask, b, keys)?;
                    bounded(format!("(Test.disj {ta} {tb})"))
                }
                (B::Cap, [a, b]) => {
                    let ta = self.key_in_set_expr(kref, _kmask, a, keys)?;
                    let tb = self.key_in_set_expr(kref, _kmask, b, keys)?;
                    bounded(format!("(Test.conj {ta} {tb})"))
                }
                (B::SetMinus, [a, b]) => {
                    let ta = self.key_in_set_expr(kref, _kmask, a, keys)?;
                    let tb = self.key_in_set_expr(kref, _kmask, b, keys)?;
                    bounded(format!("(Test.conj {ta} (Test.neg {tb}))"))
                }
                _ => None,
            },
            ExprKind::SetFilter { bound, pred } => {
                let BoundVars::Many(ids) = &bound.vars else { return None };
                let [id] = ids.as_slice() else { return None };
                let in_dom = self.key_in_set_expr(kref, _kmask, &bound.set, keys)?;
                let kexpr = self.key_ref_expr(kref, keys, set.span)?;
                let sub = subst_local(pred, *id, &kexpr);
                let pt = self.test(&sub, keys)?;
                bounded(format!("(Test.conj {in_dom} {pt})"))
            }
            _ => None,
        }
    }

    pub(super) fn value(&mut self, e: &Expr, keys: &[(LocalId, GroupMask)]) -> Option<String> {
        let result = self.value_inner(e, keys)?;
        bounded(result)
    }

    fn value_inner(&mut self, e: &Expr, keys: &[(LocalId, GroupMask)]) -> Option<String> {
        if let ExprKind::If { cond, then, els } = &*e.kind {
            return Some(format!("(ValueExpr.branch {} {} {})", self.test(cond, keys)?, self.value(then, keys)?, self.value(els, keys)?));
        }
        self.leaf(e, keys, "ValueExpr")
    }

    pub(super) fn slot_expr(&mut self, e: &Expr, mask: GroupMask, has_fixed: bool, keys: &[(LocalId, GroupMask)]) -> Option<String> {
        if let ExprKind::If { cond, then, els } = &*e.kind {
            return bounded(format!(
                "(SlotExpr.branch {} {} {})",
                self.test(cond, keys)?,
                self.slot_expr(then, mask, has_fixed, keys)?,
                self.slot_expr(els, mask, has_fixed, keys)?
            ));
        }
        if let Some((kref, kmask, k_has_fixed)) = self.key_ref(e, keys) {
            if (kmask & !mask) != 0 || (k_has_fixed && !has_fixed) {
                return None;
            }
            return Some(format!("(SlotExpr.ref {})", kref.lean()));
        }
        if has_fixed {
            let mut next = max_local(e).checked_add(1)?;
            let mut reads = LeafReads::new();
            let masked = self.mask(e, keys, &mut next, &mut reads)?;
            let id = self.atoms.len();
            self.atoms.push(format!("SlotExpr.fixedVal HIR: {masked:#?}\nPayload holes: {:?}", reads.holes));
            let mut term = format!(
                "(SlotExpr.fixedVal {id} [{}] [{}] [{}])",
                reads.map_reads.join(", "),
                reads.slot_map_reads.join(", "),
                reads.slot_fixed_reads.join(", ")
            );
            for (cmask, pred) in reads.counts {
                term = bounded(format!("(SlotExpr.bindCount {} {pred} {term})", self.mask_lean(cmask)))?;
            }
            return Some(term);
        }
        None
    }

    pub(super) fn key_ref(&self, e: &Expr, keys: &[(LocalId, GroupMask)]) -> Option<(KeyRef, GroupMask, bool)> {
        match &*e.kind {
            ExprKind::Local(id) => {
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
                let v = variable(record, false)?;
                if let VarShape::FixedRecord { fields } = &self.shapes[v.idx()] {
                    if let Some(FieldShape::ScalarSlot { mask, has_fixed, slot_id }) = fields.get(field) {
                        return Some((KeyRef::Slot(*slot_id), *mask, *has_fixed));
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn key_or_fixed_ref(&mut self, e: &Expr, keys: &[(LocalId, GroupMask)]) -> Option<KeyRef> {
        if let Some((kref, _, _)) = self.key_ref(e, keys) {
            return Some(kref);
        }
        if let Some(atom) = self.domains.atom_value(e) {
            if !self.all_keys.contains(&atom) {
                let id = self.fixed_atoms.len();
                self.fixed_atoms.push(format!("{atom:?}"));
                return Some(KeyRef::Fixed(id));
            }
        }
        None
    }

    fn fixed_map_target(&self, e: &Expr) -> Option<(GroupMask, usize)> {
        match &*e.kind {
            ExprKind::Var(v) => match self.shapes[v.idx()] {
                VarShape::FixedMap { mask, map_id } => Some((mask, map_id)),
                _ => None,
            },
            ExprKind::Field { record, field } => {
                let v = variable(record, false)?;
                if let VarShape::FixedRecord { fields } = &self.shapes[v.idx()] {
                    if let Some(FieldShape::FixedMap { mask, map_id }) = fields.get(field) {
                        return Some((*mask, *map_id));
                    }
                }
                None
            }
            _ => None,
        }
    }

    fn keyset_mem_leaf(&mut self, map_id: usize, kref: KeyRef) -> Option<String> {
        let id = self.atoms.len();
        self.atoms.push(format!("KeySet membership read map {map_id}"));
        match kref {
            KeyRef::Bound(idx) => Some(format!("(Test.leaf {id} [(⟨{map_id}, by decide⟩, {idx})] [] [])")),
            KeyRef::Slot(s) => Some(format!("(Test.leaf {id} [] [(⟨{map_id}, by decide⟩, ⟨{s}, by decide⟩)] [])")),
            KeyRef::Fixed(_) => None,
        }
    }

    fn slot_fixed_in_keyset_test(&mut self, var: VarId, slot_id: usize) -> String {
        let id = self.atoms.len();
        self.atoms.push(format!("Slot {slot_id} fixed-atom membership in KeySet var {}", var.idx()));
        format!("(Test.leaf {id} [] [] [⟨{slot_id}, by decide⟩])")
    }

    fn record_set_mem_test(&mut self, map_id: usize, kref: KeyRef, rest_rec: &Expr, keys: &[(LocalId, GroupMask)]) -> Option<String> {
        let mut next = max_local(rest_rec).checked_add(1)?;
        let mut reads = LeafReads::new();
        match kref {
            KeyRef::Bound(idx) => reads.map_reads.push(format!("(⟨{map_id}, by decide⟩, {idx})")),
            KeyRef::Slot(s) => reads.slot_map_reads.push(format!("(⟨{map_id}, by decide⟩, ⟨{s}, by decide⟩)")),
            KeyRef::Fixed(_) => return None,
        }
        let masked = self.mask(rest_rec, keys, &mut next, &mut reads)?;
        let id = self.atoms.len();
        self.atoms.push(format!("RecordSet membership map {map_id} payload HIR: {masked:#?}\nPayload holes: {:?}", reads.holes));
        let mut term = format!(
            "(Test.leaf {id} [{}] [{}] [{}])",
            reads.map_reads.join(", "),
            reads.slot_map_reads.join(", "),
            reads.slot_fixed_reads.join(", ")
        );
        for (cmask, pred) in reads.counts {
            term = bounded(format!("(Test.bindCount {} {pred} {term})", self.mask_lean(cmask)))?;
        }
        Some(term)
    }

    pub(super) fn record_set_add_value(
        &mut self,
        map_id: usize,
        kref: KeyRef,
        rest_rec: &Expr,
        keys: &[(LocalId, GroupMask)],
    ) -> Option<String> {
        let mut next = max_local(rest_rec).checked_add(1)?;
        let mut reads = LeafReads::new();
        match kref {
            KeyRef::Bound(idx) => reads.map_reads.push(format!("(⟨{map_id}, by decide⟩, {idx})")),
            KeyRef::Slot(s) => reads.slot_map_reads.push(format!("(⟨{map_id}, by decide⟩, ⟨{s}, by decide⟩)")),
            KeyRef::Fixed(_) => return None,
        }
        let masked = self.mask(rest_rec, keys, &mut next, &mut reads)?;
        let id = self.atoms.len();
        self.atoms.push(format!("RecordSet insert map {map_id} payload HIR: {masked:#?}\nPayload holes: {:?}", reads.holes));
        let mut term = format!(
            "(ValueExpr.leaf {id} [{}] [{}] [{}])",
            reads.map_reads.join(", "),
            reads.slot_map_reads.join(", "),
            reads.slot_fixed_reads.join(", ")
        );
        for (cmask, pred) in reads.counts {
            term = bounded(format!("(ValueExpr.bindCount {} {pred} {term})", self.mask_lean(cmask)))?;
        }
        Some(term)
    }

    pub(super) fn leaf(&mut self, e: &Expr, keys: &[(LocalId, GroupMask)], kind: &str) -> Option<String> {
        let mut next = max_local(e).checked_add(1)?;
        let mut reads = LeafReads::new();
        let masked = self.mask(e, keys, &mut next, &mut reads)?;
        let id = self.atoms.len();
        self.atoms.push(format!("{kind} HIR: {masked:#?}\nPayload holes: {:?}", reads.holes));
        let mut term = format!(
            "({kind}.leaf {id} [{}] [{}] [{}])",
            reads.map_reads.join(", "),
            reads.slot_map_reads.join(", "),
            reads.slot_fixed_reads.join(", ")
        );
        for (cmask, pred) in reads.counts {
            term = bounded(format!("({kind}.bindCount {} {pred} {term})", self.mask_lean(cmask)))?;
        }
        Some(term)
    }

    fn mask(&mut self, e: &Expr, keys: &[(LocalId, GroupMask)], next: &mut u32, reads: &mut LeafReads) -> Option<Expr> {
        // Proved type membership inside a leaf
        if let ExprKind::Builtin { op: B::In, args } = &*e.kind {
            if let [value, set] = args.as_slice() {
                if let Some(v) = variable(value, false).filter(|v| self.is_non_core(*v)) {
                    if self.domains.belongs(&self.domains.vars[v.idx()], set) {
                        return Some(Expr::new(ExprKind::Bool(true), e.span));
                    }
                }
            }
        }
        if let ExprKind::Builtin { op: B::SubsetEq, args } = &*e.kind {
            if let [value, set] = args.as_slice() {
                if let Some(v) = variable(value, false).filter(|v| self.is_non_core(*v)) {
                    if self.domains.subset_belongs(&self.domains.vars[v.idx()], set) {
                        return Some(Expr::new(ExprKind::Bool(true), e.span));
                    }
                }
            }
        }
        // Cardinality of a pure KeySet (`has_fixed: false`) or filtered key set -> bindCount hole!
        if let ExprKind::Builtin { op: B::Cardinality, args } = &*e.kind {
            if let [arg] = args.as_slice() {
                if let Some((cmask, pred)) = self.cardinality_target(arg, keys) {
                    let hole = LocalId(*next);
                    *next = next.checked_add(1)?;
                    reads.counts.push((cmask, pred));
                    reads.holes.push(hole);
                    return Some(Expr::new(ExprKind::Local(hole), e.span));
                }
            }
        }
        // Core field of a FixedRecord (`chan.rdy`, `coordinator.alive`): allow reading the core field directly!
        if let ExprKind::Field { record, field } = &*e.kind {
            if let Some(v) = variable(record, false) {
                if let VarShape::FixedRecord { fields } = &self.shapes[v.idx()] {
                    if matches!(fields.get(field), Some(FieldShape::Core)) {
                        return Some(e.clone());
                    }
                }
            }
        }
        // Map lookup `m[k]` for FixedMap, MixedMap, or FixedRecord's map field!
        if let ExprKind::FnApp { func, args } = &*e.kind {
            if let Some((mask, map_id)) = self.fixed_map_target(func) {
                let [arg] = args.as_slice() else { return None };
                let (kref, kmask, _) = self.key_ref(arg, keys)?;
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
                reads.holes.push(hole);
                return Some(Expr::new(ExprKind::Local(hole), e.span));
            }
            if let Some(v) = variable(func, false) {
                if let VarShape::MixedMap { mask, fixed_keys, map_id } = self.shapes[v.idx()].clone() {
                    let [arg] = args.as_slice() else { return None };
                    if let Some((kref, kmask, false)) = self.key_ref(arg, keys) {
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
                        reads.holes.push(hole);
                        return Some(Expr::new(ExprKind::Local(hole), e.span));
                    }
                    if let Some(atom) = self.domains.atom_value(arg) {
                        if fixed_keys.contains(&atom) {
                            // Fixed index read of a mixed map belongs to C!
                            return Some(e.clone());
                        }
                    }
                    return None;
                }
            }
        }
        match &*e.kind {
            ExprKind::Var(v) if self.is_non_core(*v) || self.omitted.contains(v) => return None,
            ExprKind::Local(id) if keys.iter().any(|(k, _)| k == id) => return None,
            ExprKind::Const(_) if !independent(&self.domains.value(e, &Locals::new()), self.all_keys) => return None,
            ExprKind::Builtin { op: B::Prime, .. } if self.mentions_non_core(e) => return None,
            // Never move a binder-dependent read outside its scope.
            ExprKind::Quant { .. }
            | ExprKind::Choose { .. }
            | ExprKind::FnConstruct { .. }
            | ExprKind::SetFilter { .. }
            | ExprKind::SetMap { .. }
                if self.mentions_non_core(e) || self.mentions_keys(e, keys) =>
            {
                return None;
            }
            _ => {}
        }
        let mut masked = e.clone();
        let mut valid = true;
        visit::children_mut(&mut masked, &mut |child| {
            if let Some(c) = self.mask(child, keys, next, reads) {
                *child = c;
            } else {
                valid = false;
            }
        });
        valid.then_some(masked)
    }

    fn cardinality_target(&mut self, set: &Expr, keys: &[(LocalId, GroupMask)]) -> Option<(GroupMask, String)> {
        // Case 1: `Cardinality(S)` where `S` is a pure KeySet variable (`has_fixed == false`).
        // Mixed sets (`has_fixed == true`, e.g. `Proc \cup {0}`) are declined here so `countKeys`
        // never replaces the fixed-element contribution; `equiv_sym` certifies them directly.
        if let Some(v) = variable(set, false) {
            if let VarShape::KeySet { mask, has_fixed: false, .. } = self.shapes[v.idx()] {
                let fresh = self.alloc_local();
                let mut scope = keys.to_vec();
                scope.insert(0, (fresh, mask));
                let pred = self.key_in_set_expr(KeyRef::Bound(0), mask, set, &scope)?;
                return Some((mask, pred));
            }
        }
        // Case 2: `Cardinality({k \in K_mask : P(k)})`
        if let ExprKind::SetFilter { bound, pred } = &*set.kind {
            let BoundVars::Many(ids) = &bound.vars else { return None };
            let [id] = ids.as_slice() else { return None };
            if let Some(exact) = self.domains.exact_set(&bound.set) {
                let (mask, fixed) = group_mask_exact(self.groups, &exact)?;
                if mask != 0 && fixed.is_empty() {
                    let mut scope = keys.to_vec();
                    scope.insert(0, (*id, mask));
                    let p = self.test(pred, &scope)?;
                    return Some((mask, p));
                }
            }
        }
        None
    }

    fn mentions_non_core(&self, e: &Expr) -> bool {
        if matches!(&*e.kind, ExprKind::Var(v) if self.is_non_core(*v) || self.omitted.contains(v)) {
            return true;
        }
        let mut found = false;
        visit::children(e, &mut |c| found |= self.mentions_non_core(c));
        found
    }

    fn mentions_keys(&self, e: &Expr, keys: &[(LocalId, GroupMask)]) -> bool {
        if matches!(&*e.kind, ExprKind::Local(id) if keys.iter().any(|(k, _)| k == id)) {
            return true;
        }
        let mut found = false;
        visit::children(e, &mut |c| found |= self.mentions_keys(c, keys));
        found
    }
}

// Boolean IF expansion duplicates its condition. Bound each intermediate term
// so deeply nested conditions cannot expand an otherwise small HIR exponentially.
pub(super) fn bounded(term: String) -> Option<String> {
    (term.len() <= 1_000_000).then_some(term)
}
