//! Forward integer interval inference from `Init` and `Next` (never invariants),
//! including relational `(FixedMap, Flag)` bounds for flag-guarded updates such as
//! `Elect(p)` (`votes[p] < 2 /\ leaders' = leaders \cup {p}`) followed by `StepLeader`.

use super::super::{variable, Branch};
use super::domain_infer::{exact_k_subset_family, GroupInfo, VarShape};
use super::{ast_equiv, Domains, GroupMask};
use crate::{builtins::Builtin as B, hir::*, Program};
use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;
use tlx_front::cfg::{CfgValue, Config};

pub(super) const I32_MIN: i128 = i32::MIN as i128;
pub(super) const I32_MAX: i128 = i32::MAX as i128;

/// Abstract integer interval lattice.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum IntBound {
    /// No integer value observed yet.
    Bottom,
    /// Guaranteed integer in `[lo, hi]` (`None` = unbounded in that direction).
    Interval { lo: Option<i128>, hi: Option<i128> },
    /// Unknown or potentially non-integer value.
    Top,
}

impl IntBound {
    pub(super) fn exact(n: i128) -> Self {
        Self::Interval { lo: Some(n), hi: Some(n) }
    }

    pub(super) fn range(lo: i128, hi: i128) -> Self {
        if lo <= hi {
            Self::Interval { lo: Some(lo), hi: Some(hi) }
        } else {
            Self::Bottom
        }
    }

    pub(super) fn finite(self) -> Option<(i128, i128)> {
        match self {
            Self::Interval { lo: Some(lo), hi: Some(hi) } if lo <= hi => Some((lo, hi)),
            _ => None,
        }
    }

    pub(super) fn fits_i32(self) -> Option<(i128, i128)> {
        let (lo, hi) = self.finite()?;
        (I32_MIN <= lo && hi <= I32_MAX).then_some((lo, hi))
    }

    pub(super) fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, x) | (x, Self::Bottom) => x,
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Interval { lo: l1, hi: h1 }, Self::Interval { lo: l2, hi: h2 }) => {
                Self::Interval { lo: l1.zip(l2).map(|(a, b)| a.min(b)), hi: h1.zip(h2).map(|(a, b)| a.max(b)) }
            }
        }
    }

    pub(super) fn meet(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Top, x) | (x, Self::Top) => x,
            (Self::Interval { lo: l1, hi: h1 }, Self::Interval { lo: l2, hi: h2 }) => {
                let lo = match (l1, l2) {
                    (Some(a), Some(b)) => Some(a.max(b)),
                    (Some(a), None) | (None, Some(a)) => Some(a),
                    (None, None) => None,
                };
                let hi = match (h1, h2) {
                    (Some(a), Some(b)) => Some(a.min(b)),
                    (Some(a), None) | (None, Some(a)) => Some(a),
                    (None, None) => None,
                };
                if let (Some(l), Some(h)) = (lo, hi) {
                    if l > h {
                        return Self::Bottom;
                    }
                }
                Self::Interval { lo, hi }
            }
        }
    }

    fn refine(self, lo_opt: Option<i128>, hi_opt: Option<i128>) -> Self {
        match self {
            Self::Bottom => Self::Bottom,
            Self::Top => match (lo_opt, hi_opt) {
                (Some(l), Some(h)) => Self::range(l, h),
                _ => Self::Top,
            },
            Self::Interval { .. } => self.meet(Self::Interval { lo: lo_opt, hi: hi_opt }),
        }
    }

    fn widen(old: Self, new: Self) -> Self {
        match (old, new) {
            (Self::Bottom, x) => x,
            (Self::Interval { lo: l1, hi: h1 }, Self::Interval { lo: l2, hi: h2 }) => {
                let lo = match (l1, l2) {
                    (Some(a), Some(b)) if b < a => None,
                    (_, b) => b,
                };
                let hi = match (h1, h2) {
                    (Some(a), Some(b)) if b > a => None,
                    (_, b) => b,
                };
                Self::Interval { lo, hi }
            }
            (_, x) => x,
        }
    }

    fn is_subset_of(self, other: Self) -> bool {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Top) => true,
            (Self::Top, _) | (_, Self::Bottom) => false,
            (Self::Interval { lo: l1, hi: h1 }, Self::Interval { lo: l2, hi: h2 }) => {
                let lo_ok = match (l1, l2) {
                    (_, None) => true,
                    (Some(a), Some(b)) => a >= b,
                    (None, Some(_)) => false,
                };
                let hi_ok = match (h1, h2) {
                    (_, None) => true,
                    (Some(a), Some(b)) => a <= b,
                    (None, Some(_)) => false,
                };
                lo_ok && hi_ok
            }
        }
    }

    pub(super) fn add(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Interval { lo: l1, hi: h1 }, Self::Interval { lo: l2, hi: h2 }) => {
                Self::Interval { lo: l1.zip(l2).and_then(|(a, b)| a.checked_add(b)), hi: h1.zip(h2).and_then(|(a, b)| a.checked_add(b)) }
            }
            _ => Self::Top,
        }
    }

    pub(super) fn sub(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Interval { lo: l1, hi: h1 }, Self::Interval { lo: l2, hi: h2 }) => {
                Self::Interval { lo: l1.zip(h2).and_then(|(a, b)| a.checked_sub(b)), hi: h1.zip(l2).and_then(|(a, b)| a.checked_sub(b)) }
            }
            _ => Self::Top,
        }
    }

    pub(super) fn neg(self) -> Self {
        match self {
            Self::Bottom => Self::Bottom,
            Self::Interval { lo, hi } => Self::Interval { lo: hi.and_then(|h| h.checked_neg()), hi: lo.and_then(|l| l.checked_neg()) },
            Self::Top => Self::Top,
        }
    }

    pub(super) fn mul(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Interval { lo: Some(l1), hi: Some(h1) }, Self::Interval { lo: Some(l2), hi: Some(h2) }) => {
                let Some(p1) = l1.checked_mul(l2) else { return Self::Interval { lo: None, hi: None } };
                let Some(p2) = l1.checked_mul(h2) else { return Self::Interval { lo: None, hi: None } };
                let Some(p3) = h1.checked_mul(l2) else { return Self::Interval { lo: None, hi: None } };
                let Some(p4) = h1.checked_mul(h2) else { return Self::Interval { lo: None, hi: None } };
                Self::Interval { lo: Some(p1.min(p2).min(p3).min(p4)), hi: Some(p1.max(p2).max(p3).max(p4)) }
            }
            (Self::Interval { .. }, Self::Interval { .. }) => Self::Interval { lo: None, hi: None },
            _ => Self::Top,
        }
    }

    /// Conservative `\div` covering both `Integers` (floor division) and `Naturals`
    /// (`tlx_value::arith::div_naturals` truncating-near-zero division, where `(-1) \div 2 = 0`).
    pub(super) fn div_tla(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Interval { lo: Some(l1), hi: Some(h1) }, Self::Interval { lo: Some(l2), hi: Some(h2) })
                if l2 >= 1 && I32_MIN <= l1 && h1 <= I32_MAX && h2 <= I32_MAX =>
            {
                let mut lo = i128::MAX;
                let mut hi = i128::MIN;
                for a in [l1, h1] {
                    for b in [l2, h2] {
                        let floor = a.div_euclid(b);
                        let mut nat = a / b;
                        if nat < 0 && nat * b != a {
                            nat -= 1;
                        }
                        lo = lo.min(floor).min(nat);
                        hi = hi.max(floor).max(nat);
                    }
                }
                Self::Interval { lo: Some(lo), hi: Some(hi) }
            }
            (Self::Interval { .. }, Self::Interval { .. }) => Self::Interval { lo: None, hi: None },
            _ => Self::Top,
        }
    }

    pub(super) fn rem_euclid(self, other: Self) -> Self {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Interval { .. }, Self::Interval { lo: Some(l2), hi: Some(h2) }) if l2 >= 1 => {
                Self::Interval { lo: Some(0), hi: Some(h2 - 1) }
            }
            (Self::Interval { .. }, Self::Interval { .. }) => Self::Interval { lo: Some(0), hi: None },
            _ => Self::Top,
        }
    }
}

/// Abstract value bound carrying nested integer intervals for maps, sets, and records.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum ValBound {
    Bottom,
    Int(IntBound),
    Map(Box<ValBound>),
    Set(Box<ValBound>),
    Record(BTreeMap<Arc<str>, ValBound>),
    Top,
}

impl ValBound {
    pub(super) fn as_int(&self) -> IntBound {
        match self {
            Self::Bottom => IntBound::Bottom,
            Self::Int(b) => *b,
            _ => IntBound::Top,
        }
    }

    pub(super) fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bottom, x) | (x, Self::Bottom) => x.clone(),
            (Self::Top, _) | (_, Self::Top) => Self::Top,
            (Self::Int(a), Self::Int(b)) => Self::Int(a.join(*b)),
            (Self::Map(a), Self::Map(b)) => Self::Map(Box::new(a.join(b))),
            (Self::Set(a), Self::Set(b)) => Self::Set(Box::new(a.join(b))),
            (Self::Record(a), Self::Record(b)) if a.keys().eq(b.keys()) => {
                Self::Record(a.iter().map(|(k, v)| (k.clone(), v.join(&b[k]))).collect())
            }
            _ => Self::Top,
        }
    }

    fn meet(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Bottom) => Self::Bottom,
            (Self::Top, x) | (x, Self::Top) => x.clone(),
            (Self::Int(a), Self::Int(b)) => Self::Int(a.meet(*b)),
            (Self::Map(a), Self::Map(b)) => Self::Map(Box::new(a.meet(b))),
            (Self::Set(a), Self::Set(b)) => Self::Set(Box::new(a.meet(b))),
            (Self::Record(a), Self::Record(b)) if a.keys().eq(b.keys()) => {
                Self::Record(a.iter().map(|(k, v)| (k.clone(), v.meet(&b[k]))).collect())
            }
            _ => self.clone(),
        }
    }

    fn widen(old: &Self, new: &Self) -> Self {
        match (old, new) {
            (Self::Bottom, x) => x.clone(),
            (Self::Int(a), Self::Int(b)) => Self::Int(IntBound::widen(*a, *b)),
            (Self::Map(a), Self::Map(b)) => Self::Map(Box::new(Self::widen(a, b))),
            (Self::Set(a), Self::Set(b)) => Self::Set(Box::new(Self::widen(a, b))),
            (Self::Record(a), Self::Record(b)) if a.keys().eq(b.keys()) => {
                Self::Record(a.iter().map(|(k, v)| (k.clone(), Self::widen(v, &b[k]))).collect())
            }
            (_, x) => x.clone(),
        }
    }

    fn is_subset_of(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Bottom, _) | (_, Self::Top) => true,
            (Self::Top, _) | (_, Self::Bottom) => false,
            (Self::Int(a), Self::Int(b)) => a.is_subset_of(*b),
            (Self::Map(a), Self::Map(b)) => a.is_subset_of(b),
            (Self::Set(a), Self::Set(b)) => a.is_subset_of(b),
            (Self::Record(a), Self::Record(b)) if a.keys().eq(b.keys()) => a.iter().all(|(k, v)| v.is_subset_of(&b[k])),
            _ => false,
        }
    }

    fn refine_int(&self, lo_opt: Option<i128>, hi_opt: Option<i128>) -> Self {
        match self {
            Self::Bottom => Self::Bottom,
            Self::Int(b) => Self::Int(b.refine(lo_opt, hi_opt)),
            Self::Top => match (lo_opt, hi_opt) {
                (Some(l), Some(h)) => Self::Int(IntBound::range(l, h)),
                _ => Self::Top,
            },
            other => other.clone(),
        }
    }

    pub(super) fn field(&self, name: &str) -> Self {
        match self {
            Self::Bottom => Self::Bottom,
            Self::Record(fs) => fs.get(name).cloned().unwrap_or(Self::Top),
            _ => Self::Top,
        }
    }

    pub(super) fn map_elem(&self) -> Self {
        match self {
            Self::Bottom => Self::Bottom,
            Self::Map(e) => (**e).clone(),
            _ => Self::Top,
        }
    }

    pub(super) fn set_elem(&self) -> Self {
        match self {
            Self::Bottom => Self::Bottom,
            Self::Set(e) => (**e).clone(),
            _ => Self::Top,
        }
    }
}

pub(super) type LocalBounds = HashMap<LocalId, ValBound>;

/// Sound forward bounds derived exclusively from `Init` and `Next` (never invariants).
#[derive(Clone, Debug)]
pub(super) struct ModelBounds {
    pub(super) vars: Vec<ValBound>,
    pub(super) consts: HashMap<ConstId, ValBound>,
    /// Relational bound: for `(map_var, flag_var)`, whenever `k` is active in `flag_var`,
    /// `map_var[k]` lies within this entry bound.
    pub(super) flagged_maps: HashMap<(VarId, VarId), ValBound>,
}

pub(super) struct BranchGuards<'a> {
    /// Direct integer refinements `(target_expr, lo_opt, hi_opt)`.
    int_refinements: Vec<(Expr, Option<i128>, Option<i128>)>,
    /// Direct flag memberships `(key_expr, flag_var)`.
    active_flags: Vec<(Expr, VarId)>,
    shapes: &'a [VarShape],
    fold_vars: &'a HashMap<LocalId, Option<Expr>>,
}

impl<'a> BranchGuards<'a> {
    fn from_branch(
        b: &Branch,
        shapes: &'a [VarShape],
        fold_vars: &'a HashMap<LocalId, Option<Expr>>,
        consts: &HashMap<ConstId, ValBound>,
        domains: &Domains,
    ) -> Self {
        let mut out = Self { int_refinements: Vec::new(), active_flags: Vec::new(), shapes, fold_vars };
        let mut flat = Vec::new();
        for term in &b.terms {
            flatten_and(term, &mut flat);
        }
        for g in flat {
            out.record_guard(g, consts, domains);
        }
        out
    }

    fn record_guard(&mut self, g: &Expr, consts: &HashMap<ConstId, ValBound>, domains: &Domains) {
        match &*g.kind {
            ExprKind::FnApp { func, args } if args.len() == 1 => {
                if let Some(fv) = variable(func, false) {
                    if matches!(self.shapes[fv.idx()], VarShape::BoolMapFlag { .. }) {
                        self.active_flags.push((args[0].clone(), fv));
                    }
                }
            }
            ExprKind::Builtin { op, args } if args.len() == 2 => {
                let (a, b) = (&args[0], &args[1]);
                match op {
                    B::In => {
                        if let Some(fv) = variable(b, false) {
                            if matches!(self.shapes[fv.idx()], VarShape::KeySetFlag { .. }) {
                                self.active_flags.push((a.clone(), fv));
                            }
                        }
                        if let Some((lo, hi)) = const_int_set_range(b, consts, domains) {
                            self.int_refinements.push((a.clone(), Some(lo), Some(hi)));
                        }
                    }
                    B::Eq => {
                        if matches!(&*b.kind, ExprKind::Bool(true)) {
                            self.record_guard(a, consts, domains);
                        } else if matches!(&*a.kind, ExprKind::Bool(true)) {
                            self.record_guard(b, consts, domains);
                        } else if let Some(n) = const_int_val(b, consts) {
                            self.int_refinements.push((a.clone(), Some(n), Some(n)));
                        } else if let Some(n) = const_int_val(a, consts) {
                            self.int_refinements.push((b.clone(), Some(n), Some(n)));
                        }
                    }
                    B::Lt => {
                        if let Some(n) = const_int_val(b, consts) {
                            if let Some(hi) = n.checked_sub(1) {
                                self.int_refinements.push((a.clone(), None, Some(hi)));
                            }
                        } else if let Some(n) = const_int_val(a, consts) {
                            if let Some(lo) = n.checked_add(1) {
                                self.int_refinements.push((b.clone(), Some(lo), None));
                            }
                        }
                    }
                    B::Le => {
                        if let Some(n) = const_int_val(b, consts) {
                            self.int_refinements.push((a.clone(), None, Some(n)));
                        } else if let Some(n) = const_int_val(a, consts) {
                            self.int_refinements.push((b.clone(), Some(n), None));
                        }
                    }
                    B::Gt => {
                        if let Some(n) = const_int_val(b, consts) {
                            if let Some(lo) = n.checked_add(1) {
                                self.int_refinements.push((a.clone(), Some(lo), None));
                            }
                        } else if let Some(n) = const_int_val(a, consts) {
                            if let Some(hi) = n.checked_sub(1) {
                                self.int_refinements.push((b.clone(), None, Some(hi)));
                            }
                        }
                    }
                    B::Ge => {
                        if let Some(n) = const_int_val(b, consts) {
                            self.int_refinements.push((a.clone(), Some(n), None));
                        } else if let Some(n) = const_int_val(a, consts) {
                            self.int_refinements.push((b.clone(), None, Some(n)));
                        }
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }

    fn apply_refinements(&self, expr: &Expr, mut val: ValBound) -> ValBound {
        for (target, lo, hi) in &self.int_refinements {
            if ast_equiv(expr, target, self.fold_vars) {
                val = val.refine_int(*lo, *hi);
            }
        }
        val
    }

    fn key_flags(&self, kexpr: &Expr) -> Vec<VarId> {
        let mut out = Vec::new();
        for (k, fv) in &self.active_flags {
            if ast_equiv(kexpr, k, self.fold_vars) && !out.contains(fv) {
                out.push(*fv);
            }
        }
        // Also extract flag guarantees directly from `CHOOSE v \in S : P(v)`.
        if let ExprKind::Choose { vars: BoundVars::Many(ids), set: Some(cset), body: cpred } = &*kexpr.kind {
            if let [v] = ids.as_slice() {
                if let Some(fv) = variable(cset, false) {
                    if matches!(self.shapes[fv.idx()], VarShape::KeySetFlag { .. }) && !out.contains(&fv) {
                        out.push(fv);
                    }
                }
                if let ExprKind::SetFilter { bound, pred: fpred } = &*cset.kind {
                    if let Some(fv) = variable(&bound.set, false) {
                        if matches!(self.shapes[fv.idx()], VarShape::KeySetFlag { .. }) && !out.contains(&fv) {
                            out.push(fv);
                        }
                    }
                    if let BoundVars::Many(fids) = &bound.vars {
                        if let [fid] = fids.as_slice() {
                            collect_choose_flag_vars(fpred, *fid, self.shapes, &mut out);
                        }
                    }
                }
                collect_choose_flag_vars(cpred, *v, self.shapes, &mut out);
            }
        }
        out
    }
}

fn collect_choose_flag_vars(pred: &Expr, v: LocalId, shapes: &[VarShape], out: &mut Vec<VarId>) {
    let mut flat = Vec::new();
    flatten_and(pred, &mut flat);
    for c in flat {
        match &*c.kind {
            ExprKind::Builtin { op: B::In, args } if args.len() == 2 => {
                if matches!(&*args[0].kind, ExprKind::Local(l) if *l == v) {
                    if let Some(fv) = variable(&args[1], false) {
                        if matches!(shapes[fv.idx()], VarShape::KeySetFlag { .. }) && !out.contains(&fv) {
                            out.push(fv);
                        }
                    }
                }
            }
            ExprKind::FnApp { func, args } if args.len() == 1 => {
                if matches!(&*args[0].kind, ExprKind::Local(l) if *l == v) {
                    if let Some(fv) = variable(func, false) {
                        if matches!(shapes[fv.idx()], VarShape::BoolMapFlag { .. }) && !out.contains(&fv) {
                            out.push(fv);
                        }
                    }
                }
            }
            ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 => {
                if matches!(&*args[1].kind, ExprKind::Bool(true)) {
                    collect_choose_flag_vars(&args[0], v, shapes, out);
                } else if matches!(&*args[0].kind, ExprKind::Bool(true)) {
                    collect_choose_flag_vars(&args[1], v, shapes, out);
                }
            }
            _ => {}
        }
    }
}

fn flatten_and<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
    match &*e.kind {
        ExprKind::And(es) => es.iter().for_each(|x| flatten_and(x, out)),
        _ => out.push(e),
    }
}

fn const_int_val(e: &Expr, consts: &HashMap<ConstId, ValBound>) -> Option<i128> {
    match &*e.kind {
        ExprKind::Num(n) => Some(*n),
        ExprKind::Builtin { op: B::Neg, args } if args.len() == 1 => const_int_val(&args[0], consts)?.checked_neg(),
        ExprKind::Const(cid) => {
            let (lo, hi) = consts.get(cid)?.as_int().finite()?;
            (lo == hi).then_some(lo)
        }
        _ => None,
    }
}

fn const_int_set_range(e: &Expr, consts: &HashMap<ConstId, ValBound>, domains: &Domains) -> Option<(i128, i128)> {
    match &*e.kind {
        ExprKind::Builtin { op: B::DotDot, args } if args.len() == 2 => {
            let lo = const_int_val(&args[0], consts)?;
            let hi = const_int_val(&args[1], consts)?;
            (lo <= hi).then_some((lo, hi))
        }
        ExprKind::SetEnum(es) if !es.is_empty() => {
            let mut b = IntBound::Bottom;
            for item in es {
                let n = const_int_val(item, consts)?;
                b = b.join(IntBound::exact(n));
            }
            b.finite()
        }
        ExprKind::Const(cid) => consts.get(cid)?.set_elem().as_int().finite(),
        _ => {
            let exact = domains.exact_set(e)?;
            if exact.is_empty() {
                return None;
            }
            let mut b = IntBound::Bottom;
            for a in exact {
                let super::super::domain::Atom::Num(n) = a else { return None };
                b = b.join(IntBound::exact(n));
            }
            b.finite()
        }
    }
}

fn cfg_val_bound(v: &CfgValue) -> ValBound {
    match v {
        CfgValue::Int(n) => ValBound::Int(IntBound::exact(i128::from(*n))),
        CfgValue::Set(es) => {
            let elem = es.iter().fold(ValBound::Bottom, |acc, item| acc.join(&cfg_val_bound(item)));
            ValBound::Set(Box::new(elem))
        }
        _ => ValBound::Top,
    }
}

#[allow(clippy::too_many_arguments)] // forward interval fixed-point over Init/Next branches and model metadata
pub(super) fn infer_model_bounds(
    program: &Program,
    cfg: &Config,
    domains: &Domains,
    shapes: &[VarShape],
    fold_vars: &HashMap<LocalId, Option<Expr>>,
    groups: &[GroupInfo],
    init: &[Branch],
    next: &[Branch],
) -> ModelBounds {
    let mut consts = HashMap::new();
    for (i, c) in program.consts.iter().enumerate() {
        if c.arity != 0 {
            continue;
        }
        if let Some(val) = cfg.last_constant_value(&c.name) {
            consts.insert(ConstId(i as u32), cfg_val_bound(val));
        }
    }

    let map_flag_pairs: Vec<(VarId, VarId)> = (0..shapes.len())
        .filter(|&mi| matches!(shapes[mi], VarShape::FixedMap { .. }))
        .flat_map(|mi| {
            let mmask = match shapes[mi] {
                VarShape::FixedMap { mask, .. } => mask,
                _ => 0,
            };
            (0..shapes.len()).filter_map(move |fi| match shapes[fi] {
                VarShape::KeySetFlag { mask, .. } | VarShape::BoolMapFlag { mask, .. } if mask == mmask => {
                    Some((VarId(mi as u32), VarId(fi as u32)))
                }
                _ => None,
            })
        })
        .collect();

    let mut cur = ModelBounds {
        vars: vec![ValBound::Bottom; program.vars.len()],
        consts,
        flagged_maps: map_flag_pairs.iter().map(|&pair| (pair, ValBound::Bottom)).collect(),
    };

    for iter in 0..32 {
        let mut next_state = ModelBounds {
            vars: vec![ValBound::Bottom; program.vars.len()],
            consts: cur.consts.clone(),
            flagged_maps: map_flag_pairs.iter().map(|&pair| (pair, ValBound::Bottom)).collect(),
        };

        // 1. Transfer over Init branches.
        for ib in init {
            let guards = BranchGuards::from_branch(ib, shapes, fold_vars, &cur.consts, domains);
            let mut locals = LocalBounds::new();
            for bnd in &ib.bounds {
                let eb = eval_elem_bound(&bnd.set, &cur, &locals, Some(&guards), domains, fold_vars, groups, shapes, 0);
                for l in bnd.vars.locals() {
                    locals.insert(*l, if matches!(bnd.vars, BoundVars::Many(_)) { eb.clone() } else { ValBound::Top });
                }
            }
            let binds = super::super::BranchBindings::new(ib, false);
            let mut init_var_vals = vec![ValBound::Top; program.vars.len()];
            for (vi, slot) in init_var_vals.iter_mut().enumerate() {
                let var = VarId(vi as u32);
                let img = match binds.get(var) {
                    Some(rhs) => eval_val_bound(&rhs, &cur, &locals, Some(&guards), domains, fold_vars, groups, shapes, 0),
                    None => branch_membership_bound(
                        ib,
                        var,
                        false,
                        &cur,
                        &locals,
                        Some(&guards),
                        domains,
                        fold_vars,
                        groups,
                        shapes,
                        program,
                        cfg,
                    ),
                };
                *slot = img.clone();
                next_state.vars[vi] = next_state.vars[vi].join(&img);
            }
            for &(mv, fv) in &map_flag_pairs {
                if !flag_init_is_empty(&binds, fv, &shapes[fv.idx()]) {
                    let entry = init_var_vals[mv.idx()].map_elem();
                    let slot = next_state.flagged_maps.get_mut(&(mv, fv)).unwrap();
                    *slot = slot.join(&entry);
                }
            }
        }

        // 2. Transfer over Next branches.
        for sb in next {
            let guards = BranchGuards::from_branch(sb, shapes, fold_vars, &cur.consts, domains);
            let mut locals = LocalBounds::new();
            for bnd in &sb.bounds {
                let eb = eval_elem_bound(&bnd.set, &cur, &locals, Some(&guards), domains, fold_vars, groups, shapes, 0);
                for l in bnd.vars.locals() {
                    locals.insert(*l, if matches!(bnd.vars, BoundVars::Many(_)) { eb.clone() } else { ValBound::Top });
                }
            }
            let binds = super::super::BranchBindings::new(sb, true);
            let mut step_var_rhs: Vec<Option<Expr>> = Vec::with_capacity(program.vars.len());
            let mut step_var_vals: Vec<ValBound> = Vec::with_capacity(program.vars.len());
            for vi in 0..program.vars.len() {
                let var = VarId(vi as u32);
                let rhs_opt = binds.get(var);
                let img = match &rhs_opt {
                    Some(rhs) => eval_val_bound(rhs, &cur, &locals, Some(&guards), domains, fold_vars, groups, shapes, 0),
                    None => branch_membership_bound(
                        sb,
                        var,
                        true,
                        &cur,
                        &locals,
                        Some(&guards),
                        domains,
                        fold_vars,
                        groups,
                        shapes,
                        program,
                        cfg,
                    ),
                };
                step_var_rhs.push(rhs_opt);
                step_var_vals.push(img.clone());
                next_state.vars[vi] = next_state.vars[vi].join(&img);
            }

            // Update relational `(map, flag)` bounds soundly.
            for &(mv, fv) in &map_flag_pairs {
                let old_flagged = cur.flagged_maps[&(mv, fv)].clone();
                let map_post_entry = step_var_vals[mv.idx()].map_elem();
                let map_unchanged = step_var_rhs[mv.idx()].as_ref().is_some_and(|r| variable(r, false) == Some(mv));
                let single_map_update = step_var_rhs[mv.idx()].as_ref().and_then(|r| match_single_map_except(mv, r));

                let next_flagged = match classify_flag_step(fv, &shapes[fv.idx()], step_var_rhs[fv.idx()].as_ref()) {
                    FlagStepSummary::Clear => ValBound::Bottom,
                    FlagStepSummary::Keep => {
                        if map_unchanged {
                            old_flagged
                        } else {
                            old_flagged.join(&map_post_entry)
                        }
                    }
                    FlagStepSummary::ClearPoint(k_clear) => {
                        if map_unchanged {
                            old_flagged
                        } else if let Some((k_upd, _)) = &single_map_update {
                            if ast_equiv(&k_clear, k_upd, fold_vars) {
                                // The only updated key is simultaneously cleared from the flag!
                                old_flagged
                            } else {
                                old_flagged.join(&map_post_entry)
                            }
                        } else {
                            old_flagged.join(&map_post_entry)
                        }
                    }
                    FlagStepSummary::Singleton(k_set) => {
                        if map_unchanged {
                            let read = Expr::new(
                                ExprKind::FnApp { func: Expr::new(ExprKind::Var(mv), k_set.span), args: vec![k_set] },
                                sb.terms.first().map(|t| t.span).unwrap_or_default(),
                            );
                            eval_val_bound(&read, &cur, &locals, Some(&guards), domains, fold_vars, groups, shapes, 0)
                        } else if let Some((k_upd, upd_rhs)) = &single_map_update {
                            if ast_equiv(&k_set, k_upd, fold_vars) {
                                eval_val_bound(upd_rhs, &cur, &locals, Some(&guards), domains, fold_vars, groups, shapes, 0)
                            } else {
                                map_post_entry
                            }
                        } else {
                            map_post_entry
                        }
                    }
                    FlagStepSummary::SetPoint(k_set) => {
                        let at_k_set = if map_unchanged {
                            let read = Expr::new(
                                ExprKind::FnApp { func: Expr::new(ExprKind::Var(mv), k_set.span), args: vec![k_set.clone()] },
                                sb.terms.first().map(|t| t.span).unwrap_or_default(),
                            );
                            eval_val_bound(&read, &cur, &locals, Some(&guards), domains, fold_vars, groups, shapes, 0)
                        } else if let Some((k_upd, upd_rhs)) = &single_map_update {
                            if ast_equiv(&k_set, k_upd, fold_vars) {
                                eval_val_bound(upd_rhs, &cur, &locals, Some(&guards), domains, fold_vars, groups, shapes, 0)
                            } else {
                                map_post_entry.clone()
                            }
                        } else {
                            map_post_entry.clone()
                        };
                        let rest = if map_unchanged {
                            old_flagged
                        } else if let Some((k_upd, _)) = &single_map_update {
                            if ast_equiv(&k_set, k_upd, fold_vars) {
                                old_flagged
                            } else {
                                old_flagged.join(&map_post_entry)
                            }
                        } else {
                            old_flagged.join(&map_post_entry)
                        };
                        rest.join(&at_k_set)
                    }
                    FlagStepSummary::Other => map_post_entry,
                };
                let slot = next_state.flagged_maps.get_mut(&(mv, fv)).unwrap();
                *slot = slot.join(&next_flagged);
            }
        }

        // Check genuine post-fixed point (`next_state <= cur`) before any widening.
        let vars_ok = next_state.vars.iter().zip(&cur.vars).all(|(n, c)| n.is_subset_of(c));
        let flags_ok = next_state.flagged_maps.iter().all(|(k, n)| n.is_subset_of(&cur.flagged_maps[k]));
        if vars_ok && flags_ok {
            // One final narrowing check: if `next_state == cur` we are done; otherwise if strictly
            // tighter we can keep tightening down as long as `next_state <= cur` (still sound!).
            if next_state.vars == cur.vars && next_state.flagged_maps == cur.flagged_maps {
                return cur;
            }
            if iter >= 16 {
                // `cur` is ALREADY a verified post-fixed point (`F(cur) <= cur`)!
                return cur;
            }
            cur = next_state;
            continue;
        }

        // Widen unstable bounds after 8 exact iterations so unbounded counters converge quickly,
        // then subsequent iterations narrow back to guard caps and verify post-fixed point.
        if iter >= 8 {
            for (c, n) in cur.vars.iter_mut().zip(&next_state.vars) {
                *c = ValBound::widen(c, &c.join(n));
            }
            for (k, n) in &next_state.flagged_maps {
                let c = cur.flagged_maps.get_mut(k).unwrap();
                *c = ValBound::widen(c, &c.join(n));
            }
        } else {
            for (c, n) in cur.vars.iter_mut().zip(&next_state.vars) {
                *c = c.join(n);
            }
            for (k, n) in &next_state.flagged_maps {
                let c = cur.flagged_maps.get_mut(k).unwrap();
                *c = c.join(n);
            }
        }
    }

    // Did not verify a post-fixed point within budget: fall back soundly to Top!
    ModelBounds {
        vars: vec![ValBound::Top; program.vars.len()],
        consts: cur.consts,
        flagged_maps: map_flag_pairs.into_iter().map(|pair| (pair, ValBound::Top)).collect(),
    }
}

enum FlagStepSummary {
    Keep,
    Clear,
    Singleton(Expr),
    ClearPoint(Expr),
    SetPoint(Expr),
    Other,
}

fn flag_init_is_empty(binds: &super::super::BranchBindings, fv: VarId, shape: &VarShape) -> bool {
    let Some(rhs) = binds.get(fv) else { return false };
    match shape {
        VarShape::KeySetFlag { .. } => matches!(&*rhs.kind, ExprKind::SetEnum(es) if es.is_empty()),
        VarShape::BoolMapFlag { .. } => {
            matches!(&*rhs.kind, ExprKind::FnConstruct { body, .. } if matches!(&*body.kind, ExprKind::Bool(false)))
        }
        _ => false,
    }
}

fn classify_flag_step(fv: VarId, shape: &VarShape, rhs_opt: Option<&Expr>) -> FlagStepSummary {
    let Some(rhs) = rhs_opt else { return FlagStepSummary::Other };
    if variable(rhs, false) == Some(fv) {
        return FlagStepSummary::Keep;
    }
    match shape {
        VarShape::KeySetFlag { .. } => match &*rhs.kind {
            ExprKind::SetEnum(es) if es.is_empty() => FlagStepSummary::Clear,
            ExprKind::SetEnum(es) if es.len() == 1 => FlagStepSummary::Singleton(es[0].clone()),
            ExprKind::Builtin { op: B::Cup, args } if args.len() == 2 => {
                let single = if variable(&args[0], false) == Some(fv) {
                    Some(&args[1])
                } else if variable(&args[1], false) == Some(fv) {
                    Some(&args[0])
                } else {
                    None
                };
                if let Some(s) = single {
                    if let ExprKind::SetEnum(es) = &*s.kind {
                        if let [item] = es.as_slice() {
                            return FlagStepSummary::SetPoint(item.clone());
                        }
                    }
                }
                FlagStepSummary::Other
            }
            ExprKind::Builtin { op: B::SetMinus, args } if args.len() == 2 && variable(&args[0], false) == Some(fv) => {
                if let ExprKind::SetEnum(es) = &*args[1].kind {
                    if let [item] = es.as_slice() {
                        return FlagStepSummary::ClearPoint(item.clone());
                    }
                }
                FlagStepSummary::Other
            }
            _ => FlagStepSummary::Other,
        },
        VarShape::BoolMapFlag { .. } => match &*rhs.kind {
            ExprKind::FnConstruct { body, .. } if matches!(&*body.kind, ExprKind::Bool(false)) => FlagStepSummary::Clear,
            ExprKind::Except { base, updates } if variable(base, false) == Some(fv) && updates.len() == 1 => {
                let (path, val) = &updates[0];
                if let [ExceptKey::Index(args)] = path.as_slice() {
                    if let [idx_expr] = args.as_slice() {
                        return match &*val.kind {
                            ExprKind::Bool(false) => FlagStepSummary::ClearPoint(idx_expr.clone()),
                            ExprKind::Bool(true) => FlagStepSummary::SetPoint(idx_expr.clone()),
                            _ => FlagStepSummary::Other,
                        };
                    }
                }
                FlagStepSummary::Other
            }
            _ => FlagStepSummary::Other,
        },
        _ => FlagStepSummary::Other,
    }
}

fn match_single_map_except(mv: VarId, rhs: &Expr) -> Option<(Expr, Expr)> {
    let ExprKind::Except { base, updates } = &*rhs.kind else { return None };
    if variable(base, false) != Some(mv) || updates.len() != 1 {
        return None;
    }
    let (path, val) = &updates[0];
    let [ExceptKey::Index(args)] = path.as_slice() else { return None };
    let [idx] = args.as_slice() else { return None };
    Some((idx.clone(), val.clone()))
}

#[allow(clippy::too_many_arguments)] // shares the forward interval transfer context across Init/Next branches
fn branch_membership_bound(
    b: &Branch,
    v: VarId,
    primed: bool,
    model: &ModelBounds,
    locals: &LocalBounds,
    guards: Option<&BranchGuards<'_>>,
    domains: &Domains,
    fold_vars: &HashMap<LocalId, Option<Expr>>,
    groups: &[GroupInfo],
    shapes: &[VarShape],
    program: &Program,
    cfg: &Config,
) -> ValBound {
    let mut fallback = ValBound::Top;
    for term in &b.terms {
        if let ExprKind::Builtin { op, args } = &*term.kind {
            if args.len() == 2 && variable(&args[0], primed) == Some(v) {
                match op {
                    B::In => {
                        if exact_k_subset_family(program, cfg, &args[1], groups).is_some() {
                            return ValBound::Set(Box::new(ValBound::Top));
                        }
                        let eb = eval_elem_bound(&args[1], model, locals, guards, domains, fold_vars, groups, shapes, 0);
                        if !matches!(eb, ValBound::Top) {
                            return eb;
                        }
                    }
                    B::SubsetEq => {
                        let eb = eval_elem_bound(&args[1], model, locals, guards, domains, fold_vars, groups, shapes, 0);
                        if !matches!(eb, ValBound::Top) {
                            return ValBound::Set(Box::new(eb));
                        }
                        fallback = ValBound::Set(Box::new(ValBound::Top));
                    }
                    _ => {}
                }
            }
        }
    }
    fallback
}

#[allow(clippy::too_many_arguments)] // mutually recursive with eval_val_bound over the interval transfer context
pub(super) fn eval_elem_bound(
    set: &Expr,
    model: &ModelBounds,
    locals: &LocalBounds,
    guards: Option<&BranchGuards<'_>>,
    domains: &Domains,
    fold_vars: &HashMap<LocalId, Option<Expr>>,
    groups: &[GroupInfo],
    shapes: &[VarShape],
    depth: usize,
) -> ValBound {
    if depth >= 32 {
        return ValBound::Top;
    }
    match &*set.kind {
        ExprKind::SetEnum(es) => es.iter().fold(ValBound::Bottom, |acc, e| {
            acc.join(&eval_val_bound(e, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1))
        }),
        ExprKind::SetFilter { bound, .. } => {
            eval_elem_bound(&bound.set, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1)
        }
        ExprKind::SetMap { expr, bounds } => {
            let mut scope = locals.clone();
            for bnd in bounds {
                let eb = eval_elem_bound(&bnd.set, model, &scope, guards, domains, fold_vars, groups, shapes, depth + 1);
                for id in bnd.vars.locals() {
                    scope.insert(*id, if matches!(bnd.vars, BoundVars::Many(_)) { eb.clone() } else { ValBound::Top });
                }
            }
            eval_val_bound(expr, model, &scope, guards, domains, fold_vars, groups, shapes, depth + 1)
        }
        ExprKind::FnSet { range, .. } => {
            let elem = eval_elem_bound(range, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1);
            ValBound::Map(Box::new(elem))
        }
        ExprKind::RecordSet(fs) => ValBound::Record(
            fs.iter()
                .map(|(k, s)| (k.clone(), eval_elem_bound(s, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1)))
                .collect(),
        ),
        ExprKind::Builtin { op: B::Cup, args } if args.len() == 2 => eval_elem_bound(
            &args[0],
            model,
            locals,
            guards,
            domains,
            fold_vars,
            groups,
            shapes,
            depth + 1,
        )
        .join(&eval_elem_bound(&args[1], model, locals, guards, domains, fold_vars, groups, shapes, depth + 1)),
        ExprKind::Builtin { op: B::Cap | B::SetMinus, args } if args.len() == 2 => {
            eval_elem_bound(&args[0], model, locals, guards, domains, fold_vars, groups, shapes, depth + 1)
        }
        ExprKind::Builtin { op: B::DotDot, args } if args.len() == 2 => {
            let a = eval_val_bound(&args[0], model, locals, guards, domains, fold_vars, groups, shapes, depth + 1).as_int();
            let b = eval_val_bound(&args[1], model, locals, guards, domains, fold_vars, groups, shapes, depth + 1).as_int();
            match (a, b) {
                (IntBound::Bottom, _) | (_, IntBound::Bottom) => ValBound::Bottom,
                (IntBound::Interval { lo, .. }, IntBound::Interval { hi, .. }) => ValBound::Int(IntBound::Interval { lo, hi }),
                _ => ValBound::Top,
            }
        }
        ExprKind::Builtin { op: B::Nat, .. } => ValBound::Int(IntBound::Interval { lo: Some(0), hi: None }),
        ExprKind::Builtin { op: B::Int, .. } => ValBound::Int(IntBound::Interval { lo: None, hi: None }),
        _ => eval_val_bound(set, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1).set_elem(),
    }
}

#[allow(clippy::too_many_arguments)] // mutually recursive with eval_elem_bound over the interval transfer context
pub(super) fn eval_val_bound(
    e: &Expr,
    model: &ModelBounds,
    locals: &LocalBounds,
    guards: Option<&BranchGuards<'_>>,
    domains: &Domains,
    fold_vars: &HashMap<LocalId, Option<Expr>>,
    groups: &[GroupInfo],
    shapes: &[VarShape],
    depth: usize,
) -> ValBound {
    if depth >= 32 {
        return ValBound::Top;
    }
    let raw = match &*e.kind {
        ExprKind::Num(n) => ValBound::Int(IntBound::exact(*n)),
        ExprKind::Var(v) => model.vars[v.idx()].clone(),
        ExprKind::Local(l) => locals.get(l).cloned().unwrap_or(ValBound::Top),
        ExprKind::Const(cid) => model.consts.get(cid).cloned().unwrap_or(ValBound::Top),
        ExprKind::SetEnum(es) => ValBound::Set(Box::new(es.iter().fold(ValBound::Bottom, |acc, item| {
            acc.join(&eval_val_bound(item, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1))
        }))),
        ExprKind::SetFilter { bound, .. } => {
            eval_val_bound(&bound.set, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1)
        }
        ExprKind::SetMap { expr, bounds } => {
            let mut scope = locals.clone();
            for bnd in bounds {
                let eb = eval_elem_bound(&bnd.set, model, &scope, guards, domains, fold_vars, groups, shapes, depth + 1);
                for id in bnd.vars.locals() {
                    scope.insert(*id, if matches!(bnd.vars, BoundVars::Many(_)) { eb.clone() } else { ValBound::Top });
                }
            }
            ValBound::Set(Box::new(eval_val_bound(expr, model, &scope, guards, domains, fold_vars, groups, shapes, depth + 1)))
        }
        ExprKind::Record(fs) => ValBound::Record(
            fs.iter()
                .map(|(k, x)| (k.clone(), eval_val_bound(x, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1)))
                .collect(),
        ),
        ExprKind::Field { record, field } => {
            eval_val_bound(record, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1).field(field)
        }
        ExprKind::FnConstruct { bounds, body } if bounds.len() == 1 => {
            let mut scope = locals.clone();
            let eb = eval_elem_bound(&bounds[0].set, model, &scope, guards, domains, fold_vars, groups, shapes, depth + 1);
            for id in bounds[0].vars.locals() {
                scope.insert(*id, if matches!(bounds[0].vars, BoundVars::Many(_)) { eb.clone() } else { ValBound::Top });
            }
            ValBound::Map(Box::new(eval_val_bound(body, model, &scope, guards, domains, fold_vars, groups, shapes, depth + 1)))
        }
        ExprKind::FnApp { func, args } if args.len() == 1 => {
            let mut elem = eval_val_bound(func, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1).map_elem();
            if let Some(mv) = variable(func, false) {
                if let Some(g) = guards {
                    for fv in g.key_flags(&args[0]) {
                        if let Some(fb) = model.flagged_maps.get(&(mv, fv)) {
                            elem = elem.meet(fb);
                        }
                    }
                }
            }
            elem
        }
        ExprKind::Except { base, updates } => {
            let mut res = eval_val_bound(base, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1);
            for (path, rhs) in updates {
                let vd = eval_val_bound(rhs, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1);
                update_val_bound(&mut res, path, &vd);
            }
            res
        }
        ExprKind::If { then, els, .. } => eval_val_bound(then, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1)
            .join(&eval_val_bound(els, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1)),
        ExprKind::Choose { vars: BoundVars::Many(ids), set: Some(s), body } if ids.len() == 1 => {
            if fold_vars.contains_key(&ids[0]) {
                let mut scope = locals.clone();
                scope.insert(ids[0], ValBound::Top);
                let tb = eval_val_bound(body, model, &scope, guards, domains, fold_vars, groups, shapes, depth + 1).as_int();
                if let Some((lo, hi)) = tb.finite() {
                    if let Some(n) = set_max_card(s, domains, groups, shapes) {
                        let lo_sum = n.checked_mul(lo.min(0));
                        let hi_sum = n.checked_mul(hi.max(0));
                        ValBound::Int(IntBound::Interval { lo: lo_sum, hi: hi_sum })
                    } else {
                        ValBound::Int(IntBound::Interval { lo: None, hi: None })
                    }
                } else {
                    ValBound::Int(IntBound::Interval { lo: None, hi: None })
                }
            } else {
                eval_elem_bound(s, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1)
            }
        }
        ExprKind::Builtin { op, args } => match (op, args.as_slice()) {
            (B::Plus, [a, b]) => ValBound::Int(
                eval_val_bound(a, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1)
                    .as_int()
                    .add(eval_val_bound(b, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1).as_int()),
            ),
            (B::Minus, [a, b]) => ValBound::Int(
                eval_val_bound(a, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1)
                    .as_int()
                    .sub(eval_val_bound(b, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1).as_int()),
            ),
            (B::Mul, [a, b]) => ValBound::Int(
                eval_val_bound(a, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1)
                    .as_int()
                    .mul(eval_val_bound(b, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1).as_int()),
            ),
            (B::Neg, [a]) => {
                ValBound::Int(eval_val_bound(a, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1).as_int().neg())
            }
            (B::Div, [a, b]) => ValBound::Int(
                eval_val_bound(a, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1)
                    .as_int()
                    .div_tla(eval_val_bound(b, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1).as_int()),
            ),
            (B::Mod, [a, b]) => ValBound::Int(
                eval_val_bound(a, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1)
                    .as_int()
                    .rem_euclid(eval_val_bound(b, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1).as_int()),
            ),
            (B::Cardinality, [s]) => {
                if let Some(n) = set_max_card(s, domains, groups, shapes) {
                    ValBound::Int(IntBound::range(0, n))
                } else {
                    ValBound::Int(IntBound::Interval { lo: Some(0), hi: None })
                }
            }
            (B::Len, [_]) => ValBound::Int(IntBound::Interval { lo: Some(0), hi: None }),
            (B::Cup, [a, b]) => {
                let da = eval_val_bound(a, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1);
                let db = eval_val_bound(b, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1);
                match (da, db) {
                    (ValBound::Bottom, _) | (_, ValBound::Bottom) => ValBound::Bottom,
                    (ValBound::Set(ea), ValBound::Set(eb)) => ValBound::Set(Box::new(ea.join(&eb))),
                    _ => ValBound::Top,
                }
            }
            (B::Cap | B::SetMinus, [a, b]) => {
                let da = eval_val_bound(a, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1);
                let db = eval_val_bound(b, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1);
                if matches!(da, ValBound::Bottom) || matches!(db, ValBound::Bottom) {
                    ValBound::Bottom
                } else {
                    da
                }
            }
            (B::DotDot, [a, b]) => {
                let ba = eval_val_bound(a, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1).as_int();
                let bb = eval_val_bound(b, model, locals, guards, domains, fold_vars, groups, shapes, depth + 1).as_int();
                match (ba, bb) {
                    (IntBound::Bottom, _) | (_, IntBound::Bottom) => ValBound::Bottom,
                    (IntBound::Interval { lo, .. }, IntBound::Interval { hi, .. }) => {
                        ValBound::Set(Box::new(ValBound::Int(IntBound::Interval { lo, hi })))
                    }
                    _ => ValBound::Top,
                }
            }
            _ => ValBound::Top,
        },
        _ => ValBound::Top,
    };
    match guards {
        Some(g) => g.apply_refinements(e, raw),
        None => raw,
    }
}

fn update_val_bound(bound: &mut ValBound, path: &[ExceptKey], val: &ValBound) {
    let Some((key, rest)) = path.split_first() else {
        *bound = bound.join(val);
        return;
    };
    match (key, &mut *bound) {
        (ExceptKey::Index(_), ValBound::Map(elem)) => update_val_bound(elem, rest, val),
        (ExceptKey::Field(f), ValBound::Record(fs)) => {
            if let Some(fd) = fs.get_mut(f) {
                update_val_bound(fd, rest, val);
            }
        }
        (_, ValBound::Bottom) => {}
        _ => *bound = ValBound::Top,
    }
}

pub(super) fn set_max_card(s: &Expr, domains: &Domains, groups: &[GroupInfo], shapes: &[VarShape]) -> Option<i128> {
    if let Some(exact) = domains.exact_set(s) {
        return Some(exact.len() as i128);
    }
    if let Some(v) = variable(s, false) {
        if let VarShape::KeySetFlag { mask, .. } = shapes[v.idx()] {
            return Some(mask_key_count(groups, mask));
        }
    }
    match &*s.kind {
        ExprKind::SetEnum(es) => Some(es.len() as i128),
        ExprKind::SetFilter { bound, .. } => set_max_card(&bound.set, domains, groups, shapes),
        ExprKind::SetMap { bounds, .. } => {
            let mut prod: i128 = 1;
            for b in bounds {
                let c = set_max_card(&b.set, domains, groups, shapes)?;
                for _ in b.vars.locals() {
                    prod = prod.checked_mul(c)?;
                }
            }
            Some(prod)
        }
        ExprKind::Builtin { op: B::Cup, args } if args.len() == 2 => {
            set_max_card(&args[0], domains, groups, shapes)?.checked_add(set_max_card(&args[1], domains, groups, shapes)?)
        }
        ExprKind::Builtin { op: B::Cap | B::SetMinus, args } if args.len() == 2 => set_max_card(&args[0], domains, groups, shapes),
        _ => None,
    }
}

pub(super) fn mask_key_count(groups: &[GroupInfo], mask: GroupMask) -> i128 {
    groups.iter().enumerate().filter(|(gi, _)| (mask & (1 << gi)) != 0).map(|(_, g)| g.size as i128).sum()
}

/// Check that every partial sum of at most `n` summands in `[lo, hi]` fits in checked 32-bit signed integers.
pub(super) fn fold_partial_sums_fit_i32(bound: IntBound, key_count: i128) -> bool {
    let Some((lo, hi)) = bound.fits_i32() else { return false };
    let Some(max_pos) = key_count.checked_mul(hi.max(0)) else { return false };
    let Some(min_neg) = key_count.checked_mul(lo.min(0)) else { return false };
    min_neg >= I32_MIN && max_pos <= I32_MAX
}
