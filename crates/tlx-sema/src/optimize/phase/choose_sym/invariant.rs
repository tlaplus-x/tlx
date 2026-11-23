//! Inductive choice-irrelevance invariant synthesis (`InvPlan`), rule-IR step/init kinds,
//! and branch empty/uniform guard extraction.

use super::super::variable;
use super::domain_infer::VarShape;
use super::mentions_local;
use super::pure_expr::AuxScope;
use super::{Emitter, GroupMask, InitCase, KeyRef, StepCase};
use crate::{builtins::Builtin as B, hir::*};

#[derive(Clone, Debug)]
pub(super) enum FlagInitKind {
    Empty,
    Singleton { mask: GroupMask, key_idx: usize },
    All { mask: GroupMask },
    Cardinal { mask: GroupMask, card: usize },
}

impl FlagInitKind {
    pub(super) fn lean(&self, e: &Emitter<'_>) -> String {
        match self {
            Self::Empty => "FlagInit.empty".into(),
            Self::Singleton { mask, key_idx } => format!("(FlagInit.singleton {} {key_idx})", e.mask_lean(*mask)),
            Self::All { mask } => format!("(FlagInit.all {})", e.mask_lean(*mask)),
            Self::Cardinal { mask, card } => format!("(FlagInit.cardinal {} {card})", e.mask_lean(*mask)),
        }
    }
}

#[derive(Clone, Debug)]
pub(super) enum MsgInitKind {
    Empty,
    ComprehensionConst { mask: GroupMask, meta_id: usize, const_id: usize },
    ComprehensionCore { mask: GroupMask, meta_id: usize, core_id: usize },
}

impl MsgInitKind {
    pub(super) fn lean(&self, e: &Emitter<'_>) -> String {
        match self {
            Self::Empty => "MsgInit.empty".into(),
            Self::ComprehensionConst { mask, meta_id, const_id } => {
                format!("(MsgInit.comprehensionConst {} {meta_id} {const_id})", e.mask_lean(*mask))
            }
            Self::ComprehensionCore { mask, meta_id, core_id } => {
                format!("(MsgInit.comprehensionCore {} {meta_id} {core_id})", e.mask_lean(*mask))
            }
        }
    }
}

#[derive(Clone, Debug)]
pub(super) enum FlagStepKind {
    Keep,
    Clear,
    Singleton { mask: GroupMask, target: KeyRef },
    ClearPoint { target: KeyRef },
    SetPoint { mask: GroupMask, target: KeyRef },
    GeneralAll { mask: GroupMask, pred: String },
    Cardinal { mask: GroupMask, card: usize },
}

impl FlagStepKind {
    pub(super) fn lean(&self, e: &Emitter<'_>) -> String {
        match self {
            Self::Keep => "FlagStep.keep".into(),
            Self::Clear => "FlagStep.clear".into(),
            Self::Singleton { mask, target } => format!("(FlagStep.singleton {} {})", e.mask_lean(*mask), target.lean()),
            Self::ClearPoint { target } => format!("(FlagStep.clearPoint {})", target.lean()),
            Self::SetPoint { mask, target } => format!("(FlagStep.setPoint {} {})", e.mask_lean(*mask), target.lean()),
            Self::GeneralAll { mask, pred } => format!("(FlagStep.generalAll {} {pred})", e.mask_lean(*mask)),
            Self::Cardinal { mask, card } => format!("(FlagStep.cardinal {} {card})", e.mask_lean(*mask)),
        }
    }
}

#[derive(Clone, Debug)]
pub(super) enum MsgStepKind {
    Keep,
    Clear,
    ComprehensionAll { mask: GroupMask, meta_expr: String, val_expr: String },
    AddConst { mask: GroupMask, target: KeyRef, meta_expr: String, const_id: usize },
    AddWhenEmpty { mask: GroupMask, target: KeyRef, meta_expr: String, val_expr: String },
    AddMatchingGuard { mask: GroupMask, target: KeyRef, meta_expr: String, ug_idx: usize },
    AddGeneral { mask: GroupMask, target: KeyRef, meta_expr: String, val_expr: String },
}

impl MsgStepKind {
    pub(super) fn lean(&self, e: &Emitter<'_>) -> String {
        match self {
            Self::Keep => "MsgStep.keep".into(),
            Self::Clear => "MsgStep.clear".into(),
            Self::ComprehensionAll { mask, meta_expr, val_expr } => {
                format!("(MsgStep.comprehensionAll {} {meta_expr} {val_expr})", e.mask_lean(*mask))
            }
            Self::AddConst { mask, target, meta_expr, const_id } => {
                format!("(MsgStep.addConst {} {} {meta_expr} {const_id})", e.mask_lean(*mask), target.lean())
            }
            Self::AddWhenEmpty { mask, target, meta_expr, val_expr } => {
                format!("(MsgStep.addWhenEmpty {} {} {meta_expr} {val_expr})", e.mask_lean(*mask), target.lean())
            }
            Self::AddMatchingGuard { mask, target, meta_expr, ug_idx } => {
                format!("(MsgStep.addMatchingGuard {} {} {meta_expr} {ug_idx})", e.mask_lean(*mask), target.lean())
            }
            Self::AddGeneral { mask, target, meta_expr, val_expr } => {
                format!("(MsgStep.addGeneral {} {} {meta_expr} {val_expr})", e.mask_lean(*mask), target.lean())
            }
        }
    }
}

pub(super) struct InvPlan {
    pub(super) at_most_one_flags: Vec<(usize, GroupMask)>,
    pub(super) const_val_msgs: Vec<(usize, usize)>,
    pub(super) uniform_val_msgs: Vec<usize>,
}

impl Emitter<'_> {
    pub(super) fn inspect_uniform_guard(
        &mut self,
        gexpr: &Expr,
        keys: &[(LocalId, GroupMask)],
        aux: &AuxScope,
        uniform_guards: &mut Vec<(usize, String)>,
    ) {
        let ExprKind::Quant { kind: QuantKind::Forall, bounds, body } = &*gexpr.kind else { return };
        let [Bound { vars: BoundVars::Many(ids), set }] = bounds.as_slice() else { return };
        let [m_id] = ids.as_slice() else { return };
        let Some(mv) = variable(set, false) else { return };
        let VarShape::MsgSet { msg_id, val_field: Some(ref vf), .. } = self.shapes[mv.idx()].clone() else { return };
        let ExprKind::Builtin { op: B::Eq, args } = &*body.kind else { return };
        let [lhs, rhs] = args.as_slice() else { return };
        let target_opt = if matches!(&*lhs.kind, ExprKind::Field { record, field } if field == vf && matches!(&*record.kind, ExprKind::Local(l) if l == m_id))
            && !mentions_local(rhs, *m_id)
        {
            Some(rhs)
        } else if matches!(&*rhs.kind, ExprKind::Field { record, field } if field == vf && matches!(&*record.kind, ExprKind::Local(l) if l == m_id))
            && !mentions_local(lhs, *m_id)
        {
            Some(lhs)
        } else {
            None
        };
        if let Some(texpr) = target_opt {
            if let Some(vp) = self.pure_expr(texpr, keys, aux) {
                uniform_guards.push((msg_id, vp));
            }
        }
    }

    pub(super) fn synthesize_inv_plan(&self, init_cases: &[InitCase], step_cases: &[StepCase]) -> Option<InvPlan> {
        let mut at_most_one_flags = Vec::new();
        for &(fid, fmask) in &self.req_at_most_one_flags {
            let init_ok = init_cases.iter().all(|ic| match ic.flag_inits[fid] {
                FlagInitKind::Empty => true,
                FlagInitKind::Singleton { mask: smask, .. } => (smask & !fmask) == 0,
                _ => false,
            });
            let step_ok = step_cases.iter().all(|sc| match sc.flag_steps[fid] {
                FlagStepKind::Keep | FlagStepKind::Clear | FlagStepKind::ClearPoint { .. } => true,
                FlagStepKind::Singleton { mask: smask, .. } => (smask & !fmask) == 0,
                FlagStepKind::SetPoint { mask: smask, .. } => {
                    (smask & !fmask) == 0 && sc.empty_flag_guards.iter().any(|&(efid, gmask)| efid == fid && (fmask & !gmask) == 0)
                }
                _ => false,
            });
            if !init_ok || !step_ok {
                return None;
            }
            at_most_one_flags.push((fid, fmask));
        }

        let mut const_val_msgs = Vec::new();
        let mut uniform_val_msgs = Vec::new();
        for &mid in &self.req_uniform_msgs {
            let mut candidate_cid: Option<usize> = None;
            let mut const_possible = true;
            for ic in init_cases {
                match ic.msg_inits[mid] {
                    MsgInitKind::Empty => {}
                    MsgInitKind::ComprehensionConst { const_id, .. } => match candidate_cid {
                        None => candidate_cid = Some(const_id),
                        Some(c) if c == const_id => {}
                        Some(_) => const_possible = false,
                    },
                    MsgInitKind::ComprehensionCore { .. } => const_possible = false,
                }
            }
            for sc in step_cases {
                match sc.msg_steps[mid] {
                    MsgStepKind::Keep | MsgStepKind::Clear => {}
                    MsgStepKind::AddConst { const_id, .. } => match candidate_cid {
                        None => candidate_cid = Some(const_id),
                        Some(c) if c == const_id => {}
                        Some(_) => const_possible = false,
                    },
                    _ => const_possible = false,
                }
            }
            if const_possible {
                const_val_msgs.push((mid, candidate_cid.unwrap_or(0)));
                continue;
            }

            let init_ok = init_cases.iter().all(|ic| {
                matches!(
                    ic.msg_inits[mid],
                    MsgInitKind::Empty | MsgInitKind::ComprehensionConst { .. } | MsgInitKind::ComprehensionCore { .. }
                )
            });
            let step_ok = step_cases.iter().all(|sc| match sc.msg_steps[mid] {
                MsgStepKind::Keep | MsgStepKind::Clear | MsgStepKind::ComprehensionAll { .. } => true,
                MsgStepKind::AddWhenEmpty { .. } => sc.empty_msg_guards.contains(&mid),
                MsgStepKind::AddMatchingGuard { ug_idx, .. } => {
                    sc.choices.is_empty() && sc.uniform_guards.get(ug_idx).is_some_and(|(m, _)| *m == mid)
                }
                _ => false,
            });
            if !init_ok || !step_ok {
                return None;
            }
            uniform_val_msgs.push(mid);
        }

        Some(InvPlan { at_most_one_flags, const_val_msgs, uniform_val_msgs })
    }
}

pub(super) fn record_empty_guards(
    pt: &str,
    num_groups: usize,
    empty_flag_guards: &mut Vec<(usize, GroupMask)>,
    empty_msg_guards: &mut Vec<usize>,
) {
    if let Some(rest) = pt.strip_prefix("(PureTest.msgEmpty ⟨") {
        if let Some((num_str, _)) = rest.split_once(',') {
            if let Ok(mid) = num_str.trim().parse::<usize>() {
                empty_msg_guards.push(mid);
            }
        }
    }
    if let Some(rest) = pt.strip_prefix("(PureTest.all ") {
        if let Some((mask_str, tail)) = rest.split_once(" (PureTest.neg (PureTest.flag ⟨") {
            if let Some((fid_str, end)) = tail.split_once(", by decide⟩ (KeyRef.bound 0))))") {
                if end.is_empty() {
                    if let (Some(gmask), Ok(fid)) = (parse_mask_lean(mask_str, num_groups), fid_str.trim().parse::<usize>()) {
                        empty_flag_guards.push((fid, gmask));
                    }
                }
            }
        }
    }
}

fn parse_mask_lean(s: &str, num_groups: usize) -> Option<GroupMask> {
    let all_mask: GroupMask = (1u16 << num_groups) - 1;
    if s == "(fun _ => true)" {
        return Some(all_mask);
    }
    if s == "(fun _ => false)" {
        return Some(0);
    }
    let mut mask: GroupMask = 0;
    for part in s.split("| ") {
        if let Some((idx_s, _)) = part.split_once(" => true") {
            if let Ok(gi) = idx_s.trim().parse::<usize>() {
                if gi < num_groups {
                    mask |= 1 << gi;
                }
            }
        }
    }
    (mask != 0).then_some(mask)
}
