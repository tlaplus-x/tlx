//! Replace record reads by explicit phase/data inputs. No raw record reaches C.
use super::super::super::variable;
use super::{Emitter, Reads};
use crate::{builtins::Builtin as B, hir::*, visit};

impl Emitter<'_, '_> {
    pub(super) fn leaf(&mut self, e: &Expr, kind: &str, actor: Option<LocalId>, reads: &mut Reads) -> Option<String> {
        let mut next = max_local(e).checked_add(1)?;
        let mut holes = vec![];
        let masked = self.mask(e, kind, actor, reads, &mut next, &mut holes)?;
        let id = self.atoms.len();
        self.atoms.push(format!("{kind} HIR: {masked:#?}\nRecord holes: {holes:#?}"));
        Some(match kind {
            "initial" => format!("(sem.initial {id} c choice.2)"),
            "observe" => format!("(sem.observe {id} c p input)"),
            _ => format!("(sem.{kind} {id} c d choice.2 p input)"),
        })
    }

    fn mask(
        &self,
        e: &Expr,
        kind: &str,
        actor: Option<LocalId>,
        reads: &mut Reads,
        next: &mut u32,
        holes: &mut Vec<String>,
    ) -> Option<Expr> {
        if let ExprKind::Builtin { op: B::In, args } = &*e.kind {
            if args.len() == 2
                && variable(&args[0], false) == Some(self.a.var)
                && self.a.domains.belongs(&self.a.domains.vars[self.a.var.idx()], &args[1])
            {
                return Some(Expr::new(ExprKind::Bool(true), e.span));
            }
        }
        if let ExprKind::Field { record, field } = &*e.kind {
            let index = if self.a.keys.is_none() && variable(record, false) == Some(self.a.var) {
                Some(None)
            } else if let ExprKind::FnApp { func, args } = &*record.kind {
                if variable(func, false) == Some(self.a.var) && args.len() == 1 {
                    Some(Some(&args[0]))
                } else {
                    None
                }
            } else {
                None
            };
            if let Some(index) = index {
                if kind == "initial" {
                    return None;
                }
                let actor_read = kind != "observe"
                    && (self.a.keys.is_none() || index.is_some_and(|i| matches!(&*i.kind, ExprKind::Local(l) if Some(*l) == actor)));
                let slot = if field.as_ref() == self.a.control {
                    "phase".to_owned()
                } else {
                    let f = self.fields.iter().position(|f| f == field)?;
                    if actor_read {
                        reads.actor[f] = true;
                    } else {
                        reads.global[f] = true;
                    }
                    format!("data field {f}")
                };
                let index = if let Some(e) = index { Some(self.mask(e, kind, actor, reads, next, holes)?) } else { None };
                let local = LocalId(*next);
                *next = next.checked_add(1)?;
                holes.push(format!("{local:?} = {slot}, source key {index:#?}; actor-relative={actor_read}"));
                return Some(Expr::new(ExprKind::Local(local), e.span));
            }
        }
        if matches!(&*e.kind, ExprKind::Var(v) if *v == self.a.var)
            || matches!(&*e.kind, ExprKind::Builtin { op: B::Prime, .. } if mentions(e, self.a.var))
        {
            return None;
        }
        let mut result = e.clone();
        let mut valid = true;
        visit::children_mut(&mut result, &mut |child| {
            if let Some(e) = self.mask(child, kind, actor, reads, next, holes) {
                *child = e;
            } else {
                valid = false;
            }
        });
        valid.then_some(result)
    }
}

pub(super) fn mentions(e: &Expr, var: VarId) -> bool {
    if matches!(&*e.kind, ExprKind::Var(v) if *v == var) {
        return true;
    }
    let mut found = false;
    visit::children(e, &mut |e| found |= mentions(e, var));
    found
}

// Bound declarations, even unused ones, must not capture inserted inputs.
fn max_local(e: &Expr) -> u32 {
    let mut max = 0;
    let mut ids = |ids: &[LocalId]| {
        for id in ids {
            max = max.max(id.0);
        }
    };
    match &*e.kind {
        ExprKind::Local(id) => ids(&[*id]),
        ExprKind::Quant { bounds, .. } | ExprKind::FnConstruct { bounds, .. } | ExprKind::SetMap { bounds, .. } => {
            for b in bounds {
                ids(b.vars.locals());
            }
        }
        ExprKind::SetFilter { bound, .. } => ids(bound.vars.locals()),
        ExprKind::Choose { vars, .. } => ids(vars.locals()),
        ExprKind::Lambda { params, .. } => ids(params),
        ExprKind::QuantUnbounded { vars, .. } | ExprKind::TemporalQuant { vars, .. } => ids(vars),
        _ => {}
    }
    visit::children(e, &mut |e| max = max.max(max_local(e)));
    max
}
