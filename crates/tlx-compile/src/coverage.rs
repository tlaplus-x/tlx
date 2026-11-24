//! Typed-coverage diagnostics over the IR: node counts (`Coverage`) and a
//! histogram of the boxed / interpreted node kinds (`TLX_COVERAGE`).

use std::collections::HashMap;
use std::fmt::Debug;

use tlx_layout::Shape;
use tlx_sema::hir;
use tlx_value::Value;

use crate::ir::{Expr, ExprKind, ShapeId, Stmt, Ty};
use crate::types::Typing;

/// Node counts of an IR function, for reporting typed coverage.
#[derive(Clone, Copy, Debug, Default)]
pub struct Coverage {
    pub nodes: usize,
    /// Nodes computing on boxed values (`Val`-typed, `ValOp`, `Apply`, ...).
    pub boxed: usize,
    /// Interpreter fallbacks.
    pub interp: usize,
}

impl Coverage {
    pub fn fully_typed(&self) -> bool {
        self.boxed == 0 && self.interp == 0
    }

    pub fn of_stmt(s: &Stmt) -> Coverage {
        let mut c = Coverage::default();
        c.stmt(s);
        c
    }

    fn stmt(&mut self, s: &Stmt) {
        if let Some(e) = s.expr() {
            self.expr(e);
        }
        s.for_each_sub_stmt(&mut |b| self.stmt(b));
    }

    pub fn expr(&mut self, e: &Expr) {
        self.nodes += 1;
        match node_class(e) {
            "interpreted" => {
                self.interp += 1;
                return;
            }
            "boxed" => self.boxed += 1,
            _ => {}
        }
        e.for_each_child(&mut |c| self.expr(c));
    }
}

/// Representation classification, independent of native backend support.
pub(crate) fn node_class(e: &Expr) -> &'static str {
    match &*e.kind {
        ExprKind::Interp { .. } => "interpreted",
        ExprKind::ValOp { .. } | ExprKind::Apply(..) | ExprKind::ValField(..) | ExprKind::Tuple(_) => "boxed",
        _ if e.ty == Ty::Val
            && !matches!(
                &*e.kind,
                ExprKind::Const(_)
                    | ExprKind::ConstElems { .. }
                    | ExprKind::IntRange(..)
                    | ExprKind::Subsets(_)
                    | ExprKind::OrderedSet { .. }
            ) =>
        {
            "boxed"
        }
        _ => "typed",
    }
}

/// Operation and argument representation shapes, without constant payloads.
pub(crate) fn operation(e: &Expr, typing: &Typing) -> (String, Vec<String>) {
    let kind = match &*e.kind {
        ExprKind::ValOp { op, .. } => format!("ValOp {}", op.name()),
        ExprKind::Call { func, .. } => {
            format!("Call {}", typing.funcs.get(*func as usize).map(|f| f.name.as_ref()).unwrap_or("<unknown function>"))
        }
        ExprKind::Interp { expr, .. } => format!("Interp {}", hir_kind(expr)),
        _ => variant_name(&e.kind),
    };
    let mut args = Vec::new();
    e.for_each_child(&mut |c| {
        let c = unconvert(c);
        args.push(match c.ty {
            Ty::Enc(s) => tlx_layout::decisions::summary(typing.shape(s)),
            t => format!("{t:?}"),
        });
    });
    (kind, args)
}

/// All expression nodes, by representation, kind and operand shapes.
pub(crate) fn node_histogram(s: &Stmt, out: &mut HashMap<String, usize>, typing: &Typing) {
    fn expr(e: &Expr, out: &mut HashMap<String, usize>, typing: &Typing) {
        let (kind, args) = operation(e, typing);
        *out.entry(format!("{} {kind} | {}", node_class(e), args.join(", "))).or_default() += 1;
        if node_class(e) != "interpreted" {
            e.for_each_child(&mut |c| expr(c, out, typing));
        }
    }
    if let Some(e) = s.expr() {
        expr(e, out, typing);
    }
    s.for_each_sub_stmt(&mut |b| node_histogram(b, out, typing));
}

/// Histogram of boxed / interpreter node kinds (for coverage analysis),
/// with shape details for function applications.
pub fn boxed_histogram_typed(s: &Stmt, out: &mut HashMap<String, usize>, typing: &Typing) {
    Histogram { typing, out }.stmt(s)
}

struct Histogram<'a> {
    typing: &'a Typing,
    out: &'a mut HashMap<String, usize>,
}

impl Histogram<'_> {
    fn stmt(&mut self, s: &Stmt) {
        if let Some(e) = s.expr() {
            self.expr(e);
        }
        s.for_each_sub_stmt(&mut |b| self.stmt(b));
    }

    fn expr(&mut self, e: &Expr) {
        if let Some(k) = self.key(e) {
            *self.out.entry(k).or_default() += 1;
        }
        if !matches!(&*e.kind, ExprKind::Interp { .. }) {
            e.for_each_child(&mut |c| self.expr(c));
        }
    }

    /// The histogram key of a boxed / interpreted node (None for others).
    fn key(&self, e: &Expr) -> Option<String> {
        Some(match &*e.kind {
            ExprKind::Interp { expr, .. } => format!("interp:{}", hir_kind(expr)),
            ExprKind::ValOp { op, args }
                if args.len() == 2 && matches!(op.name(), "\\in" | "\\notin" | "\\subseteq" | "\\cup" | "\\" | "\\cap") =>
            {
                format!("valop:{} {} , {}", op.name(), self.arg_desc(unconvert(&args[0])), self.arg_desc(unconvert(&args[1])))
            }
            ExprKind::ValOp { op, .. } => format!("valop:{}", op.name()),
            ExprKind::Apply(f, a) => match &*f.kind {
                ExprKind::Convert(x) if matches!(x.ty, Ty::Enc(_)) => {
                    let Ty::Enc(fs) = x.ty else { unreachable!() };
                    format!("apply on {} to {}", self.shape_desc(fs), self.arg_desc(unconvert(a)))
                }
                _ => format!("apply on {}", source(f)),
            },
            ExprKind::ValField(r, _) => format!("field on {}", source(r)),
            ExprKind::Tuple(_) => "tuple".into(),
            _ => return None,
        })
    }

    /// Representation and kind of an operand.
    fn arg_desc(&self, a: &Expr) -> String {
        let k = variant_name(&a.kind);
        match a.ty {
            Ty::Enc(sid) => format!("{}:{k}", self.shape_desc(sid)),
            t => format!("{t:?}:{k}"),
        }
    }

    /// Short description of an encoded shape.
    fn shape_desc(&self, sid: ShapeId) -> String {
        match self.typing.shape(sid) {
            Shape::Fcn { dom, range, .. } => {
                let dk = if dom.iter().all(|d| matches!(d, Value::Int(_))) {
                    "ints"
                } else if dom.iter().all(|d| matches!(d, Value::ModelValue(_) | Value::Str(_))) {
                    "atoms"
                } else {
                    "composite"
                };
                format!("Fcn[{dk}]->{}", variant_name(range))
            }
            other => variant_name(other),
        }
    }
}

/// A short description of a host region's root (`-stats`): the root
/// below its representation conversion and LETs, with its first operand,
/// or the kind and position of an interpreter fallback.
pub(crate) fn region_root(e: &Expr) -> String {
    let mut x = unconvert(e);
    while let ExprKind::Let { body, .. } = &*x.kind {
        x = unconvert(body);
    }
    if let ExprKind::Interp { expr, .. } = &*x.kind {
        return format!("interp {} @{}:{}", hir_kind(expr), expr.span.line, expr.span.col);
    }
    let mut first = None;
    x.for_each_child(&mut |c| {
        first.get_or_insert_with(|| crate::ir_fmt::label(unconvert(c)));
    });
    match first {
        Some(f) => format!("{} / {f}", crate::ir_fmt::label(x)),
        None => crate::ir_fmt::label(x),
    }
}

/// `x` without a representation conversion around it.
fn unconvert(x: &Expr) -> &Expr {
    match &*x.kind {
        ExprKind::Convert(y) => y,
        _ => x,
    }
}

/// Where a boxed operand comes from.
fn source(e: &Expr) -> String {
    match &*e.kind {
        ExprKind::Convert(x) => match x.ty {
            Ty::Enc(_) => "encoded (converted)".into(),
            t => format!("{t:?}"),
        },
        ExprKind::Temp(_) => "boxed temp".into(),
        ExprKind::Interp { .. } => "interp".into(),
        ExprKind::Apply(..) => "apply".into(),
        ExprKind::ValField(..) => "field".into(),
        ExprKind::Const(_) => "const".into(),
        _ => "other".into(),
    }
}

fn hir_kind(e: &hir::Expr) -> String {
    use tlx_sema::hir::ExprKind as H;
    match &*e.kind {
        H::Builtin { op, .. } => format!("builtin {}", op.name()),
        H::Apply { .. } => format!("apply-def @{}:{}", e.span.line, e.span.col),
        other => variant_name(other),
    }
}

/// The enum variant name of `x` (the first token of its `Debug` output).
fn variant_name(x: &impl Debug) -> String {
    format!("{x:?}").split([' ', '(', '{']).next().unwrap_or("?").to_string()
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;

    #[test]
    fn census_call_keeps_the_callee_for_joining_native_rejections() {
        let mut typing = Typing::new(Arc::new(tlx_layout::Layout::new(vec![])));
        typing.funcs.push(crate::ir::FnDef {
            name: "EventuallyRunnable".into(),
            params: vec![0],
            temps: vec![Ty::Int],
            ret: Ty::Bool,
            body: Expr::new(Ty::Bool, ExprKind::Const(Value::Bool(true))),
            budgeted: false,
        });
        let call = Expr::new(Ty::Bool, ExprKind::Call { func: 0, args: vec![Expr::new(Ty::Int, ExprKind::Const(Value::Int(0)))] });
        let (kind, args) = operation(&call, &typing);
        assert_eq!(kind, "Call EventuallyRunnable");
        assert_eq!(args, ["Int"]);
    }
}
