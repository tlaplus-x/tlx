//! Whether the compiled tier's layout can ever miss: a conservative static
//! closure analysis of `Init`, `Next` and the materialized definitions
//! (design.md §6.5.3, scale.md §6).
//!
//! The driver keeps the layout-miss archive only while a later value can fail
//! `Layout::encode_state`. When this analysis proves that every value an
//! assignment can produce fits its slot, and so does every materialized
//! definition, the archive is pure overhead and is elided.
//!
//! The analysis is an abstract interpretation over HIR whose value domain is
//! [`Shape`]: a state variable's abstract value is its layout slot (an
//! over-approximation of the values reachable states hold, the induction
//! hypothesis), a constant's is `Shape::of` its value, and any construct this
//! analysis does not understand becomes `Shape::Dyn` (top). For each
//! assignment `x = e` (Init) or `x' = e` (Next) the shape of `e` must be
//! accepted by `x`'s slot ([`Shape::accepts_shape`]); `x' \in S` and
//! `x' \subseteq S` are checked against `S`'s element and subset shapes.
//! Anything that leaves a value unproven — an unsupported operator, a
//! recursive definition, a `Dyn` operand — keeps the archive.
//!
//! [`VShape`] additionally tracks `lo..hi` interval *values*
//! (`Value::Interval`): such a value can only live in a `Dyn`/`Ref` slot, so
//! it must not be conflated with `Shape::Set` (shape inference maps it to
//! `Dyn`), while its integer elements and set view are still exact and useful
//! for `\in`/`\subseteq` assignments and function domains.
//!
//! The traversal mirrors `tlx_eval::enumerate`: only the positions that can
//! assign a state variable are followed as actions (`\land`, `\lor`, `=>`'s
//! consequent, `\E`/`\A` bodies, `IF`/`CASE` branches, `LET` bodies, expanded
//! definition calls, `UNCHANGED`, `\cdot` and the action operators), and the
//! interpreter's expansion rules decide whether a definition is followed or
//! evaluated as a test (a test cannot assign). Analyzing every branch
//! (rather than only a condition's chosen one) is sound: a successor that is
//! not generated is also not missed.
//!
//! A proof failure is always safe: it only restores the archive. The
//! `TLX_PARANOID` assertion in the driver checks a proof against the running
//! search.
//!
//! The abstract domain and the proof driver live here; `refine` owns the
//! abstract environments and guard narrowing, `action` the action-position
//! traversal, and `expr` the value-position transfer functions.

mod action;
mod expr;
mod refine;
#[cfg(test)]
mod tests;

use tlx_eval::env::{Env, OpVal};
use tlx_eval::model::InterpModel;
use tlx_layout::Shape;
use tlx_sema::hir::{DefId, DefKind, Expr, LocalId};

/// Whether a run with this layout can never raise a layout miss.
///
/// `Err` names the first construct that could not be proven closed (the run
/// then keeps its archive). `vars` are the layout slots in variable order and
/// `defs` the materialized definitions with their layout shapes: the shapes
/// the encoded model actually uses (`Speculation::layout_shapes`).
pub(super) fn layout_is_closed(base: &InterpModel, vars: &[Shape], defs: &[(DefId, Shape)]) -> Result<(), String> {
    // Fast path: when every variable and materialized definition slot is
    // unbounded (`Dyn` / `Ref`), no assignment or definition can raise a layout
    // miss regardless of the expressions in `Init` or `Next`.
    if vars.iter().all(Shape::is_unbounded) && defs.iter().all(|(_, s)| s.is_unbounded()) {
        return Ok(());
    }
    let mut a = Analyzer::new(base, vars.to_vec(), defs.to_vec());
    a.check_init();
    if a.reason.is_none() {
        a.check_actions();
    }
    if a.reason.is_none() {
        a.check_defs();
    }
    match a.reason {
        Some(why) => Err(why),
        None => Ok(()),
    }
}

/// Most finite keys a function-constructor domain may have before the analysis
/// treats it as a map instead of enumerating its keys.
const MAX_EXACT_DOMAIN: i64 = 4096;
/// Maximum expression nodes one analysis may visit. The traversal is linear in
/// the (inlined) model; this only bounds pathological nesting, where it
/// forfeits the proof (the archive is kept).
const BUDGET: usize = 500_000;
/// Maximum inlining depth (definitions, binders, function constructors).
const DEPTH: usize = 96;

/// An abstract value: a value shape, or an integer-interval value
/// (`Value::Interval`, which only a `Dyn`/`Ref` slot can hold).
#[derive(Clone)]
enum VShape {
    Shape(Shape),
    Interval { lo: i64, hi: i64 },
}

impl VShape {
    fn as_shape(&self) -> Shape {
        match self {
            VShape::Shape(s) => s.clone(),
            VShape::Interval { .. } => Shape::Dyn,
        }
    }

    /// The shape its elements take, when the value is a set or an interval.
    fn elem(&self) -> Shape {
        match self {
            VShape::Shape(Shape::Set { elem, .. }) => (**elem).clone(),
            VShape::Shape(Shape::Never) => Shape::Never,
            VShape::Interval { lo, hi } => {
                if lo <= hi {
                    Shape::Int { lo: *lo, hi: *hi }
                } else {
                    Shape::Never
                }
            }
            _ => Shape::Dyn,
        }
    }

    /// The set view `(element shape, max cardinality)`, when the value is a
    /// set or an interval.
    fn as_set(&self) -> Option<(Shape, usize)> {
        match self {
            VShape::Shape(Shape::Set { elem, max_card }) => Some(((**elem).clone(), *max_card)),
            VShape::Interval { lo, hi } => {
                if hi < lo {
                    return Some((Shape::Never, 0));
                }
                let card = usize::try_from((*hi as i128) - (*lo as i128) + 1).ok()?;
                Some((Shape::Int { lo: *lo, hi: *hi }, card))
            }
            _ => None,
        }
    }

    fn join(&self, other: &VShape) -> VShape {
        match (self, other) {
            (VShape::Shape(Shape::Never), x) | (x, VShape::Shape(Shape::Never)) => x.clone(),
            (VShape::Shape(a), VShape::Shape(b)) => VShape::Shape(a.join(b)),
            // Two interval values are both intervals at runtime, but no `Shape`
            // describes interval values; any other mix is beyond the domain.
            _ => VShape::Shape(Shape::Dyn),
        }
    }
}

impl From<Shape> for VShape {
    fn from(s: Shape) -> VShape {
        VShape::Shape(s)
    }
}

/// An abstract local binding: a value shape, a call-by-name argument (its
/// expression may still assign when used in action position), or an operator
/// value.
#[derive(Clone)]
enum Abs {
    Val(VShape),
    Thunk(Expr, Env),
    Op(OpVal),
}

struct Analyzer<'a> {
    base: &'a InterpModel,
    /// The abstract value of each state variable: its layout slot (an
    /// over-approximation by induction over the reachable states).
    vars: Vec<Shape>,
    /// Materialized definitions and their layout slots.
    defs: Vec<(DefId, Shape)>,
    /// Analyzing `Init` (assignments are unprimed) instead of an action.
    init: bool,
    /// The value of `@` inside the update of an `EXCEPT`.
    at: Option<Shape>,
    /// Abstract bindings, innermost scope last.
    scopes: Vec<Vec<(LocalId, Abs)>>,
    /// Definitions currently being inlined (recursion).
    active: Vec<DefId>,
    /// Remaining expression nodes this analysis may visit.
    budget: usize,
    /// Inlining depth.
    depth: usize,
    /// Definition/local-following depth (0-ary definition chains, by-name
    /// bindings, function-constructor resolution).
    follow: usize,
    /// Path refinements from already-tested guards (`x < 10` narrows `x` for
    /// the conjuncts to its right and for the branches the guard selects).
    refine: Vec<Refine>,
    /// The first construct that cannot be proven closed.
    reason: Option<String>,
}

/// A guard-derived narrowing of one variable's values on the current path.
#[derive(Clone)]
struct Refine {
    var: usize,
    /// The guard reads the variable primed (`x'`).
    primed: bool,
    shape: Shape,
}

impl<'a> Analyzer<'a> {
    fn new(base: &'a InterpModel, vars: Vec<Shape>, defs: Vec<(DefId, Shape)>) -> Analyzer<'a> {
        Analyzer {
            base,
            vars,
            defs,
            init: false,
            at: None,
            scopes: Vec::new(),
            active: Vec::new(),
            refine: Vec::new(),
            budget: BUDGET,
            depth: 0,
            follow: 0,
            reason: None,
        }
    }

    // ------------------------------------------------------------------
    // proof driver

    fn fail(&mut self, why: impl Into<String>) {
        if self.reason.is_none() {
            self.reason = Some(why.into());
        }
    }

    /// Charge one expression node; false (and a failure) when the budget is
    /// exhausted or the proof already failed.
    fn spend(&mut self) -> bool {
        if self.reason.is_some() {
            return false;
        }
        if self.budget == 0 {
            self.reason = Some("the closed-layout analysis budget is exhausted".into());
            return false;
        }
        self.budget -= 1;
        true
    }

    fn check_init(&mut self) {
        let init = self.base.init_expr().clone();
        self.init = true;
        self.action(&init, &Env::default());
        self.init = false;
    }

    fn check_actions(&mut self) {
        let actions = self.base.actions().iter().map(|a| (a.name.to_string(), a.expr.clone(), a.env.clone())).collect::<Vec<_>>();
        for (i, (name, expr, env)) in actions.into_iter().enumerate() {
            if self.reason.is_some() {
                return;
            }
            self.init = false;
            self.action(&expr, &env);
            if let Some(why) = self.reason.take() {
                self.reason = Some(format!("action {} (#{i}): {why}", name));
            }
        }
    }

    fn check_defs(&mut self) {
        let defs = self.defs.clone();
        for (orig_d, slot) in defs {
            if self.reason.is_some() {
                return;
            }
            if slot.is_unbounded() {
                continue;
            }
            let d = self.base.ip.redirect_def(orig_d);
            let def = &self.base.ip.prog.defs[d.idx()];
            if def.builtin.is_some() || self.base.ip.has_def_value(orig_d) || self.base.ip.has_def_value(d) {
                self.fail(format!("definition {} is evaluated from the configuration", def.name));
                continue;
            }
            let body = match &def.kind {
                DefKind::Op(body) if def.params.is_empty() => body.clone(),
                _ => {
                    self.fail(format!("definition {} cannot be analyzed as a 0-ary operator", def.name));
                    continue;
                }
            };
            let shape = self.value(&body, &Env::default()).as_shape();
            if !slot.accepts_shape(&shape) {
                self.fail(format!("materialized definition {} can produce a value outside its shape", def.name));
            }
        }
    }
}
