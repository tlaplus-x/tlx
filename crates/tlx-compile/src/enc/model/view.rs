//! A VIEW computed into the encoding of the VIEW definition's shape.

use std::sync::Arc;

use tlx_eval::InterpModel;
use tlx_layout::{Layout, Shape};
use tlx_native::native::{NativeLib, OK};
use tlx_sema::hir::DefId;

use crate::enc::native;
use crate::exec::fast;
use crate::ir::{ActionFn, Stmt, Ty};
use crate::lower::Lowerer;
use crate::settings::Settings;
use crate::types::Typing;

/// A VIEW computed into the encoding of the VIEW definition's shape.
///
/// The VIEW's value is the extra variable of an extended layout (the state
/// variables followed by it): a single action, lowered and generated
/// natively like any other, assigns it and emits the extended state.
pub(super) struct View {
    /// Index of the VIEW definition in `def_shapes` (where its misses are
    /// recorded).
    /// None for an anonymous expression whose shape follows from the layout.
    pub(super) def: Option<usize>,
    /// Typing of the extended layout (whose last variable is the VIEW's
    /// value).
    pub(super) typing: Typing,
    pub(super) action: ActionFn,
    pub(super) native: Option<NativeLib>,
    /// The VIEW's value compiled for the closure executor (None: not covered).
    pub(super) fast: Option<(fast::Program, fast::ExprProg)>,
    /// Words of the VIEW's value in the extended state.
    pub(super) at: std::ops::Range<usize>,
    /// Generated projections canonicalize their result, not the full state.
    pub(super) orbit: Option<ProjectionOrbit>,
}

pub(super) struct ProjectionOrbit {
    group: Vec<Vec<tlx_layout::permute::PermPlan>>,
    order: Vec<usize>,
    layout: Layout,
}

impl ProjectionOrbit {
    fn compile(base: &InterpModel, shape: &Shape, notes: &mut Vec<String>) -> Option<Self> {
        let Shape::Tuple(parts) = shape else { return None };
        let fl = tlx_layout::pack::FieldLayout::of_shape(shape)?;
        let mut units = Vec::new();
        for group in fl.word_groups() {
            match group {
                tlx_layout::pack::FieldGroup::Word { index, .. } => units.push(parts[*index].clone()),
                tlx_layout::pack::FieldGroup::Packed { fields, .. } => {
                    units.push(Shape::Tuple(fields.iter().map(|&(i, _)| parts[i].clone()).collect()));
                }
            }
        }
        let layout = Layout::new(units);
        debug_assert_eq!(layout.words, fl.words);
        // Keep the existing by-value path for store-backed shapes. This
        // path compares only canonical encodings, never handle identities.
        if super::SemFp::of(&layout, None).is_some() {
            return None;
        }
        let group = super::symmetry::compile_symmetry(base, &layout, notes)?;
        let order = super::symmetry::symmetry_order(&layout);
        Some(Self { group, order, layout })
    }

    pub(super) fn fingerprint(&self, words: &[u64]) -> u64 {
        assert_eq!(words.len(), self.layout.words);
        super::symmetry::orbit_fp(&self.group, &self.order, &self.layout, words, None)
    }
}

impl View {
    pub(super) fn result_node(&self) -> &tlx_layout::LayoutNode {
        self.typing.layout.node(self.typing.layout.vars.len() - 1)
    }
    pub(super) fn compile(
        base: &InterpModel,
        layout: &Layout,
        def_shapes: &[(DefId, Shape)],
        settings: &Settings,
        notes: &mut Vec<String>,
    ) -> Option<View> {
        // A structural order plan replaces its identity VIEW at the value
        // fingerprint boundary. Lowering that placeholder would silently
        // restore the full graph. Use the existing decoded-value path.
        if base.ordered_projection().is_some() {
            notes.push("view: structural order projection on decoded values".into());
            return None;
        }
        if base.has_projected_symmetry() && settings.escape {
            return None;
        }
        let named = crate::enc::speculate::view_def(base);
        let def = named.and_then(|d| def_shapes.iter().position(|(x, _)| *x == d));
        let mut shape = match (named, def) {
            (Some(_), Some(i)) => def_shapes[i].1.clone(),
            (None, _) => super::view_shape::infer(base.view_expr()?, layout)?,
            _ => return None,
        };
        // Components of a tuple VIEW that are state variables: in their
        // layout encoding (plain copies, and they always fit).
        if let (Some(es), Shape::Tuple(parts)) = (named.and_then(|d| crate::enc::speculate::view_tuple(base, d)), &shape) {
            if es.len() == parts.len() {
                let parts = es.iter().zip(parts.iter()).map(|(e, s)| match &*e.kind {
                    tlx_sema::hir::ExprKind::Var(v) => layout.vars[v.idx()].clone(),
                    _ => s.clone(),
                });
                shape = Shape::Tuple(parts.collect());
            }
        }
        let mut def_shapes = def_shapes.to_vec();
        if let Some(i) = def {
            def_shapes[i].1 = shape.clone();
        }
        let orbit = if base.has_projected_symmetry() { Some(ProjectionOrbit::compile(base, &shape, notes)?) } else { None };
        let mut vars = layout.vars.clone();
        vars.push(shape.clone());
        let ext = Arc::new(Layout::new(vars));
        let var = layout.vars.len();
        let at = ext.offsets[var]..ext.words;
        let ip = base.ip.clone();
        let mut lw = Lowerer::with_typing(&ip, Typing::with_defs(ext, &def_shapes));
        let action = lw.lower_value_action("VIEW", base.view_expr()?, var)?;
        let typing = lw.into_typing();
        let native = if settings.no_native { None } else { native::build_view(&typing, &action, settings, notes) };
        notes.push(format!("view: fingerprints of the encoded VIEW ({})", if native.is_some() { "native" } else { "IR" }));
        let fast = match &action.body {
            Stmt::Assign { value, .. } => {
                let prog = fast::Program::new(&typing);
                prog.expr(&typing, &action.temps, &[], value).ok().map(|p| (prog, p))
            }
            _ => None,
        };
        Some(View { def, typing, action, native, fast, at, orbit })
    }

    /// Compute the VIEW's encoding of the extended state `ext` (the state
    /// followed by zeros) into `out`, natively or in the IR executor. False
    /// if that failed (the interpreter decides).
    pub(super) fn compiled(&self, base: &InterpModel, ext: &[u64], level: u32, out: &mut Vec<u64>) -> bool {
        if let Some(lib) = &self.native {
            let mut buf = Vec::with_capacity(1);
            if lib.next_into(ext, 0, &mut buf) == OK && buf.len() == 1 {
                out.extend_from_slice(&buf[0][self.at.clone()]);
                return true;
            }
            return false;
        }
        let Stmt::Assign { value, .. } = &self.action.body else { return false };
        let sid = self.typing.var_sid[self.typing.var_sid.len() - 1];
        if value.ty != Ty::Enc(sid) {
            return false;
        }
        if let Some((prog, p)) = &self.fast {
            let at = out.len();
            // SAFETY: the matching encoder/program produced these words.
            // Active Dyn handles were published before this call.
            let ok = unsafe { fast::eval_words(&fast::Run::words(&base.ip, &self.typing, prog, level), p, ext, out) }.is_ok()
                && out.len() - at == self.at.len();
            if !ok {
                out.truncate(at);
            }
            return ok;
        }
        false
    }
}
