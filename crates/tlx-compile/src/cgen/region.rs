//! Mixed mode: host region calls (docs/mixed-mode.md §2, §4).
//!
//! `expr` tries to compile an expression natively; if C cannot compile the
//! node itself (a boxed operation, an interpreter fallback, a conversion
//! from a boxed value, a loop over a boxed set...), the whole expression
//! becomes a region and the code generated for its children so far is
//! discarded. Since the node fails before (or instead of) its children
//! failing, region roots are as small as possible: a parent that compiles
//! stays in C and only its failing children become regions.
//!
//! A region's inputs are the temps it reads that are bound outside it, in
//! order of first occurrence (`lower::free_temps`); the states it sees are
//! the call's (`s0`, and `s1`: the next state being built, or the local one
//! of an `ENABLED`). Its result is written by the host in the region's
//! representation: a scalar, the words of an encoding, or a handle.

use std::fmt::Write;

use super::{no, temp, CGen, R};
use crate::enc::mixed::{Region, RegionCtx, RegionInfo};
use crate::ir::*;
use crate::native_plan::site;

/// What `expr` rolls back when a node is not native after all.
pub(super) struct Snapshot {
    bufs: usize,
    nbuf: usize,
    statics: usize,
    nstatic: usize,
    nstatic_u64: usize,
    nstatic_arr: usize,
    regions: usize,
    handles: usize,
    loop_region: bool,
}

impl CGen<'_> {
    /// C code of `e`: native code, or (mixed mode) a region call.
    pub(super) fn expr(&mut self, e: &Expr) -> R<String> {
        if !self.mixing {
            return self.expr_native(e);
        }
        if self.force_now(e) {
            return self.region(e);
        }
        let snap = self.snapshot();
        match self.expr_native(e) {
            Ok(code) => Ok(code),
            Err(err) => {
                self.rollback(snap);
                self.region(e).map_err(|_| err)
            }
        }
    }

    pub(super) fn snapshot(&self) -> Snapshot {
        Snapshot {
            bufs: self.bufs.len(),
            nbuf: self.nbuf,
            statics: self.statics.len(),
            nstatic: self.nstatic,
            nstatic_u64: self.static_u64_keys.len(),
            nstatic_arr: self.static_arr_keys.len(),
            regions: self.regions.len(),
            handles: self.handles,
            loop_region: self.loop_region,
        }
    }

    pub(super) fn rollback(&mut self, s: Snapshot) {
        self.bufs.truncate(s.bufs);
        self.nbuf = s.nbuf;
        self.statics.truncate(s.statics);
        self.nstatic = s.nstatic;
        for key in self.static_u64_keys.drain(s.nstatic_u64..) {
            self.static_u64_dedup.remove(&key);
        }
        for key in self.static_arr_keys.drain(s.nstatic_arr..) {
            self.static_arr_dedup.remove(&key);
        }
        self.regions.truncate(s.regions);
        self.handles = s.handles;
        self.loop_region = s.loop_region;
    }

    /// `Mixed::force`: whether to make `e` a region although C may compile
    /// it.
    fn force_now(&mut self, e: &Expr) -> bool {
        let k = self.mixed.as_ref().map_or(0, |m| m.force);
        if k == 0 || matches!(&*e.kind, ExprKind::ConstElems { .. } | ExprKind::IntRange(..)) {
            return false;
        }
        self.nforce += 1;
        self.nforce.is_multiple_of(k as u64)
    }

    /// Whether code generated since `handles` (a value of `self.handles`)
    /// makes handles: a loop around it releases them after each iteration.
    pub(super) fn made_handles(&self, handles: usize) -> bool {
        self.handles > handles
    }

    /// Start of an expression-level loop over `set`: C only loops over
    /// typed sources (a loop over a boxed set is a region as a whole).
    /// Returns `self.handles` (see `foreach`).
    pub(super) fn loop_start(&self, set: &Expr) -> R<usize> {
        if !set.is_typed_source() {
            return no("iteration over a boxed set");
        }
        Ok(self.handles)
    }

    /// `code` (of a boolean or integer) releasing the handles it makes, if
    /// it made any since `handles`.
    pub(super) fn scoped_scalar(&mut self, code: &str, handles: usize) -> String {
        if !self.made_handles(handles) {
            return code.to_string();
        }
        let k = self.fresh();
        format!("({{ uint64_t mk{k} = h->mark(cx); int64_t v{k} = {code}; h->release(cx, mk{k}); v{k}; }})")
    }

    /// `body` (code of a loop iteration) releasing the handles it makes,
    /// if `release`. (Leaving the loop early skips the release: the
    /// handles then live until the function returns.)
    pub(super) fn released(&mut self, body: &str, release: bool, pad: &str) -> String {
        if !release {
            return body.to_string();
        }
        let k = self.fresh();
        format!("{pad}{{ uint64_t mk{k} = h->mark(cx);\n{body}{pad}h->release(cx, mk{k}); }}\n")
    }

    /// A call of a new region evaluating `e` (in `e`'s representation).
    pub(super) fn region(&mut self, e: &Expr) -> R<String> {
        self.region_at(e, site(e, false))
    }

    /// `region`, called from `site`.
    pub(super) fn region_at(&mut self, e: &Expr, site: usize) -> R<String> {
        if matches!(&*e.kind, ExprKind::ConstElems { .. } | ExprKind::IntRange(..)) {
            return no("iteration source outside iteration");
        }
        let inputs = crate::lower::free_temps(e);
        if inputs.iter().any(|t| self.stmt_loops.iter().any(|b| b.contains(t))) {
            self.loop_region = true;
        }
        let mut args = Vec::with_capacity(inputs.len());
        for t in &inputs {
            let field = match self.temps[*t as usize] {
                Ty::Bool | Ty::Int => "i",
                Ty::Enc(_) => "w",
                Ty::Val => "h",
            };
            args.push(format!("{{.{field} = {}}}", temp(*t)));
        }
        let oracle = self.mixed.as_ref().expect("regions in mixed mode only").oracle;
        // Inside ENABLED: the action's context, over its local next state.
        let enabled = self.in_enabled;
        let ctx = if enabled { RegionCtx::Action } else { self.rctx };
        // (An action that prints is mixed, `RegionOracle::mixes_next`: its
        // printing regions must not be memoized.)
        let info = RegionInfo { func: self.fn_name.clone(), enabled, pure: !oracle.expr_volatile(e), reads: oracle.reads(e) };
        let region = Region { expr: e.clone(), temps: self.fn_temps.clone(), inputs, ctx, assigned: self.assigned.as_slice().into(), info };
        crate::verify::enforce(crate::verify::region(self.ty, &region)).map_err(super::Unsupported)?;
        crate::verify::enforce(crate::verify::region_call(&region, &self.temps, e.ty, ctx)).map_err(super::Unsupported)?;
        let rid = self.regions.push(region, site);
        let mut a = String::new();
        if args.is_empty() {
            a.push_str("const tlx_arg *a_ = 0;");
        } else {
            write!(a, "tlx_arg a_[{}] = {{{}}};", args.len(), args.join(", ")).unwrap();
        }
        let call = |out: &str| format!("if (h->eval(cx, {rid}, s0, s1, a_, {out})) return TLX_ERR;");
        Ok(match e.ty {
            Ty::Bool | Ty::Int => format!("({{ {a} int64_t r_; {} r_; }})", call("(uint64_t *)&r_")),
            Ty::Enc(sid) => {
                let b = self.buf(self.words(sid));
                format!("({{ {a} {} (const uint64_t *){b}; }})", call(&b))
            }
            Ty::Val => {
                self.handles += 1;
                format!("({{ {a} uint64_t r_; {} r_; }})", call("&r_"))
            }
        })
    }
}
