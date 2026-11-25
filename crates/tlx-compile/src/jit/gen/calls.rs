//! Runtime-helper calls, `emit`, function calls and the mixed-mode host regions of the Cranelift translation.

use cranelift_codegen::cursor::{Cursor, FuncCursor};
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{AbiParam, InstBuilder, SigRef, Value};
use cranelift_module::Module;

use super::super::{Unsupported, I32, I64, R};
use super::*;
use crate::ir::*;

impl<'c, 't, 'f> Gen<'c, 't, 'f> {
    /// Call the helper at `addr` (an `extern "C" fn(i64...) -> i64`).
    pub(in crate::jit) fn call_rt(&mut self, addr: *const u8, args: &[Value]) -> Value {
        self.effects += 1;
        let n = args.len();
        let sig = match self.sigs.get(&n) {
            Some(s) => *s,
            None => {
                let mut s = self.cx.module.make_signature();
                s.params.extend((0..n).map(|_| AbiParam::new(I64)));
                s.returns.push(AbiParam::new(I64));
                let r = self.b.import_signature(s);
                self.sigs.insert(n, r);
                r
            }
        };
        let f = self.iconst(addr as i64);
        let call = self.b.ins().call_indirect(sig, f, args);
        self.b.inst_results(call)[0]
    }

    /// `h->emit(cx, s1, 0)`; return TLX_STOP if it asks to stop. The callback
    /// and its signature come from the ABI owner like the other host calls.
    pub(in crate::jit) fn emit(&mut self) {
        let sig = self.host_sig(HostFn::Emit);
        let h = self.h;
        let f = self.b.ins().load(I64, Self::flags(), h, HostFn::Emit.offset());
        let a = self.b.ins().iconst(I32, 0);
        let (hcx, s1) = (self.hcx, self.s1);
        let call = self.b.ins().call_indirect(sig, f, &[hcx, s1, a]);
        let r = self.b.inst_results(call)[0];
        self.stop_if(r);
    }

    /// Call compiled function `i` (returns its i32 result code).
    pub(in crate::jit) fn call_fn(&mut self, i: u32, args: &[Value]) -> Value {
        self.effects += 1;
        let fr = match self.fn_refs.get(&i) {
            Some(f) => *f,
            None => {
                let id = self.cx.fn_ids[i as usize];
                let f = self.cx.module.declare_func_in_func(id, self.b.func);
                self.fn_refs.insert(i, f);
                f
            }
        };
        let call = self.b.ins().call(fr, args);
        self.b.inst_results(call)[0]
    }

    // ---- mixed mode ----

    fn host_sig(&mut self, f: HostFn) -> SigRef {
        if let Some(s) = self.host_sigs.get(&f) {
            return *s;
        }
        let sig = f.signature(self.cx);
        let r = self.b.import_signature(sig);
        self.host_sigs.insert(f, r);
        r
    }

    /// Call host callback `f` with `cx` and `args`; its result, if any.
    pub(in crate::jit) fn call_host(&mut self, f: HostFn, args: &[Value]) -> Option<Value> {
        self.effects += 1;
        let sig = self.host_sig(f);
        let h = self.h;
        let fp = self.b.ins().load(I64, Self::flags(), h, f.offset());
        let mut all = vec![self.hcx];
        all.extend_from_slice(args);
        let call = self.b.ins().call_indirect(sig, fp, &all);
        self.b.inst_results(call).first().copied()
    }

    /// Start a scope (a loop iteration, a predicate evaluated per element)
    /// that releases the handles it makes when it ends (`end_scope`), as
    /// `CGen::released` / `CGen::scoped_scalar` do.
    pub(in crate::jit) fn scope(&mut self) -> Scope {
        if !self.mixing {
            return Scope(None);
        }
        let blk = self.b.create_block();
        self.b.ins().jump(blk, &[]);
        self.switch(blk);
        Scope(Some((blk, self.handles)))
    }

    /// End `s` here: if code made handles in it, mark the arena at its
    /// start (inserted now that this is known) and release to the mark.
    /// (Leaving the scope early skips the release: the handles then live
    /// until the function returns.)
    pub(in crate::jit) fn end_scope(&mut self, s: Scope) {
        let Scope(Some((blk, h0))) = s else { return };
        if self.handles == h0 {
            return;
        }
        let sig = self.host_sig(HostFn::Mark);
        let (h, hcx) = (self.h, self.hcx);
        let mark = {
            let mut pos = FuncCursor::new(self.b.func).at_first_insertion_point(blk);
            let fp = pos.ins().load(I64, Self::flags(), h, HostFn::Mark.offset());
            let call = pos.ins().call_indirect(sig, fp, &[hcx]);
            pos.func.dfg.inst_results(call)[0]
        };
        self.call_host(HostFn::Release, &[mark]);
    }

    /// A call of region `rid` (of the C generator's table): its result in
    /// the region's representation.
    pub(in crate::jit) fn region(&mut self, rid: u32, result: Ty) -> R<Value> {
        let table = self.cx.regions.as_ref().expect("regions in mixed mode only").table;
        let r = &table.regions[rid as usize];
        use crate::enc::mixed::RegionCtx;
        let context = if self.in_enabled {
            RegionCtx::Action
        } else {
            match self.kind {
                super::Kind::Init => RegionCtx::Init,
                super::Kind::Action => RegionCtx::Action,
                super::Kind::Invariant => RegionCtx::StatePred,
                super::Kind::ActionProperty => RegionCtx::TransPred,
                super::Kind::Func(_) => return Err(Unsupported("region in compiled function".into())),
            }
        };
        crate::verify::enforce(crate::verify::region_call(r, &self.temps, result, context)).map_err(Unsupported)?;
        let args = if r.inputs.is_empty() {
            self.iconst(0)
        } else {
            let mut vals = Vec::with_capacity(r.inputs.len());
            for t in &r.inputs {
                vals.push(self.vals.get(*t as usize).copied().flatten().ok_or(Unsupported(format!("region input: unbound temp {t}")))?);
            }
            let a = self.buf(vals.len());
            let ap = self.addr(a);
            for (i, v) in vals.into_iter().enumerate() {
                self.store(v, ap, i);
            }
            ap
        };
        let ty = r.expr.ty;
        let out = match ty {
            Ty::Enc(sid) => {
                let n = self.cx.ty.words(sid) as usize;
                self.buf(n)
            }
            _ => self.buf(1),
        };
        let op = self.addr(out);
        let id = self.b.ins().iconst(I32, rid as i64);
        let (s0, s1) = (self.s0, self.s1);
        let rc = self.call_host(HostFn::Eval, &[id, s0, s1, args, op]).expect("eval returns a code");
        let ok = self.cmp_imm(IntCC::Equal, rc, 0);
        self.check(ok);
        Ok(match ty {
            Ty::Enc(_) => op,
            Ty::Val => {
                self.handles += 1;
                self.load(op, 0)
            }
            Ty::Bool | Ty::Int => self.load(op, 0),
        })
    }
}
