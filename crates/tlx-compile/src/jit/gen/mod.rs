//! Per-function state of the Cranelift translation and the building blocks
//! shared by statements and expressions (memory, checks, loops, calls).

mod calls;
#[cfg(test)]
mod fingerprint;
mod loops;
mod memory;
#[cfg(test)]
pub(super) use fingerprint::fp_words_ir;

use std::collections::{HashMap, HashSet};

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{
    AbiParam, Block, BlockArg, FuncRef, Function, Inst, InstBuilder, InstructionData, Opcode, SigRef, Signature, StackSlot, StackSlotData,
    StackSlotKind, Value, ValueDef,
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext, Variable};
use cranelift_module::Module;

use cranelift_codegen::ir::types;

use super::{no, Cx, I32, I64, R};
use crate::ir::*;

/// Return codes (tlx_abi.h).
pub(super) const OK: i64 = 0;
pub(super) const STOP: i64 = 1;
pub(super) const ERR: i64 = -1;

/// Inline copies / clears / comparisons up to this many words.
const INLINE_WORDS: usize = 16;

/// The kind of a generated function (fixes its signature and what `s0`,
/// `s1`, `h` and `cx` are).
#[derive(Clone, Copy, Debug)]
pub(crate) enum Kind {
    /// `(h, cx) -> i32`, emits from a zeroed local next state.
    Init,
    /// `(h, cx, s0) -> i32`, emits from a local next state.
    Action,
    /// `(h, cx, s0) -> i32`: 1 / 0 / error.
    Invariant,
    /// `(h, cx, s0, s1) -> i32`.
    ActionProperty,
    /// Compiled function `i`: `(s0, s1, depth, calls, params..., out) -> i32`.
    Func(u32),
}

impl Kind {
    pub(super) fn try_signature(self, cx: &Cx) -> R<Signature> {
        let mut s = cx.module.make_signature();
        let n = match self {
            Kind::Init => 2,
            Kind::Action => 4,
            Kind::Invariant => 3,
            Kind::ActionProperty => 4,
            Kind::Func(i) => {
                let f = &cx.ty.funcs[i as usize];
                for p in &f.params {
                    if f.temps[*p as usize] == Ty::Val {
                        return no("boxed parameter");
                    }
                }
                if f.ret == Ty::Val {
                    return no("boxed result");
                }
                4 + f.params.len() + 1
            }
        };
        s.params.extend((0..n).map(|_| AbiParam::new(I64)));
        s.returns.push(AbiParam::new(I32));
        Ok(s)
    }

    pub(super) fn signature(self, cx: &Cx) -> Signature {
        self.try_signature(cx).unwrap_or_else(|_| cx.module.make_signature())
    }
}

/// A word whose value is known at translation time (see `Gen::know`).
#[derive(Clone, Copy)]
pub(super) enum Known {
    Const(u64),
    Val(Value),
}

/// Inline copies (and clears) of up to this many words as pairs of words;
/// longer ones call `memmove` (`memzero`).
const VECTOR_COPY_WORDS: usize = 32;

/// Largest encoding whose words are tracked.
const MAX_KNOWN: usize = 256;

/// Largest encoding built as words (`Gen::materialize`) rather than copied
/// into its buffer.
pub(super) const MAX_SSA_WORDS: usize = INLINE_WORDS;

/// A function-scope buffer.
#[derive(Clone, Copy)]
pub(super) struct Buf(StackSlot);

/// Host callbacks of mixed mode (`tlx_host` in tlx_abi.h) that the JIT
/// calls. The ABI owner (`tlx_native::native`) declares every callback, its
/// offset and its signature; this enum names the ones the JIT uses, and both
/// facts are derived from that owner descriptor instead of written out again.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub(super) enum HostFn {
    /// The state sink.
    Emit,
    /// A boxed region, evaluated by the host.
    Eval,
    /// The elements of a set handle.
    Elems,
    /// The handle-arena watermark.
    Mark,
    /// Release the handles made after a mark.
    Release,
    /// A value-store operation (ABI v5).
    RefOp,
    /// The elements of a stored set (ABI v5).
    RefElems,
}

impl HostFn {
    /// The owner's descriptor of this callback: same name, same field.
    fn owner(self) -> tlx_native::native::HostFn {
        use tlx_native::native::HostFn as A;
        match self {
            HostFn::Emit => A::Emit,
            HostFn::Eval => A::Eval,
            HostFn::Elems => A::Elems,
            HostFn::Mark => A::Mark,
            HostFn::Release => A::Release,
            HostFn::RefOp => A::RefOp,
            HostFn::RefElems => A::RefElems,
        }
    }

    /// Offset of the function pointer in `tlx_host`.
    fn offset(self) -> i32 {
        self.owner().offset() as i32
    }

    fn signature(self, cx: &Cx) -> Signature {
        host_signature(cx, self.owner().abi())
    }
}

/// The Cranelift type of a host-callback parameter or result: a pointer or
/// `uint64_t` is `i64`, a 32-bit kind `i32` (the ABI owner declares the
/// widths, `tlx_native::native::HostArg::bits`).
pub(super) fn host_type(a: tlx_native::native::HostArg) -> cranelift_codegen::ir::Type {
    if a.bits() == 32 {
        I32
    } else {
        I64
    }
}

/// The Cranelift signature of a host callback, from the ABI owner's
/// `HostSignature` (see `host_type`).
pub(super) fn host_signature(cx: &Cx, abi: tlx_native::native::HostSignature) -> Signature {
    let mut s = cx.module.make_signature();
    s.params.extend(abi.params.iter().map(|a| AbiParam::new(host_type(*a))));
    s.returns.extend(abi.ret.map(|a| AbiParam::new(host_type(a))));
    s
}

/// A scope whose handles are released when it ends (`Gen::scope`): the
/// block it starts with and the handles made before it.
pub(super) struct Scope(Option<(Block, usize)>);

pub(crate) struct Gen<'c, 't, 'f> {
    pub(super) cx: &'c mut Cx<'t>,
    pub(super) b: FunctionBuilder<'f>,
    kind: Kind,
    pub(super) h: Value,
    pub(super) hcx: Value,
    pub(super) s0: Value,
    pub(super) s1: Value,
    /// Compiled functions: call depth, budget counter, parameters, result.
    pub(super) depth: Value,
    pub(super) calls: Value,
    pub(super) params: Vec<Value>,
    pub(super) out: Value,
    err: Block,
    stop: Block,
    /// Representation and current value of each IR temporary.
    pub(super) temps: Vec<Ty>,
    pub(super) vals: Vec<Option<Value>>,
    /// Inside `ENABLED`: mixed-mode regions run in `RegionCtx::Action`.
    pub(super) in_enabled: bool,
    /// Redirect `Stmt::Emit` to `block`; when the flag is true (`ENABLED`),
    /// pass `1` as the block argument.
    pub(super) emit_target: Option<(Block, bool)>,
    /// Path counters of `Repeat`s.
    pub(super) counts: HashMap<u32, Variable>,
    sigs: HashMap<usize, SigRef>,
    fn_refs: HashMap<u32, FuncRef>,
    pub(super) in_fn: bool,
    /// Pointers whose words are known (constants, unranked elements).
    known: HashMap<Value, Vec<Known>>,
    /// Sub-word bitfields of known pointers (`Pack`, `unrank`, `for_bitset`).
    known_bits: HashMap<Value, Vec<(BitPos, Known)>>,
    /// Mixed mode: the function calls the host regions the C generator
    /// made of it (`Cx::regions`), and boxed values are handles.
    pub(super) mixing: bool,
    /// Region calls and loops over boxed sets making handles, so far.
    pub(super) handles: usize,
    host_sigs: HashMap<HostFn, SigRef>,
    /// Buffers written once by `materialize` (address, stores): the stores
    /// are removed at the end if nothing but known loads read the buffer.
    elide: Vec<(Value, Vec<Inst>)>,
    /// Product of the arm counts of the loops specialized per union arm
    /// around the code being generated (`Gen::for_bitset`).
    pub(super) spec: usize,
    /// Exclusive unsigned upper bounds of values known at translation
    /// time (unranked digits).
    bounds: HashMap<Value, u64>,
    /// Possible effects generated so far (checks, failures, calls,
    /// emits): see `Gen::for_bitset`.
    pub(super) effects: usize,
    /// Module-local global value pointing to the `var_offsets` byte-offset table.
    pub(super) var_offsets_gv: Option<cranelift_codegen::ir::GlobalValue>,
}

impl<'c, 't, 'f> Gen<'c, 't, 'f> {
    pub(super) fn new(cx: &'c mut Cx<'t>, func: &'f mut Function, fbc: &'f mut FunctionBuilderContext, kind: Kind) -> Self {
        let mut b = FunctionBuilder::new(func, fbc);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        let p = b.block_params(entry).to_vec();
        let zero = b.ins().iconst(I64, 0);
        let words = cx.ty.layout.words;
        let local_state = |b: &mut FunctionBuilder| {
            let ss = b.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, (words.max(1) * 8) as u32, 3));
            b.ins().stack_addr(I64, ss, 0)
        };
        let (mut h, mut hcx, mut s0, mut s1, mut depth, mut calls, mut out) = (zero, zero, zero, zero, zero, zero, zero);
        let mut params = Vec::new();
        match kind {
            Kind::Init => {
                (h, hcx) = (p[0], p[1]);
                s1 = local_state(&mut b);
            }
            Kind::Action => (h, hcx, s0, s1) = (p[0], p[1], p[2], p[3]),
            Kind::Invariant => (h, hcx, s0) = (p[0], p[1], p[2]),
            Kind::ActionProperty => (h, hcx, s0, s1) = (p[0], p[1], p[2], p[3]),
            Kind::Func(_) => {
                (s0, s1, depth, calls) = (p[0], p[1], p[2], p[3]);
                params = p[4..p.len() - 1].to_vec();
                out = p[p.len() - 1];
            }
        }
        let err = b.create_block();
        let stop = b.create_block();
        b.set_cold_block(err);
        b.set_cold_block(stop);
        let mut g = Gen {
            cx,
            b,
            kind,
            h,
            hcx,
            s0,
            s1,
            depth,
            calls,
            params,
            out,
            err,
            stop,
            temps: Vec::new(),
            vals: Vec::new(),
            in_enabled: false,
            emit_target: None,
            counts: HashMap::new(),
            sigs: HashMap::new(),
            fn_refs: HashMap::new(),
            known: HashMap::new(),
            known_bits: HashMap::new(),
            in_fn: matches!(kind, Kind::Func(_)),
            mixing: false,
            handles: 0,
            host_sigs: HashMap::new(),
            elide: Vec::new(),
            spec: 1,
            bounds: HashMap::new(),
            effects: 0,
            var_offsets_gv: None,
        };
        if matches!(kind, Kind::Init) {
            let s1 = g.s1;
            g.zero(s1, words);
        }
        g
    }

    pub(super) fn set_temps(&mut self, temps: &[Ty]) {
        self.temps = temps.to_vec();
        self.vals = vec![None; temps.len()];
    }

    /// Fill the error / stop blocks and finalize the function.
    pub(super) fn finish(mut self) {
        // The current block is the (unreachable) one after the body's
        // final terminator.
        let err = self.err;
        self.switch(err);
        let e = self.b.ins().iconst(I32, ERR);
        self.b.ins().return_(&[e]);
        self.b.switch_to_block(self.stop);
        let s = self.b.ins().iconst(I32, STOP);
        self.b.ins().return_(&[s]);
        self.b.seal_all_blocks();
        self.elide_stores();
        self.b.finalize();
    }

    /// Remove the stores of the `materialize`d buffers whose address is
    /// not used other than to store their words (all their reads were
    /// known loads), directly or through unused offsets.
    fn elide_stores(&mut self) {
        if self.elide.is_empty() {
            return;
        }
        let func = &mut *self.b.func;
        let mut users: HashMap<Value, Vec<Inst>> = HashMap::new();
        for blk in func.layout.blocks() {
            for inst in func.layout.block_insts(blk) {
                for v in func.dfg.inst_values(inst) {
                    users.entry(func.dfg.resolve_aliases(v)).or_default().push(inst);
                }
            }
        }
        fn escapes(func: &Function, users: &HashMap<Value, Vec<Inst>>, v: Value, stores: &HashSet<Inst>) -> bool {
            users.get(&v).is_some_and(|us| {
                us.iter().any(|&u| {
                    let args = func.dfg.inst_args(u);
                    if stores.contains(&u) && args.len() == 2 && args[0] != v {
                        return false;
                    }
                    match func.dfg.insts[u] {
                        InstructionData::BinaryImm64 { opcode: Opcode::IaddImm, .. } => {
                            escapes(func, users, func.dfg.first_result(u), stores)
                        }
                        _ => true,
                    }
                })
            })
        }
        for (p, stores) in std::mem::take(&mut self.elide) {
            let set: HashSet<Inst> = stores.iter().copied().collect();
            if !escapes(func, &users, p, &set) {
                for st in stores {
                    func.layout.remove_inst(st);
                }
            }
        }
    }

    /// Return `rc` (i32) from the function here.
    pub(super) fn ret(&mut self, rc: i64) {
        let v = self.b.ins().iconst(I32, rc);
        self.b.ins().return_(&[v]);
        self.dead();
    }

    /// Continue in a fresh (unreachable) block after a terminator.
    pub(super) fn dead(&mut self) {
        let blk = self.b.create_block();
        self.b.switch_to_block(blk);
    }

    /// Switch to `blk`. A current block left without a terminator is
    /// unreachable code after a terminator (`dead`): it is closed with a
    /// jump to the error block.
    pub(super) fn switch(&mut self, blk: Block) {
        if let Some(cur) = self.b.current_block() {
            let open = match self.b.func.layout.last_inst(cur) {
                Some(i) => !self.b.func.dfg.insts[i].opcode().is_terminator(),
                None => true,
            };
            if open {
                let err = self.err;
                self.b.ins().jump(err, &[]);
            }
        }
        self.b.switch_to_block(blk);
    }

    // ---- values and checks ----

    pub(super) fn iconst(&mut self, v: i64) -> Value {
        self.b.ins().iconst(I64, v)
    }

    /// The value of `v` if it is a constant (an `iconst`). The translation
    /// folds what it can with it: Cranelift folds constant arithmetic but
    /// not branches, and code after a decided branch (a union arm
    /// specialized by `for_bitset`, a known tag) should not be generated
    /// live at all.
    pub(super) fn konst(&self, v: Value) -> Option<i64> {
        let dfg = &self.b.func.dfg;
        match dfg.value_def(v) {
            ValueDef::Result(inst, _) => match dfg.insts[inst] {
                InstructionData::UnaryImm { opcode: Opcode::Iconst, imm } => Some(imm.bits()),
                _ => None,
            },
            _ => None,
        }
    }

    /// An exclusive unsigned upper bound of `v`, if known.
    pub(super) fn bound(&self, v: Value) -> Option<u64> {
        match self.konst(v) {
            Some(k) => Some(k as u64).and_then(|k| k.checked_add(1)),
            None => self.bounds.get(&v).copied(),
        }
    }

    /// Record that `v < bound` (unsigned).
    pub(super) fn set_bound(&mut self, v: Value, bound: u64) {
        self.bounds.insert(v, bound);
    }

    /// `(q / d, q % d)` for a constant `d > 0` and `q < bound`. Small
    /// quotients use a short multiply-shift instead of the 64-bit magic
    /// number (four instructions to materialize, in every block).
    pub(super) fn udivrem(&mut self, q: Value, d: u64, bound: u64) -> (Value, Value) {
        if let Some(k) = self.konst(q) {
            let k = k as u64;
            return (self.iconst((k / d) as i64), self.iconst((k % d) as i64));
        }
        let (quot, rem) = if bound <= d {
            (self.iconst(0), q)
        } else if d == 1 {
            (q, self.iconst(0))
        } else if d.is_power_of_two() {
            (self.b.ins().ushr_imm(q, d.trailing_zeros() as i64), self.b.ins().band_imm(q, (d - 1) as i64))
        } else if let Some((m, sh)) = small_magic(d, bound) {
            let t = self.b.ins().imul_imm(q, m as i64);
            let quot = self.b.ins().ushr_imm(t, sh as i64);
            let qd = self.b.ins().imul_imm(quot, d as i64);
            (quot, self.b.ins().isub(q, qd))
        } else {
            (self.b.ins().udiv_imm(q, d as i64), self.b.ins().urem_imm(q, d as i64))
        };
        self.bounds.insert(quot, bound.div_ceil(d));
        self.bounds.insert(rem, d.min(bound));
        (quot, rem)
    }

    /// An i8 condition constant.
    fn cond_const(&mut self, c: bool) -> Value {
        self.b.ins().iconst(types::I8, c as i64)
    }

    /// i8 condition -> i64 0/1.
    pub(super) fn b2i(&mut self, c: Value) -> Value {
        match self.konst(c) {
            Some(k) => self.iconst((k != 0) as i64),
            None => self.b.ins().uextend(I64, c),
        }
    }

    pub(super) fn cmp(&mut self, cc: IntCC, a: Value, b: Value) -> Value {
        match (self.konst(a), self.konst(b)) {
            (Some(x), Some(y)) => self.cond_const(eval_cc(cc, x, y)),
            (None, Some(y)) => self.b.ins().icmp_imm(cc, a, y),
            _ => self.b.ins().icmp(cc, a, b),
        }
    }

    pub(super) fn cmp_imm(&mut self, cc: IntCC, a: Value, k: i64) -> Value {
        match self.konst(a) {
            Some(x) => self.cond_const(eval_cc(cc, x, k)),
            None => self.b.ins().icmp_imm(cc, a, k),
        }
    }

    /// `a & b` of i64 booleans.
    pub(super) fn and_i(&mut self, a: Value, b: Value) -> Value {
        match (self.konst(a), self.konst(b)) {
            (Some(0), _) | (_, Some(0)) => self.iconst(0),
            (Some(_), _) => b,
            (_, Some(_)) => a,
            _ => self.b.ins().band(a, b),
        }
    }

    /// `a | b` of i64 booleans.
    pub(super) fn or_i(&mut self, a: Value, b: Value) -> Value {
        match (self.konst(a), self.konst(b)) {
            (Some(0), _) => b,
            (_, Some(0)) => a,
            (Some(_), _) | (_, Some(_)) => self.iconst(1),
            _ => self.b.ins().bor(a, b),
        }
    }

    /// `a + k`.
    pub(super) fn add_imm(&mut self, a: Value, k: i64) -> Value {
        match self.konst(a) {
            Some(x) => self.iconst(x.wrapping_add(k)),
            None if k == 0 => a,
            None => self.b.ins().iadd_imm(a, k),
        }
    }

    /// `brif`, or a jump if `c` is a constant.
    pub(super) fn brif(&mut self, c: Value, t: Block, ta: &[BlockArg], f: Block, fa: &[BlockArg]) {
        match self.konst(c) {
            Some(k) => {
                let (to, args) = if k != 0 { (t, ta) } else { (f, fa) };
                self.b.ins().jump(to, args);
            }
            None => {
                self.b.ins().brif(c, t, ta, f, fa);
            }
        }
    }

    /// Generate `f` as unreachable code, then continue here: an operand
    /// whose value does not matter is still translated, so that what does
    /// not translate and the region calls are the same as in the C code.
    pub(super) fn dead_code(&mut self, f: impl FnOnce(&mut Self) -> R<()>) -> R<()> {
        let cont = self.b.create_block();
        self.b.ins().jump(cont, &[]);
        self.dead();
        f(self)?;
        self.switch(cont);
        Ok(())
    }

    /// Continue if `ok` (nonzero), else return TLX_ERR.
    pub(super) fn check(&mut self, ok: Value) {
        if self.konst(ok).is_some_and(|k| k != 0) {
            return;
        }
        self.effects += 1;
        let cont = self.b.create_block();
        let err = self.err;
        self.brif(ok, cont, &[], err, &[]);
        self.switch(cont);
    }

    /// Return TLX_ERR here.
    pub(super) fn fail(&mut self) {
        self.effects += 1;
        let err = self.err;
        self.b.ins().jump(err, &[]);
        self.dead();
    }

    /// Return TLX_STOP if `stop` (nonzero).
    pub(super) fn stop_if(&mut self, stop: Value) {
        self.effects += 1;
        let cont = self.b.create_block();
        let st = self.stop;
        self.brif(stop, st, &[], cont, &[]);
        self.switch(cont);
    }

    /// `v` fits in 32 bits (i8 condition).
    pub(super) fn fits_i32(&mut self, v: Value) -> Value {
        if let Some(k) = self.konst(v) {
            return self.cond_const(k == k as i32 as i64);
        }
        let n = self.b.ins().ireduce(I32, v);
        let w = self.b.ins().sextend(I64, n);
        self.cmp(IntCC::Equal, v, w)
    }

    // ---- function bodies ----

    /// Body of an action / Init function (emits into `s1`).
    pub(super) fn action(&mut self, f: &ActionFn) -> R<()> {
        self.set_temps(&f.temps);
        self.stmt(&f.body)?;
        self.ret(OK);
        Ok(())
    }

    /// A predicate translated whole: `return c ? 1 : 0`.
    pub(super) fn pred_whole(&mut self, p: &PredFn) -> R<()> {
        self.set_temps(&p.temps);
        let c = self.bool_expr(&p.body)?;
        let r = self.b.ins().ireduce(I32, c);
        self.b.ins().return_(&[r]);
        self.dead();
        Ok(())
    }

    /// A predicate decided by its native prefix (`CGen::pred_prefix`).
    pub(super) fn pred_prefix_fn(&mut self, p: &PredFn) -> R<()> {
        self.set_temps(&p.temps);
        self.pred_prefix(&p.body)
    }

    fn pred_prefix(&mut self, e: &Expr) -> R<()> {
        let temps = self.temps.clone();
        let kind = self.kind;
        // Probe in a scratch function with the bindings in scope.
        let vals_bound: Vec<Option<()>> = self.vals.iter().map(|v| v.map(|_| ())).collect();
        let probe = |g: &mut Self, x: &Expr| {
            g.cx.probe(kind, &temps, |s| {
                for (i, b) in vals_bound.iter().enumerate() {
                    if b.is_some() {
                        let z = s.iconst(0);
                        s.vals[i] = Some(z);
                    }
                }
                s.bool_expr(x).map(|_| ())
            })
        };
        if probe(self, e).is_ok() {
            let c = self.bool_expr(e)?;
            let r = self.b.ins().ireduce(I32, c);
            self.b.ins().return_(&[r]);
            self.dead();
            return Ok(());
        }
        match &*e.kind {
            ExprKind::And(xs) | ExprKind::Or(xs) => {
                let and = matches!(&*e.kind, ExprKind::And(_));
                let mut decided = 0;
                for x in xs {
                    if probe(self, x).is_err() {
                        break;
                    }
                    let c = self.bool_expr(x)?;
                    let (exit, cont) = (self.b.create_block(), self.b.create_block());
                    if and {
                        self.brif(c, cont, &[], exit, &[]);
                    } else {
                        self.brif(c, exit, &[], cont, &[]);
                    }
                    self.switch(exit);
                    self.ret(if and { 0 } else { 1 });
                    self.switch(cont);
                    decided += 1;
                }
                if decided == 0 {
                    return no("predicate without a native prefix");
                }
                self.ret(tlx_native::native::UNSUPPORTED as i64);
            }
            ExprKind::Let { temp: t, value, body } => {
                if value.ty == Ty::Val {
                    return no("boxed value");
                }
                let v = self.expr(value)?;
                self.with_temp(*t, v, |g| g.pred_prefix(body))?;
            }
            _ => return no("predicate without a native prefix"),
        }
        Ok(())
    }

    /// Body of compiled function `f` (`CGen::function`).
    pub(super) fn function_body(&mut self, f: &FnDef) -> R<()> {
        self.set_temps(&f.temps);
        let depth = self.depth;
        let too_deep = self.cmp_imm(IntCC::SignedGreaterThan, depth, crate::exec::eval::MAX_CALL_DEPTH as i64);
        let ok = self.b.ins().bxor_imm(too_deep, 1);
        self.check(ok);
        if f.budgeted {
            let calls = self.calls;
            let n = self.load(calls, 0);
            let n = self.b.ins().iadd_imm(n, 1);
            self.store(n, calls, 0);
            let ok = self.cmp_imm(IntCC::UnsignedLessThanOrEqual, n, crate::exec::eval::MAX_BUDGETED_CALLS as i64);
            self.check(ok);
        }
        for (k, p) in f.params.iter().enumerate() {
            let v = self.params[k];
            self.vals[*p as usize] = Some(v);
        }
        let v = self.expr(&f.body)?;
        let out = self.out;
        match f.ret {
            Ty::Enc(sid) => {
                let n = self.cx.ty.words(sid) as usize;
                self.copy(out, v, n);
            }
            _ => self.store(v, out, 0),
        }
        self.ret(OK);
        Ok(())
    }
}

/// `(m, s)` such that `q * m >> s == q / d` for all `q < bound` (checked),
/// with `m` small, if `bound` is small enough to check.
fn small_magic(d: u64, bound: u64) -> Option<(u64, u32)> {
    if bound > 1 << 16 {
        return None;
    }
    let n = 64 - bound.saturating_sub(1).leading_zeros();
    let s = n + (64 - (d - 1).leading_zeros());
    let m = (1u64 << s).div_ceil(d);
    (0..bound).all(|q| (q * m) >> s == q / d).then_some((m, s))
}

/// `cc` on constants.
fn eval_cc(cc: IntCC, x: i64, y: i64) -> bool {
    let (ux, uy) = (x as u64, y as u64);
    match cc {
        IntCC::Equal => x == y,
        IntCC::NotEqual => x != y,
        IntCC::SignedLessThan => x < y,
        IntCC::SignedLessThanOrEqual => x <= y,
        IntCC::SignedGreaterThan => x > y,
        IntCC::SignedGreaterThanOrEqual => x >= y,
        IntCC::UnsignedLessThan => ux < uy,
        IntCC::UnsignedLessThanOrEqual => ux <= uy,
        IntCC::UnsignedGreaterThan => ux > uy,
        IntCC::UnsignedGreaterThanOrEqual => ux >= uy,
    }
}

#[cfg(test)]
mod tests {
    use super::{host_type, HostFn, I32, I64};
    use tlx_native::native::{HostArg, HostFn as A};

    /// The JIT calls the ABI owner's callbacks by name: a swap would load
    /// one field's function pointer where another's is meant (their offsets
    /// differ, see the owner's `HostFn::ALL` order).
    #[test]
    fn host_callbacks_are_the_abi_owners() {
        let cases = [
            (HostFn::Emit, A::Emit),
            (HostFn::Eval, A::Eval),
            (HostFn::Elems, A::Elems),
            (HostFn::Mark, A::Mark),
            (HostFn::Release, A::Release),
            (HostFn::RefOp, A::RefOp),
            (HostFn::RefElems, A::RefElems),
        ];
        let mut offsets = Vec::new();
        for (jit, owner) in cases {
            assert_eq!(jit.owner(), owner);
            assert_eq!(jit.offset() as usize, owner.offset());
            offsets.push(jit.offset());
        }
        offsets.sort_unstable();
        offsets.dedup();
        assert_eq!(offsets.len(), cases.len(), "each callback is a distinct field");
    }

    /// The width mapping the host signatures are built from.
    #[test]
    fn host_argument_widths_follow_the_c_types() {
        assert_eq!(host_type(HostArg::I32), I32);
        assert_eq!(host_type(HostArg::U32), I32);
        for a in [HostArg::Ctx, HostArg::State, HostArg::WordOut, HostArg::Args, HostArg::ElemsOut, HostArg::U64] {
            assert_eq!(host_type(a), I64);
        }
    }
}
