//! Interpreter fallbacks (`ExprKind::Interp`): inputs, evaluation and the memo of their results.

use std::sync::Arc;

use tlx_eval::env::{Binding, Env, OpVal, Thunk};
use tlx_sema::hir::{self, DefId, DefKind, LocalId, OpRef};
use tlx_value::Value;

use super::super::super::memo;
use super::super::{Code, Fx, R};
use crate::ir::*;

/// An input of an interpreter fallback.
pub(super) struct InterpBind {
    pub(super) local: LocalId,
    /// A materialized definition's value: (definition, primed).
    pub(super) def: Option<(DefId, bool)>,
    pub(super) code: Code,
    pub(super) ty: Ty,
}

/// An interpreter fallback (`ExprKind::Interp`).
pub(super) struct InterpNode {
    pub(super) node: usize,
    pub(super) expr: hir::Expr,
    /// The IR's binds (for the memo's dependency analysis).
    pub(super) binds: Vec<(LocalId, Expr)>,
    pub(super) codes: Vec<InterpBind>,
    pub(super) deferred: Vec<Deferred>,
    pub(super) env: Env,
}

impl InterpNode {
    pub(super) fn eval(&self, fx: &mut Fx) -> R<Value> {
        // (Not memoized in Init: variables are read from the next state.)
        if fx.memo != 0 && !fx.init {
            return self.eval_memo(fx);
        }
        self.eval_plain(fx)
    }

    fn eval_plain(&self, fx: &mut Fx) -> R<Value> {
        let mut vals = Vec::with_capacity(self.codes.len());
        for b in &self.codes {
            // A definition value that will not be seeded (already known, or a
            // next-state value while the next state is partial) is not computed.
            if let Some((d, primed)) = b.def {
                if fx.cache().knows(d, primed) || (primed && !fx.s1_complete()) {
                    vals.push(Value::TRUE);
                    continue;
                }
            }
            vals.push(bind_value(fx, &b.code, b.ty)?);
        }
        self.eval_with(fx, vals)
    }

    /// The fallback with the values of its binds.
    fn eval_with(&self, fx: &mut Fx, vals: Vec<Value>) -> R<Value> {
        let mut env = self.env.clone();
        for (b, v) in self.codes.iter().zip(vals) {
            // A materialized definition's value: seed the definition cache
            // instead of binding a local.
            if let Some((d, primed)) = b.def {
                if !fx.cache().knows(d, primed) && (!primed || fx.s1_complete()) {
                    fx.cache().seed(d, primed, v);
                }
                continue;
            }
            // The value of a LET definition computed once at its LET.
            let x = if tlx_eval::env::is_let_cache_key(b.local) {
                Binding::LetCache(tlx_eval::env::LetCell::with_value(v))
            } else {
                Binding::Val(v)
            };
            env = env.bind(b.local, x);
        }
        for d in &self.deferred {
            env = match d {
                Deferred::Thunk(l, e) => {
                    let t = Thunk { expr: e.clone(), env: env.clone(), memo: None };
                    env.bind(*l, Binding::Thunk(Arc::new(t)))
                }
                Deferred::Once(l, e) => {
                    let t = Thunk { expr: e.clone(), env: env.clone(), memo: Some(Default::default()) };
                    env.bind(*l, Binding::Thunk(Arc::new(t)))
                }
                Deferred::Lambda(l, params, body) => {
                    let o = OpVal::Lambda { params: params.clone(), body: body.clone(), env: env.clone() };
                    env.bind(*l, Binding::Op(o))
                }
                Deferred::OpRef(l, OpRef::Def(d)) if fx.ip.prog.def_is_let(*d) => match &fx.ip.prog.defs[d.idx()].kind {
                    DefKind::Op(body) => {
                        let o =
                            OpVal::Lambda { params: fx.ip.prog.defs[d.idx()].params.clone().into(), body: body.clone(), env: env.clone() };
                        env.bind(*l, Binding::Op(o))
                    }
                    _ => env.bind(*l, Binding::Op(OpVal::Ref(OpRef::Def(*d)))),
                },
                Deferred::OpRef(l, r) => env.bind(*l, Binding::Op(OpVal::Ref(*r))),
            };
        }
        let expr = &self.expr;
        fx.with_ctx(|ip, cx| ip.eval(expr, &env, cx))
    }

    /// `eval`, memoized if the node is pure (`exec::memo`): the key is the
    /// encoding of its binds and of the current-state variables it reads.
    fn eval_memo(&self, fx: &mut Fx) -> R<Value> {
        let ip = fx.ip;
        let probe = memo::probe(fx.memo, self.node, || {
            (memo::analyze(ip, &self.expr, &self.binds, &self.deferred, &self.env), memo::label(ip, &self.expr))
        });
        let memo::Probe::On(vars) = probe else { return self.eval_plain(fx) };
        let mut key = memo::KeyBuf::new();
        let mut keyed = true;
        let mut inputs = Vec::with_capacity(self.codes.len());
        for b in &self.codes {
            // Evaluate every input in order, even on a hit. An encoding
            // may live in scratch overwritten by the next input: snapshot
            // its words into the owned key buffer before continuing.
            let (input, k) = memo_input(fx, &b.code, &mut key.words, keyed)?;
            keyed &= k;
            inputs.push(input);
        }
        if keyed {
            let t = fx.typing();
            vars.iter().for_each(|&i| key.words.extend_from_slice(&fx.s0[t.var_range(i as usize)]));
        }
        if !keyed {
            // Snapshots refer to ranges in key.words; decode them before
            // returning that buffer to the memo (nested calls reuse it).
            let vals = self.input_values(fx, inputs, &key.words);
            memo::unkeyed(self.node, key);
            return self.eval_with(fx, vals);
        }
        if let Some(v) = memo::get(self.node, &key) {
            memo::release(key);
            return Ok(v);
        }
        let t0 = memo::probation_timer(self.node);
        let vals = self.input_values(fx, inputs, &key.words);
        let r = self.eval_with(fx, vals);
        memo::fill(self.node, key, r.as_ref().ok(), t0);
        r
    }

    fn input_values(&self, fx: &Fx, inputs: Vec<MemoInput>, words: &[u64]) -> Vec<Value> {
        inputs
            .into_iter()
            .zip(&self.codes)
            .map(|(input, b)| match input {
                MemoInput::Val(v) => v,
                MemoInput::Enc(range) => {
                    let Ty::Enc(sid) = b.ty else { panic!("internal: encoded code of type {:?}", b.ty) };
                    decode_input(fx, sid, &words[range])
                }
            })
            .collect()
    }
}

/// A memo input, either already boxed or an owned snapshot in the key's
/// word buffer. Even after a lazy input makes the key unusable, subsequent
/// encodings are copied there so that decoding never reads stale scratch.
enum MemoInput {
    Val(Value),
    Enc(std::ops::Range<usize>),
}

fn memo_input(fx: &mut Fx, code: &Code, words: &mut Vec<u64>, keyed: bool) -> R<(MemoInput, bool)> {
    Ok(match code {
        Code::B(f) => {
            let b = f(fx)?;
            if keyed {
                memo::push_bool(b, words);
            }
            (MemoInput::Val(Value::Bool(b)), true)
        }
        Code::I(f) => {
            let i = f(fx)?;
            if keyed {
                memo::push_int(i, words);
            }
            (MemoInput::Val(Value::Int(i)), true)
        }
        Code::E(f, n) => {
            let l = f(fx)?;
            let start = words.len() + 2; // push_words' tag and length
            memo::push_words(fx.get(l, *n), words);
            (MemoInput::Enc(start..start + n), true)
        }
        Code::V(f) => {
            let v = f(fx)?;
            let k = !keyed || memo::push_value(&v, words);
            (MemoInput::Val(v), k)
        }
    })
}

/// The value of an interpreter fallback's input, without memoization.
fn bind_value(fx: &mut Fx, code: &Code, ty: Ty) -> R<Value> {
    Ok(match code {
        Code::B(f) => Value::Bool(f(fx)?),
        Code::I(f) => Value::Int(f(fx)?),
        Code::E(f, n) => {
            let l = f(fx)?;
            let Ty::Enc(sid) = ty else { panic!("internal: encoded code of type {ty:?}") };
            decode_input(fx, sid, fx.get(l, *n))
        }
        Code::V(f) => f(fx)?,
    })
}

fn decode_input(fx: &Fx, sid: ShapeId, words: &[u64]) -> Value {
    #[cfg(test)]
    tests::DECODES.with(|n| n.set(n.get() + 1));

    // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
    unsafe { fx.typing().node(sid).decode_unchecked(words) }
}

#[cfg(test)]
#[path = "interp_tests.rs"]
mod tests;
